import V185TrunkScan23Chunk0819

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4851895 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 1, 6, 2]
def baseStart_4851895 : Nat := 118140960795 + 4851895 * 2 ^ 59
def prefixEnd_4851895 : Nat := 4983230072969 + 3 ^ 40 * 4851895 * 2
def baseEnd_4851895 : Nat := 2491354220146399672199047

theorem tailTrace_4851895 : CollatzResearch.WordTrace tailWord_4851895 prefixEnd_4851895 2491354220146399672199047 := by
  unfold tailWord_4851895
  simp only [CollatzResearch.WordTrace]
  refine ⟨176963148757420527539893139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117975432504947018359928759 176963148757420527539893139)
  ·
    refine ⟨265444723136130791309839709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176963148757420527539893139 265444723136130791309839709)
    ·
      refine ⟨99541771176049046741189891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265444723136130791309839709 99541771176049046741189891)
      ·
        refine ⟨149312656764073570111784837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99541771176049046741189891 149312656764073570111784837)
        ·
          refine ⟨27996123143263794395959657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149312656764073570111784837 27996123143263794395959657)
          ·
            refine ⟨20997092357447845796969743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27996123143263794395959657 20997092357447845796969743)
            ·
              refine ⟨31495638536171768695454615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20997092357447845796969743 31495638536171768695454615)
              ·
                refine ⟨47243457804257653043181923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31495638536171768695454615 47243457804257653043181923)
                ·
                  refine ⟨70865186706386479564772885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47243457804257653043181923 70865186706386479564772885)
                  ·
                    refine ⟨3321805626861866229598729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70865186706386479564772885 3321805626861866229598729)
                    ·
                      refine ⟨2491354220146399672199047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3321805626861866229598729 2491354220146399672199047)
                      ·
                        rfl

theorem cell23_4851895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 6, 2].length) (baseStart_4851895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851895 prefixEnd_4851895 := by exact prefixLift 4851895
  have htrace : WordTrace (prefixWord ++ tailWord_4851895) baseStart_4851895 baseEnd_4851895 := by
    simpa [prefixWord, tailWord_4851895, baseEnd_4851895] using wordTrace_append hprefix tailTrace_4851895
  have hstable : (prefixWord ++ tailWord_4851895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851895).length < 2 ^ (prefixWord ++ tailWord_4851895).sum := by decide
  have hdescent : baseEnd_4851895 < baseStart_4851895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851939 : List Nat := [1, 1, 1, 8, 1, 1, 2, 1, 3, 4]
def baseStart_4851939 : Nat := 118140960795 + 4851939 * 2 ^ 59
def prefixEnd_4851939 : Nat := 4983230072969 + 3 ^ 40 * 4851939 * 2
def baseEnd_4851939 : Nat := 830458937765065833349615

theorem tailTrace_4851939 : CollatzResearch.WordTrace tailWord_4851939 prefixEnd_4851939 830458937765065833349615 := by
  unfold tailWord_4851939
  simp only [CollatzResearch.WordTrace]
  refine ⟨176964753569261123054494871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117976502379507415369663247 176964753569261123054494871)
  ·
    refine ⟨265447130353891684581742307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176964753569261123054494871 265447130353891684581742307)
    ·
      refine ⟨398170695530837526872613461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265447130353891684581742307 398170695530837526872613461)
      ·
        refine ⟨4666062838252002268038439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 398170695530837526872613461 4666062838252002268038439)
        ·
          refine ⟨6999094257378003402057659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4666062838252002268038439 6999094257378003402057659)
          ·
            refine ⟨10498641386067005103086489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6999094257378003402057659 10498641386067005103086489)
            ·
              refine ⟨7873981039550253827314867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10498641386067005103086489 7873981039550253827314867)
              ·
                refine ⟨11810971559325380740972301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7873981039550253827314867 11810971559325380740972301)
                ·
                  refine ⟨4429114334747017777864613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11810971559325380740972301 4429114334747017777864613)
                  ·
                    refine ⟨830458937765065833349615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4429114334747017777864613 830458937765065833349615)
                    ·
                      rfl

theorem cell23_4851939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 4].length) (baseStart_4851939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851939 prefixEnd_4851939 := by exact prefixLift 4851939
  have htrace : WordTrace (prefixWord ++ tailWord_4851939) baseStart_4851939 baseEnd_4851939 := by
    simpa [prefixWord, tailWord_4851939, baseEnd_4851939] using wordTrace_append hprefix tailTrace_4851939
  have hstable : (prefixWord ++ tailWord_4851939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851939).length < 2 ^ (prefixWord ++ tailWord_4851939).sum := by decide
  have hdescent : baseEnd_4851939 < baseStart_4851939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851945 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 7, 1, 3]
def baseStart_4851945 : Nat := 118140960795 + 4851945 * 2 ^ 59
def prefixEnd_4851945 : Nat := 4983230072969 + 3 ^ 40 * 4851945 * 2
def baseEnd_4851945 : Nat := 2491379894179124476573817

theorem tailTrace_4851945 : CollatzResearch.WordTrace tailWord_4851945 prefixEnd_4851945 2491379894179124476573817 := by
  unfold tailWord_4851945
  simp only [CollatzResearch.WordTrace]
  refine ⟨176964972407239386079213289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117976648271492924052808859 176964972407239386079213289)
  ·
    refine ⟨132723729305429539559409967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176964972407239386079213289 132723729305429539559409967)
    ·
      refine ⟨199085593958144309339114951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132723729305429539559409967 199085593958144309339114951)
      ·
        refine ⟨298628390937216464008672427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199085593958144309339114951 298628390937216464008672427)
        ·
          refine ⟨447942586405824696013008641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298628390937216464008672427 447942586405824696013008641)
          ·
            refine ⟨335956939804368522009756481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 447942586405824696013008641 335956939804368522009756481)
            ·
              refine ⟨251967704853276391507317361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335956939804368522009756481 251967704853276391507317361)
              ·
                refine ⟨188975778639957293630488021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251967704853276391507317361 188975778639957293630488021)
                ·
                  refine ⟨4429119811873999069464563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 188975778639957293630488021 4429119811873999069464563)
                  ·
                    refine ⟨6643679717810998604196845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4429119811873999069464563 6643679717810998604196845)
                    ·
                      refine ⟨2491379894179124476573817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6643679717810998604196845 2491379894179124476573817)
                      ·
                        rfl

theorem cell23_4851945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 1, 3].length) (baseStart_4851945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851945 prefixEnd_4851945 := by exact prefixLift 4851945
  have htrace : WordTrace (prefixWord ++ tailWord_4851945) baseStart_4851945 baseEnd_4851945 := by
    simpa [prefixWord, tailWord_4851945, baseEnd_4851945] using wordTrace_append hprefix tailTrace_4851945
  have hstable : (prefixWord ++ tailWord_4851945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851945).length < 2 ^ (prefixWord ++ tailWord_4851945).sum := by decide
  have hdescent : baseEnd_4851945 < baseStart_4851945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851955 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 3, 5, 2]
def baseStart_4851955 : Nat := 118140960795 + 4851955 * 2 ^ 59
def prefixEnd_4851955 : Nat := 4983230072969 + 3 ^ 40 * 4851955 * 2
def baseEnd_4851955 : Nat := 2491385028985669437448771

theorem tailTrace_4851955 : CollatzResearch.WordTrace tailWord_4851955 prefixEnd_4851955 2491385028985669437448771 := by
  unfold tailWord_4851955
  simp only [CollatzResearch.WordTrace]
  refine ⟨176965337137203157787077319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117976891424802105191384879 176965337137203157787077319)
  ·
    refine ⟨265448005705804736680615979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176965337137203157787077319 265448005705804736680615979)
    ·
      refine ⟨398172008558707105020923969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265448005705804736680615979 398172008558707105020923969)
      ·
        refine ⟨298629006419030328765692977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 398172008558707105020923969 298629006419030328765692977)
        ·
          refine ⟨223971754814272746574269733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298629006419030328765692977 223971754814272746574269733)
          ·
            refine ⟨41994704027676139982675575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 223971754814272746574269733 41994704027676139982675575)
            ·
              refine ⟨62992056041514209974013363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41994704027676139982675575 62992056041514209974013363)
              ·
                refine ⟨94488084062271314961020045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62992056041514209974013363 94488084062271314961020045)
                ·
                  refine ⟨35433031523351743110382517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94488084062271314961020045 35433031523351743110382517)
                  ·
                    refine ⟨3321846705314225916598361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35433031523351743110382517 3321846705314225916598361)
                    ·
                      refine ⟨2491385028985669437448771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3321846705314225916598361 2491385028985669437448771)
                      ·
                        rfl

theorem cell23_4851955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 5, 2].length) (baseStart_4851955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851955 prefixEnd_4851955 := by exact prefixLift 4851955
  have htrace : WordTrace (prefixWord ++ tailWord_4851955) baseStart_4851955 baseEnd_4851955 := by
    simpa [prefixWord, tailWord_4851955, baseEnd_4851955] using wordTrace_append hprefix tailTrace_4851955
  have hstable : (prefixWord ++ tailWord_4851955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851955).length < 2 ^ (prefixWord ++ tailWord_4851955).sum := by decide
  have hdescent : baseEnd_4851955 < baseStart_4851955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851962 : List Nat := [3, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3]
def baseStart_4851962 : Nat := 118140960795 + 4851962 * 2 ^ 59
def prefixEnd_4851962 : Nat := 4983230072969 + 3 ^ 40 * 4851962 * 2
def baseEnd_4851962 : Nat := 2491388623350250910061239

theorem tailTrace_4851962 : CollatzResearch.WordTrace tailWord_4851962 prefixEnd_4851962 2491388623350250910061239 := by
  unfold tailWord_4851962
  simp only [CollatzResearch.WordTrace]
  refine ⟨44241398112044449495645535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117977061632118531988388093 44241398112044449495645535)
  ·
    refine ⟨66362097168066674243468303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44241398112044449495645535 66362097168066674243468303)
    ·
      refine ⟨99543145752100011365202455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66362097168066674243468303 99543145752100011365202455)
      ·
        refine ⟨149314718628150017047803683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99543145752100011365202455 149314718628150017047803683)
        ·
          refine ⟨223972077942225025571705525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149314718628150017047803683 223972077942225025571705525)
          ·
            refine ⟨20997382307083596147347393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 223972077942225025571705525 20997382307083596147347393)
            ·
              refine ⟨15748036730312697110510545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20997382307083596147347393 15748036730312697110510545)
              ·
                refine ⟨11811027547734522832882909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15748036730312697110510545 11811027547734522832882909)
                ·
                  refine ⟨4429135330400446062331091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11811027547734522832882909 4429135330400446062331091)
                  ·
                    refine ⟨6643702995600669093496637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4429135330400446062331091 6643702995600669093496637)
                    ·
                      refine ⟨2491388623350250910061239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6643702995600669093496637 2491388623350250910061239)
                      ·
                        rfl

theorem cell23_4851962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3].length) (baseStart_4851962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851962 prefixEnd_4851962 := by exact prefixLift 4851962
  have htrace : WordTrace (prefixWord ++ tailWord_4851962) baseStart_4851962 baseEnd_4851962 := by
    simpa [prefixWord, tailWord_4851962, baseEnd_4851962] using wordTrace_append hprefix tailTrace_4851962
  have hstable : (prefixWord ++ tailWord_4851962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851962).length < 2 ^ (prefixWord ++ tailWord_4851962).sum := by decide
  have hdescent : baseEnd_4851962 < baseStart_4851962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851995 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 4, 4]
def baseStart_4851995 : Nat := 118140960795 + 4851995 * 2 ^ 59
def prefixEnd_4851995 : Nat := 4983230072969 + 3 ^ 40 * 4851995 * 2
def baseEnd_4851995 : Nat := 830468522737283093649529

theorem tailTrace_4851995 : CollatzResearch.WordTrace tailWord_4851995 prefixEnd_4851995 830468522737283093649529 := by
  unfold tailWord_4851995
  simp only [CollatzResearch.WordTrace]
  refine ⟨176966796057058244618533439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117977864038038829745688959 176966796057058244618533439)
  ·
    refine ⟨265450194085587366927800159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176966796057058244618533439 265450194085587366927800159)
    ·
      refine ⟨398175291128381050391700239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265450194085587366927800159 398175291128381050391700239)
      ·
        refine ⟨597262936692571575587550359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398175291128381050391700239 597262936692571575587550359)
        ·
          refine ⟨895894405038857363381325539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597262936692571575587550359 895894405038857363381325539)
          ·
            refine ⟨1343841607558286045071988309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 895894405038857363381325539 1343841607558286045071988309)
            ·
              refine ⟨15748143838573664590687363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1343841607558286045071988309 15748143838573664590687363)
              ·
                refine ⟨23622215757860496886031045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15748143838573664590687363 23622215757860496886031045)
                ·
                  refine ⟨4429165454598843166130821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23622215757860496886031045 4429165454598843166130821)
                  ·
                    refine ⟨830468522737283093649529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4429165454598843166130821 830468522737283093649529)
                    ·
                      rfl

theorem cell23_4851995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 4].length) (baseStart_4851995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851995 prefixEnd_4851995 := by exact prefixLift 4851995
  have htrace : WordTrace (prefixWord ++ tailWord_4851995) baseStart_4851995 baseEnd_4851995 := by
    simpa [prefixWord, tailWord_4851995, baseEnd_4851995] using wordTrace_append hprefix tailTrace_4851995
  have hstable : (prefixWord ++ tailWord_4851995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851995).length < 2 ^ (prefixWord ++ tailWord_4851995).sum := by decide
  have hdescent : baseEnd_4851995 < baseStart_4851995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852025 : List Nat := [1, 2, 1, 6, 1, 1, 2, 9]
def baseStart_4852025 : Nat := 118140960795 + 4852025 * 2 ^ 59
def prefixEnd_4852025 : Nat := 4983230072969 + 3 ^ 40 * 4852025 * 2
def baseEnd_4852025 : Nat := 92274850838203117169387

theorem tailTrace_4852025 : CollatzResearch.WordTrace tailWord_4852025 prefixEnd_4852025 92274850838203117169387 := by
  unfold tailWord_4852025
  simp only [CollatzResearch.WordTrace]
  refine ⟨176967890246949559742125529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117978593497966373161417019 176967890246949559742125529)
  ·
    refine ⟨132725917685212169806594147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176967890246949559742125529 132725917685212169806594147)
    ·
      refine ⟨199088876527818254709891221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132725917685212169806594147 199088876527818254709891221)
      ·
        refine ⟨9332291087241480689526151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 199088876527818254709891221 9332291087241480689526151)
        ·
          refine ⟨13998436630862221034289227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9332291087241480689526151 13998436630862221034289227)
          ·
            refine ⟨20997654946293331551433841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13998436630862221034289227 20997654946293331551433841)
            ·
              refine ⟨15748241209719998663575381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20997654946293331551433841 15748241209719998663575381)
              ·
                refine ⟨92274850838203117169387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15748241209719998663575381 92274850838203117169387)
                ·
                  rfl

theorem cell23_4852025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 9].length) (baseStart_4852025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852025 prefixEnd_4852025 := by exact prefixLift 4852025
  have htrace : WordTrace (prefixWord ++ tailWord_4852025) baseStart_4852025 baseEnd_4852025 := by
    simpa [prefixWord, tailWord_4852025, baseEnd_4852025] using wordTrace_append hprefix tailTrace_4852025
  have hstable : (prefixWord ++ tailWord_4852025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852025).length < 2 ^ (prefixWord ++ tailWord_4852025).sum := by decide
  have hdescent : baseEnd_4852025 < baseStart_4852025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852035 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 3]
def baseStart_4852035 : Nat := 118140960795 + 4852035 * 2 ^ 59
def prefixEnd_4852035 : Nat := 4983230072969 + 3 ^ 40 * 4852035 * 2
def baseEnd_4852035 : Nat := 2491426107438029124448403

theorem tailTrace_4852035 : CollatzResearch.WordTrace tailWord_4852035 prefixEnd_4852035 2491426107438029124448403 := by
  unfold tailWord_4852035
  simp only [CollatzResearch.WordTrace]
  refine ⟨176968254976913331449989559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117978836651275554299993039 176968254976913331449989559)
  ·
    refine ⟨265452382465369997174984339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176968254976913331449989559 265452382465369997174984339)
    ·
      refine ⟨398178573698054995762476509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265452382465369997174984339 398178573698054995762476509)
      ·
        refine ⟨149316965136770623410928691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 398178573698054995762476509 149316965136770623410928691)
        ·
          refine ⟨223975447705155935116393037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149316965136770623410928691 223975447705155935116393037)
          ·
            refine ⟨83990792889433475668647389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 223975447705155935116393037 83990792889433475668647389)
            ·
              refine ⟨31496547333537553375742771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83990792889433475668647389 31496547333537553375742771)
              ·
                refine ⟨47244821000306330063614157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31496547333537553375742771 47244821000306330063614157)
                ·
                  refine ⟨17716807875114873773855309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47244821000306330063614157 17716807875114873773855309)
                  ·
                    refine ⟨6643802953168077665195741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17716807875114873773855309 6643802953168077665195741)
                    ·
                      refine ⟨2491426107438029124448403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6643802953168077665195741 2491426107438029124448403)
                      ·
                        rfl

theorem cell23_4852035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 3].length) (baseStart_4852035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852035 prefixEnd_4852035 := by exact prefixLift 4852035
  have htrace : WordTrace (prefixWord ++ tailWord_4852035) baseStart_4852035 baseEnd_4852035 := by
    simpa [prefixWord, tailWord_4852035, baseEnd_4852035] using wordTrace_append hprefix tailTrace_4852035
  have hstable : (prefixWord ++ tailWord_4852035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852035).length < 2 ^ (prefixWord ++ tailWord_4852035).sum := by decide
  have hdescent : baseEnd_4852035 < baseStart_4852035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852039 : List Nat := [1, 1, 4, 1, 2, 2, 5, 1, 1, 2, 3]
def baseStart_4852039 : Nat := 118140960795 + 4852039 * 2 ^ 59
def prefixEnd_4852039 : Nat := 4983230072969 + 3 ^ 40 * 4852039 * 2
def baseEnd_4852039 : Nat := 2491428161360647108798385

theorem tailTrace_4852039 : CollatzResearch.WordTrace tailWord_4852039 prefixEnd_4852039 2491428161360647108798385 := by
  unfold tailWord_4852039
  simp only [CollatzResearch.WordTrace]
  refine ⟨176968400868898840133135171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117978933912599226755423447 176968400868898840133135171)
  ·
    refine ⟨265452601303348260199702757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176968400868898840133135171 265452601303348260199702757)
    ·
      refine ⟨49772362744377798787444267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 265452601303348260199702757 49772362744377798787444267)
      ·
        refine ⟨74658544116566698181166401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49772362744377798787444267 74658544116566698181166401)
        ·
          refine ⟨55993908087425023635874801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74658544116566698181166401 55993908087425023635874801)
          ·
            refine ⟨41995431065568767726906101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55993908087425023635874801 41995431065568767726906101)
            ·
              refine ⟨3937071662397071974397447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41995431065568767726906101 3937071662397071974397447)
              ·
                refine ⟨5905607493595607961596171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3937071662397071974397447 5905607493595607961596171)
                ·
                  refine ⟨8858411240393411942394257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5905607493595607961596171 8858411240393411942394257)
                  ·
                    refine ⟨6643808430295058956795693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8858411240393411942394257 6643808430295058956795693)
                    ·
                      refine ⟨2491428161360647108798385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6643808430295058956795693 2491428161360647108798385)
                      ·
                        rfl

theorem cell23_4852039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 1, 2, 3].length) (baseStart_4852039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852039 prefixEnd_4852039 := by exact prefixLift 4852039
  have htrace : WordTrace (prefixWord ++ tailWord_4852039) baseStart_4852039 baseEnd_4852039 := by
    simpa [prefixWord, tailWord_4852039, baseEnd_4852039] using wordTrace_append hprefix tailTrace_4852039
  have hstable : (prefixWord ++ tailWord_4852039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852039).length < 2 ^ (prefixWord ++ tailWord_4852039).sum := by decide
  have hdescent : baseEnd_4852039 < baseStart_4852039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852053 : List Nat := [1, 3, 2, 2, 4, 1, 1, 4, 1, 2, 2]
def baseStart_4852053 : Nat := 118140960795 + 4852053 * 2 ^ 59
def prefixEnd_4852053 : Nat := 4983230072969 + 3 ^ 40 * 4852053 * 2
def baseEnd_4852053 : Nat := 2491435350089810054023321

theorem tailTrace_4852053 : CollatzResearch.WordTrace tailWord_4852053 prefixEnd_4852053 2491435350089810054023321 := by
  unfold tailWord_4852053
  simp only [CollatzResearch.WordTrace]
  refine ⟨176968911490848120524144813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117979274327232080349429875 176968911490848120524144813)
  ·
    refine ⟨66363341809068045196554305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176968911490848120524144813 66363341809068045196554305)
    ·
      refine ⟨49772506356801033897415729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66363341809068045196554305 49772506356801033897415729)
      ·
        refine ⟨37329379767600775423061797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49772506356801033897415729 37329379767600775423061797)
        ·
          refine ⟨6999258706425145391824087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37329379767600775423061797 6999258706425145391824087)
          ·
            refine ⟨10498888059637718087736131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6999258706425145391824087 10498888059637718087736131)
            ·
              refine ⟨15748332089456577131604197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10498888059637718087736131 15748332089456577131604197)
              ·
                refine ⟨2952812266773108212175787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15748332089456577131604197 2952812266773108212175787)
                ·
                  refine ⟨4429218400159662318263681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2952812266773108212175787 4429218400159662318263681)
                  ·
                    refine ⟨3321913800119746738697761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4429218400159662318263681 3321913800119746738697761)
                    ·
                      refine ⟨2491435350089810054023321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3321913800119746738697761 2491435350089810054023321)
                      ·
                        rfl

theorem cell23_4852053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_4852053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852053 prefixEnd_4852053 := by exact prefixLift 4852053
  have htrace : WordTrace (prefixWord ++ tailWord_4852053) baseStart_4852053 baseEnd_4852053 := by
    simpa [prefixWord, tailWord_4852053, baseEnd_4852053] using wordTrace_append hprefix tailTrace_4852053
  have hstable : (prefixWord ++ tailWord_4852053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852053).length < 2 ^ (prefixWord ++ tailWord_4852053).sum := by decide
  have hdescent : baseEnd_4852053 < baseStart_4852053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852069 : List Nat := [1, 3, 1, 3, 1, 3, 2, 3, 2, 1, 3]
def baseStart_4852069 : Nat := 118140960795 + 4852069 * 2 ^ 59
def prefixEnd_4852069 : Nat := 4983230072969 + 3 ^ 40 * 4852069 * 2
def baseEnd_4852069 : Nat := 2491443565780281991423247

theorem tailTrace_4852069 : CollatzResearch.WordTrace tailWord_4852069 prefixEnd_4852069 2491443565780281991423247 := by
  unfold tailWord_4852069
  simp only [CollatzResearch.WordTrace]
  refine ⟨176969495058790155256727261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117979663372526770171151507 176969495058790155256727261)
  ·
    refine ⟨66363560647046308221272723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176969495058790155256727261 66363560647046308221272723)
    ·
      refine ⟨99545340970569462331909085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66363560647046308221272723 99545340970569462331909085)
      ·
        refine ⟨37329502863963548374465907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99545340970569462331909085 37329502863963548374465907)
        ·
          refine ⟨55994254295945322561698861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37329502863963548374465907 55994254295945322561698861)
          ·
            refine ⟨20997845360979495960637073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55994254295945322561698861 20997845360979495960637073)
            ·
              refine ⟨15748384020734621970477805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20997845360979495960637073 15748384020734621970477805)
              ·
                refine ⟨5905644007775483238929177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15748384020734621970477805 5905644007775483238929177)
                ·
                  refine ⟨4429233005831612429196883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5905644007775483238929177 4429233005831612429196883)
                  ·
                    refine ⟨6643849508747418643795325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4429233005831612429196883 6643849508747418643795325)
                    ·
                      refine ⟨2491443565780281991423247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6643849508747418643795325 2491443565780281991423247)
                      ·
                        rfl

theorem cell23_4852069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_4852069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852069 prefixEnd_4852069 := by exact prefixLift 4852069
  have htrace : WordTrace (prefixWord ++ tailWord_4852069) baseStart_4852069 baseEnd_4852069 := by
    simpa [prefixWord, tailWord_4852069, baseEnd_4852069] using wordTrace_append hprefix tailTrace_4852069
  have hstable : (prefixWord ++ tailWord_4852069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852069).length < 2 ^ (prefixWord ++ tailWord_4852069).sum := by decide
  have hdescent : baseEnd_4852069 < baseStart_4852069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852092 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 3, 4, 2]
def baseStart_4852092 : Nat := 118140960795 + 4852092 * 2 ^ 59
def prefixEnd_4852092 : Nat := 4983230072969 + 3 ^ 40 * 4852092 * 2
def baseEnd_4852092 : Nat := 2491455375835335401435641

theorem tailTrace_4852092 : CollatzResearch.WordTrace tailWord_4852092 prefixEnd_4852092 2491455375835335401435641 := by
  unfold tailWord_4852092
  simp only [CollatzResearch.WordTrace]
  refine ⟨88485166968853415092407265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117980222625137886789876353 88485166968853415092407265)
  ·
    refine ⟨66363875226640061319305449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88485166968853415092407265 66363875226640061319305449)
    ·
      refine ⟨49772906419980045989479087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66363875226640061319305449 49772906419980045989479087)
      ·
        refine ⟨74659359629970068984218631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49772906419980045989479087 74659359629970068984218631)
        ·
          refine ⟨111989039444955103476327947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74659359629970068984218631 111989039444955103476327947)
          ·
            refine ⟨167983559167432655214491921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111989039444955103476327947 167983559167432655214491921)
            ·
              refine ⟨125987669375574491410868941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167983559167432655214491921 125987669375574491410868941)
              ·
                refine ⟨47245376015840434279075853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125987669375574491410868941 47245376015840434279075853)
                ·
                  refine ⟨17717016005940162854653445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47245376015840434279075853 17717016005940162854653445)
                  ·
                    refine ⟨3321940501113780535247521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17717016005940162854653445 3321940501113780535247521)
                    ·
                      refine ⟨2491455375835335401435641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3321940501113780535247521 2491455375835335401435641)
                      ·
                        rfl

theorem cell23_4852092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 3, 4, 2].length) (baseStart_4852092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852092 prefixEnd_4852092 := by exact prefixLift 4852092
  have htrace : WordTrace (prefixWord ++ tailWord_4852092) baseStart_4852092 baseEnd_4852092 := by
    simpa [prefixWord, tailWord_4852092, baseEnd_4852092] using wordTrace_append hprefix tailTrace_4852092
  have hstable : (prefixWord ++ tailWord_4852092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852092).length < 2 ^ (prefixWord ++ tailWord_4852092).sum := by decide
  have hdescent : baseEnd_4852092 < baseStart_4852092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852095 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 3]
def baseStart_4852095 : Nat := 118140960795 + 4852095 * 2 ^ 59
def prefixEnd_4852095 : Nat := 4983230072969 + 3 ^ 40 * 4852095 * 2
def baseEnd_4852095 : Nat := 2491456916277298889698127

theorem tailTrace_4852095 : CollatzResearch.WordTrace tailWord_4852095 prefixEnd_4852095 2491456916277298889698127 := by
  unfold tailWord_4852095
  simp only [CollatzResearch.WordTrace]
  refine ⟨176970443356695961697173739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117980295571130641131449159 176970443356695961697173739)
  ·
    refine ⟨265455665035043942545760609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176970443356695961697173739 265455665035043942545760609)
    ·
      refine ⟨199091748776282956909320457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265455665035043942545760609 199091748776282956909320457)
      ·
        refine ⟨149318811582212217681990343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199091748776282956909320457 149318811582212217681990343)
        ·
          refine ⟨223978217373318326522985515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149318811582212217681990343 223978217373318326522985515)
          ·
            refine ⟨335967326059977489784478273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223978217373318326522985515 335967326059977489784478273)
            ·
              refine ⟨251975494544983117338358705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335967326059977489784478273 251975494544983117338358705)
              ·
                refine ⟨188981620908737338003769029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251975494544983117338358705 188981620908737338003769029)
                ·
                  refine ⟨35434053920388250875706693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 188981620908737338003769029 35434053920388250875706693)
                  ·
                    refine ⟨6643885110072797039195005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35434053920388250875706693 6643885110072797039195005)
                    ·
                      refine ⟨2491456916277298889698127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6643885110072797039195005 2491456916277298889698127)
                      ·
                        rfl

theorem cell23_4852095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 3].length) (baseStart_4852095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852095 prefixEnd_4852095 := by exact prefixLift 4852095
  have htrace : WordTrace (prefixWord ++ tailWord_4852095) baseStart_4852095 baseEnd_4852095 := by
    simpa [prefixWord, tailWord_4852095, baseEnd_4852095] using wordTrace_append hprefix tailTrace_4852095
  have hstable : (prefixWord ++ tailWord_4852095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852095).length < 2 ^ (prefixWord ++ tailWord_4852095).sum := by decide
  have hdescent : baseEnd_4852095 < baseStart_4852095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852122 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4]
def baseStart_4852122 : Nat := 118140960795 + 4852122 * 2 ^ 59
def prefixEnd_4852122 : Nat := 4983230072969 + 3 ^ 40 * 4852122 * 2
def baseEnd_4852122 : Nat := 2491470780254970284060503

theorem tailTrace_4852122 : CollatzResearch.WordTrace tailWord_4852122 prefixEnd_4852122 2491470780254970284060503 := by
  unfold tailWord_4852122
  simp only [CollatzResearch.WordTrace]
  refine ⟨44242857031899536327101655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117980952085065430205604413 44242857031899536327101655)
  ·
    refine ⟨66364285547849304490652483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44242857031899536327101655 66364285547849304490652483)
    ·
      refine ⟨99546428321773956735978725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66364285547849304490652483 99546428321773956735978725)
      ·
        refine ⟨18664955310332616887996011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99546428321773956735978725 18664955310332616887996011)
        ·
          refine ⟨27997432965498925331994017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18664955310332616887996011 27997432965498925331994017)
          ·
            refine ⟨20998074724124193998995513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27997432965498925331994017 20998074724124193998995513)
            ·
              refine ⟨15748556043093145499246635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20998074724124193998995513 15748556043093145499246635)
              ·
                refine ⟨23622834064639718248869953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15748556043093145499246635 23622834064639718248869953)
                ·
                  refine ⟨17717125548479788686652465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23622834064639718248869953 17717125548479788686652465)
                  ·
                    refine ⟨13287844161359841514989349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17717125548479788686652465 13287844161359841514989349)
                    ·
                      refine ⟨2491470780254970284060503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13287844161359841514989349 2491470780254970284060503)
                      ·
                        rfl

theorem cell23_4852122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_4852122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852122 prefixEnd_4852122 := by exact prefixLift 4852122
  have htrace : WordTrace (prefixWord ++ tailWord_4852122) baseStart_4852122 baseEnd_4852122 := by
    simpa [prefixWord, tailWord_4852122, baseEnd_4852122] using wordTrace_append hprefix tailTrace_4852122
  have hstable : (prefixWord ++ tailWord_4852122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852122).length < 2 ^ (prefixWord ++ tailWord_4852122).sum := by decide
  have hdescent : baseEnd_4852122 < baseStart_4852122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852152 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 1, 7, 2]
def baseStart_4852152 : Nat := 118140960795 + 4852152 * 2 ^ 59
def prefixEnd_4852152 : Nat := 4983230072969 + 3 ^ 40 * 4852152 * 2
def baseEnd_4852152 : Nat := 2491486184674605166685365

theorem tailTrace_4852152 : CollatzResearch.WordTrace tailWord_4852152 prefixEnd_4852152 2491486184674605166685365 := by
  unfold tailWord_4852152
  simp only [CollatzResearch.WordTrace]
  refine ⟨88486261158744730215999355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117981681544992973621332473 88486261158744730215999355)
  ·
    refine ⟨132729391738117095323999033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88486261158744730215999355 132729391738117095323999033)
    ·
      refine ⟨99547043803587821492999275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132729391738117095323999033 99547043803587821492999275)
      ·
        refine ⟨149320565705381732239498913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99547043803587821492999275 149320565705381732239498913)
        ·
          refine ⟨111990424279036299179624185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149320565705381732239498913 111990424279036299179624185)
          ·
            refine ⟨83992818209277224384718139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111990424279036299179624185 83992818209277224384718139)
            ·
              refine ⟨125989227313915836577077209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83992818209277224384718139 125989227313915836577077209)
              ·
                refine ⟨94491920485436877432807907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125989227313915836577077209 94491920485436877432807907)
                ·
                  refine ⟨141737880728155316149211861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94491920485436877432807907 141737880728155316149211861)
                  ·
                    refine ⟨3321981579566140222247153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 141737880728155316149211861 3321981579566140222247153)
                    ·
                      refine ⟨2491486184674605166685365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3321981579566140222247153 2491486184674605166685365)
                      ·
                        rfl

theorem cell23_4852152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 7, 2].length) (baseStart_4852152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852152 prefixEnd_4852152 := by exact prefixLift 4852152
  have htrace : WordTrace (prefixWord ++ tailWord_4852152) baseStart_4852152 baseEnd_4852152 := by
    simpa [prefixWord, tailWord_4852152, baseEnd_4852152] using wordTrace_append hprefix tailTrace_4852152
  have hstable : (prefixWord ++ tailWord_4852152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852152).length < 2 ^ (prefixWord ++ tailWord_4852152).sum := by decide
  have hdescent : baseEnd_4852152 < baseStart_4852152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852165 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 2, 7, 4]
def baseStart_4852165 : Nat := 118140960795 + 4852165 * 2 ^ 59
def prefixEnd_4852165 : Nat := 4983230072969 + 3 ^ 40 * 4852165 * 2
def baseEnd_4852165 : Nat := 2491492859923113615822805

theorem tailTrace_4852165 : CollatzResearch.WordTrace tailWord_4852165 prefixEnd_4852165 2491492859923113615822805 := by
  unfold tailWord_4852165
  simp only [CollatzResearch.WordTrace]
  refine ⟨176972996466442363652221949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117981997644294909101481299 176972996466442363652221949)
  ·
    refine ⟨66364873674915886369583231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176972996466442363652221949 66364873674915886369583231)
    ·
      refine ⟨99547310512373829554374847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66364873674915886369583231 99547310512373829554374847)
      ·
        refine ⟨149320965768560744331562271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99547310512373829554374847 149320965768560744331562271)
        ·
          refine ⟨223981448652841116497343407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149320965768560744331562271 223981448652841116497343407)
          ·
            refine ⟨335972172979261674746015111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223981448652841116497343407 335972172979261674746015111)
            ·
              refine ⟨503958259468892512119022667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335972172979261674746015111 503958259468892512119022667)
              ·
                refine ⟨755937389203338768178534001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 503958259468892512119022667 755937389203338768178534001)
                ·
                  refine ⟨566953041902504076133900501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 755937389203338768178534001 566953041902504076133900501)
                  ·
                    refine ⟨13287961919589939284388293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 566953041902504076133900501 13287961919589939284388293)
                    ·
                      refine ⟨2491492859923113615822805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13287961919589939284388293 2491492859923113615822805)
                      ·
                        rfl

theorem cell23_4852165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_4852165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852165 prefixEnd_4852165 := by exact prefixLift 4852165
  have htrace : WordTrace (prefixWord ++ tailWord_4852165) baseStart_4852165 baseEnd_4852165 := by
    simpa [prefixWord, tailWord_4852165, baseEnd_4852165] using wordTrace_append hprefix tailTrace_4852165
  have hstable : (prefixWord ++ tailWord_4852165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852165).length < 2 ^ (prefixWord ++ tailWord_4852165).sum := by decide
  have hdescent : baseEnd_4852165 < baseStart_4852165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852192 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 5, 4]
def baseStart_4852192 : Nat := 118140960795 + 4852192 * 2 ^ 59
def prefixEnd_4852192 : Nat := 4983230072969 + 3 ^ 40 * 4852192 * 2
def baseEnd_4852192 : Nat := 830502241300261670061727

theorem tailTrace_4852192 : CollatzResearch.WordTrace tailWord_4852192 prefixEnd_4852192 830502241300261670061727 := by
  unfold tailWord_4852192
  simp only [CollatzResearch.WordTrace]
  refine ⟨88486990618672273631727415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117982654158229698175636553 88486990618672273631727415)
  ·
    refine ⟨132730485928008410447591123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88486990618672273631727415 132730485928008410447591123)
    ·
      refine ⟨199095728892012615671386685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132730485928008410447591123 199095728892012615671386685)
      ·
        refine ⟨74660898334504730876770007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199095728892012615671386685 74660898334504730876770007)
        ·
          refine ⟨111991347501757096315155011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74660898334504730876770007 111991347501757096315155011)
          ·
            refine ⟨167987021252635644472732517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111991347501757096315155011 167987021252635644472732517)
            ·
              refine ⟨31497566484869183338637347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 167987021252635644472732517 31497566484869183338637347)
              ·
                refine ⟨47246349727303775007956021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31497566484869183338637347 47246349727303775007956021)
                ·
                  refine ⟨4429345286934728906995877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47246349727303775007956021 4429345286934728906995877)
                  ·
                    refine ⟨830502241300261670061727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4429345286934728906995877 830502241300261670061727)
                    ·
                      rfl

theorem cell23_4852192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 5, 4].length) (baseStart_4852192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852192 prefixEnd_4852192 := by exact prefixLift 4852192
  have htrace : WordTrace (prefixWord ++ tailWord_4852192) baseStart_4852192 baseEnd_4852192 := by
    simpa [prefixWord, tailWord_4852192, baseEnd_4852192] using wordTrace_append hprefix tailTrace_4852192
  have hstable : (prefixWord ++ tailWord_4852192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852192).length < 2 ^ (prefixWord ++ tailWord_4852192).sum := by decide
  have hdescent : baseEnd_4852192 < baseStart_4852192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852199 : List Nat := [1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 4]
def baseStart_4852199 : Nat := 118140960795 + 4852199 * 2 ^ 59
def prefixEnd_4852199 : Nat := 4983230072969 + 3 ^ 40 * 4852199 * 2
def baseEnd_4852199 : Nat := 2491510318265366482797649

theorem tailTrace_4852199 : CollatzResearch.WordTrace tailWord_4852199 prefixEnd_4852199 2491510318265366482797649 := by
  unfold tailWord_4852199
  simp only [CollatzResearch.WordTrace]
  refine ⟨176974236548319187458959651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117982824365546124972639767 176974236548319187458959651)
  ·
    refine ⟨265461354822478781188439477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176974236548319187458959651 265461354822478781188439477)
    ·
      refine ⟨24887002014607385736416201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 265461354822478781188439477 24887002014607385736416201)
      ·
        refine ⟨18665251510955539302312151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24887002014607385736416201 18665251510955539302312151)
        ·
          refine ⟨27997877266433308953468227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18665251510955539302312151 27997877266433308953468227)
          ·
            refine ⟨41996815899649963430202341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27997877266433308953468227 41996815899649963430202341)
            ·
              refine ⟨7874402981184368143162939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41996815899649963430202341 7874402981184368143162939)
              ·
                refine ⟨11811604471776552214744409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7874402981184368143162939 11811604471776552214744409)
                ·
                  refine ⟨8858703353832414161058307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11811604471776552214744409 8858703353832414161058307)
                  ·
                    refine ⟨13288055030748621241587461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8858703353832414161058307 13288055030748621241587461)
                    ·
                      refine ⟨2491510318265366482797649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13288055030748621241587461 2491510318265366482797649)
                      ·
                        rfl

theorem cell23_4852199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_4852199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852199 prefixEnd_4852199 := by exact prefixLift 4852199
  have htrace : WordTrace (prefixWord ++ tailWord_4852199) baseStart_4852199 baseEnd_4852199 := by
    simpa [prefixWord, tailWord_4852199, baseEnd_4852199] using wordTrace_append hprefix tailTrace_4852199
  have hstable : (prefixWord ++ tailWord_4852199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852199).length < 2 ^ (prefixWord ++ tailWord_4852199).sum := by decide
  have hdescent : baseEnd_4852199 < baseStart_4852199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852232 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 2, 5, 3]
def baseStart_4852232 : Nat := 118140960795 + 4852232 * 2 ^ 59
def prefixEnd_4852232 : Nat := 4983230072969 + 3 ^ 40 * 4852232 * 2
def baseEnd_4852232 : Nat := 2491527263126964853684997

theorem tailTrace_4852232 : CollatzResearch.WordTrace tailWord_4852232 prefixEnd_4852232 2491527263126964853684997 := by
  unfold tailWord_4852232
  simp only [CollatzResearch.WordTrace]
  refine ⟨88487720078599817047455475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117983626771466422729940633 88487720078599817047455475)
  ·
    refine ⟨132731580117899725571183213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88487720078599817047455475 132731580117899725571183213)
    ·
      refine ⟨49774342544212397089193705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132731580117899725571183213 49774342544212397089193705)
      ·
        refine ⟨37330756908159297816895279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49774342544212397089193705 37330756908159297816895279)
        ·
          refine ⟨55996135362238946725342919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37330756908159297816895279 55996135362238946725342919)
          ·
            refine ⟨83994203043358420088014379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55996135362238946725342919 83994203043358420088014379)
            ·
              refine ⟨125991304565037630132021569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83994203043358420088014379 125991304565037630132021569)
              ·
                refine ⟨94493478423778222599016177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125991304565037630132021569 94493478423778222599016177)
                ·
                  refine ⟨70870108817833666949262133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94493478423778222599016177 70870108817833666949262133)
                  ·
                    refine ⟨6644072701671906276493325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70870108817833666949262133 6644072701671906276493325)
                    ·
                      refine ⟨2491527263126964853684997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6644072701671906276493325 2491527263126964853684997)
                      ·
                        rfl

theorem cell23_4852232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_4852232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852232 prefixEnd_4852232 := by exact prefixLift 4852232
  have htrace : WordTrace (prefixWord ++ tailWord_4852232) baseStart_4852232 baseEnd_4852232 := by
    simpa [prefixWord, tailWord_4852232, baseEnd_4852232] using wordTrace_append hprefix tailTrace_4852232
  have hstable : (prefixWord ++ tailWord_4852232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852232).length < 2 ^ (prefixWord ++ tailWord_4852232).sum := by decide
  have hdescent : baseEnd_4852232 < baseStart_4852232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852249 : List Nat := [1, 2, 1, 2, 1, 1, 2, 6, 3, 1, 3]
def baseStart_4852249 : Nat := 118140960795 + 4852249 * 2 ^ 59
def prefixEnd_4852249 : Nat := 4983230072969 + 3 ^ 40 * 4852249 * 2
def baseEnd_4852249 : Nat := 2491535992298091287172419

theorem tailTrace_4852249 : CollatzResearch.WordTrace tailWord_4852249 prefixEnd_4852249 2491535992298091287172419 := by
  unfold tailWord_4852249
  simp only [CollatzResearch.WordTrace]
  refine ⟨176976060198138045998279801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117984040132092030665519867 176976060198138045998279801)
  ·
    refine ⟨132732045148603534498709851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176976060198138045998279801 132732045148603534498709851)
    ·
      refine ⟨199098067722905301748064777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132732045148603534498709851 199098067722905301748064777)
      ·
        refine ⟨149323550792178976311048583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199098067722905301748064777 149323550792178976311048583)
        ·
          refine ⟨223985326188268464466572875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149323550792178976311048583 223985326188268464466572875)
          ·
            refine ⟨335977989282402696699859313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223985326188268464466572875 335977989282402696699859313)
            ·
              refine ⟨251983491961802022524894485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335977989282402696699859313 251983491961802022524894485)
              ·
                refine ⟨11811726185709469805854429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 251983491961802022524894485 11811726185709469805854429)
                ·
                  refine ⟨4429397319641051177195411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11811726185709469805854429 4429397319641051177195411)
                  ·
                    refine ⟨6644095979461576765793117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4429397319641051177195411 6644095979461576765793117)
                    ·
                      refine ⟨2491535992298091287172419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6644095979461576765793117 2491535992298091287172419)
                      ·
                        rfl

theorem cell23_4852249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 1, 3].length) (baseStart_4852249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852249 prefixEnd_4852249 := by exact prefixLift 4852249
  have htrace : WordTrace (prefixWord ++ tailWord_4852249) baseStart_4852249 baseEnd_4852249 := by
    simpa [prefixWord, tailWord_4852249, baseEnd_4852249] using wordTrace_append hprefix tailTrace_4852249
  have hstable : (prefixWord ++ tailWord_4852249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852249).length < 2 ^ (prefixWord ++ tailWord_4852249).sum := by decide
  have hdescent : baseEnd_4852249 < baseStart_4852249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852260 : List Nat := [2, 3, 1, 5, 1, 1, 2, 3, 1, 4]
def baseStart_4852260 : Nat := 118140960795 + 4852260 * 2 ^ 59
def prefixEnd_4852260 : Nat := 4983230072969 + 3 ^ 40 * 4852260 * 2
def baseEnd_4852260 : Nat := 830513880195096914711623

theorem tailTrace_4852260 : CollatzResearch.WordTrace tailWord_4852260 prefixEnd_4852260 830513880195096914711623 := by
  unfold tailWord_4852260
  simp only [CollatzResearch.WordTrace]
  refine ⟨88488230700549097438465117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117984307600732129917953489 88488230700549097438465117)
  ·
    refine ⟨33183086512705911539424419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88488230700549097438465117 33183086512705911539424419)
    ·
      refine ⟨49774629769058867309136629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33183086512705911539424419 49774629769058867309136629)
      ·
        refine ⟨4666371540849268810231559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49774629769058867309136629 4666371540849268810231559)
        ·
          refine ⟨6999557311273903215347339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4666371540849268810231559 6999557311273903215347339)
          ·
            refine ⟨10499335966910854823021009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6999557311273903215347339 10499335966910854823021009)
            ·
              refine ⟨7874501975183141117265757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10499335966910854823021009 7874501975183141117265757)
              ·
                refine ⟨2952938240693677918974659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7874501975183141117265757 2952938240693677918974659)
                ·
                  refine ⟨4429407361040516878461989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2952938240693677918974659 4429407361040516878461989)
                  ·
                    refine ⟨830513880195096914711623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4429407361040516878461989 830513880195096914711623)
                    ·
                      rfl

theorem cell23_4852260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_4852260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852260 prefixEnd_4852260 := by exact prefixLift 4852260
  have htrace : WordTrace (prefixWord ++ tailWord_4852260) baseStart_4852260 baseEnd_4852260 := by
    simpa [prefixWord, tailWord_4852260, baseEnd_4852260] using wordTrace_append hprefix tailTrace_4852260
  have hstable : (prefixWord ++ tailWord_4852260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852260).length < 2 ^ (prefixWord ++ tailWord_4852260).sum := by decide
  have hdescent : baseEnd_4852260 < baseStart_4852260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852299 : List Nat := [1, 1, 1, 1, 3, 1, 4, 5, 2, 4]
def baseStart_4852299 : Nat := 118140960795 + 4852299 * 2 ^ 59
def prefixEnd_4852299 : Nat := 4983230072969 + 3 ^ 40 * 4852299 * 2
def baseEnd_4852299 : Nat := 830520555443605363849063

theorem tailTrace_4852299 : CollatzResearch.WordTrace tailWord_4852299 prefixEnd_4852299 830520555443605363849063 := by
  unfold tailWord_4852299
  simp only [CollatzResearch.WordTrace]
  refine ⟨176977883847956904537599951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117985255898637936358399967 176977883847956904537599951)
  ·
    refine ⟨265466825771935356806399927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176977883847956904537599951 265466825771935356806399927)
    ·
      refine ⟨398200238657903035209599891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265466825771935356806399927 398200238657903035209599891)
      ·
        refine ⟨597300357986854552814399837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398200238657903035209599891 597300357986854552814399837)
        ·
          refine ⟨223987634245070457305399939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 597300357986854552814399837 223987634245070457305399939)
          ·
            refine ⟨335981451367605685958099909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223987634245070457305399939 335981451367605685958099909)
            ·
              refine ⟨62996522131426066117143733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 335981451367605685958099909 62996522131426066117143733)
              ·
                refine ⟨5905923949821193698482225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62996522131426066117143733 5905923949821193698482225)
                ·
                  refine ⟨4429442962365895273861669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5905923949821193698482225 4429442962365895273861669)
                  ·
                    refine ⟨830520555443605363849063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4429442962365895273861669 830520555443605363849063)
                    ·
                      rfl

theorem cell23_4852299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 4].length) (baseStart_4852299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852299 prefixEnd_4852299 := by exact prefixLift 4852299
  have htrace : WordTrace (prefixWord ++ tailWord_4852299) baseStart_4852299 baseEnd_4852299 := by
    simpa [prefixWord, tailWord_4852299, baseEnd_4852299] using wordTrace_append hprefix tailTrace_4852299
  have hstable : (prefixWord ++ tailWord_4852299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852299).length < 2 ^ (prefixWord ++ tailWord_4852299).sum := by decide
  have hdescent : baseEnd_4852299 < baseStart_4852299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852306 : List Nat := [3, 2, 2, 1, 2, 1, 4, 2, 1, 1, 4]
def baseStart_4852306 : Nat := 118140960795 + 4852306 * 2 ^ 59
def prefixEnd_4852306 : Nat := 4983230072969 + 3 ^ 40 * 4852306 * 2
def baseEnd_4852306 : Nat := 2491565260695397564159657

theorem tailTrace_4852306 : CollatzResearch.WordTrace tailWord_4852306 prefixEnd_4852306 2491565260695397564159657 := by
  unfold tailWord_4852306
  simp only [CollatzResearch.WordTrace]
  refine ⟨44244534789732886183276193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117985426105954363155403181 44244534789732886183276193)
  ·
    refine ⟨33183401092299664637457145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44244534789732886183276193 33183401092299664637457145)
    ·
      refine ⟨24887550819224748478092859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33183401092299664637457145 24887550819224748478092859)
      ·
        refine ⟨37331326228837122717139289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24887550819224748478092859 37331326228837122717139289)
        ·
          refine ⟨27998494671627842037854467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37331326228837122717139289 27998494671627842037854467)
          ·
            refine ⟨41997742007441763056781701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27998494671627842037854467 41997742007441763056781701)
            ·
              refine ⟨7874576626395330573146569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41997742007441763056781701 7874576626395330573146569)
              ·
                refine ⟨5905932469796497929859927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7874576626395330573146569 5905932469796497929859927)
                ·
                  refine ⟨8858898704694746894789891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5905932469796497929859927 8858898704694746894789891)
                  ·
                    refine ⟨13288348057042120342184837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8858898704694746894789891 13288348057042120342184837)
                    ·
                      refine ⟨2491565260695397564159657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13288348057042120342184837 2491565260695397564159657)
                      ·
                        rfl

theorem cell23_4852306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_4852306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852306 prefixEnd_4852306 := by exact prefixLift 4852306
  have htrace : WordTrace (prefixWord ++ tailWord_4852306) baseStart_4852306 baseEnd_4852306 := by
    simpa [prefixWord, tailWord_4852306, baseEnd_4852306] using wordTrace_append hprefix tailTrace_4852306
  have hstable : (prefixWord ++ tailWord_4852306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852306).length < 2 ^ (prefixWord ++ tailWord_4852306).sum := by decide
  have hdescent : baseEnd_4852306 < baseStart_4852306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852309 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 3, 2, 3]
def baseStart_4852309 : Nat := 118140960795 + 4852309 * 2 ^ 59
def prefixEnd_4852309 : Nat := 4983230072969 + 3 ^ 40 * 4852309 * 2
def baseEnd_4852309 : Nat := 2491566801137361052422143

theorem tailTrace_4852309 : CollatzResearch.WordTrace tailWord_4852309 prefixEnd_4852309 2491566801137361052422143 := by
  unfold tailWord_4852309
  simp only [CollatzResearch.WordTrace]
  refine ⟨176978248577920676245463981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117985499051947117496975987 176978248577920676245463981)
  ·
    refine ⟨66366843216720253592048993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176978248577920676245463981 66366843216720253592048993)
    ·
      refine ⟨49775132412540190194036745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66366843216720253592048993 49775132412540190194036745)
      ·
        refine ⟨37331349309405142645527559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49775132412540190194036745 37331349309405142645527559)
        ·
          refine ⟨55997023964107713968291339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37331349309405142645527559 55997023964107713968291339)
          ·
            refine ⟨83995535946161570952437009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55997023964107713968291339 83995535946161570952437009)
            ·
              refine ⟨62996651959621178214327757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83995535946161570952437009 62996651959621178214327757)
              ·
                refine ⟨23623744484857941830372909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62996651959621178214327757 23623744484857941830372909)
                ·
                  refine ⟨8858904181821728186389841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23623744484857941830372909 8858904181821728186389841)
                  ·
                    refine ⟨6644178136366296139792381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8858904181821728186389841 6644178136366296139792381)
                    ·
                      refine ⟨2491566801137361052422143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6644178136366296139792381 2491566801137361052422143)
                      ·
                        rfl

theorem cell23_4852309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_4852309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852309 prefixEnd_4852309 := by exact prefixLift 4852309
  have htrace : WordTrace (prefixWord ++ tailWord_4852309) baseStart_4852309 baseEnd_4852309 := by
    simpa [prefixWord, tailWord_4852309, baseEnd_4852309] using wordTrace_append hprefix tailTrace_4852309
  have hstable : (prefixWord ++ tailWord_4852309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852309).length < 2 ^ (prefixWord ++ tailWord_4852309).sum := by decide
  have hdescent : baseEnd_4852309 < baseStart_4852309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852354 : List Nat := [3, 4, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_4852354 : Nat := 118140960795 + 4852354 * 2 ^ 59
def prefixEnd_4852354 : Nat := 4983230072969 + 3 ^ 40 * 4852354 * 2
def baseEnd_4852354 : Nat := 830529969255604458786479

theorem tailTrace_4852354 : CollatzResearch.WordTrace tailWord_4852354 prefixEnd_4852354 830529969255604458786479 := by
  unfold tailWord_4852354
  simp only [CollatzResearch.WordTrace]
  refine ⟨44244972465689412232713029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117986593241838432620568077 44244972465689412232713029)
  ·
    refine ⟨8295932337316764793633693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44244972465689412232713029 8295932337316764793633693)
    ·
      refine ⟨3110974626493786797612635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8295932337316764793633693 3110974626493786797612635)
      ·
        refine ⟨4666461939740680196418953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3110974626493786797612635 4666461939740680196418953)
        ·
          refine ⟨3499846454805510147314215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4666461939740680196418953 3499846454805510147314215)
          ·
            refine ⟨5249769682208265220971323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3499846454805510147314215 5249769682208265220971323)
            ·
              refine ⟨7874654523312397831456985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5249769682208265220971323 7874654523312397831456985)
              ·
                refine ⟨5905990892484298373592739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7874654523312397831456985 5905990892484298373592739)
                ·
                  refine ⟨8858986338726447560389109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5905990892484298373592739 8858986338726447560389109)
                  ·
                    refine ⟨830529969255604458786479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8858986338726447560389109 830529969255604458786479)
                    ·
                      rfl

theorem cell23_4852354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_4852354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852354 prefixEnd_4852354 := by exact prefixLift 4852354
  have htrace : WordTrace (prefixWord ++ tailWord_4852354) baseStart_4852354 baseEnd_4852354 := by
    simpa [prefixWord, tailWord_4852354, baseEnd_4852354] using wordTrace_append hprefix tailTrace_4852354
  have hstable : (prefixWord ++ tailWord_4852354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852354).length < 2 ^ (prefixWord ++ tailWord_4852354).sum := by decide
  have hdescent : baseEnd_4852354 < baseStart_4852354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852391 : List Nat := [1, 1, 6, 3, 1, 2, 2, 2, 1, 2, 2]
def baseStart_4852391 : Nat := 118140960795 + 4852391 * 2 ^ 59
def prefixEnd_4852391 : Nat := 4983230072969 + 3 ^ 40 * 4852391 * 2
def baseEnd_4852391 : Nat := 2491608906551029731596767

theorem tailTrace_4852391 : CollatzResearch.WordTrace tailWord_4852391 prefixEnd_4852391 2491608906551029731596767 := by
  unfold tailWord_4852391
  simp only [CollatzResearch.WordTrace]
  refine ⟨176981239363623604249949027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117987492909082402833299351 176981239363623604249949027)
  ·
    refine ⟨265471859045435406374923541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176981239363623604249949027 265471859045435406374923541)
    ·
      refine ⟨12443993392754784673824541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 265471859045435406374923541 12443993392754784673824541)
      ·
        refine ⟨4666497522283044252684203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12443993392754784673824541 4666497522283044252684203)
        ·
          refine ⟨6999746283424566379026305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4666497522283044252684203 6999746283424566379026305)
          ·
            refine ⟨5249809712568424784269729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6999746283424566379026305 5249809712568424784269729)
            ·
              refine ⟨3937357284426318588202297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5249809712568424784269729 3937357284426318588202297)
              ·
                refine ⟨2953017963319738941151723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3937357284426318588202297 2953017963319738941151723)
                ·
                  refine ⟨4429526944979608411727585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2953017963319738941151723 4429526944979608411727585)
                  ·
                    refine ⟨3322145208734706308795689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4429526944979608411727585 3322145208734706308795689)
                    ·
                      refine ⟨2491608906551029731596767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3322145208734706308795689 2491608906551029731596767)
                      ·
                        rfl

theorem cell23_4852391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_4852391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852391 prefixEnd_4852391 := by exact prefixLift 4852391
  have htrace : WordTrace (prefixWord ++ tailWord_4852391) baseStart_4852391 baseEnd_4852391 := by
    simpa [prefixWord, tailWord_4852391, baseEnd_4852391] using wordTrace_append hprefix tailTrace_4852391
  have hstable : (prefixWord ++ tailWord_4852391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852391).length < 2 ^ (prefixWord ++ tailWord_4852391).sum := by decide
  have hdescent : baseEnd_4852391 < baseStart_4852391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852399 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 3]
def baseStart_4852399 : Nat := 118140960795 + 4852399 * 2 ^ 59
def prefixEnd_4852399 : Nat := 4983230072969 + 3 ^ 40 * 4852399 * 2
def baseEnd_4852399 : Nat := 2491613014396265700296729

theorem tailTrace_4852399 : CollatzResearch.WordTrace tailWord_4852399 prefixEnd_4852399 2491613014396265700296729 := by
  unfold tailWord_4852399
  simp only [CollatzResearch.WordTrace]
  refine ⟨176981531147594621616240251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117987687431729747744160167 176981531147594621616240251)
  ·
    refine ⟨265472296721391932424360377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176981531147594621616240251 265472296721391932424360377)
    ·
      refine ⟨199104222541043949318270283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265472296721391932424360377 199104222541043949318270283)
      ·
        refine ⟨298656333811565923977405425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199104222541043949318270283 298656333811565923977405425)
        ·
          refine ⟨223992250358674442983054069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298656333811565923977405425 223992250358674442983054069)
          ·
            refine ⟨20999273471125729029661319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 223992250358674442983054069 20999273471125729029661319)
            ·
              refine ⟨31498910206688593544491979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20999273471125729029661319 31498910206688593544491979)
              ·
                refine ⟨47248365310032890316737969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31498910206688593544491979 47248365310032890316737969)
                ·
                  refine ⟨35436273982524667737553477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47248365310032890316737969 35436273982524667737553477)
                  ·
                    refine ⟨6644301371723375200791277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35436273982524667737553477 6644301371723375200791277)
                    ·
                      refine ⟨2491613014396265700296729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6644301371723375200791277 2491613014396265700296729)
                      ·
                        rfl

theorem cell23_4852399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 3].length) (baseStart_4852399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852399 prefixEnd_4852399 := by exact prefixLift 4852399
  have htrace : WordTrace (prefixWord ++ tailWord_4852399) baseStart_4852399 baseEnd_4852399 := by
    simpa [prefixWord, tailWord_4852399, baseEnd_4852399] using wordTrace_append hprefix tailTrace_4852399
  have hstable : (prefixWord ++ tailWord_4852399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852399).length < 2 ^ (prefixWord ++ tailWord_4852399).sum := by decide
  have hdescent : baseEnd_4852399 < baseStart_4852399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852413 : List Nat := [1, 4, 1, 2, 1, 4, 2, 1, 1, 4, 2]
def baseStart_4852413 : Nat := 118140960795 + 4852413 * 2 ^ 59
def prefixEnd_4852413 : Nat := 4983230072969 + 3 ^ 40 * 4852413 * 2
def baseEnd_4852413 : Nat := 2491620203125428645521665

theorem tailTrace_4852413 : CollatzResearch.WordTrace tailWord_4852413 prefixEnd_4852413 2491620203125428645521665 := by
  unfold tailWord_4852413
  simp only [CollatzResearch.WordTrace]
  refine ⟨176982041769543902007249893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117988027846362601338166595 176982041769543902007249893)
  ·
    refine ⟨33184132831789481626359355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176982041769543902007249893 33184132831789481626359355)
    ·
      refine ⟨49776199247684222439539033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33184132831789481626359355 49776199247684222439539033)
      ·
        refine ⟨37332149435763166829654275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49776199247684222439539033 37332149435763166829654275)
        ·
          refine ⟨55998224153644750244481413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37332149435763166829654275 55998224153644750244481413)
          ·
            refine ⟨10499667028808390670840265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55998224153644750244481413 10499667028808390670840265)
            ·
              refine ⟨7874750271606293003130199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10499667028808390670840265 7874750271606293003130199)
              ·
                refine ⟨11812125407409439504695299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7874750271606293003130199 11812125407409439504695299)
                ·
                  refine ⟨17718188111114159257042949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11812125407409439504695299 17718188111114159257042949)
                  ·
                    refine ⟨3322160270833904860695553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17718188111114159257042949 3322160270833904860695553)
                    ·
                      refine ⟨2491620203125428645521665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3322160270833904860695553 2491620203125428645521665)
                      ·
                        rfl

theorem cell23_4852413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_4852413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852413 prefixEnd_4852413 := by exact prefixLift 4852413
  have htrace : WordTrace (prefixWord ++ tailWord_4852413) baseStart_4852413 baseEnd_4852413 := by
    simpa [prefixWord, tailWord_4852413, baseEnd_4852413] using wordTrace_append hprefix tailTrace_4852413
  have hstable : (prefixWord ++ tailWord_4852413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852413).length < 2 ^ (prefixWord ++ tailWord_4852413).sum := by decide
  have hdescent : baseEnd_4852413 < baseStart_4852413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852434 : List Nat := [3, 2, 2, 2, 4, 1, 2, 1, 1, 3, 2]
def baseStart_4852434 : Nat := 118140960795 + 4852434 * 2 ^ 59
def prefixEnd_4852434 : Nat := 4983230072969 + 3 ^ 40 * 4852434 * 2
def baseEnd_4852434 : Nat := 2491630986219173063359069

theorem tailTrace_4852434 : CollatzResearch.WordTrace tailWord_4852434 prefixEnd_4852434 2491630986219173063359069 := by
  unfold tailWord_4852434
  simp only [CollatzResearch.WordTrace]
  refine ⟨44245701925616955648441089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117988538468311881729176237 44245701925616955648441089)
  ·
    refine ⟨33184276444212716736330817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44245701925616955648441089 33184276444212716736330817)
    ·
      refine ⟨24888207333159537552248113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33184276444212716736330817 24888207333159537552248113)
      ·
        refine ⟨18666155499869653164186085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24888207333159537552248113 18666155499869653164186085)
        ·
          refine ⟨3499904156225559968284891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18666155499869653164186085 3499904156225559968284891)
          ·
            refine ⟨5249856234338339952427337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3499904156225559968284891 5249856234338339952427337)
            ·
              refine ⟨3937392175753754964320503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5249856234338339952427337 3937392175753754964320503)
              ·
                refine ⟨5906088263630632446480755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3937392175753754964320503 5906088263630632446480755)
                ·
                  refine ⟨8859132395445948669721133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5906088263630632446480755 8859132395445948669721133)
                  ·
                    refine ⟨3322174648292230751145425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8859132395445948669721133 3322174648292230751145425)
                    ·
                      refine ⟨2491630986219173063359069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3322174648292230751145425 2491630986219173063359069)
                      ·
                        rfl

theorem cell23_4852434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_4852434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852434 prefixEnd_4852434 := by exact prefixLift 4852434
  have htrace : WordTrace (prefixWord ++ tailWord_4852434) baseStart_4852434 baseEnd_4852434 := by
    simpa [prefixWord, tailWord_4852434, baseEnd_4852434] using wordTrace_append hprefix tailTrace_4852434
  have hstable : (prefixWord ++ tailWord_4852434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852434).length < 2 ^ (prefixWord ++ tailWord_4852434).sum := by decide
  have hdescent : baseEnd_4852434 < baseStart_4852434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852503 : List Nat := [1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 4]
def baseStart_4852503 : Nat := 118140960795 + 4852503 * 2 ^ 59
def prefixEnd_4852503 : Nat := 4983230072969 + 3 ^ 40 * 4852503 * 2
def baseEnd_4852503 : Nat := 2491666416384333293396251

theorem tailTrace_4852503 : CollatzResearch.WordTrace tailWord_4852503 prefixEnd_4852503 2491666416384333293396251 := by
  unfold tailWord_4852503
  simp only [CollatzResearch.WordTrace]
  refine ⟨176985324339217847378026163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117990216226145231585350775 176985324339217847378026163)
  ·
    refine ⟨265477986508826771067039245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176985324339217847378026163 265477986508826771067039245)
    ·
      refine ⟨99554244940810039150139717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265477986508826771067039245 99554244940810039150139717)
      ·
        refine ⟨18666420926401882340651197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99554244940810039150139717 18666420926401882340651197)
        ·
          refine ⟨6999907847400705877744199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18666420926401882340651197 6999907847400705877744199)
          ·
            refine ⟨10499861771101058816616299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6999907847400705877744199 10499861771101058816616299)
            ·
              refine ⟨15749792656651588224924449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10499861771101058816616299 15749792656651588224924449)
              ·
                refine ⟨11812344492488691168693337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15749792656651588224924449 11812344492488691168693337)
                ·
                  refine ⟨8859258369366518376520003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11812344492488691168693337 8859258369366518376520003)
                  ·
                    refine ⟨13288887554049777564780005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8859258369366518376520003 13288887554049777564780005)
                    ·
                      refine ⟨2491666416384333293396251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13288887554049777564780005 2491666416384333293396251)
                      ·
                        rfl

theorem cell23_4852503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_4852503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852503 prefixEnd_4852503 := by exact prefixLift 4852503
  have htrace : WordTrace (prefixWord ++ tailWord_4852503) baseStart_4852503 baseEnd_4852503 := by
    simpa [prefixWord, tailWord_4852503, baseEnd_4852503] using wordTrace_append hprefix tailTrace_4852503
  have hstable : (prefixWord ++ tailWord_4852503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852503).length < 2 ^ (prefixWord ++ tailWord_4852503).sum := by decide
  have hdescent : baseEnd_4852503 < baseStart_4852503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852549 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 2, 4, 5]
def baseStart_4852549 : Nat := 118140960795 + 4852549 * 2 ^ 59
def prefixEnd_4852549 : Nat := 4983230072969 + 3 ^ 40 * 4852549 * 2
def baseEnd_4852549 : Nat := 2491690036494440113421039

theorem tailTrace_4852549 : CollatzResearch.WordTrace tailWord_4852549 prefixEnd_4852549 2491690036494440113421039 := by
  unfold tailWord_4852549
  simp only [CollatzResearch.WordTrace]
  refine ⟨176987002097051197234200701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117991334731367464822800467 176987002097051197234200701)
  ·
    refine ⟨66370125786394198962825263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176987002097051197234200701 66370125786394198962825263)
    ·
      refine ⟨99555188679591298444237895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66370125786394198962825263 99555188679591298444237895)
      ·
        refine ⟨149332783019386947666356843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99555188679591298444237895 149332783019386947666356843)
        ·
          refine ⟨223999174529080421499535265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149332783019386947666356843 223999174529080421499535265)
          ·
            refine ⟨167999380896810316124651449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223999174529080421499535265 167999380896810316124651449)
            ·
              refine ⟨125999535672607737093488587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167999380896810316124651449 125999535672607737093488587)
              ·
                refine ⟨188999303508911605640232881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125999535672607737093488587 188999303508911605640232881)
                ·
                  refine ⟨141749477631683704230174661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188999303508911605640232881 141749477631683704230174661)
                  ·
                    refine ⟨26578027055940694543157749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 141749477631683704230174661 26578027055940694543157749)
                    ·
                      refine ⟨2491690036494440113421039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26578027055940694543157749 2491690036494440113421039)
                      ·
                        rfl

theorem cell23_4852549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_4852549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852549 prefixEnd_4852549 := by exact prefixLift 4852549
  have htrace : WordTrace (prefixWord ++ tailWord_4852549) baseStart_4852549 baseEnd_4852549 := by
    simpa [prefixWord, tailWord_4852549, baseEnd_4852549] using wordTrace_append hprefix tailTrace_4852549
  have hstable : (prefixWord ++ tailWord_4852549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852549).length < 2 ^ (prefixWord ++ tailWord_4852549).sum := by decide
  have hdescent : baseEnd_4852549 < baseStart_4852549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852564 : List Nat := [2, 4, 1, 1, 4, 2, 2, 2, 1, 4]
def baseStart_4852564 : Nat := 118140960795 + 4852564 * 2 ^ 59
def prefixEnd_4852564 : Nat := 4983230072969 + 3 ^ 40 * 4852564 * 2
def baseEnd_4852564 : Nat := 830565912901419184911157

theorem tailTrace_4852564 : CollatzResearch.WordTrace tailWord_4852564 prefixEnd_4852564 830565912901419184911157 := by
  unfold tailWord_4852564
  simp only [CollatzResearch.WordTrace]
  refine ⟨88493774595998427397998373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117991699461331236530664497 88493774595998427397998373)
  ·
    refine ⟨16592582736749705137124695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88493774595998427397998373 16592582736749705137124695)
    ·
      refine ⟨24888874105124557705687043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16592582736749705137124695 24888874105124557705687043)
      ·
        refine ⟨37333311157686836558530565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24888874105124557705687043 37333311157686836558530565)
        ·
          refine ⟨6999995842066281854724481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37333311157686836558530565 6999995842066281854724481)
          ·
            refine ⟨5249996881549711391043361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6999995842066281854724481 5249996881549711391043361)
            ·
              refine ⟨3937497661162283543282521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5249996881549711391043361 3937497661162283543282521)
              ·
                refine ⟨2953123245871712657461891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3937497661162283543282521 2953123245871712657461891)
                ·
                  refine ⟨4429684868807568986192837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2953123245871712657461891 4429684868807568986192837)
                  ·
                    refine ⟨830565912901419184911157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4429684868807568986192837 830565912901419184911157)
                    ·
                      rfl

theorem cell23_4852564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_4852564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852564 prefixEnd_4852564 := by exact prefixLift 4852564
  have htrace : WordTrace (prefixWord ++ tailWord_4852564) baseStart_4852564 baseEnd_4852564 := by
    simpa [prefixWord, tailWord_4852564, baseEnd_4852564] using wordTrace_append hprefix tailTrace_4852564
  have hstable : (prefixWord ++ tailWord_4852564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852564).length < 2 ^ (prefixWord ++ tailWord_4852564).sum := by decide
  have hdescent : baseEnd_4852564 < baseStart_4852564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852576 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 4]
def baseStart_4852576 : Nat := 118140960795 + 4852576 * 2 ^ 59
def prefixEnd_4852576 : Nat := 4983230072969 + 3 ^ 40 * 4852576 * 2
def baseEnd_4852576 : Nat := 2491703900472111507783415

theorem tailTrace_4852576 : CollatzResearch.WordTrace tailWord_4852576 prefixEnd_4852576 2491703900472111507783415 := by
  unfold tailWord_4852576
  simp only [CollatzResearch.WordTrace]
  refine ⟨88493993433976690422716791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117991991245302253896955721 88493993433976690422716791)
  ·
    refine ⟨132740990150965035634075187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88493993433976690422716791 132740990150965035634075187)
    ·
      refine ⟨199111485226447553451112781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132740990150965035634075187 199111485226447553451112781)
      ·
        refine ⟨74666806959917832544167293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199111485226447553451112781 74666806959917832544167293)
        ·
          refine ⟨28000052609969187204062735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74666806959917832544167293 28000052609969187204062735)
          ·
            refine ⟨42000078914953780806094103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28000052609969187204062735 42000078914953780806094103)
            ·
              refine ⟨63000118372430671209141155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42000078914953780806094103 63000118372430671209141155)
              ·
                refine ⟨94500177558646006813711733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63000118372430671209141155 94500177558646006813711733)
                ·
                  refine ⟨8859391646123063138785475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94500177558646006813711733 8859391646123063138785475)
                  ·
                    refine ⟨13289087469184594708178213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8859391646123063138785475 13289087469184594708178213)
                    ·
                      refine ⟨2491703900472111507783415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13289087469184594708178213 2491703900472111507783415)
                      ·
                        rfl

theorem cell23_4852576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_4852576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852576 prefixEnd_4852576 := by exact prefixLift 4852576
  have htrace : WordTrace (prefixWord ++ tailWord_4852576) baseStart_4852576 baseEnd_4852576 := by
    simpa [prefixWord, tailWord_4852576, baseEnd_4852576] using wordTrace_append hprefix tailTrace_4852576
  have hstable : (prefixWord ++ tailWord_4852576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852576).length < 2 ^ (prefixWord ++ tailWord_4852576).sum := by decide
  have hdescent : baseEnd_4852576 < baseStart_4852576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852597 : List Nat := [1, 3, 4, 1, 1, 4, 1, 1, 2, 3, 2]
def baseStart_4852597 : Nat := 118140960795 + 4852597 * 2 ^ 59
def prefixEnd_4852597 : Nat := 4983230072969 + 3 ^ 40 * 4852597 * 2
def baseEnd_4852597 : Nat := 2491714683565855925620819

theorem tailTrace_4852597 : CollatzResearch.WordTrace tailWord_4852597 prefixEnd_4852597 2491714683565855925620819 := by
  unfold tailWord_4852597
  simp only [CollatzResearch.WordTrace]
  refine ⟨176988752800877301431948045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117992501867251534287965363 176988752800877301431948045)
  ·
    refine ⟨66370782300328988036980517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176988752800877301431948045 66370782300328988036980517)
    ·
      refine ⟨12444521681311685256933847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66370782300328988036980517 12444521681311685256933847)
      ·
        refine ⟨18666782521967527885400771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12444521681311685256933847 18666782521967527885400771)
        ·
          refine ⟨28000173782951291828101157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18666782521967527885400771 28000173782951291828101157)
          ·
            refine ⟨5250032584303367217768967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28000173782951291828101157 5250032584303367217768967)
            ·
              refine ⟨7875048876455050826653451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5250032584303367217768967 7875048876455050826653451)
              ·
                refine ⟨11812573314682576239980177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7875048876455050826653451 11812573314682576239980177)
                ·
                  refine ⟨8859429986011932179985133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11812573314682576239980177 8859429986011932179985133)
                  ·
                    refine ⟨3322286244754474567494425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8859429986011932179985133 3322286244754474567494425)
                    ·
                      refine ⟨2491714683565855925620819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3322286244754474567494425 2491714683565855925620819)
                      ·
                        rfl

theorem cell23_4852597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_4852597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852597 prefixEnd_4852597 := by exact prefixLift 4852597
  have htrace : WordTrace (prefixWord ++ tailWord_4852597) baseStart_4852597 baseEnd_4852597 := by
    simpa [prefixWord, tailWord_4852597, baseEnd_4852597] using wordTrace_append hprefix tailTrace_4852597
  have hstable : (prefixWord ++ tailWord_4852597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852597).length < 2 ^ (prefixWord ++ tailWord_4852597).sum := by decide
  have hdescent : baseEnd_4852597 < baseStart_4852597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852599 : List Nat := [1, 1, 3, 1, 1, 2, 1, 13]
def baseStart_4852599 : Nat := 118140960795 + 4852599 * 2 ^ 59
def prefixEnd_4852599 : Nat := 4983230072969 + 3 ^ 40 * 4852599 * 2
def baseEnd_4852599 : Nat := 92285767056561663622067

theorem tailTrace_4852599 : CollatzResearch.WordTrace tailWord_4852599 prefixEnd_4852599 92285767056561663622067 := by
  unfold tailWord_4852599
  simp only [CollatzResearch.WordTrace]
  refine ⟨176988825746870055773520851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117992550497913370515680567 176988825746870055773520851)
  ·
    refine ⟨265483238620305083660281277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176988825746870055773520851 265483238620305083660281277)
    ·
      refine ⟨99556214482614406372605479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265483238620305083660281277 99556214482614406372605479)
      ·
        refine ⟨149334321723921609558908219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99556214482614406372605479 149334321723921609558908219)
        ·
          refine ⟨224001482585882414338362329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149334321723921609558908219 224001482585882414338362329)
          ·
            refine ⟨168001111939411810753771747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224001482585882414338362329 168001111939411810753771747)
            ·
              refine ⟨252001667909117716130657621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168001111939411810753771747 252001667909117716130657621)
              ·
                refine ⟨92285767056561663622067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 252001667909117716130657621 92285767056561663622067)
                ·
                  rfl

theorem cell23_4852599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 13].length) (baseStart_4852599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852599 prefixEnd_4852599 := by exact prefixLift 4852599
  have htrace : WordTrace (prefixWord ++ tailWord_4852599) baseStart_4852599 baseEnd_4852599 := by
    simpa [prefixWord, tailWord_4852599, baseEnd_4852599] using wordTrace_append hprefix tailTrace_4852599
  have hstable : (prefixWord ++ tailWord_4852599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852599).length < 2 ^ (prefixWord ++ tailWord_4852599).sum := by decide
  have hdescent : baseEnd_4852599 < baseStart_4852599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852616 : List Nat := [2, 1, 3, 3, 2, 2, 10]
def baseStart_4852616 : Nat := 118140960795 + 4852616 * 2 ^ 59
def prefixEnd_4852616 : Nat := 4983230072969 + 3 ^ 40 * 4852616 * 2
def baseEnd_4852616 : Nat := 30762030119731991991151

theorem tailTrace_4852616 : CollatzResearch.WordTrace tailWord_4852616 prefixEnd_4852616 30762030119731991991151 := by
  unfold tailWord_4852616
  simp only [CollatzResearch.WordTrace]
  refine ⟨88494722893904233838444851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117992963858538978451259801 88494722893904233838444851)
  ·
    refine ⟨132742084340856350757667277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88494722893904233838444851 132742084340856350757667277)
    ·
      refine ⟨49778281627821131534125229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132742084340856350757667277 49778281627821131534125229)
      ·
        refine ⟨18666855610432924325296961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49778281627821131534125229 18666855610432924325296961)
        ·
          refine ⟨14000141707824693243972721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18666855610432924325296961 14000141707824693243972721)
          ·
            refine ⟨10500106280868519932979541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14000141707824693243972721 10500106280868519932979541)
            ·
              refine ⟨30762030119731991991151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10500106280868519932979541 30762030119731991991151)
              ·
                rfl

theorem cell23_4852616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 10].length) (baseStart_4852616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852616 prefixEnd_4852616 := by exact prefixLift 4852616
  have htrace : WordTrace (prefixWord ++ tailWord_4852616) baseStart_4852616 baseEnd_4852616 := by
    simpa [prefixWord, tailWord_4852616, baseEnd_4852616] using wordTrace_append hprefix tailTrace_4852616
  have hstable : (prefixWord ++ tailWord_4852616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852616).length < 2 ^ (prefixWord ++ tailWord_4852616).sum := by decide
  have hdescent : baseEnd_4852616 < baseStart_4852616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852643 : List Nat := [1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 3]
def baseStart_4852643 : Nat := 118140960795 + 4852643 * 2 ^ 59
def prefixEnd_4852643 : Nat := 4983230072969 + 3 ^ 40 * 4852643 * 2
def baseEnd_4852643 : Nat := 2491738303675962745645607

theorem tailTrace_4852643 : CollatzResearch.WordTrace tailWord_4852643 prefixEnd_4852643 2491738303675962745645607 := by
  unfold tailWord_4852643
  simp only [CollatzResearch.WordTrace]
  refine ⟨176990430558710651288122583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117993620372473767525415055 176990430558710651288122583)
  ·
    refine ⟨265485645838065976932183875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176990430558710651288122583 265485645838065976932183875)
    ·
      refine ⟨398228468757098965398275813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265485645838065976932183875 398228468757098965398275813)
      ·
        refine ⟨74667837891956056012176715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 398228468757098965398275813 74667837891956056012176715)
        ·
          refine ⟨112001756837934084018265073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74667837891956056012176715 112001756837934084018265073)
          ·
            refine ⟨84001317628450563013698805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112001756837934084018265073 84001317628450563013698805)
            ·
              refine ⟨7875123527667240282534263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84001317628450563013698805 7875123527667240282534263)
              ·
                refine ⟨11812685291500860423801395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7875123527667240282534263 11812685291500860423801395)
                ·
                  refine ⟨17719027937251290635702093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11812685291500860423801395 17719027937251290635702093)
                  ·
                    refine ⟨6644635476469233988388285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17719027937251290635702093 6644635476469233988388285)
                    ·
                      refine ⟨2491738303675962745645607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6644635476469233988388285 2491738303675962745645607)
                      ·
                        rfl

theorem cell23_4852643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_4852643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852643 prefixEnd_4852643 := by exact prefixLift 4852643
  have htrace : WordTrace (prefixWord ++ tailWord_4852643) baseStart_4852643 baseEnd_4852643 := by
    simpa [prefixWord, tailWord_4852643, baseEnd_4852643] using wordTrace_append hprefix tailTrace_4852643
  have hstable : (prefixWord ++ tailWord_4852643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852643).length < 2 ^ (prefixWord ++ tailWord_4852643).sum := by decide
  have hdescent : baseEnd_4852643 < baseStart_4852643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852647 : List Nat := [1, 1, 6, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_4852647 : Nat := 118140960795 + 4852647 * 2 ^ 59
def prefixEnd_4852647 : Nat := 4983230072969 + 3 ^ 40 * 4852647 * 2
def baseEnd_4852647 : Nat := 2491740357598580729995589

theorem tailTrace_4852647 : CollatzResearch.WordTrace tailWord_4852647 prefixEnd_4852647 2491740357598580729995589 := by
  unfold tailWord_4852647
  simp only [CollatzResearch.WordTrace]
  refine ⟨176990576450696159971268195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117993717633797439980845463 176990576450696159971268195)
  ·
    refine ⟨265485864676044239956902293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176990576450696159971268195 265485864676044239956902293)
    ·
      refine ⟨12444649906689573747979795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 265485864676044239956902293 12444649906689573747979795)
      ·
        refine ⟨18666974860034360621969693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12444649906689573747979795 18666974860034360621969693)
        ·
          refine ⟨7000115572512885233238635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18666974860034360621969693 7000115572512885233238635)
          ·
            refine ⟨10500173358769327849857953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7000115572512885233238635 10500173358769327849857953)
            ·
              refine ⟨7875130019076995887393465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10500173358769327849857953 7875130019076995887393465)
              ·
                refine ⟨5906347514307746915545099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7875130019076995887393465 5906347514307746915545099)
                ·
                  refine ⟨8859521271461620373317649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5906347514307746915545099 8859521271461620373317649)
                  ·
                    refine ⟨6644640953596215279988237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8859521271461620373317649 6644640953596215279988237)
                    ·
                      refine ⟨2491740357598580729995589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6644640953596215279988237 2491740357598580729995589)
                      ·
                        rfl

theorem cell23_4852647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_4852647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852647 prefixEnd_4852647 := by exact prefixLift 4852647
  have htrace : WordTrace (prefixWord ++ tailWord_4852647) baseStart_4852647 baseEnd_4852647 := by
    simpa [prefixWord, tailWord_4852647, baseEnd_4852647] using wordTrace_append hprefix tailTrace_4852647
  have hstable : (prefixWord ++ tailWord_4852647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852647).length < 2 ^ (prefixWord ++ tailWord_4852647).sum := by decide
  have hdescent : baseEnd_4852647 < baseStart_4852647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852694 : List Nat := [5, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_4852694 : Nat := 118140960795 + 4852694 * 2 ^ 59
def prefixEnd_4852694 : Nat := 4983230072969 + 3 ^ 40 * 4852694 * 2
def baseEnd_4852694 : Nat := 2491764491189342046107873

theorem tailTrace_4852694 : CollatzResearch.WordTrace tailWord_4852694 prefixEnd_4852694 2491764491189342046107873 := by
  unfold tailWord_4852694
  simp only [CollatzResearch.WordTrace]
  refine ⟨11062018167595367937389321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117994860454350591332152757 11062018167595367937389321)
  ·
    refine ⟨8296513625696525953041991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11062018167595367937389321 8296513625696525953041991)
    ·
      refine ⟨12444770438544788929562987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8296513625696525953041991 12444770438544788929562987)
      ·
        refine ⟨18667155657817183394344481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12444770438544788929562987 18667155657817183394344481)
        ·
          refine ⟨14000366743362887545758361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18667155657817183394344481 14000366743362887545758361)
          ·
            refine ⟨10500275057522165659318771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14000366743362887545758361 10500275057522165659318771)
            ·
              refine ⟨15750412586283248488978157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10500275057522165659318771 15750412586283248488978157)
              ·
                refine ⟨5906404719856218183366809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15750412586283248488978157 5906404719856218183366809)
                ·
                  refine ⟨4429803539892163637525107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5906404719856218183366809 4429803539892163637525107)
                  ·
                    refine ⟨6644705309838245456287661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4429803539892163637525107 6644705309838245456287661)
                    ·
                      refine ⟨2491764491189342046107873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6644705309838245456287661 2491764491189342046107873)
                      ·
                        rfl

theorem cell23_4852694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_4852694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852694 prefixEnd_4852694 := by exact prefixLift 4852694
  have htrace : WordTrace (prefixWord ++ tailWord_4852694) baseStart_4852694 baseEnd_4852694 := by
    simpa [prefixWord, tailWord_4852694, baseEnd_4852694] using wordTrace_append hprefix tailTrace_4852694
  have hstable : (prefixWord ++ tailWord_4852694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852694).length < 2 ^ (prefixWord ++ tailWord_4852694).sum := by decide
  have hdescent : baseEnd_4852694 < baseStart_4852694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852733 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 2, 3, 3]
def baseStart_4852733 : Nat := 118140960795 + 4852733 * 2 ^ 59
def prefixEnd_4852733 : Nat := 4983230072969 + 3 ^ 40 * 4852733 * 2
def baseEnd_4852733 : Nat := 2491784516934867393520193

theorem tailTrace_4852733 : CollatzResearch.WordTrace tailWord_4852733 prefixEnd_4852733 2491784516934867393520193 := by
  unfold tailWord_4852733
  simp only [CollatzResearch.WordTrace]
  refine ⟨176993713128384596658898853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117995808752256397772599235 176993713128384596658898853)
  ·
    refine ⟨33186321211572111873543535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176993713128384596658898853 33186321211572111873543535)
    ·
      refine ⟨49779481817358167810315303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33186321211572111873543535 49779481817358167810315303)
      ·
        refine ⟨74669222726037251715472955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49779481817358167810315303 74669222726037251715472955)
        ·
          refine ⟨112003834089055877573209433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74669222726037251715472955 112003834089055877573209433)
          ·
            refine ⟨84002875566791908179907075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112003834089055877573209433 84002875566791908179907075)
            ·
              refine ⟨126004313350187862269860613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84002875566791908179907075 126004313350187862269860613)
              ·
                refine ⟨23625808753160224175598865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126004313350187862269860613 23625808753160224175598865)
                ·
                  refine ⟨17719356564870168131699149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23625808753160224175598865 17719356564870168131699149)
                  ·
                    refine ⟨6644758711826313049387181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17719356564870168131699149 6644758711826313049387181)
                    ·
                      refine ⟨2491784516934867393520193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6644758711826313049387181 2491784516934867393520193)
                      ·
                        rfl

theorem cell23_4852733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_4852733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852733 prefixEnd_4852733 := by exact prefixLift 4852733
  have htrace : WordTrace (prefixWord ++ tailWord_4852733) baseStart_4852733 baseEnd_4852733 := by
    simpa [prefixWord, tailWord_4852733, baseEnd_4852733] using wordTrace_append hprefix tailTrace_4852733
  have hstable : (prefixWord ++ tailWord_4852733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852733).length < 2 ^ (prefixWord ++ tailWord_4852733).sum := by decide
  have hdescent : baseEnd_4852733 < baseStart_4852733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852750 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3]
def baseStart_4852750 : Nat := 118140960795 + 4852750 * 2 ^ 59
def prefixEnd_4852750 : Nat := 4983230072969 + 3 ^ 40 * 4852750 * 2
def baseEnd_4852750 : Nat := 2491793246105993827007615

theorem tailTrace_4852750 : CollatzResearch.WordTrace tailWord_4852750 prefixEnd_4852750 2491793246105993827007615 := by
  unfold tailWord_4852750
  simp only [CollatzResearch.WordTrace]
  refine ⟨22124291646165376070283463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117996222112882005708178469 22124291646165376070283463)
  ·
    refine ⟨33186437469248064105425195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22124291646165376070283463 33186437469248064105425195)
    ·
      refine ⟨49779656203872096158137793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33186437469248064105425195 49779656203872096158137793)
      ·
        refine ⟨37334742152904072118603345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49779656203872096158137793 37334742152904072118603345)
        ·
          refine ⟨28001056614678054088952509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37334742152904072118603345 28001056614678054088952509)
          ·
            refine ⟨10500396230504270283357191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28001056614678054088952509 10500396230504270283357191)
            ·
              refine ⟨15750594345756405425035787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10500396230504270283357191 15750594345756405425035787)
              ·
                refine ⟨23625891518634608137553681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15750594345756405425035787 23625891518634608137553681)
                ·
                  refine ⟨17719418638975956103165261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23625891518634608137553681 17719418638975956103165261)
                  ·
                    refine ⟨6644781989615983538686973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17719418638975956103165261 6644781989615983538686973)
                    ·
                      refine ⟨2491793246105993827007615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6644781989615983538686973 2491793246105993827007615)
                      ·
                        rfl

theorem cell23_4852750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_4852750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852750 prefixEnd_4852750 := by exact prefixLift 4852750
  have htrace : WordTrace (prefixWord ++ tailWord_4852750) baseStart_4852750 baseEnd_4852750 := by
    simpa [prefixWord, tailWord_4852750, baseEnd_4852750] using wordTrace_append hprefix tailTrace_4852750
  have hstable : (prefixWord ++ tailWord_4852750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852750).length < 2 ^ (prefixWord ++ tailWord_4852750).sum := by decide
  have hdescent : baseEnd_4852750 < baseStart_4852750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852770 : List Nat := [3, 3, 1, 1, 1, 3, 3, 1, 2, 5]
def baseStart_4852770 : Nat := 118140960795 + 4852770 * 2 ^ 59
def prefixEnd_4852770 : Nat := 4983230072969 + 3 ^ 40 * 4852770 * 2
def baseEnd_4852770 : Nat := 830601171906361249585841

theorem tailTrace_4852770 : CollatzResearch.WordTrace tailWord_4852770 prefixEnd_4852770 830601171906361249585841 := by
  unfold tailWord_4852770
  simp only [CollatzResearch.WordTrace]
  refine ⟨44248765657312637994498941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117996708419500367985330509 44248765657312637994498941)
  ·
    refine ⟨16593287121492239247937103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44248765657312637994498941 16593287121492239247937103)
    ·
      refine ⟨24889930682238358871905655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16593287121492239247937103 24889930682238358871905655)
      ·
        refine ⟨37334896023357538307858483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24889930682238358871905655 37334896023357538307858483)
        ·
          refine ⟨56002344035036307461787725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37334896023357538307858483 56002344035036307461787725)
          ·
            refine ⟨21000879013138615298170397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56002344035036307461787725 21000879013138615298170397)
            ·
              refine ⟨7875329629926980736813899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21000879013138615298170397 7875329629926980736813899)
              ·
                refine ⟨11812994444890471105220849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7875329629926980736813899 11812994444890471105220849)
                ·
                  refine ⟨8859745833667853328915637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11812994444890471105220849 8859745833667853328915637)
                  ·
                    refine ⟨830601171906361249585841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8859745833667853328915637 830601171906361249585841)
                    ·
                      rfl

theorem cell23_4852770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_4852770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852770 prefixEnd_4852770 := by exact prefixLift 4852770
  have htrace : WordTrace (prefixWord ++ tailWord_4852770) baseStart_4852770 baseEnd_4852770 := by
    simpa [prefixWord, tailWord_4852770, baseEnd_4852770] using wordTrace_append hprefix tailTrace_4852770
  have hstable : (prefixWord ++ tailWord_4852770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852770).length < 2 ^ (prefixWord ++ tailWord_4852770).sum := by decide
  have hdescent : baseEnd_4852770 < baseStart_4852770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852773 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 1, 3, 4]
def baseStart_4852773 : Nat := 118140960795 + 4852773 * 2 ^ 59
def prefixEnd_4852773 : Nat := 4983230072969 + 3 ^ 40 * 4852773 * 2
def baseEnd_4852773 : Nat := 2491805056161047237020009

theorem tailTrace_4852773 : CollatzResearch.WordTrace tailWord_4852773 prefixEnd_4852773 2491805056161047237020009 := by
  unfold tailWord_4852773
  simp only [CollatzResearch.WordTrace]
  refine ⟨176995172048239683490354973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117996781365493122326903315 176995172048239683490354973)
  ·
    refine ⟨66373189518089881308883115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176995172048239683490354973 66373189518089881308883115)
    ·
      refine ⟨99559784277134821963324673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66373189518089881308883115 99559784277134821963324673)
      ·
        refine ⟨74669838207851116472493505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99559784277134821963324673 74669838207851116472493505)
        ·
          refine ⟨56002378655888337354370129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74669838207851116472493505 56002378655888337354370129)
          ·
            refine ⟨42001783991916253015777597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56002378655888337354370129 42001783991916253015777597)
            ·
              refine ⟨15750668996968594880916599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42001783991916253015777597 15750668996968594880916599)
              ·
                refine ⟨23626003495452892321374899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15750668996968594880916599 23626003495452892321374899)
                ·
                  refine ⟨35439005243179338482062349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23626003495452892321374899 35439005243179338482062349)
                  ·
                    refine ⟨13289626966192251930773381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35439005243179338482062349 13289626966192251930773381)
                    ·
                      refine ⟨2491805056161047237020009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13289626966192251930773381 2491805056161047237020009)
                      ·
                        rfl

theorem cell23_4852773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_4852773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852773 prefixEnd_4852773 := by exact prefixLift 4852773
  have htrace : WordTrace (prefixWord ++ tailWord_4852773) baseStart_4852773 baseEnd_4852773 := by
    simpa [prefixWord, tailWord_4852773, baseEnd_4852773] using wordTrace_append hprefix tailTrace_4852773
  have hstable : (prefixWord ++ tailWord_4852773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852773).length < 2 ^ (prefixWord ++ tailWord_4852773).sum := by decide
  have hdescent : baseEnd_4852773 < baseStart_4852773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852800 : List Nat := [2, 1, 1, 2, 2, 3, 4, 1, 3, 4]
def baseStart_4852800 : Nat := 118140960795 + 4852800 * 2 ^ 59
def prefixEnd_4852800 : Nat := 4983230072969 + 3 ^ 40 * 4852800 * 2
def baseEnd_4852800 : Nat := 830606306712906210460795

theorem tailTrace_4852800 : CollatzResearch.WordTrace tailWord_4852800 prefixEnd_4852800 830606306712906210460795 := by
  unfold tailWord_4852800
  simp only [CollatzResearch.WordTrace]
  refine ⟨88498078409570933550793927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117997437879427911401058569 88498078409570933550793927)
  ·
    refine ⟨132747117614356400326190891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88498078409570933550793927 132747117614356400326190891)
    ·
      refine ⟨199120676421534600489286337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132747117614356400326190891 199120676421534600489286337)
      ·
        refine ⟨149340507316150950366964753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199120676421534600489286337 149340507316150950366964753)
        ·
          refine ⟨112005380487113212775223565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149340507316150950366964753 112005380487113212775223565)
          ·
            refine ⟨42002017682667454790708837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112005380487113212775223565 42002017682667454790708837)
            ·
              refine ⟨7875378315500147773257907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42002017682667454790708837 7875378315500147773257907)
              ·
                refine ⟨11813067473250221659886861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7875378315500147773257907 11813067473250221659886861)
                ·
                  refine ⟨4429900302468833122457573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11813067473250221659886861 4429900302468833122457573)
                  ·
                    refine ⟨830606306712906210460795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4429900302468833122457573 830606306712906210460795)
                    ·
                      rfl

theorem cell23_4852800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 3, 4].length) (baseStart_4852800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852800 prefixEnd_4852800 := by exact prefixLift 4852800
  have htrace : WordTrace (prefixWord ++ tailWord_4852800) baseStart_4852800 baseEnd_4852800 := by
    simpa [prefixWord, tailWord_4852800, baseEnd_4852800] using wordTrace_append hprefix tailTrace_4852800
  have hstable : (prefixWord ++ tailWord_4852800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852800).length < 2 ^ (prefixWord ++ tailWord_4852800).sum := by decide
  have hdescent : baseEnd_4852800 < baseStart_4852800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852823 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 3]
def baseStart_4852823 : Nat := 118140960795 + 4852823 * 2 ^ 59
def prefixEnd_4852823 : Nat := 4983230072969 + 3 ^ 40 * 4852823 * 2
def baseEnd_4852823 : Nat := 2491830730193772041394779

theorem tailTrace_4852823 : CollatzResearch.WordTrace tailWord_4852823 prefixEnd_4852823 2491830730193772041394779 := by
  unfold tailWord_4852823
  simp only [CollatzResearch.WordTrace]
  refine ⟨176996995698058542029675123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117997997132039028019783415 176996995698058542029675123)
  ·
    refine ⟨265495493547087813044512685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176996995698058542029675123 265495493547087813044512685)
    ·
      refine ⟨99560810080157929891692257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265495493547087813044512685 99560810080157929891692257)
      ·
        refine ⟨74670607560118447418769193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99560810080157929891692257 74670607560118447418769193)
        ·
          refine ⟨56002955670088835564076895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74670607560118447418769193 56002955670088835564076895)
          ·
            refine ⟨84004433505133253346115343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56002955670088835564076895 84004433505133253346115343)
            ·
              refine ⟨126006650257699880019173015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84004433505133253346115343 126006650257699880019173015)
              ·
                refine ⟨189009975386549820028759523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126006650257699880019173015 189009975386549820028759523)
                ·
                  refine ⟨283514963079824730043139285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189009975386549820028759523 283514963079824730043139285)
                  ·
                    refine ⟨6644881947183392110386077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 283514963079824730043139285 6644881947183392110386077)
                    ·
                      refine ⟨2491830730193772041394779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6644881947183392110386077 2491830730193772041394779)
                      ·
                        rfl

theorem cell23_4852823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_4852823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852823 prefixEnd_4852823 := by exact prefixLift 4852823
  have htrace : WordTrace (prefixWord ++ tailWord_4852823) baseStart_4852823 baseEnd_4852823 := by
    simpa [prefixWord, tailWord_4852823, baseEnd_4852823] using wordTrace_append hprefix tailTrace_4852823
  have hstable : (prefixWord ++ tailWord_4852823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852823).length < 2 ^ (prefixWord ++ tailWord_4852823).sum := by decide
  have hdescent : baseEnd_4852823 < baseStart_4852823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852880 : List Nat := [2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 4]
def baseStart_4852880 : Nat := 118140960795 + 4852880 * 2 ^ 59
def prefixEnd_4852880 : Nat := 4983230072969 + 3 ^ 40 * 4852880 * 2
def baseEnd_4852880 : Nat := 2491859998591078318382017

theorem tailTrace_4852880 : CollatzResearch.WordTrace tailWord_4852880 prefixEnd_4852880 2491859998591078318382017 := by
  unfold tailWord_4852880
  simp only [CollatzResearch.WordTrace]
  refine ⟨88499537329426020382250047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117999383105901360509666729 88499537329426020382250047)
  ·
    refine ⟨132749305994139030573375071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88499537329426020382250047 132749305994139030573375071)
    ·
      refine ⟨199123958991208545860062607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132749305994139030573375071 199123958991208545860062607)
      ·
        refine ⟨298685938486812818790093911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199123958991208545860062607 298685938486812818790093911)
        ·
          refine ⟨448028907730219228185140867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298685938486812818790093911 448028907730219228185140867)
          ·
            refine ⟨672043361595328842277711301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448028907730219228185140867 672043361595328842277711301)
            ·
              refine ⟨126008130299124157927070869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 672043361595328842277711301 126008130299124157927070869)
              ·
                refine ⟨5906631107771444902831447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 126008130299124157927070869 5906631107771444902831447)
                ·
                  refine ⟨8859946661657167354247171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5906631107771444902831447 8859946661657167354247171)
                  ·
                    refine ⟨13289919992485751031370757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8859946661657167354247171 13289919992485751031370757)
                    ·
                      refine ⟨2491859998591078318382017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13289919992485751031370757 2491859998591078318382017)
                      ·
                        rfl

theorem cell23_4852880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 4].length) (baseStart_4852880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852880 prefixEnd_4852880 := by exact prefixLift 4852880
  have htrace : WordTrace (prefixWord ++ tailWord_4852880) baseStart_4852880 baseEnd_4852880 := by
    simpa [prefixWord, tailWord_4852880, baseEnd_4852880] using wordTrace_append hprefix tailTrace_4852880
  have hstable : (prefixWord ++ tailWord_4852880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852880).length < 2 ^ (prefixWord ++ tailWord_4852880).sum := by decide
  have hdescent : baseEnd_4852880 < baseStart_4852880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852883 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 5]
def baseStart_4852883 : Nat := 118140960795 + 4852883 * 2 ^ 59
def prefixEnd_4852883 : Nat := 4983230072969 + 3 ^ 40 * 4852883 * 2
def baseEnd_4852883 : Nat := 2491861539033041806644503

theorem tailTrace_4852883 : CollatzResearch.WordTrace tailWord_4852883 prefixEnd_4852883 2491861539033041806644503 := by
  unfold tailWord_4852883
  simp only [CollatzResearch.WordTrace]
  refine ⟨176999184077841172276859303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117999456051894114851239535 176999184077841172276859303)
  ·
    refine ⟨265498776116761758415288955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176999184077841172276859303 265498776116761758415288955)
    ·
      refine ⟨398248164175142637622933433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265498776116761758415288955 398248164175142637622933433)
      ·
        refine ⟨298686123131356978217200075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 398248164175142637622933433 298686123131356978217200075)
        ·
          refine ⟨448029184697035467325800113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298686123131356978217200075 448029184697035467325800113)
          ·
            refine ⟨336021888522776600494350085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 448029184697035467325800113 336021888522776600494350085)
            ·
              refine ⟨63004104098020612592690641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 336021888522776600494350085 63004104098020612592690641)
              ·
                refine ⟨47253078073515459444517981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63004104098020612592690641 47253078073515459444517981)
                ·
                  refine ⟨17719904277568297291694243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47253078073515459444517981 17719904277568297291694243)
                  ·
                    refine ⟨26579856416352445937541365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17719904277568297291694243 26579856416352445937541365)
                    ·
                      refine ⟨2491861539033041806644503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26579856416352445937541365 2491861539033041806644503)
                      ·
                        rfl

theorem cell23_4852883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 5].length) (baseStart_4852883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852883 prefixEnd_4852883 := by exact prefixLift 4852883
  have htrace : WordTrace (prefixWord ++ tailWord_4852883) baseStart_4852883 baseEnd_4852883 := by
    simpa [prefixWord, tailWord_4852883, baseEnd_4852883] using wordTrace_append hprefix tailTrace_4852883
  have hstable : (prefixWord ++ tailWord_4852883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852883).length < 2 ^ (prefixWord ++ tailWord_4852883).sum := by decide
  have hdescent : baseEnd_4852883 < baseStart_4852883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852890 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 3, 6]
def baseStart_4852890 : Nat := 118140960795 + 4852890 * 2 ^ 59
def prefixEnd_4852890 : Nat := 4983230072969 + 3 ^ 40 * 4852890 * 2
def baseEnd_4852890 : Nat := 830621711132541093085657

theorem tailTrace_4852890 : CollatzResearch.WordTrace tailWord_4852890 prefixEnd_4852890 830621711132541093085657 := by
  unfold tailWord_4852890
  simp only [CollatzResearch.WordTrace]
  refine ⟨44249859847203953118091031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117999626259210541648242749 44249859847203953118091031)
  ·
    refine ⟨66374789770805929677136547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44249859847203953118091031 66374789770805929677136547)
    ·
      refine ⟨99562184656208894515704821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66374789770805929677136547 99562184656208894515704821)
      ·
        refine ⟨9333954811519583860847327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99562184656208894515704821 9333954811519583860847327)
        ·
          refine ⟨14000932217279375791270991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9333954811519583860847327 14000932217279375791270991)
          ·
            refine ⟨21001398325919063686906487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14000932217279375791270991 21001398325919063686906487)
            ·
              refine ⟨31502097488878595530359731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21001398325919063686906487 31502097488878595530359731)
              ·
                refine ⟨47253146233317893295539597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31502097488878595530359731 47253146233317893295539597)
                ·
                  refine ⟨17719929837494209985827349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47253146233317893295539597 17719929837494209985827349)
                  ·
                    refine ⟨830621711132541093085657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17719929837494209985827349 830621711132541093085657)
                    ·
                      rfl

theorem cell23_4852890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_4852890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852890 prefixEnd_4852890 := by exact prefixLift 4852890
  have htrace : WordTrace (prefixWord ++ tailWord_4852890) baseStart_4852890 baseEnd_4852890 := by
    simpa [prefixWord, tailWord_4852890, baseEnd_4852890] using wordTrace_append hprefix tailTrace_4852890
  have hstable : (prefixWord ++ tailWord_4852890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852890).length < 2 ^ (prefixWord ++ tailWord_4852890).sum := by decide
  have hdescent : baseEnd_4852890 < baseStart_4852890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852933 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 4, 7]
def baseStart_4852933 : Nat := 118140960795 + 4852933 * 2 ^ 59
def prefixEnd_4852933 : Nat := 4983230072969 + 3 ^ 40 * 4852933 * 2
def baseEnd_4852933 : Nat := 830629071021922203673091

theorem tailTrace_4852933 : CollatzResearch.WordTrace tailWord_4852933 prefixEnd_4852933 830629071021922203673091 := by
  unfold tailWord_4852933
  simp only [CollatzResearch.WordTrace]
  refine ⟨177001007727660030816179453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118000671818440020544119635 177001007727660030816179453)
  ·
    refine ⟨66375377897872511556067295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177001007727660030816179453 66375377897872511556067295)
    ·
      refine ⟨99563066846808767334100943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66375377897872511556067295 99563066846808767334100943)
      ·
        refine ⟨149344600270213151001151415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99563066846808767334100943 149344600270213151001151415)
        ·
          refine ⟨224016900405319726501727123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149344600270213151001151415 224016900405319726501727123)
          ·
            refine ⟨336025350607979589752590685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224016900405319726501727123 336025350607979589752590685)
            ·
              refine ⟨126009506477992346157221507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 336025350607979589752590685 126009506477992346157221507)
              ·
                refine ⟨189014259716988519235832261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126009506477992346157221507 189014259716988519235832261)
                ·
                  refine ⟨35440173696935347356718549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 189014259716988519235832261 35440173696935347356718549)
                  ·
                    refine ⟨830629071021922203673091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35440173696935347356718549 830629071021922203673091)
                    ·
                      rfl

theorem cell23_4852933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_4852933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852933 prefixEnd_4852933 := by exact prefixLift 4852933
  have htrace : WordTrace (prefixWord ++ tailWord_4852933) baseStart_4852933 baseEnd_4852933 := by
    simpa [prefixWord, tailWord_4852933, baseEnd_4852933] using wordTrace_append hprefix tailTrace_4852933
  have hstable : (prefixWord ++ tailWord_4852933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852933).length < 2 ^ (prefixWord ++ tailWord_4852933).sum := by decide
  have hdescent : baseEnd_4852933 < baseStart_4852933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852948 : List Nat := [2, 4, 1, 4, 1, 2, 2, 1, 1, 1, 4]
def baseStart_4852948 : Nat := 118140960795 + 4852948 * 2 ^ 59
def prefixEnd_4852948 : Nat := 4983230072969 + 3 ^ 40 * 4852948 * 2
def baseEnd_4852948 : Nat := 2491894915275584052331705

theorem tailTrace_4852948 : CollatzResearch.WordTrace tailWord_4852948 prefixEnd_4852948 2491894915275584052331705 := by
  unfold tailWord_4852948
  simp only [CollatzResearch.WordTrace]
  refine ⟨88500777411302844188987749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118001036548403792251983665 88500777411302844188987749)
  ·
    refine ⟨16593895764619283285435203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88500777411302844188987749 16593895764619283285435203)
    ·
      refine ⟨24890843646928924928152805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16593895764619283285435203 24890843646928924928152805)
      ·
        refine ⟨4667033183799173424028651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24890843646928924928152805 4667033183799173424028651)
        ·
          refine ⟨7000549775698760136042977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4667033183799173424028651 7000549775698760136042977)
          ·
            refine ⟨5250412331774070102032233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7000549775698760136042977 5250412331774070102032233)
            ·
              refine ⟨3937809248830552576524175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5250412331774070102032233 3937809248830552576524175)
              ·
                refine ⟨5906713873245828864786263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3937809248830552576524175 5906713873245828864786263)
                ·
                  refine ⟨8860070809868743297179395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5906713873245828864786263 8860070809868743297179395)
                  ·
                    refine ⟨13290106214803114945769093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8860070809868743297179395 13290106214803114945769093)
                    ·
                      refine ⟨2491894915275584052331705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13290106214803114945769093 2491894915275584052331705)
                      ·
                        rfl

theorem cell23_4852948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_4852948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852948 prefixEnd_4852948 := by exact prefixLift 4852948
  have htrace : WordTrace (prefixWord ++ tailWord_4852948) baseStart_4852948 baseEnd_4852948 := by
    simpa [prefixWord, tailWord_4852948, baseEnd_4852948] using wordTrace_append hprefix tailTrace_4852948
  have hstable : (prefixWord ++ tailWord_4852948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852948).length < 2 ^ (prefixWord ++ tailWord_4852948).sum := by decide
  have hdescent : baseEnd_4852948 < baseStart_4852948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4852964 : List Nat := [2, 3, 1, 1, 1, 2, 5, 2, 2, 1, 3]
def baseStart_4852964 : Nat := 118140960795 + 4852964 * 2 ^ 59
def prefixEnd_4852964 : Nat := 4983230072969 + 3 ^ 40 * 4852964 * 2
def baseEnd_4852964 : Nat := 2491903130966055989731631

theorem tailTrace_4852964 : CollatzResearch.WordTrace tailWord_4852964 prefixEnd_4852964 2491903130966055989731631 := by
  unfold tailWord_4852964
  simp only [CollatzResearch.WordTrace]
  refine ⟨88501069195273861555278973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118001425593698482073705297 88501069195273861555278973)
  ·
    refine ⟨33187900948227698083229615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88501069195273861555278973 33187900948227698083229615)
    ·
      refine ⟨49781851422341547124844423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33187900948227698083229615 49781851422341547124844423)
      ·
        refine ⟨74672777133512320687266635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49781851422341547124844423 74672777133512320687266635)
        ·
          refine ⟨112009165700268481030899953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74672777133512320687266635 112009165700268481030899953)
          ·
            refine ⟨84006874275201360773174965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112009165700268481030899953 84006874275201360773174965)
            ·
              refine ⟨7875644463300127572485153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84006874275201360773174965 7875644463300127572485153)
              ·
                refine ⟨5906733347475095679363865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7875644463300127572485153 5906733347475095679363865)
                ·
                  refine ⟨4430050010606321759522899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5906733347475095679363865 4430050010606321759522899)
                  ·
                    refine ⟨6645075015909482639284349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4430050010606321759522899 6645075015909482639284349)
                    ·
                      refine ⟨2491903130966055989731631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6645075015909482639284349 2491903130966055989731631)
                      ·
                        rfl

theorem cell23_4852964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_4852964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4852964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4852964 prefixEnd_4852964 := by exact prefixLift 4852964
  have htrace : WordTrace (prefixWord ++ tailWord_4852964) baseStart_4852964 baseEnd_4852964 := by
    simpa [prefixWord, tailWord_4852964, baseEnd_4852964] using wordTrace_append hprefix tailTrace_4852964
  have hstable : (prefixWord ++ tailWord_4852964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4852964).length < 2 ^ (prefixWord ++ tailWord_4852964).sum := by decide
  have hdescent : baseEnd_4852964 < baseStart_4852964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4852964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853004 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 4, 2, 2]
def baseStart_4853004 : Nat := 118140960795 + 4853004 * 2 ^ 59
def prefixEnd_4853004 : Nat := 4983230072969 + 3 ^ 40 * 4853004 * 2
def baseEnd_4853004 : Nat := 2491923670192235833231447

theorem tailTrace_4853004 : CollatzResearch.WordTrace tailWord_4853004 prefixEnd_4853004 2491923670192235833231447 := by
  unfold tailWord_4853004
  simp only [CollatzResearch.WordTrace]
  refine ⟨88501798655201404971007033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118002398206935206628009377 88501798655201404971007033)
  ·
    refine ⟨66376348991401053728255275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88501798655201404971007033 66376348991401053728255275)
    ·
      refine ⟨99564523487101580592382913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66376348991401053728255275 99564523487101580592382913)
      ·
        refine ⟨74673392615326185444287185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99564523487101580592382913 74673392615326185444287185)
        ·
          refine ⟨56005044461494639083215389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74673392615326185444287185 56005044461494639083215389)
          ·
            refine ⟨21001891673060489656205771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56005044461494639083215389 21001891673060489656205771)
            ·
              refine ⟨31502837509590734484308657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21001891673060489656205771 31502837509590734484308657)
              ·
                refine ⟨23627128132193050863231493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31502837509590734484308657 23627128132193050863231493)
                ·
                  refine ⟨4430086524786197036855905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23627128132193050863231493 4430086524786197036855905)
                  ·
                    refine ⟨3322564893589647777641929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4430086524786197036855905 3322564893589647777641929)
                    ·
                      refine ⟨2491923670192235833231447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3322564893589647777641929 2491923670192235833231447)
                      ·
                        rfl

theorem cell23_4853004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 4, 2, 2].length) (baseStart_4853004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853004 prefixEnd_4853004 := by exact prefixLift 4853004
  have htrace : WordTrace (prefixWord ++ tailWord_4853004) baseStart_4853004 baseEnd_4853004 := by
    simpa [prefixWord, tailWord_4853004, baseEnd_4853004] using wordTrace_append hprefix tailTrace_4853004
  have hstable : (prefixWord ++ tailWord_4853004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853004).length < 2 ^ (prefixWord ++ tailWord_4853004).sum := by decide
  have hdescent : baseEnd_4853004 < baseStart_4853004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853021 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 4, 2, 2]
def baseStart_4853021 : Nat := 118140960795 + 4853021 * 2 ^ 59
def prefixEnd_4853021 : Nat := 4983230072969 + 3 ^ 40 * 4853021 * 2
def baseEnd_4853021 : Nat := 2491932399363362266718869

theorem tailTrace_4853021 : CollatzResearch.WordTrace tailWord_4853021 prefixEnd_4853021 2491932399363362266718869 := by
  unfold tailWord_4853021
  simp only [CollatzResearch.WordTrace]
  refine ⟨177004217351341221845382917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118002811567560814563588611 177004217351341221845382917)
  ·
    refine ⟨33188290753376479096009297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177004217351341221845382917 33188290753376479096009297)
    ·
      refine ⟨24891218065032359322006973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33188290753376479096009297 24891218065032359322006973)
      ·
        refine ⟨9334206774387134745752615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24891218065032359322006973 9334206774387134745752615)
        ·
          refine ⟨14001310161580702118628923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9334206774387134745752615 14001310161580702118628923)
          ·
            refine ⟨21001965242371053177943385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14001310161580702118628923 21001965242371053177943385)
            ·
              refine ⟨15751473931778289883457539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21001965242371053177943385 15751473931778289883457539)
              ·
                refine ⟨23627210897667434825186309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15751473931778289883457539 23627210897667434825186309)
                ·
                  refine ⟨4430102043312644029722433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23627210897667434825186309 4430102043312644029722433)
                  ·
                    refine ⟨3322576532484483022291825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4430102043312644029722433 3322576532484483022291825)
                    ·
                      refine ⟨2491932399363362266718869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3322576532484483022291825 2491932399363362266718869)
                      ·
                        rfl

theorem cell23_4853021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_4853021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853021 prefixEnd_4853021 := by exact prefixLift 4853021
  have htrace : WordTrace (prefixWord ++ tailWord_4853021) baseStart_4853021 baseEnd_4853021 := by
    simpa [prefixWord, tailWord_4853021, baseEnd_4853021] using wordTrace_append hprefix tailTrace_4853021
  have hstable : (prefixWord ++ tailWord_4853021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853021).length < 2 ^ (prefixWord ++ tailWord_4853021).sum := by decide
  have hdescent : baseEnd_4853021 < baseStart_4853021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853027 : List Nat := [1, 1, 1, 4, 2, 5, 1, 1, 7]
def baseStart_4853027 : Nat := 118140960795 + 4853027 * 2 ^ 59
def prefixEnd_4853027 : Nat := 4983230072969 + 3 ^ 40 * 4853027 * 2
def baseEnd_4853027 : Nat := 276881720027476582582649

theorem tailTrace_4853027 : CollatzResearch.WordTrace tailWord_4853027 prefixEnd_4853027 276881720027476582582649 := by
  unfold tailWord_4853027
  simp only [CollatzResearch.WordTrace]
  refine ⟨177004436189319484870101335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118002957459546323246734223 177004436189319484870101335)
  ·
    refine ⟨265506654283979227305152003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177004436189319484870101335 265506654283979227305152003)
    ·
      refine ⟨398259981425968840957728005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265506654283979227305152003 398259981425968840957728005)
      ·
        refine ⟨74673746517369157679574001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 398259981425968840957728005 74673746517369157679574001)
        ·
          refine ⟨56005309888026868259680501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74673746517369157679574001 56005309888026868259680501)
          ·
            refine ⟨5250497802002518899345047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56005309888026868259680501 5250497802002518899345047)
            ·
              refine ⟨7875746703003778349017571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5250497802002518899345047 7875746703003778349017571)
              ·
                refine ⟨11813620054505667523526357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7875746703003778349017571 11813620054505667523526357)
                ·
                  refine ⟨276881720027476582582649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11813620054505667523526357 276881720027476582582649)
                  ·
                    rfl

theorem cell23_4853027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 7].length) (baseStart_4853027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853027 prefixEnd_4853027 := by exact prefixLift 4853027
  have htrace : WordTrace (prefixWord ++ tailWord_4853027) baseStart_4853027 baseEnd_4853027 := by
    simpa [prefixWord, tailWord_4853027, baseEnd_4853027] using wordTrace_append hprefix tailTrace_4853027
  have hstable : (prefixWord ++ tailWord_4853027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853027).length < 2 ^ (prefixWord ++ tailWord_4853027).sum := by decide
  have hdescent : baseEnd_4853027 < baseStart_4853027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853040 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 4, 5]
def baseStart_4853040 : Nat := 118140960795 + 4853040 * 2 ^ 59
def prefixEnd_4853040 : Nat := 4983230072969 + 3 ^ 40 * 4853040 * 2
def baseEnd_4853040 : Nat := 830647385165265897460427

theorem tailTrace_4853040 : CollatzResearch.WordTrace tailWord_4853040 prefixEnd_4853040 830647385165265897460427 := by
  unfold tailWord_4853040
  simp only [CollatzResearch.WordTrace]
  refine ⟨88502455169136194045162287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118003273558848258726883049 88502455169136194045162287)
  ·
    refine ⟨132753682753704291067743431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88502455169136194045162287 132753682753704291067743431)
    ·
      refine ⟨199130524130556436601615147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132753682753704291067743431 199130524130556436601615147)
      ·
        refine ⟨298695786195834654902422721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199130524130556436601615147 298695786195834654902422721)
        ·
          refine ⟨224021839646875991176817041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298695786195834654902422721 224021839646875991176817041)
          ·
            refine ⟨168016379735156993382612781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224021839646875991176817041 168016379735156993382612781)
            ·
              refine ⟨63006142400683872518479793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168016379735156993382612781 63006142400683872518479793)
              ·
                refine ⟨47254606800512904388859845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63006142400683872518479793 47254606800512904388859845)
                ·
                  refine ⟨8860238775096169572911221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47254606800512904388859845 8860238775096169572911221)
                  ·
                    refine ⟨830647385165265897460427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8860238775096169572911221 830647385165265897460427)
                    ·
                      rfl

theorem cell23_4853040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 4, 5].length) (baseStart_4853040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853040 prefixEnd_4853040 := by exact prefixLift 4853040
  have htrace : WordTrace (prefixWord ++ tailWord_4853040) baseStart_4853040 baseEnd_4853040 := by
    simpa [prefixWord, tailWord_4853040, baseEnd_4853040] using wordTrace_append hprefix tailTrace_4853040
  have hstable : (prefixWord ++ tailWord_4853040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853040).length < 2 ^ (prefixWord ++ tailWord_4853040).sum := by decide
  have hdescent : baseEnd_4853040 < baseStart_4853040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853050 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7]
def baseStart_4853050 : Nat := 118140960795 + 4853050 * 2 ^ 59
def prefixEnd_4853050 : Nat := 4983230072969 + 3 ^ 40 * 4853050 * 2
def baseEnd_4853050 : Nat := 2491947290302342653256235

theorem tailTrace_4853050 : CollatzResearch.WordTrace tailWord_4853050 prefixEnd_4853050 2491947290302342653256235 := by
  unfold tailWord_4853050
  simp only [CollatzResearch.WordTrace]
  refine ⟨44251318767059039949547151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118003516712157439865459069 44251318767059039949547151)
  ·
    refine ⟨66376978150588559924320727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44251318767059039949547151 66376978150588559924320727)
    ·
      refine ⟨99565467225882839886481091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66376978150588559924320727 99565467225882839886481091)
      ·
        refine ⟨149348200838824259829721637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99565467225882839886481091 149348200838824259829721637)
        ·
          refine ⟨28002787657279548718072807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149348200838824259829721637 28002787657279548718072807)
          ·
            refine ⟨42004181485919323077109211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28002787657279548718072807 42004181485919323077109211)
            ·
              refine ⟨63006272228878984615663817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42004181485919323077109211 63006272228878984615663817)
              ·
                refine ⟨47254704171659238461747863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63006272228878984615663817 47254704171659238461747863)
                ·
                  refine ⟨70882056257488857692621795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47254704171659238461747863 70882056257488857692621795)
                  ·
                    refine ⟨106323084386233286538932693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70882056257488857692621795 106323084386233286538932693)
                    ·
                      refine ⟨2491947290302342653256235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 106323084386233286538932693 2491947290302342653256235)
                      ·
                        rfl

theorem cell23_4853050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_4853050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853050 prefixEnd_4853050 := by exact prefixLift 4853050
  have htrace : WordTrace (prefixWord ++ tailWord_4853050) baseStart_4853050 baseEnd_4853050 := by
    simpa [prefixWord, tailWord_4853050, baseEnd_4853050] using wordTrace_append hprefix tailTrace_4853050
  have hstable : (prefixWord ++ tailWord_4853050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853050).length < 2 ^ (prefixWord ++ tailWord_4853050).sum := by decide
  have hdescent : baseEnd_4853050 < baseStart_4853050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853080 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 2, 3, 5]
def baseStart_4853080 : Nat := 118140960795 + 4853080 * 2 ^ 59
def prefixEnd_4853080 : Nat := 4983230072969 + 3 ^ 40 * 4853080 * 2
def baseEnd_4853080 : Nat := 2491962694721977535881097

theorem tailTrace_4853080 : CollatzResearch.WordTrace tailWord_4853080 prefixEnd_4853080 2491962694721977535881097 := by
  unfold tailWord_4853080
  simp only [CollatzResearch.WordTrace]
  refine ⟨88503184629063737460890347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118004246172084983281187129 88503184629063737460890347)
  ·
    refine ⟨132754776943595606191335521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88503184629063737460890347 132754776943595606191335521)
    ·
      refine ⟨99566082707696704643501641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132754776943595606191335521 99566082707696704643501641)
      ·
        refine ⟨74674562030772528482626231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99566082707696704643501641 74674562030772528482626231)
        ·
          refine ⟨112011843046158792723939347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74674562030772528482626231 112011843046158792723939347)
          ·
            refine ⟨168017764569238189085909021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112011843046158792723939347 168017764569238189085909021)
            ·
              refine ⟨63006661713464320907215883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168017764569238189085909021 63006661713464320907215883)
              ·
                refine ⟨94509992570196481360823825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63006661713464320907215883 94509992570196481360823825)
                ·
                  refine ⟨70882494427647361020617869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94509992570196481360823825 70882494427647361020617869)
                  ·
                    refine ⟨26580935410367760382731701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70882494427647361020617869 26580935410367760382731701)
                    ·
                      refine ⟨2491962694721977535881097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26580935410367760382731701 2491962694721977535881097)
                      ·
                        rfl

theorem cell23_4853080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_4853080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853080 prefixEnd_4853080 := by exact prefixLift 4853080
  have htrace : WordTrace (prefixWord ++ tailWord_4853080) baseStart_4853080 baseEnd_4853080 := by
    simpa [prefixWord, tailWord_4853080, baseEnd_4853080] using wordTrace_append hprefix tailTrace_4853080
  have hstable : (prefixWord ++ tailWord_4853080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853080).length < 2 ^ (prefixWord ++ tailWord_4853080).sum := by decide
  have hdescent : baseEnd_4853080 < baseStart_4853080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853087 : List Nat := [1, 1, 2, 3, 1, 2, 1, 5, 3, 4]
def baseStart_4853087 : Nat := 118140960795 + 4853087 * 2 ^ 59
def prefixEnd_4853087 : Nat := 4983230072969 + 3 ^ 40 * 4853087 * 2
def baseEnd_4853087 : Nat := 830655429695519669497855

theorem tailTrace_4853087 : CollatzResearch.WordTrace tailWord_4853087 prefixEnd_4853087 830655429695519669497855 := by
  unfold tailWord_4853087
  simp only [CollatzResearch.WordTrace]
  refine ⟨177006624569102115117285515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118004416379401410078190343 177006624569102115117285515)
  ·
    refine ⟨265509936853653172675928273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177006624569102115117285515 265509936853653172675928273)
    ·
      refine ⟨199132452640239879506946205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265509936853653172675928273 199132452640239879506946205)
      ·
        refine ⟨74674669740089954815104827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199132452640239879506946205 74674669740089954815104827)
        ·
          refine ⟨112012004610134932222657241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74674669740089954815104827 112012004610134932222657241)
          ·
            refine ⟨84009003457601199166992931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112012004610134932222657241 84009003457601199166992931)
            ·
              refine ⟨126013505186401798750489397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84009003457601199166992931 126013505186401798750489397)
              ·
                refine ⟨11813766111225168632858381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126013505186401798750489397 11813766111225168632858381)
                ·
                  refine ⟨4430162291709438237321893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11813766111225168632858381 4430162291709438237321893)
                  ·
                    refine ⟨830655429695519669497855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4430162291709438237321893 830655429695519669497855)
                    ·
                      rfl

theorem cell23_4853087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 4].length) (baseStart_4853087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853087 prefixEnd_4853087 := by exact prefixLift 4853087
  have htrace : WordTrace (prefixWord ++ tailWord_4853087) baseStart_4853087 baseEnd_4853087 := by
    simpa [prefixWord, tailWord_4853087, baseEnd_4853087] using wordTrace_append hprefix tailTrace_4853087
  have hstable : (prefixWord ++ tailWord_4853087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853087).length < 2 ^ (prefixWord ++ tailWord_4853087).sum := by decide
  have hdescent : baseEnd_4853087 < baseStart_4853087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853120 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 6]
def baseStart_4853120 : Nat := 118140960795 + 4853120 * 2 ^ 59
def prefixEnd_4853120 : Nat := 4983230072969 + 3 ^ 40 * 4853120 * 2
def baseEnd_4853120 : Nat := 2491983233948157379380913

theorem tailTrace_4853120 : CollatzResearch.WordTrace tailWord_4853120 prefixEnd_4853120 2491983233948157379380913 := by
  unfold tailWord_4853120
  simp only [CollatzResearch.WordTrace]
  refine ⟨88503914088991280876618407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118005218785321707835491209 88503914088991280876618407)
  ·
    refine ⟨132755871133486921314927611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88503914088991280876618407 132755871133486921314927611)
    ·
      refine ⟨199133806700230381972391417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132755871133486921314927611 199133806700230381972391417)
      ·
        refine ⟨149350355025172786479293563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199133806700230381972391417 149350355025172786479293563)
        ·
          refine ⟨224025532537759179718940345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149350355025172786479293563 224025532537759179718940345)
          ·
            refine ⟨168019149403319384789205259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224025532537759179718940345 168019149403319384789205259)
            ·
              refine ⟨252028724104979077183807889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168019149403319384789205259 252028724104979077183807889)
              ·
                refine ⟨189021543078734307887855917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252028724104979077183807889 189021543078734307887855917)
                ·
                  refine ⟨70883078654525365457945969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189021543078734307887855917 70883078654525365457945969)
                  ·
                    refine ⟨53162308990894024093459477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70883078654525365457945969 53162308990894024093459477)
                    ·
                      refine ⟨2491983233948157379380913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53162308990894024093459477 2491983233948157379380913)
                      ·
                        rfl

theorem cell23_4853120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_4853120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853120 prefixEnd_4853120 := by exact prefixLift 4853120
  have htrace : WordTrace (prefixWord ++ tailWord_4853120) baseStart_4853120 baseEnd_4853120 := by
    simpa [prefixWord, tailWord_4853120, baseEnd_4853120] using wordTrace_append hprefix tailTrace_4853120
  have hstable : (prefixWord ++ tailWord_4853120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853120).length < 2 ^ (prefixWord ++ tailWord_4853120).sum := by decide
  have hdescent : baseEnd_4853120 < baseStart_4853120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853134 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 8]
def baseStart_4853134 : Nat := 118140960795 + 4853134 * 2 ^ 59
def prefixEnd_4853134 : Nat := 4983230072969 + 3 ^ 40 * 4853134 * 2
def baseEnd_4853134 : Nat := 276887824741924480511761

theorem tailTrace_4853134 : CollatzResearch.WordTrace tailWord_4853134 prefixEnd_4853134 276887824741924480511761 := by
  unfold tailWord_4853134
  simp only [CollatzResearch.WordTrace]
  refine ⟨22126042349991480268030807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118005559199954561429497637 22126042349991480268030807)
  ·
    refine ⟨33189063524987220402046211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22126042349991480268030807 33189063524987220402046211)
    ·
      refine ⟨49783595287480830603069317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33189063524987220402046211 49783595287480830603069317)
      ·
        refine ⟨9334424116402655738075497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49783595287480830603069317 9334424116402655738075497)
        ·
          refine ⟨7000818087301991803556623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9334424116402655738075497 7000818087301991803556623)
          ·
            refine ⟨10501227130952987705334935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7000818087301991803556623 10501227130952987705334935)
            ·
              refine ⟨15751840696429481558002403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10501227130952987705334935 15751840696429481558002403)
              ·
                refine ⟨23627761044644222337003605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15751840696429481558002403 23627761044644222337003605)
                ·
                  refine ⟨276887824741924480511761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23627761044644222337003605 276887824741924480511761)
                  ·
                    rfl

theorem cell23_4853134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_4853134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853134 prefixEnd_4853134 := by exact prefixLift 4853134
  have htrace : WordTrace (prefixWord ++ tailWord_4853134) baseStart_4853134 baseEnd_4853134 := by
    simpa [prefixWord, tailWord_4853134, baseEnd_4853134] using wordTrace_append hprefix tailTrace_4853134
  have hstable : (prefixWord ++ tailWord_4853134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853134).length < 2 ^ (prefixWord ++ tailWord_4853134).sum := by decide
  have hdescent : baseEnd_4853134 < baseStart_4853134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853138 : List Nat := [3, 2, 3, 3, 1, 1, 2, 1, 3, 4]
def baseStart_4853138 : Nat := 118140960795 + 4853138 * 2 ^ 59
def prefixEnd_4853138 : Nat := 4983230072969 + 3 ^ 40 * 4853138 * 2
def baseEnd_4853138 : Nat := 830664158866646102985277

theorem tailTrace_4853138 : CollatzResearch.WordTrace tailWord_4853138 prefixEnd_4853138 830664158866646102985277 := by
  unfold tailWord_4853138
  simp only [CollatzResearch.WordTrace]
  refine ⟨44252121172979337706848017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118005656461278233884928045 44252121172979337706848017)
  ·
    refine ⟨33189090879734503280136013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44252121172979337706848017 33189090879734503280136013)
    ·
      refine ⟨12445909079900438730051005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33189090879734503280136013 12445909079900438730051005)
      ·
        refine ⟨4667215904962664523769127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12445909079900438730051005 4667215904962664523769127)
        ·
          refine ⟨7000823857443996785653691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4667215904962664523769127 7000823857443996785653691)
          ·
            refine ⟨10501235786165995178480537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7000823857443996785653691 10501235786165995178480537)
            ·
              refine ⟨7875926839624496383860403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10501235786165995178480537 7875926839624496383860403)
              ·
                refine ⟨11813890259436744575790605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7875926839624496383860403 11813890259436744575790605)
                ·
                  refine ⟨4430208847288779215921477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11813890259436744575790605 4430208847288779215921477)
                  ·
                    refine ⟨830664158866646102985277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4430208847288779215921477 830664158866646102985277)
                    ·
                      rfl

theorem cell23_4853138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_4853138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853138 prefixEnd_4853138 := by exact prefixLift 4853138
  have htrace : WordTrace (prefixWord ++ tailWord_4853138) baseStart_4853138 baseEnd_4853138 := by
    simpa [prefixWord, tailWord_4853138, baseEnd_4853138] using wordTrace_append hprefix tailTrace_4853138
  have hstable : (prefixWord ++ tailWord_4853138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853138).length < 2 ^ (prefixWord ++ tailWord_4853138).sum := by decide
  have hdescent : baseEnd_4853138 < baseStart_4853138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853167 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 4]
def baseStart_4853167 : Nat := 118140960795 + 4853167 * 2 ^ 59
def prefixEnd_4853167 : Nat := 4983230072969 + 3 ^ 40 * 4853167 * 2
def baseEnd_4853167 : Nat := 2492007367538918695493197

theorem tailTrace_4853167 : CollatzResearch.WordTrace tailWord_4853167 prefixEnd_4853167 2492007367538918695493197 := by
  unfold tailWord_4853167
  simp only [CollatzResearch.WordTrace]
  refine ⟨177009542408812288780197755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118006361605874859186798503 177009542408812288780197755)
  ·
    refine ⟨265514313613218433170296633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177009542408812288780197755 265514313613218433170296633)
    ·
      refine ⟨199135735209913824877722475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265514313613218433170296633 199135735209913824877722475)
      ·
        refine ⟨298703602814870737316583713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199135735209913824877722475 298703602814870737316583713)
        ·
          refine ⟨224027702111153052987437785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298703602814870737316583713 224027702111153052987437785)
          ·
            refine ⟨168020776583364789740578339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224027702111153052987437785 168020776583364789740578339)
            ·
              refine ⟨252031164875047184610867509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168020776583364789740578339 252031164875047184610867509)
              ·
                refine ⟨23627921707035673557268829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 252031164875047184610867509 23627921707035673557268829)
                ·
                  refine ⟨8860470640138377583975811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23627921707035673557268829 8860470640138377583975811)
                  ·
                    refine ⟨13290705960207566375963717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8860470640138377583975811 13290705960207566375963717)
                    ·
                      refine ⟨2492007367538918695493197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13290705960207566375963717 2492007367538918695493197)
                      ·
                        rfl

theorem cell23_4853167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 4].length) (baseStart_4853167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853167 prefixEnd_4853167 := by exact prefixLift 4853167
  have htrace : WordTrace (prefixWord ++ tailWord_4853167) baseStart_4853167 baseEnd_4853167 := by
    simpa [prefixWord, tailWord_4853167, baseEnd_4853167] using wordTrace_append hprefix tailTrace_4853167
  have hstable : (prefixWord ++ tailWord_4853167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853167).length < 2 ^ (prefixWord ++ tailWord_4853167).sum := by decide
  have hdescent : baseEnd_4853167 < baseStart_4853167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853184 : List Nat := [2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 4]
def baseStart_4853184 : Nat := 118140960795 + 4853184 * 2 ^ 59
def prefixEnd_4853184 : Nat := 4983230072969 + 3 ^ 40 * 4853184 * 2
def baseEnd_4853184 : Nat := 2492016096710045128980619

theorem tailTrace_4853184 : CollatzResearch.WordTrace tailWord_4853184 prefixEnd_4853184 2492016096710045128980619 := by
  unfold tailWord_4853184
  simp only [CollatzResearch.WordTrace]
  refine ⟨88505081224875350341783303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118006774966500467122377737 88505081224875350341783303)
  ·
    refine ⟨132757621837313025512674955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88505081224875350341783303 132757621837313025512674955)
    ·
      refine ⟨199136432755969538269012433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132757621837313025512674955 199136432755969538269012433)
      ·
        refine ⟨149352324566977153701759325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199136432755969538269012433 149352324566977153701759325)
        ·
          refine ⟨56007121712616432638159747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149352324566977153701759325 56007121712616432638159747)
          ·
            refine ⟨84010682568924648957239621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56007121712616432638159747 84010682568924648957239621)
            ·
              refine ⟨15752002981673371679482429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84010682568924648957239621 15752002981673371679482429)
              ·
                refine ⟨5907001118127514379805911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15752002981673371679482429 5907001118127514379805911)
                ·
                  refine ⟨8860501677191271569708867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5907001118127514379805911 8860501677191271569708867)
                  ·
                    refine ⟨13290752515786907354563301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8860501677191271569708867 13290752515786907354563301)
                    ·
                      refine ⟨2492016096710045128980619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13290752515786907354563301 2492016096710045128980619)
                      ·
                        rfl

theorem cell23_4853184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 4].length) (baseStart_4853184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853184 prefixEnd_4853184 := by exact prefixLift 4853184
  have htrace : WordTrace (prefixWord ++ tailWord_4853184) baseStart_4853184 baseEnd_4853184 := by
    simpa [prefixWord, tailWord_4853184, baseEnd_4853184] using wordTrace_append hprefix tailTrace_4853184
  have hstable : (prefixWord ++ tailWord_4853184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853184).length < 2 ^ (prefixWord ++ tailWord_4853184).sum := by decide
  have hdescent : baseEnd_4853184 < baseStart_4853184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853187 : List Nat := [1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 5]
def baseStart_4853187 : Nat := 118140960795 + 4853187 * 2 ^ 59
def prefixEnd_4853187 : Nat := 4983230072969 + 3 ^ 40 * 4853187 * 2
def baseEnd_4853187 : Nat := 2492017637152008617243105

theorem tailTrace_4853187 : CollatzResearch.WordTrace tailWord_4853187 prefixEnd_4853187 2492017637152008617243105 := by
  unfold tailWord_4853187
  simp only [CollatzResearch.WordTrace]
  refine ⟨177010271868739832195925815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118006847912493221463950543 177010271868739832195925815)
  ·
    refine ⟨265515407803109748293888723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177010271868739832195925815 265515407803109748293888723)
    ·
      refine ⟨398273111704664622440833085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265515407803109748293888723 398273111704664622440833085)
      ·
        refine ⟨149352416889249233415312407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 398273111704664622440833085 149352416889249233415312407)
        ·
          refine ⟨224028625333873850122968611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149352416889249233415312407 224028625333873850122968611)
          ·
            refine ⟨336042938000810775184452917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224028625333873850122968611 336042938000810775184452917)
            ·
              refine ⟨31504025437576010173542461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 336042938000810775184452917 31504025437576010173542461)
              ·
                refine ⟨11814009539091003815078423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31504025437576010173542461 11814009539091003815078423)
                ·
                  refine ⟨17721014308636505722617635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11814009539091003815078423 17721014308636505722617635)
                  ·
                    refine ⟨26581521462954758583926453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17721014308636505722617635 26581521462954758583926453)
                    ·
                      refine ⟨2492017637152008617243105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26581521462954758583926453 2492017637152008617243105)
                      ·
                        rfl

theorem cell23_4853187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_4853187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853187 prefixEnd_4853187 := by exact prefixLift 4853187
  have htrace : WordTrace (prefixWord ++ tailWord_4853187) baseStart_4853187 baseEnd_4853187 := by
    simpa [prefixWord, tailWord_4853187, baseEnd_4853187] using wordTrace_append hprefix tailTrace_4853187
  have hstable : (prefixWord ++ tailWord_4853187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853187).length < 2 ^ (prefixWord ++ tailWord_4853187).sum := by decide
  have hdescent : baseEnd_4853187 < baseStart_4853187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853188 : List Nat := [2, 3, 3, 2, 1, 2, 1, 2, 2, 3, 2]
def baseStart_4853188 : Nat := 118140960795 + 4853188 * 2 ^ 59
def prefixEnd_4853188 : Nat := 4983230072969 + 3 ^ 40 * 4853188 * 2
def baseEnd_4853188 : Nat := 2492018150632663113330601

theorem tailTrace_4853188 : CollatzResearch.WordTrace tailWord_4853188 prefixEnd_4853188 2492018150632663113330601 := by
  unfold tailWord_4853188
  simp only [CollatzResearch.WordTrace]
  refine ⟨88505154170868104683356109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118006872227824139577808145 88505154170868104683356109)
  ·
    refine ⟨33189432814075539256258541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88505154170868104683356109 33189432814075539256258541)
    ·
      refine ⟨12446037305278327221096953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33189432814075539256258541 12446037305278327221096953)
      ·
        refine ⟨9334527978958745415822715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12446037305278327221096953 9334527978958745415822715)
        ·
          refine ⟨14001791968438118123734073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9334527978958745415822715 14001791968438118123734073)
          ·
            refine ⟨10501343976328588592800555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14001791968438118123734073 10501343976328588592800555)
            ·
              refine ⟨15752015964492882889200833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10501343976328588592800555 15752015964492882889200833)
              ·
                refine ⟨11814011973369662166900625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15752015964492882889200833 11814011973369662166900625)
                ·
                  refine ⟨8860508980027246625175469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11814011973369662166900625 8860508980027246625175469)
                  ·
                    refine ⟨3322690867510217484440801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8860508980027246625175469 3322690867510217484440801)
                    ·
                      refine ⟨2492018150632663113330601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3322690867510217484440801 2492018150632663113330601)
                      ·
                        rfl

theorem cell23_4853188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_4853188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853188 prefixEnd_4853188 := by exact prefixLift 4853188
  have htrace : WordTrace (prefixWord ++ tailWord_4853188) baseStart_4853188 baseEnd_4853188 := by
    simpa [prefixWord, tailWord_4853188, baseEnd_4853188] using wordTrace_append hprefix tailTrace_4853188
  have hstable : (prefixWord ++ tailWord_4853188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853188).length < 2 ^ (prefixWord ++ tailWord_4853188).sum := by decide
  have hdescent : baseEnd_4853188 < baseStart_4853188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853194 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 4, 4]
def baseStart_4853194 : Nat := 118140960795 + 4853194 * 2 ^ 59
def prefixEnd_4853194 : Nat := 4983230072969 + 3 ^ 40 * 4853194 * 2
def baseEnd_4853194 : Nat := 830673743838863363285191

theorem tailTrace_4853194 : CollatzResearch.WordTrace tailWord_4853194 prefixEnd_4853194 830673743838863363285191 := by
  unfold tailWord_4853194
  simp only [CollatzResearch.WordTrace]
  refine ⟨44252631794928618097857659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118007018119809648260953757 44252631794928618097857659)
  ·
    refine ⟨66378947692392927146786489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44252631794928618097857659 66378947692392927146786489)
    ·
      refine ⟨49784210769294695360089867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66378947692392927146786489 49784210769294695360089867)
      ·
        refine ⟨74676316153942043040134801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49784210769294695360089867 74676316153942043040134801)
        ·
          refine ⟨56007237115456532280101101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74676316153942043040134801 56007237115456532280101101)
          ·
            refine ⟨21002713918296199605037913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56007237115456532280101101 21002713918296199605037913)
            ·
              refine ⟨15752035438722149703778435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21002713918296199605037913 15752035438722149703778435)
              ·
                refine ⟨23628053158083224555667653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15752035438722149703778435 23628053158083224555667653)
                ·
                  refine ⟨4430259967140604604187685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23628053158083224555667653 4430259967140604604187685)
                  ·
                    refine ⟨830673743838863363285191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4430259967140604604187685 830673743838863363285191)
                    ·
                      rfl

theorem cell23_4853194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_4853194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853194 prefixEnd_4853194 := by exact prefixLift 4853194
  have htrace : WordTrace (prefixWord ++ tailWord_4853194) baseStart_4853194 baseEnd_4853194 := by
    simpa [prefixWord, tailWord_4853194, baseEnd_4853194] using wordTrace_append hprefix tailTrace_4853194
  have hstable : (prefixWord ++ tailWord_4853194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853194).length < 2 ^ (prefixWord ++ tailWord_4853194).sum := by decide
  have hdescent : baseEnd_4853194 < baseStart_4853194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853221 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 3, 2, 3]
def baseStart_4853221 : Nat := 118140960795 + 4853221 * 2 ^ 59
def prefixEnd_4853221 : Nat := 4983230072969 + 3 ^ 40 * 4853221 * 2
def baseEnd_4853221 : Nat := 2492035095494261484217949

theorem tailTrace_4853221 : CollatzResearch.WordTrace tailWord_4853221 prefixEnd_4853221 2492035095494261484217949 := by
  unfold tailWord_4853221
  simp only [CollatzResearch.WordTrace]
  refine ⟨177011511950616656002663517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118007674633744437335109011 177011511950616656002663517)
  ·
    refine ⟨66379316981481246000998819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177011511950616656002663517 66379316981481246000998819)
    ·
      refine ⟨99568975472221869001498229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66379316981481246000998819 99568975472221869001498229)
      ·
        refine ⟨9334591450520800218890459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99568975472221869001498229 9334591450520800218890459)
        ·
          refine ⟨14001887175781200328335689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9334591450520800218890459 14001887175781200328335689)
          ·
            refine ⟨10501415381835900246251767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14001887175781200328335689 10501415381835900246251767)
            ·
              refine ⟨15752123072753850369377651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10501415381835900246251767 15752123072753850369377651)
              ·
                refine ⟨23628184609130775554066477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15752123072753850369377651 23628184609130775554066477)
                ·
                  refine ⟨8860569228424040832774929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23628184609130775554066477 8860569228424040832774929)
                  ·
                    refine ⟨6645426921318030624581197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8860569228424040832774929 6645426921318030624581197)
                    ·
                      refine ⟨2492035095494261484217949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6645426921318030624581197 2492035095494261484217949)
                      ·
                        rfl

theorem cell23_4853221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_4853221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853221 prefixEnd_4853221 := by exact prefixLift 4853221
  have htrace : WordTrace (prefixWord ++ tailWord_4853221) baseStart_4853221 baseEnd_4853221 := by
    simpa [prefixWord, tailWord_4853221, baseEnd_4853221] using wordTrace_append hprefix tailTrace_4853221
  have hstable : (prefixWord ++ tailWord_4853221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853221).length < 2 ^ (prefixWord ++ tailWord_4853221).sum := by decide
  have hdescent : baseEnd_4853221 < baseStart_4853221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853246 : List Nat := [4, 2, 2, 3, 2, 1, 2, 2, 1, 1, 3]
def baseStart_4853246 : Nat := 118140960795 + 4853246 * 2 ^ 59
def prefixEnd_4853246 : Nat := 4983230072969 + 3 ^ 40 * 4853246 * 2
def baseEnd_4853246 : Nat := 2492047932510623886405335

theorem tailTrace_4853246 : CollatzResearch.WordTrace tailWord_4853246 prefixEnd_4853246 2492047932510623886405335 := by
  unfold tailWord_4853246
  simp only [CollatzResearch.WordTrace]
  refine ⟨22126552971940760659040449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118008282517017390181549061 22126552971940760659040449)
  ·
    refine ⟨16594914728955570494280337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22126552971940760659040449 16594914728955570494280337)
    ·
      refine ⟨12446186046716677870710253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16594914728955570494280337 12446186046716677870710253)
      ·
        refine ⟨4667319767518754201516345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12446186046716677870710253 4667319767518754201516345)
        ·
          refine ⟨3500489825639065651137259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4667319767518754201516345 3500489825639065651137259)
          ·
            refine ⟨5250734738458598476705889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3500489825639065651137259 5250734738458598476705889)
            ·
              refine ⟨3938051053843948857529417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5250734738458598476705889 3938051053843948857529417)
              ·
                refine ⟨2953538290382961643147063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3938051053843948857529417 2953538290382961643147063)
                ·
                  refine ⟨4430307435574442464720595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2953538290382961643147063 4430307435574442464720595)
                  ·
                    refine ⟨6645461153361663697080893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4430307435574442464720595 6645461153361663697080893)
                    ·
                      refine ⟨2492047932510623886405335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6645461153361663697080893 2492047932510623886405335)
                      ·
                        rfl

theorem cell23_4853246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_4853246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853246 prefixEnd_4853246 := by exact prefixLift 4853246
  have htrace : WordTrace (prefixWord ++ tailWord_4853246) baseStart_4853246 baseEnd_4853246 := by
    simpa [prefixWord, tailWord_4853246, baseEnd_4853246] using wordTrace_append hprefix tailTrace_4853246
  have hstable : (prefixWord ++ tailWord_4853246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853246).length < 2 ^ (prefixWord ++ tailWord_4853246).sum := by decide
  have hdescent : baseEnd_4853246 < baseStart_4853246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853252 : List Nat := [2, 3, 2, 3, 2, 1, 1, 4, 1, 2, 2]
def baseStart_4853252 : Nat := 118140960795 + 4853252 * 2 ^ 59
def prefixEnd_4853252 : Nat := 4983230072969 + 3 ^ 40 * 4853252 * 2
def baseEnd_4853252 : Nat := 2492051013394550862930307

theorem tailTrace_4853252 : CollatzResearch.WordTrace tailWord_4853252 prefixEnd_4853252 2492051013394550862930307 := by
  unfold tailWord_4853252
  simp only [CollatzResearch.WordTrace]
  refine ⟨88506321306752174148521005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118008428409002898864694673 88506321306752174148521005)
  ·
    refine ⟨33189870490032065305695377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88506321306752174148521005 33189870490032065305695377)
    ·
      refine ⟨24892402867524048979271533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33189870490032065305695377 24892402867524048979271533)
      ·
        refine ⟨9334651075321518367226825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24892402867524048979271533 9334651075321518367226825)
        ·
          refine ⟨7000988306491138775420119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9334651075321518367226825 7000988306491138775420119)
          ·
            refine ⟨10501482459736708163130179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7000988306491138775420119 10501482459736708163130179)
            ·
              refine ⟨15752223689605062244695269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10501482459736708163130179 15752223689605062244695269)
              ·
                refine ⟨2953541941800949170880363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15752223689605062244695269 2953541941800949170880363)
                ·
                  refine ⟨4430312912701423756320545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2953541941800949170880363 4430312912701423756320545)
                  ·
                    refine ⟨3322734684526067817240409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4430312912701423756320545 3322734684526067817240409)
                    ·
                      refine ⟨2492051013394550862930307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3322734684526067817240409 2492051013394550862930307)
                      ·
                        rfl

theorem cell23_4853252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_4853252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853252 prefixEnd_4853252 := by exact prefixLift 4853252
  have htrace : WordTrace (prefixWord ++ tailWord_4853252) baseStart_4853252 baseEnd_4853252 := by
    simpa [prefixWord, tailWord_4853252, baseEnd_4853252] using wordTrace_append hprefix tailTrace_4853252
  have hstable : (prefixWord ++ tailWord_4853252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853252).length < 2 ^ (prefixWord ++ tailWord_4853252).sum := by decide
  have hdescent : baseEnd_4853252 < baseStart_4853252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853257 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 1, 5, 4]
def baseStart_4853257 : Nat := 118140960795 + 4853257 * 2 ^ 59
def prefixEnd_4853257 : Nat := 4983230072969 + 3 ^ 40 * 4853257 * 2
def baseEnd_4853257 : Nat := 2492053580797823343367783

theorem tailTrace_4853257 : CollatzResearch.WordTrace tailWord_4853257 prefixEnd_4853257 2492053580797823343367783 := by
  unfold tailWord_4853257
  simp only [CollatzResearch.WordTrace]
  refine ⟨177012824978486234150974025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118008549985657489433982683 177012824978486234150974025)
  ·
    refine ⟨132759618733864675613230519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177012824978486234150974025 132759618733864675613230519)
    ·
      refine ⟨199139428100797013419845779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132759618733864675613230519 199139428100797013419845779)
      ·
        refine ⟨298709142151195520129768669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199139428100797013419845779 298709142151195520129768669)
        ·
          refine ⟨112015928306698320048663251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 298709142151195520129768669 112015928306698320048663251)
          ·
            refine ⟨168023892460047480072994877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112015928306698320048663251 168023892460047480072994877)
            ·
              refine ⟨63008959672517805027373079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168023892460047480072994877 63008959672517805027373079)
              ·
                refine ⟨94513439508776707541059619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63008959672517805027373079 94513439508776707541059619)
                ·
                  refine ⟨141770159263165061311589429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94513439508776707541059619 141770159263165061311589429)
                  ·
                    refine ⟨13290952430921724497961509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 141770159263165061311589429 13290952430921724497961509)
                    ·
                      refine ⟨2492053580797823343367783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13290952430921724497961509 2492053580797823343367783)
                      ·
                        rfl

theorem cell23_4853257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 5, 4].length) (baseStart_4853257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853257 prefixEnd_4853257 := by exact prefixLift 4853257
  have htrace : WordTrace (prefixWord ++ tailWord_4853257) baseStart_4853257 baseEnd_4853257 := by
    simpa [prefixWord, tailWord_4853257, baseEnd_4853257] using wordTrace_append hprefix tailTrace_4853257
  have hstable : (prefixWord ++ tailWord_4853257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853257).length < 2 ^ (prefixWord ++ tailWord_4853257).sum := by decide
  have hdescent : baseEnd_4853257 < baseStart_4853257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853267 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 1, 8]
def baseStart_4853267 : Nat := 118140960795 + 4853267 * 2 ^ 59
def prefixEnd_4853267 : Nat := 4983230072969 + 3 ^ 40 * 4853267 * 2
def baseEnd_4853267 : Nat := 830686238534789434747579

theorem tailTrace_4853267 : CollatzResearch.WordTrace tailWord_4853267 prefixEnd_4853267 830686238534789434747579 := by
  unfold tailWord_4853267
  simp only [CollatzResearch.WordTrace]
  refine ⟨177013189708450005858838055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118008793138966670572558703 177013189708450005858838055)
  ·
    refine ⟨265519784562675008788257083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177013189708450005858838055 265519784562675008788257083)
    ·
      refine ⟨398279676844012513182385625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265519784562675008788257083 398279676844012513182385625)
      ·
        refine ⟨298709757633009384886789219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 398279676844012513182385625 298709757633009384886789219)
        ·
          refine ⟨448064636449514077330183829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298709757633009384886789219 448064636449514077330183829)
          ·
            refine ⟨21003029833570972374852367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 448064636449514077330183829 21003029833570972374852367)
            ·
              refine ⟨31504544750356458562278551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21003029833570972374852367 31504544750356458562278551)
              ·
                refine ⟨47256817125534687843417827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31504544750356458562278551 47256817125534687843417827)
                ·
                  refine ⟨70885225688302031765126741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47256817125534687843417827 70885225688302031765126741)
                  ·
                    refine ⟨830686238534789434747579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70885225688302031765126741 830686238534789434747579)
                    ·
                      rfl

theorem cell23_4853267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 8].length) (baseStart_4853267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853267 prefixEnd_4853267 := by exact prefixLift 4853267
  have htrace : WordTrace (prefixWord ++ tailWord_4853267) baseStart_4853267 baseEnd_4853267 := by
    simpa [prefixWord, tailWord_4853267, baseEnd_4853267] using wordTrace_append hprefix tailTrace_4853267
  have hstable : (prefixWord ++ tailWord_4853267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853267).length < 2 ^ (prefixWord ++ tailWord_4853267).sum := by decide
  have hdescent : baseEnd_4853267 < baseStart_4853267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853297 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 11]
def baseStart_4853297 : Nat := 118140960795 + 4853297 * 2 ^ 59
def prefixEnd_4853297 : Nat := 4983230072969 + 3 ^ 40 * 4853297 * 2
def baseEnd_4853297 : Nat := 276897124447111465207511

theorem tailTrace_4853297 : CollatzResearch.WordTrace tailWord_4853297 prefixEnd_4853297 276897124447111465207511 := by
  unfold tailWord_4853297
  simp only [CollatzResearch.WordTrace]
  refine ⟨177014283898341320982430145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118009522598894213988286763 177014283898341320982430145)
  ·
    refine ⟨132760712923755990736822609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177014283898341320982430145 132760712923755990736822609)
    ·
      refine ⟨99570534692816993052616957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132760712923755990736822609 99570534692816993052616957)
      ·
        refine ⟨37338950509806372394731359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99570534692816993052616957 37338950509806372394731359)
        ·
          refine ⟨56008425764709558592097039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37338950509806372394731359 56008425764709558592097039)
          ·
            refine ⟨84012638647064337888145559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56008425764709558592097039 84012638647064337888145559)
            ·
              refine ⟨126018957970596506832218339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84012638647064337888145559 126018957970596506832218339)
              ·
                refine ⟨189028436955894760248327509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126018957970596506832218339 189028436955894760248327509)
                ·
                  refine ⟨276897124447111465207511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 189028436955894760248327509 276897124447111465207511)
                  ·
                    rfl

theorem cell23_4853297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 11].length) (baseStart_4853297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853297 prefixEnd_4853297 := by exact prefixLift 4853297
  have htrace : WordTrace (prefixWord ++ tailWord_4853297) baseStart_4853297 baseEnd_4853297 := by
    simpa [prefixWord, tailWord_4853297, baseEnd_4853297] using wordTrace_append hprefix tailTrace_4853297
  have hstable : (prefixWord ++ tailWord_4853297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853297).length < 2 ^ (prefixWord ++ tailWord_4853297).sum := by decide
  have hdescent : baseEnd_4853297 < baseStart_4853297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853302 : List Nat := [5, 1, 2, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_4853302 : Nat := 118140960795 + 4853302 * 2 ^ 59
def prefixEnd_4853302 : Nat := 4983230072969 + 3 ^ 40 * 4853302 * 2
def baseEnd_4853302 : Nat := 2492076687427275667305077

theorem tailTrace_4853302 : CollatzResearch.WordTrace tailWord_4853302 prefixEnd_4853302 2492076687427275667305077 := by
  unfold tailWord_4853302
  simp only [CollatzResearch.WordTrace]
  refine ⟨11063404141457700427272635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118009644175548804557574773 11063404141457700427272635)
  ·
    refine ⟨16595106212186550640908953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11063404141457700427272635 16595106212186550640908953)
    ·
      refine ⟨12446329659139912980681715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16595106212186550640908953 12446329659139912980681715)
      ·
        refine ⟨18669494488709869471022573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12446329659139912980681715 18669494488709869471022573)
        ·
          refine ⟨7001060433266201051633465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18669494488709869471022573 7001060433266201051633465)
          ·
            refine ⟨5250795324949650788725099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7001060433266201051633465 5250795324949650788725099)
            ·
              refine ⟨7876192987424476183087649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5250795324949650788725099 7876192987424476183087649)
              ·
                refine ⟨5907144740568357137315737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7876192987424476183087649 5907144740568357137315737)
                ·
                  refine ⟨4430358555426267852986803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5907144740568357137315737 4430358555426267852986803)
                  ·
                    refine ⟨6645537833139401779480205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4430358555426267852986803 6645537833139401779480205)
                    ·
                      refine ⟨2492076687427275667305077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6645537833139401779480205 2492076687427275667305077)
                      ·
                        rfl

theorem cell23_4853302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_4853302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853302 prefixEnd_4853302 := by exact prefixLift 4853302
  have htrace : WordTrace (prefixWord ++ tailWord_4853302) baseStart_4853302 baseEnd_4853302 := by
    simpa [prefixWord, tailWord_4853302, baseEnd_4853302] using wordTrace_append hprefix tailTrace_4853302
  have hstable : (prefixWord ++ tailWord_4853302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853302).length < 2 ^ (prefixWord ++ tailWord_4853302).sum := by decide
  have hdescent : baseEnd_4853302 < baseStart_4853302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853304 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 2, 2, 4]
def baseStart_4853304 : Nat := 118140960795 + 4853304 * 2 ^ 59
def prefixEnd_4853304 : Nat := 4983230072969 + 3 ^ 40 * 4853304 * 2
def baseEnd_4853304 : Nat := 2492077714388584659480067

theorem tailTrace_4853304 : CollatzResearch.WordTrace tailWord_4853304 prefixEnd_4853304 2492077714388584659480067 := by
  unfold tailWord_4853304
  simp only [CollatzResearch.WordTrace]
  refine ⟨88507269604657980588967483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118009692806210640785289977 88507269604657980588967483)
  ·
    refine ⟨132760904406986970883451225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88507269604657980588967483 132760904406986970883451225)
    ·
      refine ⟨99570678305240228162588419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132760904406986970883451225 99570678305240228162588419)
      ·
        refine ⟨149356017457860342243882629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99570678305240228162588419 149356017457860342243882629)
        ·
          refine ⟨28004253273348814170727993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149356017457860342243882629 28004253273348814170727993)
          ·
            refine ⟨21003189955011610628045995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28004253273348814170727993 21003189955011610628045995)
            ·
              refine ⟨31504784932517415942068993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21003189955011610628045995 31504784932517415942068993)
              ·
                refine ⟨23628588699388061956551745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31504784932517415942068993 23628588699388061956551745)
                ·
                  refine ⟨17721441524541046467413809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23628588699388061956551745 17721441524541046467413809)
                  ·
                    refine ⟨13291081143405784850560357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17721441524541046467413809 13291081143405784850560357)
                    ·
                      refine ⟨2492077714388584659480067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13291081143405784850560357 2492077714388584659480067)
                      ·
                        rfl

theorem cell23_4853304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_4853304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853304 prefixEnd_4853304 := by exact prefixLift 4853304
  have htrace : WordTrace (prefixWord ++ tailWord_4853304) baseStart_4853304 baseEnd_4853304 := by
    simpa [prefixWord, tailWord_4853304, baseEnd_4853304] using wordTrace_append hprefix tailTrace_4853304
  have hstable : (prefixWord ++ tailWord_4853304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853304).length < 2 ^ (prefixWord ++ tailWord_4853304).sum := by decide
  have hdescent : baseEnd_4853304 < baseStart_4853304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853344 : List Nat := [2, 1, 1, 3, 2, 1, 1, 5, 2, 5]
def baseStart_4853344 : Nat := 118140960795 + 4853344 * 2 ^ 59
def prefixEnd_4853344 : Nat := 4983230072969 + 3 ^ 40 * 4853344 * 2
def baseEnd_4853344 : Nat := 830699417871588167659961

theorem tailTrace_4853344 : CollatzResearch.WordTrace tailWord_4853344 prefixEnd_4853344 830699417871588167659961 := by
  unfold tailWord_4853344
  simp only [CollatzResearch.WordTrace]
  refine ⟨88507999064585524004695543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118010665419447365339594057 88507999064585524004695543)
  ·
    refine ⟨132761998596878286007043315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88507999064585524004695543 132761998596878286007043315)
    ·
      refine ⟨199142997895317429010564973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132761998596878286007043315 199142997895317429010564973)
      ·
        refine ⟨74678624210744035878961865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199142997895317429010564973 74678624210744035878961865)
        ·
          refine ⟨56008968158058026909221399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74678624210744035878961865 56008968158058026909221399)
          ·
            refine ⟨84013452237087040363832099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56008968158058026909221399 84013452237087040363832099)
            ·
              refine ⟨126020178355630560545748149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84013452237087040363832099 126020178355630560545748149)
              ·
                refine ⟨11814391720840365051163889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126020178355630560545748149 11814391720840365051163889)
                ·
                  refine ⟨8860793790630273788372917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11814391720840365051163889 8860793790630273788372917)
                  ·
                    refine ⟨830699417871588167659961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8860793790630273788372917 830699417871588167659961)
                    ·
                      rfl

theorem cell23_4853344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 2, 5].length) (baseStart_4853344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853344 prefixEnd_4853344 := by exact prefixLift 4853344
  have htrace : WordTrace (prefixWord ++ tailWord_4853344) baseStart_4853344 baseEnd_4853344 := by
    simpa [prefixWord, tailWord_4853344, baseEnd_4853344] using wordTrace_append hprefix tailTrace_4853344
  have hstable : (prefixWord ++ tailWord_4853344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853344).length < 2 ^ (prefixWord ++ tailWord_4853344).sum := by decide
  have hdescent : baseEnd_4853344 < baseStart_4853344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853348 : List Nat := [2, 3, 1, 1, 2, 5, 1, 3, 5]
def baseStart_4853348 : Nat := 118140960795 + 4853348 * 2 ^ 59
def prefixEnd_4853348 : Nat := 4983230072969 + 3 ^ 40 * 4853348 * 2
def baseEnd_4853348 : Nat := 276900034170820276369985

theorem tailTrace_4853348 : CollatzResearch.WordTrace tailWord_4853348 prefixEnd_4853348 276900034170820276369985 := by
  unfold tailWord_4853348
  simp only [CollatzResearch.WordTrace]
  refine ⟨88508072010578278346268349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118010762680771037795024465 88508072010578278346268349)
  ·
    refine ⟨33190527003966854379850631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88508072010578278346268349 33190527003966854379850631)
    ·
      refine ⟨49785790505950281569775947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33190527003966854379850631 49785790505950281569775947)
      ·
        refine ⟨74678685758925422354663921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49785790505950281569775947 74678685758925422354663921)
        ·
          refine ⟨56009014319194066765997941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74678685758925422354663921 56009014319194066765997941)
          ·
            refine ⟨5250845092424443759312307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56009014319194066765997941 5250845092424443759312307)
            ·
              refine ⟨7876267638636665638968461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5250845092424443759312307 7876267638636665638968461)
              ·
                refine ⟨2953600364488749614613173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7876267638636665638968461 2953600364488749614613173)
                ·
                  refine ⟨276900034170820276369985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2953600364488749614613173 276900034170820276369985)
                  ·
                    rfl

theorem cell23_4853348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_4853348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853348 prefixEnd_4853348 := by exact prefixLift 4853348
  have htrace : WordTrace (prefixWord ++ tailWord_4853348) baseStart_4853348 baseEnd_4853348 := by
    simpa [prefixWord, tailWord_4853348, baseEnd_4853348] using wordTrace_append hprefix tailTrace_4853348
  have hstable : (prefixWord ++ tailWord_4853348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853348).length < 2 ^ (prefixWord ++ tailWord_4853348).sum := by decide
  have hdescent : baseEnd_4853348 < baseStart_4853348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853365 : List Nat := [1, 3, 4, 2, 1, 2, 3, 2, 5]
def baseStart_4853365 : Nat := 118140960795 + 4853365 * 2 ^ 59
def prefixEnd_4853365 : Nat := 4983230072969 + 3 ^ 40 * 4853365 * 2
def baseEnd_4853365 : Nat := 276901004078723213424143

theorem tailTrace_4853365 : CollatzResearch.WordTrace tailWord_4853365 prefixEnd_4853365 276901004078723213424143 := by
  unfold tailWord_4853365
  simp only [CollatzResearch.WordTrace]
  refine ⟨177016764062094968595905549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118011176041396645730603699 177016764062094968595905549)
  ·
    refine ⟨66381286523285613223464581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177016764062094968595905549 66381286523285613223464581)
    ·
      refine ⟨12446491223116052479399609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66381286523285613223464581 12446491223116052479399609)
      ·
        refine ⟨9334868417337039359549707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12446491223116052479399609 9334868417337039359549707)
        ·
          refine ⟨14002302626005559039324561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9334868417337039359549707 14002302626005559039324561)
          ·
            refine ⟨10501726969504169279493421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14002302626005559039324561 10501726969504169279493421)
            ·
              refine ⟨3938147613564063479810033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10501726969504169279493421 3938147613564063479810033)
              ·
                refine ⟨2953610710173047609857525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3938147613564063479810033 2953610710173047609857525)
                ·
                  refine ⟨276901004078723213424143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2953610710173047609857525 276901004078723213424143)
                  ·
                    rfl

theorem cell23_4853365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 5].length) (baseStart_4853365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853365 prefixEnd_4853365 := by exact prefixLift 4853365
  have htrace : WordTrace (prefixWord ++ tailWord_4853365) baseStart_4853365 baseEnd_4853365 := by
    simpa [prefixWord, tailWord_4853365, baseEnd_4853365] using wordTrace_append hprefix tailTrace_4853365
  have hstable : (prefixWord ++ tailWord_4853365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853365).length < 2 ^ (prefixWord ++ tailWord_4853365).sum := by decide
  have hdescent : baseEnd_4853365 < baseStart_4853365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853381 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 1, 6, 2]
def baseStart_4853381 : Nat := 118140960795 + 4853381 * 2 ^ 59
def prefixEnd_4853381 : Nat := 4983230072969 + 3 ^ 40 * 4853381 * 2
def baseEnd_4853381 : Nat := 2492117252398980858217213

theorem tailTrace_4853381 : CollatzResearch.WordTrace tailWord_4853381 prefixEnd_4853381 2492117252398980858217213 := by
  unfold tailWord_4853381
  simp only [CollatzResearch.WordTrace]
  refine ⟨177017347630037003328487997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118011565086691335552325331 177017347630037003328487997)
  ·
    refine ⟨66381505361263876248182999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177017347630037003328487997 66381505361263876248182999)
    ·
      refine ⟨99572258041895814372274499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66381505361263876248182999 99572258041895814372274499)
      ·
        refine ⟨149358387062843721558411749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99572258041895814372274499 149358387062843721558411749)
        ·
          refine ⟨28004697574283197792202203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149358387062843721558411749 28004697574283197792202203)
          ·
            refine ⟨42007046361424796688303305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28004697574283197792202203 42007046361424796688303305)
            ·
              refine ⟨31505284771068597516227479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42007046361424796688303305 31505284771068597516227479)
              ·
                refine ⟨47257927156602896274341219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31505284771068597516227479 47257927156602896274341219)
                ·
                  refine ⟨70886890734904344411511829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47257927156602896274341219 70886890734904344411511829)
                  ·
                    refine ⟨3322823003198641144289617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70886890734904344411511829 3322823003198641144289617)
                    ·
                      refine ⟨2492117252398980858217213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3322823003198641144289617 2492117252398980858217213)
                      ·
                        rfl

theorem cell23_4853381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 6, 2].length) (baseStart_4853381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853381 prefixEnd_4853381 := by exact prefixLift 4853381
  have htrace : WordTrace (prefixWord ++ tailWord_4853381) baseStart_4853381 baseEnd_4853381 := by
    simpa [prefixWord, tailWord_4853381, baseEnd_4853381] using wordTrace_append hprefix tailTrace_4853381
  have hstable : (prefixWord ++ tailWord_4853381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853381).length < 2 ^ (prefixWord ++ tailWord_4853381).sum := by decide
  have hdescent : baseEnd_4853381 < baseStart_4853381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853416 : List Nat := [2, 1, 7, 1, 2, 1, 2, 2, 5]
def baseStart_4853416 : Nat := 118140960795 + 4853416 * 2 ^ 59
def prefixEnd_4853416 : Nat := 4983230072969 + 3 ^ 40 * 4853416 * 2
def baseEnd_4853416 : Nat := 276903913802432024586617

theorem tailTrace_4853416 : CollatzResearch.WordTrace tailWord_4853416 prefixEnd_4853416 276903913802432024586617 := by
  unfold tailWord_4853416
  simp only [CollatzResearch.WordTrace]
  refine ⟨88509312092455102153006051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118012416123273469537341401 88509312092455102153006051)
  ·
    refine ⟨132763968138682653229509077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88509312092455102153006051 132763968138682653229509077)
    ·
      refine ⟨3111655503250374685066619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 132763968138682653229509077 3111655503250374685066619)
      ·
        refine ⟨4667483254875562027599929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3111655503250374685066619 4667483254875562027599929)
        ·
          refine ⟨3500612441156671520699947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4667483254875562027599929 3500612441156671520699947)
          ·
            refine ⟨5250918661735007281049921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3500612441156671520699947 5250918661735007281049921)
            ·
              refine ⟨3938188996301255460787441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5250918661735007281049921 3938188996301255460787441)
              ·
                refine ⟨2953641747225941595590581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3938188996301255460787441 2953641747225941595590581)
                ·
                  refine ⟨276903913802432024586617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2953641747225941595590581 276903913802432024586617)
                  ·
                    rfl

theorem cell23_4853416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 5].length) (baseStart_4853416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853416 prefixEnd_4853416 := by exact prefixLift 4853416
  have htrace : WordTrace (prefixWord ++ tailWord_4853416) baseStart_4853416 baseEnd_4853416 := by
    simpa [prefixWord, tailWord_4853416, baseEnd_4853416] using wordTrace_append hprefix tailTrace_4853416
  have hstable : (prefixWord ++ tailWord_4853416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853416).length < 2 ^ (prefixWord ++ tailWord_4853416).sum := by decide
  have hdescent : baseEnd_4853416 < baseStart_4853416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853448 : List Nat := [2, 1, 3, 1, 2, 2, 3, 2, 3, 1, 3]
def baseStart_4853448 : Nat := 118140960795 + 4853448 * 2 ^ 59
def prefixEnd_4853448 : Nat := 4983230072969 + 3 ^ 40 * 4853448 * 2
def baseEnd_4853448 : Nat := 2492151655602832096079405

theorem tailTrace_4853448 : CollatzResearch.WordTrace tailWord_4853448 prefixEnd_4853448 2492151655602832096079405 := by
  unfold tailWord_4853448
  simp only [CollatzResearch.WordTrace]
  refine ⟨88509895660397136885588499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118013194213862849180784665 88509895660397136885588499)
  ·
    refine ⟨132764843490595705328382749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88509895660397136885588499 132764843490595705328382749)
    ·
      refine ⟨49786816308973389498143531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132764843490595705328382749 49786816308973389498143531)
      ·
        refine ⟨74680224463460084247215297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49786816308973389498143531 74680224463460084247215297)
        ·
          refine ⟨56010168347595063185411473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74680224463460084247215297 56010168347595063185411473)
          ·
            refine ⟨42007626260696297389058605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56010168347595063185411473 42007626260696297389058605)
            ·
              refine ⟨15752859847761111520896977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42007626260696297389058605 15752859847761111520896977)
              ·
                refine ⟨11814644885820833640672733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15752859847761111520896977 11814644885820833640672733)
                ·
                  refine ⟨4430491832182812615252275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11814644885820833640672733 4430491832182812615252275)
                  ·
                    refine ⟨6645737748274218922878413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4430491832182812615252275 6645737748274218922878413)
                    ·
                      refine ⟨2492151655602832096079405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6645737748274218922878413 2492151655602832096079405)
                      ·
                        rfl

theorem cell23_4853448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_4853448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853448 prefixEnd_4853448 := by exact prefixLift 4853448
  have htrace : WordTrace (prefixWord ++ tailWord_4853448) baseStart_4853448 baseEnd_4853448 := by
    simpa [prefixWord, tailWord_4853448, baseEnd_4853448] using wordTrace_append hprefix tailTrace_4853448
  have hstable : (prefixWord ++ tailWord_4853448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853448).length < 2 ^ (prefixWord ++ tailWord_4853448).sum := by decide
  have hdescent : baseEnd_4853448 < baseStart_4853448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853452 : List Nat := [2, 2, 1, 5, 3, 1, 1, 1, 2, 2, 3]
def baseStart_4853452 : Nat := 118140960795 + 4853452 * 2 ^ 59
def prefixEnd_4853452 : Nat := 4983230072969 + 3 ^ 40 * 4853452 * 2
def baseEnd_4853452 : Nat := 2492153709525450080429387

theorem tailTrace_4853452 : CollatzResearch.WordTrace tailWord_4853452 prefixEnd_4853452 2492153709525450080429387 := by
  unfold tailWord_4853452
  simp only [CollatzResearch.WordTrace]
  refine ⟨88509968606389891227161305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118013291475186521636215073 88509968606389891227161305)
  ·
    refine ⟨66382476454792418420370979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88509968606389891227161305 66382476454792418420370979)
    ·
      refine ⟨99573714682188627630556469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66382476454792418420370979 99573714682188627630556469)
      ·
        refine ⟨9335035751455183840364669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99573714682188627630556469 9335035751455183840364669)
        ·
          refine ⟨3500638406795693940136751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9335035751455183840364669 3500638406795693940136751)
          ·
            refine ⟨5250957610193540910205127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3500638406795693940136751 5250957610193540910205127)
            ·
              refine ⟨7876436415290311365307691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5250957610193540910205127 7876436415290311365307691)
              ·
                refine ⟨11814654622935467047961537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7876436415290311365307691 11814654622935467047961537)
                ·
                  refine ⟨8860990967201600285971153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11814654622935467047961537 8860990967201600285971153)
                  ·
                    refine ⟨6645743225401200214478365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8860990967201600285971153 6645743225401200214478365)
                    ·
                      refine ⟨2492153709525450080429387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6645743225401200214478365 2492153709525450080429387)
                      ·
                        rfl

theorem cell23_4853452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_4853452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853452 prefixEnd_4853452 := by exact prefixLift 4853452
  have htrace : WordTrace (prefixWord ++ tailWord_4853452) baseStart_4853452 baseEnd_4853452 := by
    simpa [prefixWord, tailWord_4853452, baseEnd_4853452] using wordTrace_append hprefix tailTrace_4853452
  have hstable : (prefixWord ++ tailWord_4853452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853452).length < 2 ^ (prefixWord ++ tailWord_4853452).sum := by decide
  have hdescent : baseEnd_4853452 < baseStart_4853452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853465 : List Nat := [1, 2, 1, 2, 3, 3, 1, 5, 1, 1, 3]
def baseStart_4853465 : Nat := 118140960795 + 4853465 * 2 ^ 59
def prefixEnd_4853465 : Nat := 4983230072969 + 3 ^ 40 * 4853465 * 2
def baseEnd_4853465 : Nat := 2492160384773958529566827

theorem tailTrace_4853465 : CollatzResearch.WordTrace tailWord_4853465 prefixEnd_4853465 2492160384773958529566827 := by
  unfold tailWord_4853465
  simp only [CollatzResearch.WordTrace]
  refine ⟨177020411361732685674545849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118013607574488457116363899 177020411361732685674545849)
  ·
    refine ⟨132765308521299514255909387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177020411361732685674545849 132765308521299514255909387)
    ·
      refine ⟨199147962781949271383864081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132765308521299514255909387 199147962781949271383864081)
      ·
        refine ⟨149360972086461953537898061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199147962781949271383864081 149360972086461953537898061)
        ·
          refine ⟨56010364532423232576711773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149360972086461953537898061 56010364532423232576711773)
          ·
            refine ⟨21003886699658712216266915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56010364532423232576711773 21003886699658712216266915)
            ·
              refine ⟨31505830049488068324400373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21003886699658712216266915 31505830049488068324400373)
              ·
                refine ⟨2953671567139506405412535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31505830049488068324400373 2953671567139506405412535)
                ·
                  refine ⟨4430507350709259608118803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2953671567139506405412535 4430507350709259608118803)
                  ·
                    refine ⟨6645761026063889412178205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4430507350709259608118803 6645761026063889412178205)
                    ·
                      refine ⟨2492160384773958529566827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6645761026063889412178205 2492160384773958529566827)
                      ·
                        rfl

theorem cell23_4853465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 1, 1, 3].length) (baseStart_4853465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853465 prefixEnd_4853465 := by exact prefixLift 4853465
  have htrace : WordTrace (prefixWord ++ tailWord_4853465) baseStart_4853465 baseEnd_4853465 := by
    simpa [prefixWord, tailWord_4853465, baseEnd_4853465] using wordTrace_append hprefix tailTrace_4853465
  have hstable : (prefixWord ++ tailWord_4853465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853465).length < 2 ^ (prefixWord ++ tailWord_4853465).sum := by decide
  have hdescent : baseEnd_4853465 < baseStart_4853465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853491 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 3]
def baseStart_4853491 : Nat := 118140960795 + 4853491 * 2 ^ 59
def prefixEnd_4853491 : Nat := 4983230072969 + 3 ^ 40 * 4853491 * 2
def baseEnd_4853491 : Nat := 2492173735270975427841707

theorem tailTrace_4853491 : CollatzResearch.WordTrace tailWord_4853491 prefixEnd_4853491 2492173735270975427841707 := by
  unfold tailWord_4853491
  simp only [CollatzResearch.WordTrace]
  refine ⟨177021359659638492114992327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118014239773092328076661551 177021359659638492114992327)
  ·
    refine ⟨265532039489457738172488491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177021359659638492114992327 265532039489457738172488491)
    ·
      refine ⟨398298059234186607258732737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265532039489457738172488491 398298059234186607258732737)
      ·
        refine ⟨298723544425639955444049553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 398298059234186607258732737 298723544425639955444049553)
        ·
          refine ⟨224042658319229966583037165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298723544425639955444049553 224042658319229966583037165)
          ·
            refine ⟨84015996869711237468638937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224042658319229966583037165 84015996869711237468638937)
            ·
              refine ⟨63011997652283428101479203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84015996869711237468638937 63011997652283428101479203)
              ·
                refine ⟨94517996478425142152218805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63011997652283428101479203 94517996478425142152218805)
                ·
                  refine ⟨8861062169852357076770513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94517996478425142152218805 8861062169852357076770513)
                  ·
                    refine ⟨6645796627389267807577885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8861062169852357076770513 6645796627389267807577885)
                    ·
                      refine ⟨2492173735270975427841707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6645796627389267807577885 2492173735270975427841707)
                      ·
                        rfl

theorem cell23_4853491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 3].length) (baseStart_4853491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853491 prefixEnd_4853491 := by exact prefixLift 4853491
  have htrace : WordTrace (prefixWord ++ tailWord_4853491) baseStart_4853491 baseEnd_4853491 := by
    simpa [prefixWord, tailWord_4853491, baseEnd_4853491] using wordTrace_append hprefix tailTrace_4853491
  have hstable : (prefixWord ++ tailWord_4853491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853491).length < 2 ^ (prefixWord ++ tailWord_4853491).sum := by decide
  have hdescent : baseEnd_4853491 < baseStart_4853491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853492 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_4853492 : Nat := 118140960795 + 4853492 * 2 ^ 59
def prefixEnd_4853492 : Nat := 4983230072969 + 3 ^ 40 * 4853492 * 2
def baseEnd_4853492 : Nat := 2492174248751629923929203

theorem tailTrace_4853492 : CollatzResearch.WordTrace tailWord_4853492 prefixEnd_4853492 2492174248751629923929203 := by
  unfold tailWord_4853492
  simp only [CollatzResearch.WordTrace]
  refine ⟨88510698066317434642889365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118014264088423246190519153 88510698066317434642889365)
  ·
    refine ⟨4148938971858629748885439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 88510698066317434642889365 4148938971858629748885439)
    ·
      refine ⟨6223408457787944623328159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4148938971858629748885439 6223408457787944623328159)
      ·
        refine ⟨9335112686681916934992239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6223408457787944623328159 9335112686681916934992239)
        ·
          refine ⟨14002669030022875402488359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9335112686681916934992239 14002669030022875402488359)
          ·
            refine ⟨21004003545034313103732539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14002669030022875402488359 21004003545034313103732539)
            ·
              refine ⟨31506005317551469655598809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21004003545034313103732539 31506005317551469655598809)
              ·
                refine ⟨23629503988163602241699107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31506005317551469655598809 23629503988163602241699107)
                ·
                  refine ⟨35444255982245403362548661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23629503988163602241699107 35444255982245403362548661)
                  ·
                    refine ⟨3322898998335506565238937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35444255982245403362548661 3322898998335506565238937)
                    ·
                      refine ⟨2492174248751629923929203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3322898998335506565238937 2492174248751629923929203)
                      ·
                        rfl

theorem cell23_4853492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_4853492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853492 prefixEnd_4853492 := by exact prefixLift 4853492
  have htrace : WordTrace (prefixWord ++ tailWord_4853492) baseStart_4853492 baseEnd_4853492 := by
    simpa [prefixWord, tailWord_4853492, baseEnd_4853492] using wordTrace_append hprefix tailTrace_4853492
  have hstable : (prefixWord ++ tailWord_4853492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853492).length < 2 ^ (prefixWord ++ tailWord_4853492).sum := by decide
  have hdescent : baseEnd_4853492 < baseStart_4853492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853501 : List Nat := [1, 4, 1, 1, 1, 1, 2, 5, 1, 2, 4]
def baseStart_4853501 : Nat := 118140960795 + 4853501 * 2 ^ 59
def prefixEnd_4853501 : Nat := 4983230072969 + 3 ^ 40 * 4853501 * 2
def baseEnd_4853501 : Nat := 2492178870077520388716661

theorem tailTrace_4853501 : CollatzResearch.WordTrace tailWord_4853501 prefixEnd_4853501 2492178870077520388716661 := by
  unfold tailWord_4853501
  simp only [CollatzResearch.WordTrace]
  refine ⟨177021724389602263822856357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118014482926401509215237571 177021724389602263822856357)
  ·
    refine ⟨33191573323050424466785567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177021724389602263822856357 33191573323050424466785567)
    ·
      refine ⟨49787359984575636700178351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33191573323050424466785567 49787359984575636700178351)
      ·
        refine ⟨74681039976863455050267527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49787359984575636700178351 74681039976863455050267527)
        ·
          refine ⟨112021559965295182575401291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74681039976863455050267527 112021559965295182575401291)
          ·
            refine ⟨168032339947942773863101937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112021559965295182575401291 168032339947942773863101937)
            ·
              refine ⟨126024254960957080397326453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168032339947942773863101937 126024254960957080397326453)
              ·
                refine ⟨11814773902589726287249355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126024254960957080397326453 11814773902589726287249355)
                ·
                  refine ⟨17722160853884589430874033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11814773902589726287249355 17722160853884589430874033)
                  ·
                    refine ⟨13291620640413442073155525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17722160853884589430874033 13291620640413442073155525)
                    ·
                      refine ⟨2492178870077520388716661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13291620640413442073155525 2492178870077520388716661)
                      ·
                        rfl

theorem cell23_4853501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_4853501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853501 prefixEnd_4853501 := by exact prefixLift 4853501
  have htrace : WordTrace (prefixWord ++ tailWord_4853501) baseStart_4853501 baseEnd_4853501 := by
    simpa [prefixWord, tailWord_4853501, baseEnd_4853501] using wordTrace_append hprefix tailTrace_4853501
  have hstable : (prefixWord ++ tailWord_4853501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853501).length < 2 ^ (prefixWord ++ tailWord_4853501).sum := by decide
  have hdescent : baseEnd_4853501 < baseStart_4853501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853504 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 7]
def baseStart_4853504 : Nat := 118140960795 + 4853504 * 2 ^ 59
def prefixEnd_4853504 : Nat := 4983230072969 + 3 ^ 40 * 4853504 * 2
def baseEnd_4853504 : Nat := 2492180410519483876979147

theorem tailTrace_4853504 : CollatzResearch.WordTrace tailWord_4853504 prefixEnd_4853504 2492180410519483876979147 := by
  unfold tailWord_4853504
  simp only [CollatzResearch.WordTrace]
  refine ⟨88510916904295697667607783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118014555872394263556810377 88510916904295697667607783)
  ·
    refine ⟨132766375356443546501411675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88510916904295697667607783 132766375356443546501411675)
    ·
      refine ⟨199149563034665319752117513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132766375356443546501411675 199149563034665319752117513)
      ·
        refine ⟨149362172275998989814088135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199149563034665319752117513 149362172275998989814088135)
        ·
          refine ⟨224043258413998484721132203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149362172275998989814088135 224043258413998484721132203)
          ·
            refine ⟨336064887620997727081698305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224043258413998484721132203 336064887620997727081698305)
            ·
              refine ⟨252048665715748295311273729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 336064887620997727081698305 252048665715748295311273729)
              ·
                refine ⟨189036499286811221483455297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252048665715748295311273729 189036499286811221483455297)
                ·
                  refine ⟨141777374465108416112591473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189036499286811221483455297 141777374465108416112591473)
                  ·
                    refine ⟨106333030848831312084443605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 141777374465108416112591473 106333030848831312084443605)
                    ·
                      refine ⟨2492180410519483876979147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 106333030848831312084443605 2492180410519483876979147)
                      ·
                        rfl

theorem cell23_4853504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_4853504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853504 prefixEnd_4853504 := by exact prefixLift 4853504
  have htrace : WordTrace (prefixWord ++ tailWord_4853504) baseStart_4853504 baseEnd_4853504 := by
    simpa [prefixWord, tailWord_4853504, baseEnd_4853504] using wordTrace_append hprefix tailTrace_4853504
  have hstable : (prefixWord ++ tailWord_4853504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853504).length < 2 ^ (prefixWord ++ tailWord_4853504).sum := by decide
  have hdescent : baseEnd_4853504 < baseStart_4853504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853505 : List Nat := [1, 2, 4, 1, 1, 1, 4, 2, 3, 2, 2]
def baseStart_4853505 : Nat := 118140960795 + 4853505 * 2 ^ 59
def prefixEnd_4853505 : Nat := 4983230072969 + 3 ^ 40 * 4853505 * 2
def baseEnd_4853505 : Nat := 2492180924000138373066643

theorem tailTrace_4853505 : CollatzResearch.WordTrace tailWord_4853505 prefixEnd_4853505 2492180924000138373066643 := by
  unfold tailWord_4853505
  simp only [CollatzResearch.WordTrace]
  refine ⟨177021870281587772506001969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118014580187725181670667979 177021870281587772506001969)
  ·
    refine ⟨132766402711190829379501477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177021870281587772506001969 132766402711190829379501477)
    ·
      refine ⟨24893700508348280508656527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132766402711190829379501477 24893700508348280508656527)
      ·
        refine ⟨37340550762522420762984791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24893700508348280508656527 37340550762522420762984791)
        ·
          refine ⟨56010826143783631144477187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37340550762522420762984791 56010826143783631144477187)
          ·
            refine ⟨84016239215675446716715781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56010826143783631144477187 84016239215675446716715781)
            ·
              refine ⟨15753044852939146259384209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84016239215675446716715781 15753044852939146259384209)
              ·
                refine ⟨11814783639704359694538157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15753044852939146259384209 11814783639704359694538157)
                ·
                  refine ⟨4430543864889134885451809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11814783639704359694538157 4430543864889134885451809)
                  ·
                    refine ⟨3322907898666851164088857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4430543864889134885451809 3322907898666851164088857)
                    ·
                      refine ⟨2492180924000138373066643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3322907898666851164088857 2492180924000138373066643)
                      ·
                        rfl

theorem cell23_4853505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_4853505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853505 prefixEnd_4853505 := by exact prefixLift 4853505
  have htrace : WordTrace (prefixWord ++ tailWord_4853505) baseStart_4853505 baseEnd_4853505 := by
    simpa [prefixWord, tailWord_4853505, baseEnd_4853505] using wordTrace_append hprefix tailTrace_4853505
  have hstable : (prefixWord ++ tailWord_4853505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853505).length < 2 ^ (prefixWord ++ tailWord_4853505).sum := by decide
  have hdescent : baseEnd_4853505 < baseStart_4853505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853510 : List Nat := [6, 2, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_4853510 : Nat := 118140960795 + 4853510 * 2 ^ 59
def prefixEnd_4853510 : Nat := 4983230072969 + 3 ^ 40 * 4853510 * 2
def baseEnd_4853510 : Nat := 830727830467803617834707

theorem tailTrace_4853510 : CollatzResearch.WordTrace tailWord_4853510 prefixEnd_4853510 830727830467803617834707 := by
  unfold tailWord_4853510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5531939145205301823747937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 118014701764379772239955989 5531939145205301823747937)
  ·
    refine ⟨4148954358903976367810953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5531939145205301823747937 4148954358903976367810953)
    ·
      refine ⟨3111715769177982275858215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4148954358903976367810953 3111715769177982275858215)
      ·
        refine ⟨4667573653766973413787323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3111715769177982275858215 4667573653766973413787323)
        ·
          refine ⟨7001360480650460120680985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4667573653766973413787323 7001360480650460120680985)
          ·
            refine ⟨5251020360487845090510739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7001360480650460120680985 5251020360487845090510739)
            ·
              refine ⟨7876530540731767635766109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5251020360487845090510739 7876530540731767635766109)
              ·
                refine ⟨2953698952774412863412291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7876530540731767635766109 2953698952774412863412291)
                ·
                  refine ⟨4430548429161619295118437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2953698952774412863412291 4430548429161619295118437)
                  ·
                    refine ⟨830727830467803617834707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4430548429161619295118437 830727830467803617834707)
                    ·
                      rfl

theorem cell23_4853510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_4853510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853510 prefixEnd_4853510 := by exact prefixLift 4853510
  have htrace : WordTrace (prefixWord ++ tailWord_4853510) baseStart_4853510 baseEnd_4853510 := by
    simpa [prefixWord, tailWord_4853510, baseEnd_4853510] using wordTrace_append hprefix tailTrace_4853510
  have hstable : (prefixWord ++ tailWord_4853510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853510).length < 2 ^ (prefixWord ++ tailWord_4853510).sum := by decide
  have hdescent : baseEnd_4853510 < baseStart_4853510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853521 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 3]
def baseStart_4853521 : Nat := 118140960795 + 4853521 * 2 ^ 59
def prefixEnd_4853521 : Nat := 4983230072969 + 3 ^ 40 * 4853521 * 2
def baseEnd_4853521 : Nat := 2492189139690610310466569

theorem tailTrace_4853521 : CollatzResearch.WordTrace tailWord_4853521 prefixEnd_4853521 2492189139690610310466569 := by
  unfold tailWord_4853521
  simp only [CollatzResearch.WordTrace]
  refine ⟨177022453849529807238584417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118014969233019871492389611 177022453849529807238584417)
  ·
    refine ⟨132766840387147355428938313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177022453849529807238584417 132766840387147355428938313)
    ·
      refine ⟨99575130290360516571703735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132766840387147355428938313 99575130290360516571703735)
      ·
        refine ⟨149362695435540774857555603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99575130290360516571703735 149362695435540774857555603)
        ·
          refine ⟨224044043153311162286333405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149362695435540774857555603 224044043153311162286333405)
          ·
            refine ⟨84016516182491685857375027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224044043153311162286333405 84016516182491685857375027)
            ·
              refine ⟨126024774273737528786062541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84016516182491685857375027 126024774273737528786062541)
              ·
                refine ⟨47259290352651573294773453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126024774273737528786062541 47259290352651573294773453)
                ·
                  refine ⟨17722233882244339985540045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47259290352651573294773453 17722233882244339985540045)
                  ·
                    refine ⟨6645837705841627494577517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17722233882244339985540045 6645837705841627494577517)
                    ·
                      refine ⟨2492189139690610310466569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6645837705841627494577517 2492189139690610310466569)
                      ·
                        rfl

theorem cell23_4853521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 3].length) (baseStart_4853521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853521 prefixEnd_4853521 := by exact prefixLift 4853521
  have htrace : WordTrace (prefixWord ++ tailWord_4853521) baseStart_4853521 baseEnd_4853521 := by
    simpa [prefixWord, tailWord_4853521, baseEnd_4853521] using wordTrace_append hprefix tailTrace_4853521
  have hstable : (prefixWord ++ tailWord_4853521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853521).length < 2 ^ (prefixWord ++ tailWord_4853521).sum := by decide
  have hdescent : baseEnd_4853521 < baseStart_4853521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853601 : List Nat := [1, 2, 3, 1, 1, 1, 4, 3, 7]
def baseStart_4853601 : Nat := 118140960795 + 4853601 * 2 ^ 59
def prefixEnd_4853601 : Nat := 4983230072969 + 3 ^ 40 * 4853601 * 2
def baseEnd_4853601 : Nat := 276914468682552221940689

theorem tailTrace_4853601 : CollatzResearch.WordTrace tailWord_4853601 prefixEnd_4853601 276914468682552221940689 := by
  unfold tailWord_4853601
  simp only [CollatzResearch.WordTrace]
  refine ⟨177025371689239980901496657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118016914459493320600997771 177025371689239980901496657)
  ·
    refine ⟨132769028766929985676122493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177025371689239980901496657 132769028766929985676122493)
    ·
      refine ⟨49788385787598744628545935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132769028766929985676122493 49788385787598744628545935)
      ·
        refine ⟨74682578681398116942818903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49788385787598744628545935 74682578681398116942818903)
        ·
          refine ⟨112023868022097175414228355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74682578681398116942818903 112023868022097175414228355)
          ·
            refine ⟨168035802033145763121342533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112023868022097175414228355 168035802033145763121342533)
            ·
              refine ⟨31506712881214830585251725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 168035802033145763121342533 31506712881214830585251725)
              ·
                refine ⟨11815017330455561469469397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31506712881214830585251725 11815017330455561469469397)
                ·
                  refine ⟨276914468682552221940689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11815017330455561469469397 276914468682552221940689)
                  ·
                    rfl

theorem cell23_4853601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 7].length) (baseStart_4853601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853601 prefixEnd_4853601 := by exact prefixLift 4853601
  have htrace : WordTrace (prefixWord ++ tailWord_4853601) baseStart_4853601 baseEnd_4853601 := by
    simpa [prefixWord, tailWord_4853601, baseEnd_4853601] using wordTrace_append hprefix tailTrace_4853601
  have hstable : (prefixWord ++ tailWord_4853601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853601).length < 2 ^ (prefixWord ++ tailWord_4853601).sum := by decide
  have hdescent : baseEnd_4853601 < baseStart_4853601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853608 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_4853608 : Nat := 118140960795 + 4853608 * 2 ^ 59
def prefixEnd_4853608 : Nat := 4983230072969 + 3 ^ 40 * 4853608 * 2
def baseEnd_4853608 : Nat := 2492233812507551470078669

theorem tailTrace_4853608 : CollatzResearch.WordTrace tailWord_4853608 prefixEnd_4853608 2492233812507551470078669 := by
  unfold tailWord_4853608
  simp only [CollatzResearch.WordTrace]
  refine ⟨88512813500107310548500739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118017084666809747398000985 88512813500107310548500739)
  ·
    refine ⟨132769220250160965822751109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88512813500107310548500739 132769220250160965822751109)
    ·
      refine ⟨24894228796905181091765833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132769220250160965822751109 24894228796905181091765833)
      ·
        refine ⟨18670671597678885818824375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24894228796905181091765833 18670671597678885818824375)
        ·
          refine ⟨28006007396518328728236563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18670671597678885818824375 28006007396518328728236563)
          ·
            refine ⟨42009011094777493092354845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28006007396518328728236563 42009011094777493092354845)
            ·
              refine ⟨15753379160541559909633067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42009011094777493092354845 15753379160541559909633067)
              ·
                refine ⟨23630068740812339864449601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15753379160541559909633067 23630068740812339864449601)
                ·
                  refine ⟨17722551555609254898337201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23630068740812339864449601 17722551555609254898337201)
                  ·
                    refine ⟨13291913666706941173752901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17722551555609254898337201 13291913666706941173752901)
                    ·
                      refine ⟨2492233812507551470078669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13291913666706941173752901 2492233812507551470078669)
                      ·
                        rfl

theorem cell23_4853608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_4853608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853608 prefixEnd_4853608 := by exact prefixLift 4853608
  have htrace : WordTrace (prefixWord ++ tailWord_4853608) baseStart_4853608 baseEnd_4853608 := by
    simpa [prefixWord, tailWord_4853608, baseEnd_4853608] using wordTrace_append hprefix tailTrace_4853608
  have hstable : (prefixWord ++ tailWord_4853608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853608).length < 2 ^ (prefixWord ++ tailWord_4853608).sum := by decide
  have hdescent : baseEnd_4853608 < baseStart_4853608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853612 : List Nat := [2, 2, 1, 1, 4, 2, 2, 3, 2, 2, 2]
def baseStart_4853612 : Nat := 118140960795 + 4853612 * 2 ^ 59
def prefixEnd_4853612 : Nat := 4983230072969 + 3 ^ 40 * 4853612 * 2
def baseEnd_4853612 : Nat := 2492235866430169454428651

theorem tailTrace_4853612 : CollatzResearch.WordTrace tailWord_4853612 prefixEnd_4853612 2492235866430169454428651 := by
  unfold tailWord_4853612
  simp only [CollatzResearch.WordTrace]
  refine ⟨88512886446100064890073545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118017181928133419853431393 88512886446100064890073545)
  ·
    refine ⟨66384664834575048667555159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88512886446100064890073545 66384664834575048667555159)
    ·
      refine ⟨99576997251862573001332739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66384664834575048667555159 99576997251862573001332739)
      ·
        refine ⟨149365495877793859501999109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99576997251862573001332739 149365495877793859501999109)
        ·
          refine ⟨28006030477086348656624833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149365495877793859501999109 28006030477086348656624833)
          ·
            refine ⟨21004522857814761492468625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28006030477086348656624833 21004522857814761492468625)
            ·
              refine ⟨15753392143361071119351469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21004522857814761492468625 15753392143361071119351469)
              ·
                refine ⟨5907522053760401669756801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15753392143361071119351469 5907522053760401669756801)
                ·
                  refine ⟨4430641540320301252317601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5907522053760401669756801 4430641540320301252317601)
                  ·
                    refine ⟨3322981155240225939238201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4430641540320301252317601 3322981155240225939238201)
                    ·
                      refine ⟨2492235866430169454428651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3322981155240225939238201 2492235866430169454428651)
                      ·
                        rfl

theorem cell23_4853612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 2, 2].length) (baseStart_4853612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853612 prefixEnd_4853612 := by exact prefixLift 4853612
  have htrace : WordTrace (prefixWord ++ tailWord_4853612) baseStart_4853612 baseEnd_4853612 := by
    simpa [prefixWord, tailWord_4853612, baseEnd_4853612] using wordTrace_append hprefix tailTrace_4853612
  have hstable : (prefixWord ++ tailWord_4853612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853612).length < 2 ^ (prefixWord ++ tailWord_4853612).sum := by decide
  have hdescent : baseEnd_4853612 < baseStart_4853612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853633 : List Nat := [1, 2, 4, 4, 2, 1, 2, 1, 1, 3, 2]
def baseStart_4853633 : Nat := 118140960795 + 4853633 * 2 ^ 59
def prefixEnd_4853633 : Nat := 4983230072969 + 3 ^ 40 * 4853633 * 2
def baseEnd_4853633 : Nat := 2492246649523913872266055

theorem tailTrace_4853633 : CollatzResearch.WordTrace tailWord_4853633 prefixEnd_4853633 2492246649523913872266055 := by
  unfold tailWord_4853633
  simp only [CollatzResearch.WordTrace]
  refine ⟨177026538825124050366661553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118017692550082700244441035 177026538825124050366661553)
  ·
    refine ⟨132769904118843037774996165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177026538825124050366661553 132769904118843037774996165)
    ·
      refine ⟨24894357022283069582811781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132769904118843037774996165 24894357022283069582811781)
      ·
        refine ⟨4667691941678075546777209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24894357022283069582811781 4667691941678075546777209)
        ·
          refine ⟨3500768956258556660082907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4667691941678075546777209 3500768956258556660082907)
          ·
            refine ⟨5251153434387834990124361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3500768956258556660082907 5251153434387834990124361)
            ·
              refine ⟨3938365075790876242593271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5251153434387834990124361 3938365075790876242593271)
              ·
                refine ⟨5907547613686314363889907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3938365075790876242593271 5907547613686314363889907)
                ·
                  refine ⟨8861321420529471545834861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5907547613686314363889907 8861321420529471545834861)
                  ·
                    refine ⟨3322995532698551829688073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8861321420529471545834861 3322995532698551829688073)
                    ·
                      refine ⟨2492246649523913872266055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3322995532698551829688073 2492246649523913872266055)
                      ·
                        rfl

theorem cell23_4853633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_4853633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853633 prefixEnd_4853633 := by exact prefixLift 4853633
  have htrace : WordTrace (prefixWord ++ tailWord_4853633) baseStart_4853633 baseEnd_4853633 := by
    simpa [prefixWord, tailWord_4853633, baseEnd_4853633] using wordTrace_append hprefix tailTrace_4853633
  have hstable : (prefixWord ++ tailWord_4853633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853633).length < 2 ^ (prefixWord ++ tailWord_4853633).sum := by decide
  have hdescent : baseEnd_4853633 < baseStart_4853633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853635 : List Nat := [1, 1, 1, 3, 4, 3, 2, 3, 5]
def baseStart_4853635 : Nat := 118140960795 + 4853635 * 2 ^ 59
def prefixEnd_4853635 : Nat := 4983230072969 + 3 ^ 40 * 4853635 * 2
def baseEnd_4853635 : Nat := 276916408498358096049005

theorem tailTrace_4853635 : CollatzResearch.WordTrace tailWord_4853635 prefixEnd_4853635 276916408498358096049005 := by
  unfold tailWord_4853635
  simp only [CollatzResearch.WordTrace]
  refine ⟨177026611771116804708234359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118017741180744536472156239 177026611771116804708234359)
  ·
    refine ⟨265539917656675207062351539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177026611771116804708234359 265539917656675207062351539)
    ·
      refine ⟨398309876485012810593527309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265539917656675207062351539 398309876485012810593527309)
      ·
        refine ⟨149366203681879803972572741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 398309876485012810593527309 149366203681879803972572741)
        ·
          refine ⟨28006163190352463244857389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149366203681879803972572741 28006163190352463244857389)
          ·
            refine ⟨10502311196382173716821521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28006163190352463244857389 10502311196382173716821521)
            ·
              refine ⟨7876733397286630287616141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10502311196382173716821521 7876733397286630287616141)
              ·
                refine ⟨2953775023982486357856053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7876733397286630287616141 2953775023982486357856053)
                ·
                  refine ⟨276916408498358096049005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2953775023982486357856053 276916408498358096049005)
                  ·
                    rfl

theorem cell23_4853635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 5].length) (baseStart_4853635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853635 prefixEnd_4853635 := by exact prefixLift 4853635
  have htrace : WordTrace (prefixWord ++ tailWord_4853635) baseStart_4853635 baseEnd_4853635 := by
    simpa [prefixWord, tailWord_4853635, baseEnd_4853635] using wordTrace_append hprefix tailTrace_4853635
  have hstable : (prefixWord ++ tailWord_4853635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853635).length < 2 ^ (prefixWord ++ tailWord_4853635).sum := by decide
  have hdescent : baseEnd_4853635 < baseStart_4853635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853668 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 1, 3, 4]
def baseStart_4853668 : Nat := 118140960795 + 4853668 * 2 ^ 59
def prefixEnd_4853668 : Nat := 4983230072969 + 3 ^ 40 * 4853668 * 2
def baseEnd_4853668 : Nat := 2492264621346821235328393

theorem tailTrace_4853668 : CollatzResearch.WordTrace tailWord_4853668 prefixEnd_4853668 2492264621346821235328393 := by
  unfold tailWord_4853668
  simp only [CollatzResearch.WordTrace]
  refine ⟨88513907689998625672092829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118018543586664834229457105 88513907689998625672092829)
  ·
    refine ⟨33192715383749484627034811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88513907689998625672092829 33192715383749484627034811)
    ·
      refine ⟨49789073075624226940552217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33192715383749484627034811 49789073075624226940552217)
      ·
        refine ⟨37341804806718170205414163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49789073075624226940552217 37341804806718170205414163)
        ·
          refine ⟨56012707210077255308121245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37341804806718170205414163 56012707210077255308121245)
          ·
            refine ⟨21004765203778970740545467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56012707210077255308121245 21004765203778970740545467)
            ·
              refine ⟨31507147805668456110818201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21004765203778970740545467 31507147805668456110818201)
              ·
                refine ⟨23630360854251342083113651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31507147805668456110818201 23630360854251342083113651)
                ·
                  refine ⟨35445541281377013124670477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23630360854251342083113651 35445541281377013124670477)
                  ·
                    refine ⟨13292077980516379921751429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35445541281377013124670477 13292077980516379921751429)
                    ·
                      refine ⟨2492264621346821235328393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13292077980516379921751429 2492264621346821235328393)
                      ·
                        rfl

theorem cell23_4853668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_4853668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853668 prefixEnd_4853668 := by exact prefixLift 4853668
  have htrace : WordTrace (prefixWord ++ tailWord_4853668) baseStart_4853668 baseEnd_4853668 := by
    simpa [prefixWord, tailWord_4853668, baseEnd_4853668] using wordTrace_append hprefix tailTrace_4853668
  have hstable : (prefixWord ++ tailWord_4853668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853668).length < 2 ^ (prefixWord ++ tailWord_4853668).sum := by decide
  have hdescent : baseEnd_4853668 < baseStart_4853668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853688 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 1, 4, 3]
def baseStart_4853688 : Nat := 118140960795 + 4853688 * 2 ^ 59
def prefixEnd_4853688 : Nat := 4983230072969 + 3 ^ 40 * 4853688 * 2
def baseEnd_4853688 : Nat := 2492274890959911157078301

theorem tailTrace_4853688 : CollatzResearch.WordTrace tailWord_4853688 prefixEnd_4853688 2492274890959911157078301 := by
  unfold tailWord_4853688
  simp only [CollatzResearch.WordTrace]
  refine ⟨88514272419962397379956859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118019029893283196506609145 88514272419962397379956859)
  ·
    refine ⟨132771408629943596069935289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88514272419962397379956859 132771408629943596069935289)
    ·
      refine ⟨99578556472457697052451467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132771408629943596069935289 99578556472457697052451467)
      ·
        refine ⟨149367834708686545578677201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99578556472457697052451467 149367834708686545578677201)
        ·
          refine ⟨112025876031514909184007901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149367834708686545578677201 112025876031514909184007901)
          ·
            refine ⟨42009703511818090944002963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112025876031514909184007901 42009703511818090944002963)
            ·
              refine ⟨63014555267727136416004445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42009703511818090944002963 63014555267727136416004445)
              ·
                refine ⟨23630458225397676156001667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63014555267727136416004445 23630458225397676156001667)
                ·
                  refine ⟨35445687338096514234002501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23630458225397676156001667 35445687338096514234002501)
                  ·
                    refine ⟨6646066375893096418875469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35445687338096514234002501 6646066375893096418875469)
                    ·
                      refine ⟨2492274890959911157078301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6646066375893096418875469 2492274890959911157078301)
                      ·
                        rfl

theorem cell23_4853688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 1, 4, 3].length) (baseStart_4853688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853688 prefixEnd_4853688 := by exact prefixLift 4853688
  have htrace : WordTrace (prefixWord ++ tailWord_4853688) baseStart_4853688 baseEnd_4853688 := by
    simpa [prefixWord, tailWord_4853688, baseEnd_4853688] using wordTrace_append hprefix tailTrace_4853688
  have hstable : (prefixWord ++ tailWord_4853688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853688).length < 2 ^ (prefixWord ++ tailWord_4853688).sum := by decide
  have hdescent : baseEnd_4853688 < baseStart_4853688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853691 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 8]
def baseStart_4853691 : Nat := 118140960795 + 4853691 * 2 ^ 59
def prefixEnd_4853691 : Nat := 4983230072969 + 3 ^ 40 * 4853691 * 2
def baseEnd_4853691 : Nat := 276919603489097182815643

theorem tailTrace_4853691 : CollatzResearch.WordTrace tailWord_4853691 prefixEnd_4853691 276919603489097182815643 := by
  unfold tailWord_4853691
  simp only [CollatzResearch.WordTrace]
  refine ⟨177028654258913926272272927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118019102839275950848181951 177028654258913926272272927)
  ·
    refine ⟨265542981388370889408409391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177028654258913926272272927 265542981388370889408409391)
    ·
      refine ⟨398314472082556334112614087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265542981388370889408409391 398314472082556334112614087)
      ·
        refine ⟨597471708123834501168921131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398314472082556334112614087 597471708123834501168921131)
        ·
          refine ⟨896207562185751751753381697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597471708123834501168921131 896207562185751751753381697)
          ·
            refine ⟨672155671639313813815036273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 896207562185751751753381697 672155671639313813815036273)
            ·
              refine ⟨504116753729485360361277205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 672155671639313813815036273 504116753729485360361277205)
              ·
                refine ⟨23630472831069626266934869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 504116753729485360361277205 23630472831069626266934869)
                ·
                  refine ⟨276919603489097182815643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23630472831069626266934869 276919603489097182815643)
                  ·
                    rfl

theorem cell23_4853691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 8].length) (baseStart_4853691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853691 prefixEnd_4853691 := by exact prefixLift 4853691
  have htrace : WordTrace (prefixWord ++ tailWord_4853691) baseStart_4853691 baseEnd_4853691 := by
    simpa [prefixWord, tailWord_4853691, baseEnd_4853691] using wordTrace_append hprefix tailTrace_4853691
  have hstable : (prefixWord ++ tailWord_4853691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853691).length < 2 ^ (prefixWord ++ tailWord_4853691).sum := by decide
  have hdescent : baseEnd_4853691 < baseStart_4853691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853708 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 8]
def baseStart_4853708 : Nat := 118140960795 + 4853708 * 2 ^ 59
def prefixEnd_4853708 : Nat := 4983230072969 + 3 ^ 40 * 4853708 * 2
def baseEnd_4853708 : Nat := 276920573397000119869801

theorem tailTrace_4853708 : CollatzResearch.WordTrace tailWord_4853708 prefixEnd_4853708 276920573397000119869801 := by
  unfold tailWord_4853708
  simp only [CollatzResearch.WordTrace]
  refine ⟨88514637149926169087820889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118019516199901558783761185 88514637149926169087820889)
  ·
    refine ⟨66385977862444626815865667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88514637149926169087820889 66385977862444626815865667)
    ·
      refine ⟨99578966793666940223798501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66385977862444626815865667 99578966793666940223798501)
      ·
        refine ⟨18671056273812551291962219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99578966793666940223798501 18671056273812551291962219)
        ·
          refine ⟨28006584410718826937943329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18671056273812551291962219 28006584410718826937943329)
          ·
            refine ⟨21004938308039120203457497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28006584410718826937943329 21004938308039120203457497)
            ·
              refine ⟨15753703731029340152593123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21004938308039120203457497 15753703731029340152593123)
              ·
                refine ⟨23630555596544010228889685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15753703731029340152593123 23630555596544010228889685)
                ·
                  refine ⟨276920573397000119869801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23630555596544010228889685 276920573397000119869801)
                  ·
                    rfl

theorem cell23_4853708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 8].length) (baseStart_4853708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853708 prefixEnd_4853708 := by exact prefixLift 4853708
  have htrace : WordTrace (prefixWord ++ tailWord_4853708) baseStart_4853708 baseEnd_4853708 := by
    simpa [prefixWord, tailWord_4853708, baseEnd_4853708] using wordTrace_append hprefix tailTrace_4853708
  have hstable : (prefixWord ++ tailWord_4853708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853708).length < 2 ^ (prefixWord ++ tailWord_4853708).sum := by decide
  have hdescent : baseEnd_4853708 < baseStart_4853708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853768 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 3, 6]
def baseStart_4853768 : Nat := 118140960795 + 4853768 * 2 ^ 59
def prefixEnd_4853768 : Nat := 4983230072969 + 3 ^ 40 * 4853768 * 2
def baseEnd_4853768 : Nat := 830771989804090281359311

theorem tailTrace_4853768 : CollatzResearch.WordTrace tailWord_4853768 prefixEnd_4853768 830771989804090281359311 := by
  unfold tailWord_4853768
  simp only [CollatzResearch.WordTrace]
  refine ⟨88515731339817484211412979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118020975119756645615217305 88515731339817484211412979)
  ·
    refine ⟨132773597009726226317119469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88515731339817484211412979 132773597009726226317119469)
    ·
      refine ⟨49790098878647334868919801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132773597009726226317119469 49790098878647334868919801)
      ·
        refine ⟨37342574158985501151689851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49790098878647334868919801 37342574158985501151689851)
        ·
          refine ⟨56013861238478251727534777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37342574158985501151689851 56013861238478251727534777)
          ·
            refine ⟨42010395928858688795651083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56013861238478251727534777 42010395928858688795651083)
            ·
              refine ⟨63015593893288033193476625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42010395928858688795651083 63015593893288033193476625)
              ·
                refine ⟨47261695419966024895107469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63015593893288033193476625 47261695419966024895107469)
                ·
                  refine ⟨17723135782487259335665301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47261695419966024895107469 17723135782487259335665301)
                  ·
                    refine ⟨830771989804090281359311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17723135782487259335665301 830771989804090281359311)
                    ·
                      rfl

theorem cell23_4853768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_4853768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853768 prefixEnd_4853768 := by exact prefixLift 4853768
  have htrace : WordTrace (prefixWord ++ tailWord_4853768) baseStart_4853768 baseEnd_4853768 := by
    simpa [prefixWord, tailWord_4853768, baseEnd_4853768] using wordTrace_append hprefix tailTrace_4853768
  have hstable : (prefixWord ++ tailWord_4853768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853768).length < 2 ^ (prefixWord ++ tailWord_4853768).sum := by decide
  have hdescent : baseEnd_4853768 < baseStart_4853768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853795 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 3]
def baseStart_4853795 : Nat := 118140960795 + 4853795 * 2 ^ 59
def prefixEnd_4853795 : Nat := 4983230072969 + 3 ^ 40 * 4853795 * 2
def baseEnd_4853795 : Nat := 2492329833389942238440309

theorem tailTrace_4853795 : CollatzResearch.WordTrace tailWord_4853795 prefixEnd_4853795 2492329833389942238440309 := by
  unfold tailWord_4853795
  simp only [CollatzResearch.WordTrace]
  refine ⟨177032447450537152034058839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118021631633691434689372559 177032447450537152034058839)
  ·
    refine ⟨265548671175805728051088259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177032447450537152034058839 265548671175805728051088259)
    ·
      refine ⟨398323006763708592076632389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265548671175805728051088259 398323006763708592076632389)
      ·
        refine ⟨74685563768195361014368573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 398323006763708592076632389 74685563768195361014368573)
        ·
          refine ⟨28007086413073260380388215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74685563768195361014368573 28007086413073260380388215)
          ·
            refine ⟨42010629619609890570582323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28007086413073260380388215 42010629619609890570582323)
            ·
              refine ⟨63015944429414835855873485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42010629619609890570582323 63015944429414835855873485)
              ·
                refine ⟨23630979161030563445952557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63015944429414835855873485 23630979161030563445952557)
                ·
                  refine ⟨8861617185386461292232209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23630979161030563445952557 8861617185386461292232209)
                  ·
                    refine ⟨6646212889039845969174157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8861617185386461292232209 6646212889039845969174157)
                    ·
                      refine ⟨2492329833389942238440309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6646212889039845969174157 2492329833389942238440309)
                      ·
                        rfl

theorem cell23_4853795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_4853795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853795 prefixEnd_4853795 := by exact prefixLift 4853795
  have htrace : WordTrace (prefixWord ++ tailWord_4853795) baseStart_4853795 baseEnd_4853795 := by
    simpa [prefixWord, tailWord_4853795, baseEnd_4853795] using wordTrace_append hprefix tailTrace_4853795
  have hstable : (prefixWord ++ tailWord_4853795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853795).length < 2 ^ (prefixWord ++ tailWord_4853795).sum := by decide
  have hdescent : baseEnd_4853795 < baseStart_4853795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853796 : List Nat := [2, 3, 1, 4, 2, 2, 1, 1, 2, 3, 2]
def baseStart_4853796 : Nat := 118140960795 + 4853796 * 2 ^ 59
def prefixEnd_4853796 : Nat := 4983230072969 + 3 ^ 40 * 4853796 * 2
def baseEnd_4853796 : Nat := 2492330346870596734527805

theorem tailTrace_4853796 : CollatzResearch.WordTrace tailWord_4853796 prefixEnd_4853796 2492330346870596734527805 := by
  unfold tailWord_4853796
  simp only [CollatzResearch.WordTrace]
  refine ⟨88516241961766764602422621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118021655949022352803230161 88516241961766764602422621)
  ·
    refine ⟨33193590735662536725908483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88516241961766764602422621 33193590735662536725908483)
    ·
      refine ⟨49790386103493805088862725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33193590735662536725908483 49790386103493805088862725)
      ·
        refine ⟨9335697394405088454161761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49790386103493805088862725 9335697394405088454161761)
        ·
          refine ⟨7001773045803816340621321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9335697394405088454161761 7001773045803816340621321)
          ·
            refine ⟨5251329784352862255465991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7001773045803816340621321 5251329784352862255465991)
            ·
              refine ⟨7876994676529293383198987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5251329784352862255465991 7876994676529293383198987)
              ·
                refine ⟨11815492014793940074798481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7876994676529293383198987 11815492014793940074798481)
                ·
                  refine ⟨8861619011095455056098861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11815492014793940074798481 8861619011095455056098861)
                  ·
                    refine ⟨3323107129160795646037073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8861619011095455056098861 3323107129160795646037073)
                    ·
                      refine ⟨2492330346870596734527805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3323107129160795646037073 2492330346870596734527805)
                      ·
                        rfl

theorem cell23_4853796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_4853796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853796 prefixEnd_4853796 := by exact prefixLift 4853796
  have htrace : WordTrace (prefixWord ++ tailWord_4853796) baseStart_4853796 baseEnd_4853796 := by
    simpa [prefixWord, tailWord_4853796, baseEnd_4853796] using wordTrace_append hprefix tailTrace_4853796
  have hstable : (prefixWord ++ tailWord_4853796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853796).length < 2 ^ (prefixWord ++ tailWord_4853796).sum := by decide
  have hdescent : baseEnd_4853796 < baseStart_4853796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853809 : List Nat := [1, 2, 2, 3, 1, 5, 2, 1, 1, 1, 4]
def baseStart_4853809 : Nat := 118140960795 + 4853809 * 2 ^ 59
def prefixEnd_4853809 : Nat := 4983230072969 + 3 ^ 40 * 4853809 * 2
def baseEnd_4853809 : Nat := 2492337022119105183665245

theorem tailTrace_4853809 : CollatzResearch.WordTrace tailWord_4853809 prefixEnd_4853809 2492337022119105183665245 := by
  unfold tailWord_4853809
  simp only [CollatzResearch.WordTrace]
  refine ⟨177032958072486432425068481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118021972048324288283378987 177032958072486432425068481)
  ·
    refine ⟨132774718554364824318801361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177032958072486432425068481 132774718554364824318801361)
    ·
      refine ⟨99581038915773618239101021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132774718554364824318801361 99581038915773618239101021)
      ·
        refine ⟨37342889593415106839662883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99581038915773618239101021 37342889593415106839662883)
        ·
          refine ⟨56014334390122660259494325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37342889593415106839662883 56014334390122660259494325)
          ·
            refine ⟨5251343849073999399327593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56014334390122660259494325 5251343849073999399327593)
            ·
              refine ⟨3938507886805499549495695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5251343849073999399327593 3938507886805499549495695)
              ·
                refine ⟨5907761830208249324243543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3938507886805499549495695 5907761830208249324243543)
                ·
                  refine ⟨8861642745312373986365315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5907761830208249324243543 8861642745312373986365315)
                  ·
                    refine ⟨13292464117968560979547973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8861642745312373986365315 13292464117968560979547973)
                    ·
                      refine ⟨2492337022119105183665245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13292464117968560979547973 2492337022119105183665245)
                      ·
                        rfl

theorem cell23_4853809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_4853809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853809 prefixEnd_4853809 := by exact prefixLift 4853809
  have htrace : WordTrace (prefixWord ++ tailWord_4853809) baseStart_4853809 baseEnd_4853809 := by
    simpa [prefixWord, tailWord_4853809, baseEnd_4853809] using wordTrace_append hprefix tailTrace_4853809
  have hstable : (prefixWord ++ tailWord_4853809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853809).length < 2 ^ (prefixWord ++ tailWord_4853809).sum := by decide
  have hdescent : baseEnd_4853809 < baseStart_4853809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853818 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6]
def baseStart_4853818 : Nat := 118140960795 + 4853818 * 2 ^ 59
def prefixEnd_4853818 : Nat := 4983230072969 + 3 ^ 40 * 4853818 * 2
def baseEnd_4853818 : Nat := 2492341643444995648452703

theorem tailTrace_4853818 : CollatzResearch.WordTrace tailWord_4853818 prefixEnd_4853818 2492341643444995648452703 := by
  unfold tailWord_4853818
  simp only [CollatzResearch.WordTrace]
  refine ⟨44258321582363456740536527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118022190886302551308097405 44258321582363456740536527)
  ·
    refine ⟨66387482373545185110804791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44258321582363456740536527 66387482373545185110804791)
    ·
      refine ⟨99581223560317777666207187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66387482373545185110804791 99581223560317777666207187)
      ·
        refine ⟨149371835340476666499310781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99581223560317777666207187 149371835340476666499310781)
        ·
          refine ⟨56014438252678749937241543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149371835340476666499310781 56014438252678749937241543)
          ·
            refine ⟨84021657379018124905862315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56014438252678749937241543 84021657379018124905862315)
            ·
              refine ⟨126032486068527187358793473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84021657379018124905862315 126032486068527187358793473)
              ·
                refine ⟨94524364551395390519095105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126032486068527187358793473 94524364551395390519095105)
                ·
                  refine ⟨70893273413546542889321329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94524364551395390519095105 70893273413546542889321329)
                  ·
                    refine ⟨53169955060159907166990997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70893273413546542889321329 53169955060159907166990997)
                    ·
                      refine ⟨2492341643444995648452703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53169955060159907166990997 2492341643444995648452703)
                      ·
                        rfl

theorem cell23_4853818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_4853818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853818 prefixEnd_4853818 := by exact prefixLift 4853818
  have htrace : WordTrace (prefixWord ++ tailWord_4853818) baseStart_4853818 baseEnd_4853818 := by
    simpa [prefixWord, tailWord_4853818, baseEnd_4853818] using wordTrace_append hprefix tailTrace_4853818
  have hstable : (prefixWord ++ tailWord_4853818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853818).length < 2 ^ (prefixWord ++ tailWord_4853818).sum := by decide
  have hdescent : baseEnd_4853818 < baseStart_4853818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853846 : List Nat := [5, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_4853846 : Nat := 118140960795 + 4853846 * 2 ^ 59
def prefixEnd_4853846 : Nat := 4983230072969 + 3 ^ 40 * 4853846 * 2
def baseEnd_4853846 : Nat := 2492356020903321538902575

theorem tailTrace_4853846 : CollatzResearch.WordTrace tailWord_4853846 prefixEnd_4853846 2492356020903321538902575 := by
  unfold tailWord_4853846
  simp only [CollatzResearch.WordTrace]
  refine ⟨11064644223334524234010337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118022871715568258496110261 11064644223334524234010337)
  ·
    refine ⟨8298483167500893175507753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11064644223334524234010337 8298483167500893175507753)
    ·
      refine ⟨6223862375625669881630815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8298483167500893175507753 6223862375625669881630815)
      ·
        refine ⟨9335793563438504822446223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6223862375625669881630815 9335793563438504822446223)
        ·
          refine ⟨14003690345157757233669335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9335793563438504822446223 14003690345157757233669335)
          ·
            refine ⟨21005535517736635850504003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14003690345157757233669335 21005535517736635850504003)
            ·
              refine ⟨31508303276604953775756005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21005535517736635850504003 31508303276604953775756005)
              ·
                refine ⟨5907806864363428832954251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31508303276604953775756005 5907806864363428832954251)
                ·
                  refine ⟨8861710296545143249431377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5907806864363428832954251 8861710296545143249431377)
                  ·
                    refine ⟨6646282722408857437073533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8861710296545143249431377 6646282722408857437073533)
                    ·
                      refine ⟨2492356020903321538902575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6646282722408857437073533 2492356020903321538902575)
                      ·
                        rfl

theorem cell23_4853846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_4853846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853846 prefixEnd_4853846 := by exact prefixLift 4853846
  have htrace : WordTrace (prefixWord ++ tailWord_4853846) baseStart_4853846 baseEnd_4853846 := by
    simpa [prefixWord, tailWord_4853846, baseEnd_4853846] using wordTrace_append hprefix tailTrace_4853846
  have hstable : (prefixWord ++ tailWord_4853846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853846).length < 2 ^ (prefixWord ++ tailWord_4853846).sum := by decide
  have hdescent : baseEnd_4853846 < baseStart_4853846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853869 : List Nat := [1, 5, 1, 1, 2, 1, 1, 5, 1, 3, 2]
def baseStart_4853869 : Nat := 118140960795 + 4853869 * 2 ^ 59
def prefixEnd_4853869 : Nat := 4983230072969 + 3 ^ 40 * 4853869 * 2
def baseEnd_4853869 : Nat := 2492367830958374948914969

theorem tailTrace_4853869 : CollatzResearch.WordTrace tailWord_4853869 prefixEnd_4853869 2492367830958374948914969 := by
  unfold tailWord_4853869
  simp only [CollatzResearch.WordTrace]
  refine ⟨177035146452269062672252661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118023430968179375114835107 177035146452269062672252661)
  ·
    refine ⟨16597044979900224625523687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 177035146452269062672252661 16597044979900224625523687)
    ·
      refine ⟨24895567469850336938285531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16597044979900224625523687 24895567469850336938285531)
      ·
        refine ⟨37343351204775505407428297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24895567469850336938285531 37343351204775505407428297)
        ·
          refine ⟨28007513403581629055571223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37343351204775505407428297 28007513403581629055571223)
          ·
            refine ⟨42011270105372443583356835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28007513403581629055571223 42011270105372443583356835)
            ·
              refine ⟨63016905158058665375035253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42011270105372443583356835 63016905158058665375035253)
              ·
                refine ⟨5907834858567999878909555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63016905158058665375035253 5907834858567999878909555)
                ·
                  refine ⟨8861752287851999818364333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5907834858567999878909555 8861752287851999818364333)
                  ·
                    refine ⟨3323157107944499931886625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8861752287851999818364333 3323157107944499931886625)
                    ·
                      refine ⟨2492367830958374948914969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3323157107944499931886625 2492367830958374948914969)
                      ·
                        rfl

theorem cell23_4853869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_4853869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853869 prefixEnd_4853869 := by exact prefixLift 4853869
  have htrace : WordTrace (prefixWord ++ tailWord_4853869) baseStart_4853869 baseEnd_4853869 := by
    simpa [prefixWord, tailWord_4853869, baseEnd_4853869] using wordTrace_append hprefix tailTrace_4853869
  have hstable : (prefixWord ++ tailWord_4853869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853869).length < 2 ^ (prefixWord ++ tailWord_4853869).sum := by decide
  have hdescent : baseEnd_4853869 < baseStart_4853869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853895 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 4]
def baseStart_4853895 : Nat := 118140960795 + 4853895 * 2 ^ 59
def prefixEnd_4853895 : Nat := 4983230072969 + 3 ^ 40 * 4853895 * 2
def baseEnd_4853895 : Nat := 2492381181455391847189849

theorem tailTrace_4853895 : CollatzResearch.WordTrace tailWord_4853895 prefixEnd_4853895 2492381181455391847189849 := by
  unfold tailWord_4853895
  simp only [CollatzResearch.WordTrace]
  refine ⟨177036094750174869112699139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118024063166783246075132759 177036094750174869112699139)
  ·
    refine ⟨265554142125262303669048709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177036094750174869112699139 265554142125262303669048709)
    ·
      refine ⟨49791401648486681937946633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 265554142125262303669048709 49791401648486681937946633)
      ·
        refine ⟨37343551236365011453459975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49791401648486681937946633 37343551236365011453459975)
        ·
          refine ⟨56015326854547517180189963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37343551236365011453459975 56015326854547517180189963)
          ·
            refine ⟨84022990281821275770284945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56015326854547517180189963 84022990281821275770284945)
            ·
              refine ⟨63017242711365956827713709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84022990281821275770284945 63017242711365956827713709)
              ·
                refine ⟨23631466016762233810392641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63017242711365956827713709 23631466016762233810392641)
                ·
                  refine ⟨17723599512571675357794481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23631466016762233810392641 17723599512571675357794481)
                  ·
                    refine ⟨13292699634428756518345861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17723599512571675357794481 13292699634428756518345861)
                    ·
                      refine ⟨2492381181455391847189849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13292699634428756518345861 2492381181455391847189849)
                      ·
                        rfl

theorem cell23_4853895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_4853895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853895 prefixEnd_4853895 := by exact prefixLift 4853895
  have htrace : WordTrace (prefixWord ++ tailWord_4853895) baseStart_4853895 baseEnd_4853895 := by
    simpa [prefixWord, tailWord_4853895, baseEnd_4853895] using wordTrace_append hprefix tailTrace_4853895
  have hstable : (prefixWord ++ tailWord_4853895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853895).length < 2 ^ (prefixWord ++ tailWord_4853895).sum := by decide
  have hdescent : baseEnd_4853895 < baseStart_4853895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853910 : List Nat := [5, 3, 2, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_4853910 : Nat := 118140960795 + 4853910 * 2 ^ 59
def prefixEnd_4853910 : Nat := 4983230072969 + 3 ^ 40 * 4853910 * 2
def baseEnd_4853910 : Nat := 2492388883665209288502281

theorem tailTrace_4853910 : CollatzResearch.WordTrace tailWord_4853910 prefixEnd_4853910 2492388883665209288502281 := by
  unfold tailWord_4853910
  simp only [CollatzResearch.WordTrace]
  refine ⟨11064790115320032917155949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118024427896747017782996789 11064790115320032917155949)
  ·
    refine ⟨4149296293245012343933481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11064790115320032917155949 4149296293245012343933481)
    ·
      refine ⟨3111972219933759257950111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4149296293245012343933481 3111972219933759257950111)
      ·
        refine ⟨4667958329900638886925167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3111972219933759257950111 4667958329900638886925167)
        ·
          refine ⟨7001937494850958330387751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4667958329900638886925167 7001937494850958330387751)
          ·
            refine ⟨10502906242276437495581627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7001937494850958330387751 10502906242276437495581627)
            ·
              refine ⟨15754359363414656243372441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10502906242276437495581627 15754359363414656243372441)
              ·
                refine ⟨11815769522560992182529331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15754359363414656243372441 11815769522560992182529331)
                ·
                  refine ⟨17723654283841488273793997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11815769522560992182529331 17723654283841488273793997)
                  ·
                    refine ⟨6646370356440558102672749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17723654283841488273793997 6646370356440558102672749)
                    ·
                      refine ⟨2492388883665209288502281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6646370356440558102672749 2492388883665209288502281)
                      ·
                        rfl

theorem cell23_4853910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_4853910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853910 prefixEnd_4853910 := by exact prefixLift 4853910
  have htrace : WordTrace (prefixWord ++ tailWord_4853910) baseStart_4853910 baseEnd_4853910 := by
    simpa [prefixWord, tailWord_4853910, baseEnd_4853910] using wordTrace_append hprefix tailTrace_4853910
  have hstable : (prefixWord ++ tailWord_4853910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853910).length < 2 ^ (prefixWord ++ tailWord_4853910).sum := by decide
  have hdescent : baseEnd_4853910 < baseStart_4853910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853933 : List Nat := [1, 5, 2, 1, 2, 2, 2, 2, 2, 2, 2]
def baseStart_4853933 : Nat := 118140960795 + 4853933 * 2 ^ 59
def prefixEnd_4853933 : Nat := 4983230072969 + 3 ^ 40 * 4853933 * 2
def baseEnd_4853933 : Nat := 2492400693720262698514675

theorem tailTrace_4853933 : CollatzResearch.WordTrace tailWord_4853933 prefixEnd_4853933 2492400693720262698514675 := by
  unfold tailWord_4853933
  simp only [CollatzResearch.WordTrace]
  refine ⟨177037480724037201602582453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118024987149358134401721635 177037480724037201602582453)
  ·
    refine ⟨16597263817878487650242105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 177037480724037201602582453 16597263817878487650242105)
    ·
      refine ⟨12447947863408865737681579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16597263817878487650242105 12447947863408865737681579)
      ·
        refine ⟨18671921795113298606522369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12447947863408865737681579 18671921795113298606522369)
        ·
          refine ⟨14003941346334973954891777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18671921795113298606522369 14003941346334973954891777)
          ·
            refine ⟨10502956009751230466168833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14003941346334973954891777 10502956009751230466168833)
            ·
              refine ⟨7877217007313422849626625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10502956009751230466168833 7877217007313422849626625)
              ·
                refine ⟨5907912755485067137219969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7877217007313422849626625 5907912755485067137219969)
                ·
                  refine ⟨4430934566613800352914977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5907912755485067137219969 4430934566613800352914977)
                  ·
                    refine ⟨3323200924960350264686233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4430934566613800352914977 3323200924960350264686233)
                    ·
                      refine ⟨2492400693720262698514675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3323200924960350264686233 2492400693720262698514675)
                      ·
                        rfl

theorem cell23_4853933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_4853933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853933 prefixEnd_4853933 := by exact prefixLift 4853933
  have htrace : WordTrace (prefixWord ++ tailWord_4853933) baseStart_4853933 baseEnd_4853933 := by
    simpa [prefixWord, tailWord_4853933, baseEnd_4853933] using wordTrace_append hprefix tailTrace_4853933
  have hstable : (prefixWord ++ tailWord_4853933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853933).length < 2 ^ (prefixWord ++ tailWord_4853933).sum := by decide
  have hdescent : baseEnd_4853933 < baseStart_4853933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853945 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 1, 2, 5]
def baseStart_4853945 : Nat := 118140960795 + 4853945 * 2 ^ 59
def prefixEnd_4853945 : Nat := 4983230072969 + 3 ^ 40 * 4853945 * 2
def baseEnd_4853945 : Nat := 2492406855488116651564619

theorem tailTrace_4853945 : CollatzResearch.WordTrace tailWord_4853945 prefixEnd_4853945 2492406855488116651564619 := by
  unfold tailWord_4853945
  simp only [CollatzResearch.WordTrace]
  refine ⟨177037918399993727652019289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118025278933329151768012859 177037918399993727652019289)
  ·
    refine ⟨132778438799995295739014467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177037918399993727652019289 132778438799995295739014467)
    ·
      refine ⟨199167658199992943608521701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132778438799995295739014467 199167658199992943608521701)
      ·
        refine ⟨37343935912498676926597819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199167658199992943608521701 37343935912498676926597819)
        ·
          refine ⟨56015903868748015389896729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37343935912498676926597819 56015903868748015389896729)
          ·
            refine ⟨42011927901561011542422547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56015903868748015389896729 42011927901561011542422547)
            ·
              refine ⟨63017891852341517313633821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42011927901561011542422547 63017891852341517313633821)
              ·
                refine ⟨23631709444628068992612683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63017891852341517313633821 23631709444628068992612683)
                ·
                  refine ⟨35447564166942103488919025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23631709444628068992612683 35447564166942103488919025)
                  ·
                    refine ⟨26585673125206577616689269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35447564166942103488919025 26585673125206577616689269)
                    ·
                      refine ⟨2492406855488116651564619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26585673125206577616689269 2492406855488116651564619)
                      ·
                        rfl

theorem cell23_4853945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_4853945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853945 prefixEnd_4853945 := by exact prefixLift 4853945
  have htrace : WordTrace (prefixWord ++ tailWord_4853945) baseStart_4853945 baseEnd_4853945 := by
    simpa [prefixWord, tailWord_4853945, baseEnd_4853945] using wordTrace_append hprefix tailTrace_4853945
  have hstable : (prefixWord ++ tailWord_4853945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853945).length < 2 ^ (prefixWord ++ tailWord_4853945).sum := by decide
  have hdescent : baseEnd_4853945 < baseStart_4853945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853985 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 1, 3, 6]
def baseStart_4853985 : Nat := 118140960795 + 4853985 * 2 ^ 59
def prefixEnd_4853985 : Nat := 4983230072969 + 3 ^ 40 * 4853985 * 2
def baseEnd_4853985 : Nat := 2492427394714296495064435

theorem tailTrace_4853985 : CollatzResearch.WordTrace tailWord_4853985 prefixEnd_4853985 2492427394714296495064435 := by
  unfold tailWord_4853985
  simp only [CollatzResearch.WordTrace]
  refine ⟨177039377319848814483475409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118026251546565876322316939 177039377319848814483475409)
  ·
    refine ⟨132779532989886610862606557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177039377319848814483475409 132779532989886610862606557)
    ·
      refine ⟨49792324871207479073477459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132779532989886610862606557 49792324871207479073477459)
      ·
        refine ⟨74688487306811218610216189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49792324871207479073477459 74688487306811218610216189)
        ·
          refine ⟨28008182740054206978831071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74688487306811218610216189 28008182740054206978831071)
          ·
            refine ⟨42012274110081310468246607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28008182740054206978831071 42012274110081310468246607)
            ·
              refine ⟨63018411165121965702369911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42012274110081310468246607 63018411165121965702369911)
              ·
                refine ⟨94527616747682948553554867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63018411165121965702369911 94527616747682948553554867)
                ·
                  refine ⟨141791425121524422830332301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94527616747682948553554867 141791425121524422830332301)
                  ·
                    refine ⟨53171784420571658561374613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 141791425121524422830332301 53171784420571658561374613)
                    ·
                      refine ⟨2492427394714296495064435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53171784420571658561374613 2492427394714296495064435)
                      ·
                        rfl

theorem cell23_4853985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_4853985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853985 prefixEnd_4853985 := by exact prefixLift 4853985
  have htrace : WordTrace (prefixWord ++ tailWord_4853985) baseStart_4853985 baseEnd_4853985 := by
    simpa [prefixWord, tailWord_4853985, baseEnd_4853985] using wordTrace_append hprefix tailTrace_4853985
  have hstable : (prefixWord ++ tailWord_4853985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853985).length < 2 ^ (prefixWord ++ tailWord_4853985).sum := by decide
  have hdescent : baseEnd_4853985 < baseStart_4853985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853989 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 2, 4, 2]
def baseStart_4853989 : Nat := 118140960795 + 4853989 * 2 ^ 59
def prefixEnd_4853989 : Nat := 4983230072969 + 3 ^ 40 * 4853989 * 2
def baseEnd_4853989 : Nat := 2492429448636914479414417

theorem tailTrace_4853989 : CollatzResearch.WordTrace tailWord_4853989 prefixEnd_4853989 2492429448636914479414417 := by
  unfold tailWord_4853989
  simp only [CollatzResearch.WordTrace]
  refine ⟨177039523211834323166621021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118026348807889548777747347 177039523211834323166621021)
  ·
    refine ⟨66389821204437871187482883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177039523211834323166621021 66389821204437871187482883)
    ·
      refine ⟨99584731806656806781224325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66389821204437871187482883 99584731806656806781224325)
      ·
        refine ⟨18672137213748151271479561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99584731806656806781224325 18672137213748151271479561)
        ·
          refine ⟨14004102910311113453609671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18672137213748151271479561 14004102910311113453609671)
          ·
            refine ⟨21006154365466670180414507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14004102910311113453609671 21006154365466670180414507)
            ·
              refine ⟨31509231548200005270621761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21006154365466670180414507 31509231548200005270621761)
              ·
                refine ⟨23631923661150003952966321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31509231548200005270621761 23631923661150003952966321)
                ·
                  refine ⟨17723942745862502964724741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23631923661150003952966321 17723942745862502964724741)
                  ·
                    refine ⟨3323239264849219305885889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17723942745862502964724741 3323239264849219305885889)
                    ·
                      refine ⟨2492429448636914479414417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3323239264849219305885889 2492429448636914479414417)
                      ·
                        rfl

theorem cell23_4853989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_4853989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853989 prefixEnd_4853989 := by exact prefixLift 4853989
  have htrace : WordTrace (prefixWord ++ tailWord_4853989) baseStart_4853989 baseEnd_4853989 := by
    simpa [prefixWord, tailWord_4853989, baseEnd_4853989] using wordTrace_append hprefix tailTrace_4853989
  have hstable : (prefixWord ++ tailWord_4853989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853989).length < 2 ^ (prefixWord ++ tailWord_4853989).sum := by decide
  have hdescent : baseEnd_4853989 < baseStart_4853989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853995 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 8]
def baseStart_4853995 : Nat := 118140960795 + 4853995 * 2 ^ 59
def prefixEnd_4853995 : Nat := 4983230072969 + 3 ^ 40 * 4853995 * 2
def baseEnd_4853995 : Nat := 276936947724537939548821

theorem tailTrace_4853995 : CollatzResearch.WordTrace tailWord_4853995 prefixEnd_4853995 276936947724537939548821 := by
  unfold tailWord_4853995
  simp only [CollatzResearch.WordTrace]
  refine ⟨177039742049812586191339439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118026494699875057460892959 177039742049812586191339439)
  ·
    refine ⟨265559613074718879287009159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177039742049812586191339439 265559613074718879287009159)
    ·
      refine ⟨398339419612078318930513739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265559613074718879287009159 398339419612078318930513739)
      ·
        refine ⟨597509129418117478395770609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398339419612078318930513739 597509129418117478395770609)
        ·
          refine ⟨448131847063588108796827957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 597509129418117478395770609 448131847063588108796827957)
          ·
            refine ⟨42012360662211385199702621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 448131847063588108796827957 42012360662211385199702621)
            ·
              refine ⟨15754635248329269449888483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42012360662211385199702621 15754635248329269449888483)
              ·
                refine ⟨23631952872493904174832725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15754635248329269449888483 23631952872493904174832725)
                ·
                  refine ⟨276936947724537939548821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23631952872493904174832725 276936947724537939548821)
                  ·
                    rfl

theorem cell23_4853995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 8].length) (baseStart_4853995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853995 prefixEnd_4853995 := by exact prefixLift 4853995
  have htrace : WordTrace (prefixWord ++ tailWord_4853995) baseStart_4853995 baseEnd_4853995 := by
    simpa [prefixWord, tailWord_4853995, baseEnd_4853995] using wordTrace_append hprefix tailTrace_4853995
  have hstable : (prefixWord ++ tailWord_4853995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853995).length < 2 ^ (prefixWord ++ tailWord_4853995).sum := by decide
  have hdescent : baseEnd_4853995 < baseStart_4853995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4853999 : List Nat := [1, 1, 2, 1, 6, 2, 2, 1, 3, 4]
def baseStart_4853999 : Nat := 118140960795 + 4853999 * 2 ^ 59
def prefixEnd_4853999 : Nat := 4983230072969 + 3 ^ 40 * 4853999 * 2
def baseEnd_4853999 : Nat := 830811527814486480096457

theorem tailTrace_4853999 : CollatzResearch.WordTrace tailWord_4853999 prefixEnd_4853999 830811527814486480096457 := by
  unfold tailWord_4853999
  simp only [CollatzResearch.WordTrace]
  refine ⟨177039887941798094874485051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118026591961198729916323367 177039887941798094874485051)
  ·
    refine ⟨265559831912697142311727577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177039887941798094874485051 265559831912697142311727577)
    ·
      refine ⟨199169873934522856733795683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265559831912697142311727577 199169873934522856733795683)
      ·
        refine ⟨298754810901784285100693525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199169873934522856733795683 298754810901784285100693525)
        ·
          refine ⟨14004131761021138364095009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 298754810901784285100693525 14004131761021138364095009)
          ·
            refine ⟨10503098820765853773071257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14004131761021138364095009 10503098820765853773071257)
            ·
              refine ⟨7877324115574390329803443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10503098820765853773071257 7877324115574390329803443)
              ·
                refine ⟨11815986173361585494705165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7877324115574390329803443 11815986173361585494705165)
                ·
                  refine ⟨4430994815010594560514437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11815986173361585494705165 4430994815010594560514437)
                  ·
                    refine ⟨830811527814486480096457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4430994815010594560514437 830811527814486480096457)
                    ·
                      rfl

theorem cell23_4853999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 4].length) (baseStart_4853999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4853999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4853999 prefixEnd_4853999 := by exact prefixLift 4853999
  have htrace : WordTrace (prefixWord ++ tailWord_4853999) baseStart_4853999 baseEnd_4853999 := by
    simpa [prefixWord, tailWord_4853999, baseEnd_4853999] using wordTrace_append hprefix tailTrace_4853999
  have hstable : (prefixWord ++ tailWord_4853999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4853999).length < 2 ^ (prefixWord ++ tailWord_4853999).sum := by decide
  have hdescent : baseEnd_4853999 < baseStart_4853999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4853999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854015 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 6]
def baseStart_4854015 : Nat := 118140960795 + 4854015 * 2 ^ 59
def prefixEnd_4854015 : Nat := 4983230072969 + 3 ^ 40 * 4854015 * 2
def baseEnd_4854015 : Nat := 2492442799133931377689297

theorem tailTrace_4854015 : CollatzResearch.WordTrace tailWord_4854015 prefixEnd_4854015 2492442799133931377689297 := by
  unfold tailWord_4854015
  simp only [CollatzResearch.WordTrace]
  refine ⟨177040471509740129607067499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118026981006493419738044999 177040471509740129607067499)
  ·
    refine ⟨265560707264610194410601249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177040471509740129607067499 265560707264610194410601249)
    ·
      refine ⟨199170530448457645807950937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265560707264610194410601249 199170530448457645807950937)
      ·
        refine ⟨149377897836343234355963203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199170530448457645807950937 149377897836343234355963203)
        ·
          refine ⟨224066846754514851533944805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149377897836343234355963203 224066846754514851533944805)
          ·
            refine ⟨42012533766471534662614651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 224066846754514851533944805 42012533766471534662614651)
            ·
              refine ⟨63018800649707301993921977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42012533766471534662614651 63018800649707301993921977)
              ·
                refine ⟨47264100487280476495441483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63018800649707301993921977 47264100487280476495441483)
                ·
                  refine ⟨70896150730920714743162225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47264100487280476495441483 70896150730920714743162225)
                  ·
                    refine ⟨53172113048190536057371669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70896150730920714743162225 53172113048190536057371669)
                    ·
                      refine ⟨2492442799133931377689297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53172113048190536057371669 2492442799133931377689297)
                      ·
                        rfl

theorem cell23_4854015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_4854015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854015 prefixEnd_4854015 := by exact prefixLift 4854015
  have htrace : WordTrace (prefixWord ++ tailWord_4854015) baseStart_4854015 baseEnd_4854015 := by
    simpa [prefixWord, tailWord_4854015, baseEnd_4854015] using wordTrace_append hprefix tailTrace_4854015
  have hstable : (prefixWord ++ tailWord_4854015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854015).length < 2 ^ (prefixWord ++ tailWord_4854015).sum := by decide
  have hdescent : baseEnd_4854015 < baseStart_4854015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854049 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 4, 3, 2]
def baseStart_4854049 : Nat := 118140960795 + 4854049 * 2 ^ 59
def prefixEnd_4854049 : Nat := 4983230072969 + 3 ^ 40 * 4854049 * 2
def baseEnd_4854049 : Nat := 2492460257476184244664141

theorem tailTrace_4854049 : CollatzResearch.WordTrace tailWord_4854049 prefixEnd_4854049 2492460257476184244664141 := by
  unfold tailWord_4854049
  simp only [CollatzResearch.WordTrace]
  refine ⟨177041711591616953413805201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118027807727744635609203467 177041711591616953413805201)
  ·
    refine ⟨132781283693712715060353901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177041711591616953413805201 132781283693712715060353901)
    ·
      refine ⟨49792981385142268147632713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132781283693712715060353901 49792981385142268147632713)
      ·
        refine ⟨37344736038856701110724535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49792981385142268147632713 37344736038856701110724535)
        ·
          refine ⟨56017104058285051666086803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37344736038856701110724535 56017104058285051666086803)
          ·
            refine ⟨84025656087427577499130205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56017104058285051666086803 84025656087427577499130205)
            ·
              refine ⟨31509621032785341562173827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84025656087427577499130205 31509621032785341562173827)
              ·
                refine ⟨47264431549178012343260741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31509621032785341562173827 47264431549178012343260741)
                ·
                  refine ⟨8862080915470877314361389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47264431549178012343260741 8862080915470877314361389)
                  ·
                    refine ⟨3323280343301578992885521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8862080915470877314361389 3323280343301578992885521)
                    ·
                      refine ⟨2492460257476184244664141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3323280343301578992885521 2492460257476184244664141)
                      ·
                        rfl

theorem cell23_4854049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_4854049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854049 prefixEnd_4854049 := by exact prefixLift 4854049
  have htrace : WordTrace (prefixWord ++ tailWord_4854049) baseStart_4854049 baseEnd_4854049 := by
    simpa [prefixWord, tailWord_4854049, baseEnd_4854049] using wordTrace_append hprefix tailTrace_4854049
  have hstable : (prefixWord ++ tailWord_4854049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854049).length < 2 ^ (prefixWord ++ tailWord_4854049).sum := by decide
  have hdescent : baseEnd_4854049 < baseStart_4854049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854096 : List Nat := [2, 1, 1, 1, 1, 7, 3, 1, 1, 1, 4]
def baseStart_4854096 : Nat := 118140960795 + 4854096 * 2 ^ 59
def prefixEnd_4854096 : Nat := 4983230072969 + 3 ^ 40 * 4854096 * 2
def baseEnd_4854096 : Nat := 2492484391066945560776425

theorem tailTrace_4854096 : CollatzResearch.WordTrace tailWord_4854096 prefixEnd_4854096 2492484391066945560776425 := by
  unfold tailWord_4854096
  simp only [CollatzResearch.WordTrace]
  refine ⟨88521712911223340220383071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118028950548297786960510761 88521712911223340220383071)
  ·
    refine ⟨132782569366835010330574607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88521712911223340220383071 132782569366835010330574607)
    ·
      refine ⟨199173854050252515495861911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132782569366835010330574607 199173854050252515495861911)
      ·
        refine ⟨298760781075378773243792867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199173854050252515495861911 298760781075378773243792867)
        ·
          refine ⟨448141171613068159865689301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298760781075378773243792867 448141171613068159865689301)
          ·
            refine ⟨10503308709681284996852093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 448141171613068159865689301 10503308709681284996852093)
            ·
              refine ⟨3938740766130481873819535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10503308709681284996852093 3938740766130481873819535)
              ·
                refine ⟨5908111149195722810729303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3938740766130481873819535 5908111149195722810729303)
                ·
                  refine ⟨8862166723793584216093955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5908111149195722810729303 8862166723793584216093955)
                  ·
                    refine ⟨13293250085690376324140933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8862166723793584216093955 13293250085690376324140933)
                    ·
                      refine ⟨2492484391066945560776425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13293250085690376324140933 2492484391066945560776425)
                      ·
                        rfl

theorem cell23_4854096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 1, 1, 4].length) (baseStart_4854096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854096 prefixEnd_4854096 := by exact prefixLift 4854096
  have htrace : WordTrace (prefixWord ++ tailWord_4854096) baseStart_4854096 baseEnd_4854096 := by
    simpa [prefixWord, tailWord_4854096, baseEnd_4854096] using wordTrace_append hprefix tailTrace_4854096
  have hstable : (prefixWord ++ tailWord_4854096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854096).length < 2 ^ (prefixWord ++ tailWord_4854096).sum := by decide
  have hdescent : baseEnd_4854096 < baseStart_4854096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854119 : List Nat := [1, 1, 5, 1, 3, 3, 1, 8]
def baseStart_4854119 : Nat := 118140960795 + 4854119 * 2 ^ 59
def prefixEnd_4854119 : Nat := 4983230072969 + 3 ^ 40 * 4854119 * 2
def baseEnd_4854119 : Nat := 92314674115629591510697

theorem tailTrace_4854119 : CollatzResearch.WordTrace tailWord_4854119 prefixEnd_4854119 92314674115629591510697 := by
  unfold tailWord_4854119
  simp only [CollatzResearch.WordTrace]
  refine ⟨177044264701363355368853411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118029509800908903579235607 177044264701363355368853411)
  ·
    refine ⟨265566397052045033053280117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177044264701363355368853411 265566397052045033053280117)
    ·
      refine ⟨24896849723629221848745011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 265566397052045033053280117 24896849723629221848745011)
      ·
        refine ⟨37345274585443832773117517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24896849723629221848745011 37345274585443832773117517)
        ·
          refine ⟨14004477969541437289919069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37345274585443832773117517 14004477969541437289919069)
          ·
            refine ⟨5251679238578038983719651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14004477969541437289919069 5251679238578038983719651)
            ·
              refine ⟨7877518857867058475579477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5251679238578038983719651 7877518857867058475579477)
              ·
                refine ⟨92314674115629591510697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7877518857867058475579477 92314674115629591510697)
                ·
                  rfl

theorem cell23_4854119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 8].length) (baseStart_4854119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854119 prefixEnd_4854119 := by exact prefixLift 4854119
  have htrace : WordTrace (prefixWord ++ tailWord_4854119) baseStart_4854119 baseEnd_4854119 := by
    simpa [prefixWord, tailWord_4854119, baseEnd_4854119] using wordTrace_append hprefix tailTrace_4854119
  have hstable : (prefixWord ++ tailWord_4854119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854119).length < 2 ^ (prefixWord ++ tailWord_4854119).sum := by decide
  have hdescent : baseEnd_4854119 < baseStart_4854119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854129 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 6, 1, 3]
def baseStart_4854129 : Nat := 118140960795 + 4854129 * 2 ^ 59
def prefixEnd_4854129 : Nat := 4983230072969 + 3 ^ 40 * 4854129 * 2
def baseEnd_4854129 : Nat := 2492501335928543931663773

theorem tailTrace_4854129 : CollatzResearch.WordTrace tailWord_4854129 prefixEnd_4854129 2492501335928543931663773 := by
  unfold tailWord_4854129
  simp only [CollatzResearch.WordTrace]
  refine ⟨177044629431327127076717441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118029752954218084717811627 177044629431327127076717441)
  ·
    refine ⟨132783472073495345307538081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177044629431327127076717441 132783472073495345307538081)
    ·
      refine ⟨99587604055121508980653561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132783472073495345307538081 99587604055121508980653561)
      ·
        refine ⟨74690703041341131735490171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99587604055121508980653561 74690703041341131735490171)
        ·
          refine ⟨112036054562011697603235257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74690703041341131735490171 112036054562011697603235257)
          ·
            refine ⟨84027040921508773202426443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112036054562011697603235257 84027040921508773202426443)
            ·
              refine ⟨126040561382263159803639665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84027040921508773202426443 126040561382263159803639665)
              ·
                refine ⟨94530421036697369852729749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126040561382263159803639665 94530421036697369852729749)
                ·
                  refine ⟨4431113486095189211846707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94530421036697369852729749 4431113486095189211846707)
                  ·
                    refine ⟨6646670229142783817770061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4431113486095189211846707 6646670229142783817770061)
                    ·
                      refine ⟨2492501335928543931663773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6646670229142783817770061 2492501335928543931663773)
                      ·
                        rfl

theorem cell23_4854129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_4854129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854129 prefixEnd_4854129 := by exact prefixLift 4854129
  have htrace : WordTrace (prefixWord ++ tailWord_4854129) baseStart_4854129 baseEnd_4854129 := by
    simpa [prefixWord, tailWord_4854129, baseEnd_4854129] using wordTrace_append hprefix tailTrace_4854129
  have hstable : (prefixWord ++ tailWord_4854129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854129).length < 2 ^ (prefixWord ++ tailWord_4854129).sum := by decide
  have hdescent : baseEnd_4854129 < baseStart_4854129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854333 : List Nat := [1, 4, 1, 3, 2, 3, 1, 2, 6]
def baseStart_4854333 : Nat := 118140960795 + 4854333 * 2 ^ 59
def prefixEnd_4854333 : Nat := 4983230072969 + 3 ^ 40 * 4854333 * 2
def baseEnd_4854333 : Nat := 276956231775784570390315

theorem tailTrace_4854333 : CollatzResearch.WordTrace tailWord_4854333 prefixEnd_4854333 276956231775784570390315 := by
  unfold tailWord_4854333
  simp only [CollatzResearch.WordTrace]
  refine ⟨177052069922588069917143653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118034713281725379944762435 177052069922588069917143653)
  ·
    refine ⟨33197263110485263109464435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177052069922588069917143653 33197263110485263109464435)
    ·
      refine ⟨49795894665727894664196653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33197263110485263109464435 49795894665727894664196653)
      ·
        refine ⟨18673460499647960499073745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49795894665727894664196653 18673460499647960499073745)
        ·
          refine ⟨14005095374735970374305309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18673460499647960499073745 14005095374735970374305309)
          ·
            refine ⟨5251910765525988890364491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14005095374735970374305309 5251910765525988890364491)
            ·
              refine ⟨7877866148288983335546737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5251910765525988890364491 7877866148288983335546737)
              ·
                refine ⟨5908399611216737501660053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7877866148288983335546737 5908399611216737501660053)
                ·
                  refine ⟨276956231775784570390315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5908399611216737501660053 276956231775784570390315)
                  ·
                    rfl

theorem cell23_4854333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_4854333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854333 prefixEnd_4854333 := by exact prefixLift 4854333
  have htrace : WordTrace (prefixWord ++ tailWord_4854333) baseStart_4854333 baseEnd_4854333 := by
    simpa [prefixWord, tailWord_4854333, baseEnd_4854333] using wordTrace_append hprefix tailTrace_4854333
  have hstable : (prefixWord ++ tailWord_4854333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854333).length < 2 ^ (prefixWord ++ tailWord_4854333).sum := by decide
  have hdescent : baseEnd_4854333 < baseStart_4854333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854343 : List Nat := [1, 1, 4, 1, 4, 1, 1, 3, 3, 1, 3]
def baseStart_4854343 : Nat := 118140960795 + 4854343 * 2 ^ 59
def prefixEnd_4854343 : Nat := 4983230072969 + 3 ^ 40 * 4854343 * 2
def baseEnd_4854343 : Nat := 2492611220788606094387789

theorem tailTrace_4854343 : CollatzResearch.WordTrace tailWord_4854343 prefixEnd_4854343 2492611220788606094387789 := by
  unfold tailWord_4854343
  simp only [CollatzResearch.WordTrace]
  refine ⟨177052434652551841625007683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118034956435034561083338455 177052434652551841625007683)
  ·
    refine ⟨265578651978827762437511525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177052434652551841625007683 265578651978827762437511525)
    ·
      refine ⟨49795997246030205457033411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 265578651978827762437511525 49795997246030205457033411)
      ·
        refine ⟨74693995869045308185550117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49795997246030205457033411 74693995869045308185550117)
        ·
          refine ⟨14005124225445995284790647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74693995869045308185550117 14005124225445995284790647)
          ·
            refine ⟨21007686338168992927185971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14005124225445995284790647 21007686338168992927185971)
            ·
              refine ⟨31511529507253489390778957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21007686338168992927185971 31511529507253489390778957)
              ·
                refine ⟨11816823565220058521542109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31511529507253489390778957 11816823565220058521542109)
                ·
                  refine ⟨4431308836957521945578291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11816823565220058521542109 4431308836957521945578291)
                  ·
                    refine ⟨6646963255436282918367437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4431308836957521945578291 6646963255436282918367437)
                    ·
                      refine ⟨2492611220788606094387789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6646963255436282918367437 2492611220788606094387789)
                      ·
                        rfl

theorem cell23_4854343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_4854343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854343 prefixEnd_4854343 := by exact prefixLift 4854343
  have htrace : WordTrace (prefixWord ++ tailWord_4854343) baseStart_4854343 baseEnd_4854343 := by
    simpa [prefixWord, tailWord_4854343, baseEnd_4854343] using wordTrace_append hprefix tailTrace_4854343
  have hstable : (prefixWord ++ tailWord_4854343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854343).length < 2 ^ (prefixWord ++ tailWord_4854343).sum := by decide
  have hdescent : baseEnd_4854343 < baseStart_4854343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854383 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 5, 2, 2]
def baseStart_4854383 : Nat := 118140960795 + 4854383 * 2 ^ 59
def prefixEnd_4854383 : Nat := 4983230072969 + 3 ^ 40 * 4854383 * 2
def baseEnd_4854383 : Nat := 2492631760014785937887605

theorem tailTrace_4854383 : CollatzResearch.WordTrace tailWord_4854383 prefixEnd_4854383 2492631760014785937887605 := by
  unfold tailWord_4854383
  simp only [CollatzResearch.WordTrace]
  refine ⟨177053893572406928456463803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118035929048271285637642535 177053893572406928456463803)
  ·
    refine ⟨265580840358610392684695705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177053893572406928456463803 265580840358610392684695705)
    ·
      refine ⟨199185630268957794513521779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265580840358610392684695705 199185630268957794513521779)
      ·
        refine ⟨298778445403436691770282669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199185630268957794513521779 298778445403436691770282669)
        ·
          refine ⟨112041917026288759413856001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 298778445403436691770282669 112041917026288759413856001)
          ·
            refine ⟨84031437769716569560392001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112041917026288759413856001 84031437769716569560392001)
            ·
              refine ⟨63023578327287427170294001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84031437769716569560392001 63023578327287427170294001)
              ·
                refine ⟨47267683745465570377720501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63023578327287427170294001 47267683745465570377720501)
                ·
                  refine ⟨4431345351137397222911297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47267683745465570377720501 4431345351137397222911297)
                  ·
                    refine ⟨3323509013353047917183473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4431345351137397222911297 3323509013353047917183473)
                    ·
                      refine ⟨2492631760014785937887605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3323509013353047917183473 2492631760014785937887605)
                      ·
                        rfl

theorem cell23_4854383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 2, 2].length) (baseStart_4854383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854383 prefixEnd_4854383 := by exact prefixLift 4854383
  have htrace : WordTrace (prefixWord ++ tailWord_4854383) baseStart_4854383 baseEnd_4854383 := by
    simpa [prefixWord, tailWord_4854383, baseEnd_4854383] using wordTrace_append hprefix tailTrace_4854383
  have hstable : (prefixWord ++ tailWord_4854383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854383).length < 2 ^ (prefixWord ++ tailWord_4854383).sum := by decide
  have hdescent : baseEnd_4854383 < baseStart_4854383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854400 : List Nat := [2, 1, 1, 2, 1, 5, 3, 1, 3, 2, 2]
def baseStart_4854400 : Nat := 118140960795 + 4854400 * 2 ^ 59
def prefixEnd_4854400 : Nat := 4983230072969 + 3 ^ 40 * 4854400 * 2
def baseEnd_4854400 : Nat := 2492640489185912371375027

theorem tailTrace_4854400 : CollatzResearch.WordTrace tailWord_4854400 prefixEnd_4854400 2492640489185912371375027 := by
  unfold tailWord_4854400
  simp only [CollatzResearch.WordTrace]
  refine ⟨88527256806672670179916327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118036342408896893573221769 88527256806672670179916327)
  ·
    refine ⟨132790885210009005269874491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88527256806672670179916327 132790885210009005269874491)
    ·
      refine ⟨199186327815013507904811737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132790885210009005269874491 199186327815013507904811737)
      ·
        refine ⟨149389745861260130928608803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199186327815013507904811737 149389745861260130928608803)
        ·
          refine ⟨224084618791890196392913205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149389745861260130928608803 224084618791890196392913205)
          ·
            refine ⟨21007933011739705911835613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 224084618791890196392913205 21007933011739705911835613)
            ·
              refine ⟨7877974879402389716938355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21007933011739705911835613 7877974879402389716938355)
              ·
                refine ⟨11816962319103584575407533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7877974879402389716938355 11816962319103584575407533)
                ·
                  refine ⟨4431360869663844215777825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11816962319103584575407533 4431360869663844215777825)
                  ·
                    refine ⟨3323520652247883161833369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4431360869663844215777825 3323520652247883161833369)
                    ·
                      refine ⟨2492640489185912371375027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3323520652247883161833369 2492640489185912371375027)
                      ·
                        rfl

theorem cell23_4854400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 3, 2, 2].length) (baseStart_4854400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854400 prefixEnd_4854400 := by exact prefixLift 4854400
  have htrace : WordTrace (prefixWord ++ tailWord_4854400) baseStart_4854400 baseEnd_4854400 := by
    simpa [prefixWord, tailWord_4854400, baseEnd_4854400] using wordTrace_append hprefix tailTrace_4854400
  have hstable : (prefixWord ++ tailWord_4854400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854400).length < 2 ^ (prefixWord ++ tailWord_4854400).sum := by decide
  have hdescent : baseEnd_4854400 < baseStart_4854400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854409 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 1, 4, 6]
def baseStart_4854409 : Nat := 118140960795 + 4854409 * 2 ^ 59
def prefixEnd_4854409 : Nat := 4983230072969 + 3 ^ 40 * 4854409 * 2
def baseEnd_4854409 : Nat := 2492645110511802836162485

theorem tailTrace_4854409 : CollatzResearch.WordTrace tailWord_4854409 prefixEnd_4854409 2492645110511802836162485 := by
  unfold tailWord_4854409
  simp only [CollatzResearch.WordTrace]
  refine ⟨177054841870312734896910281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118036561246875156597940187 177054841870312734896910281)
  ·
    refine ⟨132791131402734551172682711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177054841870312734896910281 132791131402734551172682711)
    ·
      refine ⟨199186697104101826759024067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132791131402734551172682711 199186697104101826759024067)
      ·
        refine ⟨298780045656152740138536101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199186697104101826759024067 298780045656152740138536101)
        ·
          refine ⟨56021258560528638775975519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 298780045656152740138536101 56021258560528638775975519)
          ·
            refine ⟨84031887840792958163963279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56021258560528638775975519 84031887840792958163963279)
            ·
              refine ⟨126047831761189437245944919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84031887840792958163963279 126047831761189437245944919)
              ·
                refine ⟨189071747641784155868917379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126047831761189437245944919 189071747641784155868917379)
                ·
                  refine ⟨283607621462676233803376069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189071747641784155868917379 283607621462676233803376069)
                  ·
                    refine ⟨53176429024251793838133013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 283607621462676233803376069 53176429024251793838133013)
                    ·
                      refine ⟨2492645110511802836162485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53176429024251793838133013 2492645110511802836162485)
                      ·
                        rfl

theorem cell23_4854409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_4854409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854409 prefixEnd_4854409 := by exact prefixLift 4854409
  have htrace : WordTrace (prefixWord ++ tailWord_4854409) baseStart_4854409 baseEnd_4854409 := by
    simpa [prefixWord, tailWord_4854409, baseEnd_4854409] using wordTrace_append hprefix tailTrace_4854409
  have hstable : (prefixWord ++ tailWord_4854409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854409).length < 2 ^ (prefixWord ++ tailWord_4854409).sum := by decide
  have hdescent : baseEnd_4854409 < baseStart_4854409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854410 : List Nat := [3, 1, 2, 3, 3, 1, 1, 3, 2, 4]
def baseStart_4854410 : Nat := 118140960795 + 4854410 * 2 ^ 59
def prefixEnd_4854410 : Nat := 4983230072969 + 3 ^ 40 * 4854410 * 2
def baseEnd_4854410 : Nat := 830881874664152444083327

theorem tailTrace_4854410 : CollatzResearch.WordTrace tailWord_4854410 prefixEnd_4854410 830881874664152444083327 := by
  unfold tailWord_4854410
  simp only [CollatzResearch.WordTrace]
  refine ⟨44263719585827278016924171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118036585562206074711797789 44263719585827278016924171)
  ·
    refine ⟨66395579378740917025386257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44263719585827278016924171 66395579378740917025386257)
    ·
      refine ⟨49796684534055687769039693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66395579378740917025386257 49796684534055687769039693)
      ·
        refine ⟨18673756700270882913389885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49796684534055687769039693 18673756700270882913389885)
        ·
          refine ⟨7002658762601581092521207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18673756700270882913389885 7002658762601581092521207)
          ·
            refine ⟨10503988143902371638781811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7002658762601581092521207 10503988143902371638781811)
            ·
              refine ⟨15755982215853557458172717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10503988143902371638781811 15755982215853557458172717)
              ·
                refine ⟨5908493330945084046814769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15755982215853557458172717 5908493330945084046814769)
                ·
                  refine ⟨4431369998208813035111077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5908493330945084046814769 4431369998208813035111077)
                  ·
                    refine ⟨830881874664152444083327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4431369998208813035111077 830881874664152444083327)
                    ·
                      rfl

theorem cell23_4854410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_4854410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854410 prefixEnd_4854410 := by exact prefixLift 4854410
  have htrace : WordTrace (prefixWord ++ tailWord_4854410) baseStart_4854410 baseEnd_4854410 := by
    simpa [prefixWord, tailWord_4854410, baseEnd_4854410] using wordTrace_append hprefix tailTrace_4854410
  have hstable : (prefixWord ++ tailWord_4854410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854410).length < 2 ^ (prefixWord ++ tailWord_4854410).sum := by decide
  have hdescent : baseEnd_4854410 < baseStart_4854410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854419 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 2, 7]
def baseStart_4854419 : Nat := 118140960795 + 4854419 * 2 ^ 59
def prefixEnd_4854419 : Nat := 4983230072969 + 3 ^ 40 * 4854419 * 2
def baseEnd_4854419 : Nat := 830883415106115932345813

theorem tailTrace_4854419 : CollatzResearch.WordTrace tailWord_4854419 prefixEnd_4854419 830883415106115932345813 := by
  unfold tailWord_4854419
  simp only [CollatzResearch.WordTrace]
  refine ⟨177055206600276506604774311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118036804400184337736516207 177055206600276506604774311)
  ·
    refine ⟨265582809900414759907161467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177055206600276506604774311 265582809900414759907161467)
    ·
      refine ⟨398374214850622139860742201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265582809900414759907161467 398374214850622139860742201)
      ·
        refine ⟨298780661137966604895556651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 398374214850622139860742201 298780661137966604895556651)
        ·
          refine ⟨448170991706949907343334977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298780661137966604895556651 448170991706949907343334977)
          ·
            refine ⟨336128243780212430507501233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 448170991706949907343334977 336128243780212430507501233)
            ·
              refine ⟨252096182835159322880625925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 336128243780212430507501233 252096182835159322880625925)
              ·
                refine ⟨47268034281592373040117361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 252096182835159322880625925 47268034281592373040117361)
                ·
                  refine ⟨35451025711194279780088021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47268034281592373040117361 35451025711194279780088021)
                  ·
                    refine ⟨830883415106115932345813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35451025711194279780088021 830883415106115932345813)
                    ·
                      rfl

theorem cell23_4854419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 7].length) (baseStart_4854419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854419 prefixEnd_4854419 := by exact prefixLift 4854419
  have htrace : WordTrace (prefixWord ++ tailWord_4854419) baseStart_4854419 baseEnd_4854419 := by
    simpa [prefixWord, tailWord_4854419, baseEnd_4854419] using wordTrace_append hprefix tailTrace_4854419
  have hstable : (prefixWord ++ tailWord_4854419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854419).length < 2 ^ (prefixWord ++ tailWord_4854419).sum := by decide
  have hdescent : baseEnd_4854419 < baseStart_4854419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854420 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_4854420 : Nat := 118140960795 + 4854420 * 2 ^ 59
def prefixEnd_4854420 : Nat := 4983230072969 + 3 ^ 40 * 4854420 * 2
def baseEnd_4854420 : Nat := 2492650758799002293124935

theorem tailTrace_4854420 : CollatzResearch.WordTrace tailWord_4854420 prefixEnd_4854420 2492650758799002293124935 := by
  unfold tailWord_4854420
  simp only [CollatzResearch.WordTrace]
  refine ⟨88527621536636441887780357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118036828715515255850373809 88527621536636441887780357)
  ·
    refine ⟨16598929038119332853958817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88527621536636441887780357 16598929038119332853958817)
    ·
      refine ⟨12449196778589499640469113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16598929038119332853958817 12449196778589499640469113)
      ·
        refine ⟨9336897583942124730351835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12449196778589499640469113 9336897583942124730351835)
        ·
          refine ⟨14005346375913187095527753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9336897583942124730351835 14005346375913187095527753)
          ·
            refine ⟨10504009781934890321645815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14005346375913187095527753 10504009781934890321645815)
            ·
              refine ⟨15756014672902335482468723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10504009781934890321645815 15756014672902335482468723)
              ·
                refine ⟨23634022009353503223703085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15756014672902335482468723 23634022009353503223703085)
                ·
                  refine ⟨8862758253507563708888657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23634022009353503223703085 8862758253507563708888657)
                  ·
                    refine ⟨6647068690130672781666493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8862758253507563708888657 6647068690130672781666493)
                    ·
                      refine ⟨2492650758799002293124935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6647068690130672781666493 2492650758799002293124935)
                      ·
                        rfl

theorem cell23_4854420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_4854420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854420 prefixEnd_4854420 := by exact prefixLift 4854420
  have htrace : WordTrace (prefixWord ++ tailWord_4854420) baseStart_4854420 baseEnd_4854420 := by
    simpa [prefixWord, tailWord_4854420, baseEnd_4854420] using wordTrace_append hprefix tailTrace_4854420
  have hstable : (prefixWord ++ tailWord_4854420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854420).length < 2 ^ (prefixWord ++ tailWord_4854420).sum := by decide
  have hdescent : baseEnd_4854420 < baseStart_4854420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854490 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2]
def baseStart_4854490 : Nat := 118140960795 + 4854490 * 2 ^ 59
def prefixEnd_4854490 : Nat := 4983230072969 + 3 ^ 40 * 4854490 * 2
def baseEnd_4854490 : Nat := 2492686702444817019249613

theorem tailTrace_4854490 : CollatzResearch.WordTrace tailWord_4854490 prefixEnd_4854490 2492686702444817019249613 := by
  unfold tailWord_4854490
  simp only [CollatzResearch.WordTrace]
  refine ⟨44264449045754821432652231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118038530788679523820405949 44264449045754821432652231)
  ·
    refine ⟨66396673568632232148978347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44264449045754821432652231 66396673568632232148978347)
    ·
      refine ⟨99595010352948348223467521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66396673568632232148978347 99595010352948348223467521)
      ·
        refine ⟨74696257764711261167600641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99595010352948348223467521 74696257764711261167600641)
        ·
          refine ⟨56022193323533445875700481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74696257764711261167600641 56022193323533445875700481)
          ·
            refine ⟨42016644992650084406775361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56022193323533445875700481 42016644992650084406775361)
            ·
              refine ⟨31512483744487563305081521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42016644992650084406775361 31512483744487563305081521)
              ·
                refine ⟨23634362808365672478811141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31512483744487563305081521 23634362808365672478811141)
                ·
                  refine ⟨4431443026568563589777089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23634362808365672478811141 4431443026568563589777089)
                  ·
                    refine ⟨3323582269926422692332817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4431443026568563589777089 3323582269926422692332817)
                    ·
                      refine ⟨2492686702444817019249613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3323582269926422692332817 2492686702444817019249613)
                      ·
                        rfl

theorem cell23_4854490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2].length) (baseStart_4854490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854490 prefixEnd_4854490 := by exact prefixLift 4854490
  have htrace : WordTrace (prefixWord ++ tailWord_4854490) baseStart_4854490 baseEnd_4854490 := by
    simpa [prefixWord, tailWord_4854490, baseEnd_4854490] using wordTrace_append hprefix tailTrace_4854490
  have hstable : (prefixWord ++ tailWord_4854490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854490).length < 2 ^ (prefixWord ++ tailWord_4854490).sum := by decide
  have hdescent : baseEnd_4854490 < baseStart_4854490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854513 : List Nat := [1, 2, 2, 2, 2, 2, 1, 6, 5]
def baseStart_4854513 : Nat := 118140960795 + 4854513 * 2 ^ 59
def prefixEnd_4854513 : Nat := 4983230072969 + 3 ^ 40 * 4854513 * 2
def baseEnd_4854513 : Nat := 276966501388874492140223

theorem tailTrace_4854513 : CollatzResearch.WordTrace tailWord_4854513 prefixEnd_4854513 276966501388874492140223 := by
  unfold tailWord_4854513
  simp only [CollatzResearch.WordTrace]
  refine ⟨177058635061935960658696193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118039090041290640439130795 177058635061935960658696193)
  ·
    refine ⟨132793976296451970494022145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177058635061935960658696193 132793976296451970494022145)
    ·
      refine ⟨99595482222338977870516609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132793976296451970494022145 99595482222338977870516609)
      ·
        refine ⟨74696611666754233402887457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99595482222338977870516609 74696611666754233402887457)
        ·
          refine ⟨56022458750065675052165593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74696611666754233402887457 56022458750065675052165593)
          ·
            refine ⟨42016844062549256289124195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56022458750065675052165593 42016844062549256289124195)
            ·
              refine ⟨63025266093823884433686293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42016844062549256289124195 63025266093823884433686293)
              ·
                refine ⟨2954309348147994582829045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63025266093823884433686293 2954309348147994582829045)
                ·
                  refine ⟨276966501388874492140223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2954309348147994582829045 276966501388874492140223)
                  ·
                    rfl

theorem cell23_4854513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 5].length) (baseStart_4854513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854513 prefixEnd_4854513 := by exact prefixLift 4854513
  have htrace : WordTrace (prefixWord ++ tailWord_4854513) baseStart_4854513 baseEnd_4854513 := by
    simpa [prefixWord, tailWord_4854513, baseEnd_4854513] using wordTrace_append hprefix tailTrace_4854513
  have hstable : (prefixWord ++ tailWord_4854513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854513).length < 2 ^ (prefixWord ++ tailWord_4854513).sum := by decide
  have hdescent : baseEnd_4854513 < baseStart_4854513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854524 : List Nat := [2, 2, 2, 1, 3, 3, 3, 1, 2, 2, 2]
def baseStart_4854524 : Nat := 118140960795 + 4854524 * 2 ^ 59
def prefixEnd_4854524 : Nat := 4983230072969 + 3 ^ 40 * 4854524 * 2
def baseEnd_4854524 : Nat := 2492704160787069886224457

theorem tailTrace_4854524 : CollatzResearch.WordTrace tailWord_4854524 prefixEnd_4854524 2492704160787069886224457 := by
  unfold tailWord_4854524
  simp only [CollatzResearch.WordTrace]
  refine ⟨88529518132448054768673313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118039357509930739691564417 88529518132448054768673313)
  ·
    refine ⟨66397138599336041076504985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88529518132448054768673313 66397138599336041076504985)
    ·
      refine ⟨49797853949502030807378739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66397138599336041076504985 49797853949502030807378739)
      ·
        refine ⟨74696780924253046211068109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49797853949502030807378739 74696780924253046211068109)
        ·
          refine ⟨28011292846594892329150541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74696780924253046211068109 28011292846594892329150541)
          ·
            refine ⟨10504234817473084623431453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28011292846594892329150541 10504234817473084623431453)
            ·
              refine ⟨3939088056552406733786795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10504234817473084623431453 3939088056552406733786795)
              ·
                refine ⟨5908632084828610100680193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3939088056552406733786795 5908632084828610100680193)
                ·
                  refine ⟨4431474063621457575510145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5908632084828610100680193 4431474063621457575510145)
                  ·
                    refine ⟨3323605547716093181632609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4431474063621457575510145 3323605547716093181632609)
                    ·
                      refine ⟨2492704160787069886224457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3323605547716093181632609 2492704160787069886224457)
                      ·
                        rfl

theorem cell23_4854524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 2, 2, 2].length) (baseStart_4854524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854524 prefixEnd_4854524 := by exact prefixLift 4854524
  have htrace : WordTrace (prefixWord ++ tailWord_4854524) baseStart_4854524 baseEnd_4854524 := by
    simpa [prefixWord, tailWord_4854524, baseEnd_4854524] using wordTrace_append hprefix tailTrace_4854524
  have hstable : (prefixWord ++ tailWord_4854524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854524).length < 2 ^ (prefixWord ++ tailWord_4854524).sum := by decide
  have hdescent : baseEnd_4854524 < baseStart_4854524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854533 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 2, 5, 2]
def baseStart_4854533 : Nat := 118140960795 + 4854533 * 2 ^ 59
def prefixEnd_4854533 : Nat := 4983230072969 + 3 ^ 40 * 4854533 * 2
def baseEnd_4854533 : Nat := 2492708782112960351011915

theorem tailTrace_4854533 : CollatzResearch.WordTrace tailWord_4854533 prefixEnd_4854533 2492708782112960351011915 := by
  unfold tailWord_4854533
  simp only [CollatzResearch.WordTrace]
  refine ⟨177059364521863504074424253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118039576347909002716282835 177059364521863504074424253)
  ·
    refine ⟨66397261695698814027909095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177059364521863504074424253 66397261695698814027909095)
    ·
      refine ⟨99595892543548221041863643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66397261695698814027909095 99595892543548221041863643)
      ·
        refine ⟨149393838815322331562795465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99595892543548221041863643 149393838815322331562795465)
        ·
          refine ⟨112045379111491748672096599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149393838815322331562795465 112045379111491748672096599)
          ·
            refine ⟨168068068667237623008144899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112045379111491748672096599 168068068667237623008144899)
            ·
              refine ⟨252102103000856434512217349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168068068667237623008144899 252102103000856434512217349)
              ·
                refine ⟨47269144312660581471040753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 252102103000856434512217349 47269144312660581471040753)
                ·
                  refine ⟨35451858234495436103280565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47269144312660581471040753 35451858234495436103280565)
                  ·
                    refine ⟨3323611709483947134682553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35451858234495436103280565 3323611709483947134682553)
                    ·
                      refine ⟨2492708782112960351011915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3323611709483947134682553 2492708782112960351011915)
                      ·
                        rfl

theorem cell23_4854533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 5, 2].length) (baseStart_4854533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854533 prefixEnd_4854533 := by exact prefixLift 4854533
  have htrace : WordTrace (prefixWord ++ tailWord_4854533) baseStart_4854533 baseEnd_4854533 := by
    simpa [prefixWord, tailWord_4854533, baseEnd_4854533] using wordTrace_append hprefix tailTrace_4854533
  have hstable : (prefixWord ++ tailWord_4854533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854533).length < 2 ^ (prefixWord ++ tailWord_4854533).sum := by decide
  have hdescent : baseEnd_4854533 < baseStart_4854533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854576 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 6]
def baseStart_4854576 : Nat := 118140960795 + 4854576 * 2 ^ 59
def prefixEnd_4854576 : Nat := 4983230072969 + 3 ^ 40 * 4854576 * 2
def baseEnd_4854576 : Nat := 2492730861781103682774217

theorem tailTrace_4854576 : CollatzResearch.WordTrace tailWord_4854576 prefixEnd_4854576 2492730861781103682774217 := by
  unfold tailWord_4854576
  simp only [CollatzResearch.WordTrace]
  refine ⟨88530466430353861209119791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118040621907138481612159721 88530466430353861209119791)
  ·
    refine ⟨132795699645530791813679687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88530466430353861209119791 132795699645530791813679687)
    ·
      refine ⟨199193549468296187720519531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132795699645530791813679687 199193549468296187720519531)
      ·
        refine ⟨298790324202444281580779297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199193549468296187720519531 298790324202444281580779297)
        ·
          refine ⟨224092743151833211185584473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298790324202444281580779297 224092743151833211185584473)
          ·
            refine ⟨168069557363874908389188355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224092743151833211185584473 168069557363874908389188355)
            ·
              refine ⟨252104336045812362583782533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168069557363874908389188355 252104336045812362583782533)
              ·
                refine ⟨47269563008589817984459225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 252104336045812362583782533 47269563008589817984459225)
                ·
                  refine ⟨35452172256442363488344419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47269563008589817984459225 35452172256442363488344419)
                  ·
                    refine ⟨53178258384663545232516629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35452172256442363488344419 53178258384663545232516629)
                    ·
                      refine ⟨2492730861781103682774217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53178258384663545232516629 2492730861781103682774217)
                      ·
                        rfl

theorem cell23_4854576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_4854576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854576 prefixEnd_4854576 := by exact prefixLift 4854576
  have htrace : WordTrace (prefixWord ++ tailWord_4854576) baseStart_4854576 baseEnd_4854576 := by
    simpa [prefixWord, tailWord_4854576, baseEnd_4854576] using wordTrace_append hprefix tailTrace_4854576
  have hstable : (prefixWord ++ tailWord_4854576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854576).length < 2 ^ (prefixWord ++ tailWord_4854576).sum := by decide
  have hdescent : baseEnd_4854576 < baseStart_4854576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854583 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 3]
def baseStart_4854583 : Nat := 118140960795 + 4854583 * 2 ^ 59
def prefixEnd_4854583 : Nat := 4983230072969 + 3 ^ 40 * 4854583 * 2
def baseEnd_4854583 : Nat := 2492734456145685155386685

theorem tailTrace_4854583 : CollatzResearch.WordTrace tailWord_4854583 prefixEnd_4854583 2492734456145685155386685 := by
  unfold tailWord_4854583
  simp only [CollatzResearch.WordTrace]
  refine ⟨177061188171682362613744403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118040792114454908409162935 177061188171682362613744403)
  ·
    refine ⟨265591782257523543920616605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177061188171682362613744403 265591782257523543920616605)
    ·
      refine ⟨99596918346571328970231227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265591782257523543920616605 99596918346571328970231227)
      ·
        refine ⟨149395377519856993455346841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99596918346571328970231227 149395377519856993455346841)
        ·
          refine ⟨112046533139892745091510131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149395377519856993455346841 112046533139892745091510131)
          ·
            refine ⟨168069799709839117637265197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112046533139892745091510131 168069799709839117637265197)
            ·
              refine ⟨63026174891189669113974449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168069799709839117637265197 63026174891189669113974449)
              ·
                refine ⟨47269631168392251835480837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63026174891189669113974449 47269631168392251835480837)
                ·
                  refine ⟨8863055844073547219152657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47269631168392251835480837 8863055844073547219152657)
                  ·
                    refine ⟨6647291883055160414364493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8863055844073547219152657 6647291883055160414364493)
                    ·
                      refine ⟨2492734456145685155386685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6647291883055160414364493 2492734456145685155386685)
                      ·
                        rfl

theorem cell23_4854583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 3].length) (baseStart_4854583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854583 prefixEnd_4854583 := by exact prefixLift 4854583
  have htrace : WordTrace (prefixWord ++ tailWord_4854583) baseStart_4854583 baseEnd_4854583 := by
    simpa [prefixWord, tailWord_4854583, baseEnd_4854583] using wordTrace_append hprefix tailTrace_4854583
  have hstable : (prefixWord ++ tailWord_4854583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854583).length < 2 ^ (prefixWord ++ tailWord_4854583).sum := by decide
  have hdescent : baseEnd_4854583 < baseStart_4854583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854600 : List Nat := [2, 1, 3, 1, 1, 3, 4, 1, 2, 2, 3]
def baseStart_4854600 : Nat := 118140960795 + 4854600 * 2 ^ 59
def prefixEnd_4854600 : Nat := 4983230072969 + 3 ^ 40 * 4854600 * 2
def baseEnd_4854600 : Nat := 2492743185316811588874107

theorem tailTrace_4854600 : CollatzResearch.WordTrace tailWord_4854600 prefixEnd_4854600 2492743185316811588874107 := by
  unfold tailWord_4854600
  simp only [CollatzResearch.WordTrace]
  refine ⟨88530904106310387258556627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118041205475080516344742169 88530904106310387258556627)
  ·
    refine ⟨132796356159465580887834941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88530904106310387258556627 132796356159465580887834941)
    ·
      refine ⟨49798633559799592832938103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132796356159465580887834941 49798633559799592832938103)
      ·
        refine ⟨74697950339699389249407155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49798633559799592832938103 74697950339699389249407155)
        ·
          refine ⟨112046925509549083874110733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74697950339699389249407155 112046925509549083874110733)
          ·
            refine ⟨42017597066080906452791525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112046925509549083874110733 42017597066080906452791525)
            ·
              refine ⟨7878299449890169959898411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42017597066080906452791525 7878299449890169959898411)
              ·
                refine ⟨11817449174835254939847617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7878299449890169959898411 11817449174835254939847617)
                ·
                  refine ⟨8863086881126441204885713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11817449174835254939847617 8863086881126441204885713)
                  ·
                    refine ⟨6647315160844830903664285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8863086881126441204885713 6647315160844830903664285)
                    ·
                      refine ⟨2492743185316811588874107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6647315160844830903664285 2492743185316811588874107)
                      ·
                        rfl

theorem cell23_4854600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_4854600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854600 prefixEnd_4854600 := by exact prefixLift 4854600
  have htrace : WordTrace (prefixWord ++ tailWord_4854600) baseStart_4854600 baseEnd_4854600 := by
    simpa [prefixWord, tailWord_4854600, baseEnd_4854600] using wordTrace_append hprefix tailTrace_4854600
  have hstable : (prefixWord ++ tailWord_4854600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854600).length < 2 ^ (prefixWord ++ tailWord_4854600).sum := by decide
  have hdescent : baseEnd_4854600 < baseStart_4854600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854620 : List Nat := [2, 2, 4, 2, 1, 1, 1, 4, 6]
def baseStart_4854620 : Nat := 118140960795 + 4854620 * 2 ^ 59
def prefixEnd_4854620 : Nat := 4983230072969 + 3 ^ 40 * 4854620 * 2
def baseEnd_4854620 : Nat := 276972606103322390069335

theorem tailTrace_4854620 : CollatzResearch.WordTrace tailWord_4854620 prefixEnd_4854620 276972606103322390069335 := by
  unfold tailWord_4854620
  simp only [CollatzResearch.WordTrace]
  refine ⟨88531268836274158966420657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118041691781698878621894209 88531268836274158966420657)
  ·
    refine ⟨66398451627205619224815493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88531268836274158966420657 66398451627205619224815493)
    ·
      refine ⟨12449709680101053604652905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66398451627205619224815493 12449709680101053604652905)
      ·
        refine ⟨9337282260075790203489679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12449709680101053604652905 9337282260075790203489679)
        ·
          refine ⟨14005923390113685305234519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9337282260075790203489679 14005923390113685305234519)
          ·
            refine ⟨21008885085170527957851779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14005923390113685305234519 21008885085170527957851779)
            ·
              refine ⟨31513327627755791936777669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21008885085170527957851779 31513327627755791936777669)
              ·
                refine ⟨5908748930204210988145813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31513327627755791936777669 5908748930204210988145813)
                ·
                  refine ⟨276972606103322390069335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5908748930204210988145813 276972606103322390069335)
                  ·
                    rfl

theorem cell23_4854620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 6].length) (baseStart_4854620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854620 prefixEnd_4854620 := by exact prefixLift 4854620
  have htrace : WordTrace (prefixWord ++ tailWord_4854620) baseStart_4854620 baseEnd_4854620 := by
    simpa [prefixWord, tailWord_4854620, baseEnd_4854620] using wordTrace_append hprefix tailTrace_4854620
  have hstable : (prefixWord ++ tailWord_4854620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854620).length < 2 ^ (prefixWord ++ tailWord_4854620).sum := by decide
  have hdescent : baseEnd_4854620 < baseStart_4854620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854640 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 4, 3, 2]
def baseStart_4854640 : Nat := 118140960795 + 4854640 * 2 ^ 59
def prefixEnd_4854640 : Nat := 4983230072969 + 3 ^ 40 * 4854640 * 2
def baseEnd_4854640 : Nat := 2492763724542991432373923

theorem tailTrace_4854640 : CollatzResearch.WordTrace tailWord_4854640 prefixEnd_4854640 2492763724542991432373923 := by
  unfold tailWord_4854640
  simp only [CollatzResearch.WordTrace]
  refine ⟨88531633566237930674284687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118042178088317240899046249 88531633566237930674284687)
  ·
    refine ⟨132797450349356896011427031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88531633566237930674284687 132797450349356896011427031)
    ·
      refine ⟨199196175524035344017140547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132797450349356896011427031 199196175524035344017140547)
      ·
        refine ⟨298794263286053016025710821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199196175524035344017140547 298794263286053016025710821)
        ·
          refine ⟨56023924366134940504820779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 298794263286053016025710821 56023924366134940504820779)
          ·
            refine ⟨84035886549202410757231169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56023924366134940504820779 84035886549202410757231169)
            ·
              refine ⟨63026914911901808067923377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84035886549202410757231169 63026914911901808067923377)
              ·
                refine ⟨47270186183926356050942533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63026914911901808067923377 47270186183926356050942533)
                ·
                  refine ⟨8863159909486191759551725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47270186183926356050942533 8863159909486191759551725)
                  ·
                    refine ⟨3323684966057321909831897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8863159909486191759551725 3323684966057321909831897)
                    ·
                      refine ⟨2492763724542991432373923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3323684966057321909831897 2492763724542991432373923)
                      ·
                        rfl

theorem cell23_4854640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 4, 3, 2].length) (baseStart_4854640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854640 prefixEnd_4854640 := by exact prefixLift 4854640
  have htrace : WordTrace (prefixWord ++ tailWord_4854640) baseStart_4854640 baseEnd_4854640 := by
    simpa [prefixWord, tailWord_4854640, baseEnd_4854640] using wordTrace_append hprefix tailTrace_4854640
  have hstable : (prefixWord ++ tailWord_4854640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854640).length < 2 ^ (prefixWord ++ tailWord_4854640).sum := by decide
  have hdescent : baseEnd_4854640 < baseStart_4854640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854658 : List Nat := [3, 4, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_4854658 : Nat := 118140960795 + 4854658 * 2 ^ 59
def prefixEnd_4854658 : Nat := 4983230072969 + 3 ^ 40 * 4854658 * 2
def baseEnd_4854658 : Nat := 830924322398257453982947

theorem tailTrace_4854658 : CollatzResearch.WordTrace tailWord_4854658 prefixEnd_4854658 830924322398257453982947 := by
  unfold tailWord_4854658
  simp only [CollatzResearch.WordTrace]
  refine ⟨44265980911602662605681157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118042615764273766948483085 44265980911602662605681157)
  ·
    refine ⟨8299871420925499238565217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44265980911602662605681157 8299871420925499238565217)
    ·
      refine ⟨6224903565694124428923913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8299871420925499238565217 6224903565694124428923913)
      ·
        refine ⟨4668677674270593321692935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6224903565694124428923913 4668677674270593321692935)
        ·
          refine ⟨7003016511405889982539403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4668677674270593321692935 7003016511405889982539403)
          ·
            refine ⟨10504524767108834973809105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7003016511405889982539403 10504524767108834973809105)
            ·
              refine ⟨7878393575331626230356829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10504524767108834973809105 7878393575331626230356829)
              ·
                refine ⟨2954397590749359836383811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7878393575331626230356829 2954397590749359836383811)
                ·
                  refine ⟨4431596386124039754575717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2954397590749359836383811 4431596386124039754575717)
                  ·
                    refine ⟨830924322398257453982947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4431596386124039754575717 830924322398257453982947)
                    ·
                      rfl

theorem cell23_4854658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_4854658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854658 prefixEnd_4854658 := by exact prefixLift 4854658
  have htrace : WordTrace (prefixWord ++ tailWord_4854658) baseStart_4854658 baseEnd_4854658 := by
    simpa [prefixWord, tailWord_4854658, baseEnd_4854658] using wordTrace_append hprefix tailTrace_4854658
  have hstable : (prefixWord ++ tailWord_4854658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854658).length < 2 ^ (prefixWord ++ tailWord_4854658).sum := by decide
  have hdescent : baseEnd_4854658 < baseStart_4854658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854664 : List Nat := [2, 1, 3, 3, 2, 1, 1, 5, 1, 1, 3]
def baseStart_4854664 : Nat := 118140960795 + 4854664 * 2 ^ 59
def prefixEnd_4854664 : Nat := 4983230072969 + 3 ^ 40 * 4854664 * 2
def baseEnd_4854664 : Nat := 2492776048078699338473813

theorem tailTrace_4854664 : CollatzResearch.WordTrace tailWord_4854664 prefixEnd_4854664 2492776048078699338473813 := by
  unfold tailWord_4854664
  simp only [CollatzResearch.WordTrace]
  refine ⟨88532071242194456723721523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118042761656259275631628697 88532071242194456723721523)
  ·
    refine ⟨132798106863291685085582285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88532071242194456723721523 132798106863291685085582285)
    ·
      refine ⟨49799290073734381907093357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132798106863291685085582285 49799290073734381907093357)
      ·
        refine ⟨18674733777650393215160009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49799290073734381907093357 18674733777650393215160009)
        ·
          refine ⟨14006050333237794911370007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18674733777650393215160009 14006050333237794911370007)
          ·
            refine ⟨21009075499856692367055011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14006050333237794911370007 21009075499856692367055011)
            ·
              refine ⟨31513613249785038550582517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21009075499856692367055011 31513613249785038550582517)
              ·
                refine ⟨2954401242167347364117111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31513613249785038550582517 2954401242167347364117111)
                ·
                  refine ⟨4431601863251021046175667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2954401242167347364117111 4431601863251021046175667)
                  ·
                    refine ⟨6647402794876531569263501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4431601863251021046175667 6647402794876531569263501)
                    ·
                      refine ⟨2492776048078699338473813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6647402794876531569263501 2492776048078699338473813)
                      ·
                        rfl

theorem cell23_4854664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_4854664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854664 prefixEnd_4854664 := by exact prefixLift 4854664
  have htrace : WordTrace (prefixWord ++ tailWord_4854664) baseStart_4854664 baseEnd_4854664 := by
    simpa [prefixWord, tailWord_4854664, baseEnd_4854664] using wordTrace_append hprefix tailTrace_4854664
  have hstable : (prefixWord ++ tailWord_4854664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854664).length < 2 ^ (prefixWord ++ tailWord_4854664).sum := by decide
  have hdescent : baseEnd_4854664 < baseStart_4854664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854673 : List Nat := [1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 5]
def baseStart_4854673 : Nat := 118140960795 + 4854673 * 2 ^ 59
def prefixEnd_4854673 : Nat := 4983230072969 + 3 ^ 40 * 4854673 * 2
def baseEnd_4854673 : Nat := 2492780669404589803261271

theorem tailTrace_4854673 : CollatzResearch.WordTrace tailWord_4854673 prefixEnd_4854673 2492780669404589803261271 := by
  unfold tailWord_4854673
  simp only [CollatzResearch.WordTrace]
  refine ⟨177064470741356307984520673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118042980494237538656347115 177064470741356307984520673)
  ·
    refine ⟨132798353056017230988390505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177064470741356307984520673 132798353056017230988390505)
    ·
      refine ⟨99598764792012923241292879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132798353056017230988390505 99598764792012923241292879)
      ·
        refine ⟨149398147188019384861939319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99598764792012923241292879 149398147188019384861939319)
        ·
          refine ⟨224097220782029077292908979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149398147188019384861939319 224097220782029077292908979)
          ·
            refine ⟨336145831173043615939363469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224097220782029077292908979 336145831173043615939363469)
            ·
              refine ⟨126054686689891355977261301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 336145831173043615939363469 126054686689891355977261301)
              ·
                refine ⟨11817626877177314622868247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126054686689891355977261301 11817626877177314622868247)
                ·
                  refine ⟨17726440315765971934302371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11817626877177314622868247 17726440315765971934302371)
                  ·
                    refine ⟨26589660473648957901453557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17726440315765971934302371 26589660473648957901453557)
                    ·
                      refine ⟨2492780669404589803261271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26589660473648957901453557 2492780669404589803261271)
                      ·
                        rfl

theorem cell23_4854673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_4854673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854673 prefixEnd_4854673 := by exact prefixLift 4854673
  have htrace : WordTrace (prefixWord ++ tailWord_4854673) baseStart_4854673 baseEnd_4854673 := by
    simpa [prefixWord, tailWord_4854673, baseEnd_4854673] using wordTrace_append hprefix tailTrace_4854673
  have hstable : (prefixWord ++ tailWord_4854673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854673).length < 2 ^ (prefixWord ++ tailWord_4854673).sum := by decide
  have hdescent : baseEnd_4854673 < baseStart_4854673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854690 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_4854690 : Nat := 118140960795 + 4854690 * 2 ^ 59
def prefixEnd_4854690 : Nat := 4983230072969 + 3 ^ 40 * 4854690 * 2
def baseEnd_4854690 : Nat := 2492789398575716236748693

theorem tailTrace_4854690 : CollatzResearch.WordTrace tailWord_4854690 prefixEnd_4854690 2492789398575716236748693 := by
  unfold tailWord_4854690
  simp only [CollatzResearch.WordTrace]
  refine ⟨44266272695573679971972381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118043393854863146591926349 44266272695573679971972381)
  ·
    refine ⟨16599852260840129989489643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44266272695573679971972381 16599852260840129989489643)
    ·
      refine ⟨24899778391260194984234465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16599852260840129989489643 24899778391260194984234465)
      ·
        refine ⟨18674833793445146238175849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24899778391260194984234465 18674833793445146238175849)
        ·
          refine ⟨14006125345083859678631887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18674833793445146238175849 14006125345083859678631887)
          ·
            refine ⟨21009188017625789517947831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14006125345083859678631887 21009188017625789517947831)
            ·
              refine ⟨31513782026438684276921747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21009188017625789517947831 31513782026438684276921747)
              ·
                refine ⟨47270673039658026415382621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31513782026438684276921747 47270673039658026415382621)
                ·
                  refine ⟨17726502389871759905768483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47270673039658026415382621 17726502389871759905768483)
                  ·
                    refine ⟨26589753584807639858652725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17726502389871759905768483 26589753584807639858652725)
                    ·
                      refine ⟨2492789398575716236748693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26589753584807639858652725 2492789398575716236748693)
                      ·
                        rfl

theorem cell23_4854690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_4854690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854690 prefixEnd_4854690 := by exact prefixLift 4854690
  have htrace : WordTrace (prefixWord ++ tailWord_4854690) baseStart_4854690 baseEnd_4854690 := by
    simpa [prefixWord, tailWord_4854690, baseEnd_4854690] using wordTrace_append hprefix tailTrace_4854690
  have hstable : (prefixWord ++ tailWord_4854690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854690).length < 2 ^ (prefixWord ++ tailWord_4854690).sum := by decide
  have hdescent : baseEnd_4854690 < baseStart_4854690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854697 : List Nat := [1, 2, 1, 1, 1, 1, 9, 1, 2, 4]
def baseStart_4854697 : Nat := 118140960795 + 4854697 * 2 ^ 59
def prefixEnd_4854697 : Nat := 4983230072969 + 3 ^ 40 * 4854697 * 2
def baseEnd_4854697 : Nat := 830930997646765903120387

theorem tailTrace_4854697 : CollatzResearch.WordTrace tailWord_4854697 prefixEnd_4854697 830930997646765903120387 := by
  unfold tailWord_4854697
  simp only [CollatzResearch.WordTrace]
  refine ⟨177065346093269360083394345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118043564062179573388929563 177065346093269360083394345)
  ·
    refine ⟨132799009569952020062545759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177065346093269360083394345 132799009569952020062545759)
    ·
      refine ⟨199198514354928030093818639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132799009569952020062545759 199198514354928030093818639)
      ·
        refine ⟨298797771532392045140727959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199198514354928030093818639 298797771532392045140727959)
        ·
          refine ⟨448196657298588067711091939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298797771532392045140727959 448196657298588067711091939)
          ·
            refine ⟨672294985947882101566637909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448196657298588067711091939 672294985947882101566637909)
            ·
              refine ⟨3939228433288371688867019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 672294985947882101566637909 3939228433288371688867019)
              ·
                refine ⟨5908842649932557533300529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3939228433288371688867019 5908842649932557533300529)
                ·
                  refine ⟨4431631987449418149975397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5908842649932557533300529 4431631987449418149975397)
                  ·
                    refine ⟨830930997646765903120387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4431631987449418149975397 830930997646765903120387)
                    ·
                      rfl

theorem cell23_4854697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 2, 4].length) (baseStart_4854697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854697 prefixEnd_4854697 := by exact prefixLift 4854697
  have htrace : WordTrace (prefixWord ++ tailWord_4854697) baseStart_4854697 baseEnd_4854697 := by
    simpa [prefixWord, tailWord_4854697, baseEnd_4854697] using wordTrace_append hprefix tailTrace_4854697
  have hstable : (prefixWord ++ tailWord_4854697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854697).length < 2 ^ (prefixWord ++ tailWord_4854697).sum := by decide
  have hdescent : baseEnd_4854697 < baseStart_4854697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854724 : List Nat := [2, 3, 3, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_4854724 : Nat := 118140960795 + 4854724 * 2 ^ 59
def prefixEnd_4854724 : Nat := 4983230072969 + 3 ^ 40 * 4854724 * 2
def baseEnd_4854724 : Nat := 2492806856917969103723537

theorem tailTrace_4854724 : CollatzResearch.WordTrace tailWord_4854724 prefixEnd_4854724 2492806856917969103723537 := by
  unfold tailWord_4854724
  simp only [CollatzResearch.WordTrace]
  refine ⟨88533165432085771847313613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118044220576114362463084817 88533165432085771847313613)
  ·
    refine ⟨33199937037032164442742605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88533165432085771847313613 33199937037032164442742605)
    ·
      refine ⟨12449976388887061666028477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33199937037032164442742605 12449976388887061666028477)
      ·
        refine ⟨4668741145832648124760679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12449976388887061666028477 4668741145832648124760679)
        ·
          refine ⟨7003111718748972187141019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4668741145832648124760679 7003111718748972187141019)
          ·
            refine ⟨10504667578123458280711529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7003111718748972187141019 10504667578123458280711529)
            ·
              refine ⟨7878500683592593710533647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10504667578123458280711529 7878500683592593710533647)
              ·
                refine ⟨11817751025388890565800471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7878500683592593710533647 11817751025388890565800471)
                ·
                  refine ⟨17726626538083335848700707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11817751025388890565800471 17726626538083335848700707)
                  ·
                    refine ⟨26589939807125003773051061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17726626538083335848700707 26589939807125003773051061)
                    ·
                      refine ⟨2492806856917969103723537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26589939807125003773051061 2492806856917969103723537)
                      ·
                        rfl

theorem cell23_4854724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_4854724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854724 prefixEnd_4854724 := by exact prefixLift 4854724
  have htrace : WordTrace (prefixWord ++ tailWord_4854724) baseStart_4854724 baseEnd_4854724 := by
    simpa [prefixWord, tailWord_4854724, baseEnd_4854724] using wordTrace_append hprefix tailTrace_4854724
  have hstable : (prefixWord ++ tailWord_4854724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854724).length < 2 ^ (prefixWord ++ tailWord_4854724).sum := by decide
  have hdescent : baseEnd_4854724 < baseStart_4854724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854737 : List Nat := [1, 2, 2, 1, 2, 1, 4, 4, 2, 1, 3]
def baseStart_4854737 : Nat := 118140960795 + 4854737 * 2 ^ 59
def prefixEnd_4854737 : Nat := 4983230072969 + 3 ^ 40 * 4854737 * 2
def baseEnd_4854737 : Nat := 2492813532166477552860977

theorem tailTrace_4854737 : CollatzResearch.WordTrace tailWord_4854737 prefixEnd_4854737 2492813532166477552860977 := by
  unfold tailWord_4854737
  simp only [CollatzResearch.WordTrace]
  refine ⟨177066805013124446914850465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118044536675416297943233643 177066805013124446914850465)
  ·
    refine ⟨132800103759843335186137849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177066805013124446914850465 132800103759843335186137849)
    ·
      refine ⟨99600077819882501389603387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132800103759843335186137849 99600077819882501389603387)
      ·
        refine ⟨149400116729823752084405081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99600077819882501389603387 149400116729823752084405081)
        ·
          refine ⟨112050087547367814063303811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149400116729823752084405081 112050087547367814063303811)
          ·
            refine ⟨168075131321051721094955717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112050087547367814063303811 168075131321051721094955717)
            ·
              refine ⟨31514087122697197705304197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 168075131321051721094955717 31514087122697197705304197)
              ·
                refine ⟨5908891335505724569744537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31514087122697197705304197 5908891335505724569744537)
                ·
                  refine ⟨4431668501629293427308403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5908891335505724569744537 4431668501629293427308403)
                  ·
                    refine ⟨6647502752443940140962605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4431668501629293427308403 6647502752443940140962605)
                    ·
                      refine ⟨2492813532166477552860977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6647502752443940140962605 2492813532166477552860977)
                      ·
                        rfl

theorem cell23_4854737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 1, 3].length) (baseStart_4854737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854737 prefixEnd_4854737 := by exact prefixLift 4854737
  have htrace : WordTrace (prefixWord ++ tailWord_4854737) baseStart_4854737 baseEnd_4854737 := by
    simpa [prefixWord, tailWord_4854737, baseEnd_4854737] using wordTrace_append hprefix tailTrace_4854737
  have hstable : (prefixWord ++ tailWord_4854737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854737).length < 2 ^ (prefixWord ++ tailWord_4854737).sum := by decide
  have hdescent : baseEnd_4854737 < baseStart_4854737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854753 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 1, 8]
def baseStart_4854753 : Nat := 118140960795 + 4854753 * 2 ^ 59
def prefixEnd_4854753 : Nat := 4983230072969 + 3 ^ 40 * 4854753 * 2
def baseEnd_4854753 : Nat := 830940582618983163420301

theorem tailTrace_4854753 : CollatzResearch.WordTrace tailWord_4854753 prefixEnd_4854753 830940582618983163420301 := by
  unfold tailWord_4854753
  simp only [CollatzResearch.WordTrace]
  refine ⟨177067388581066481647432913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118044925720710987764955275 177067388581066481647432913)
  ·
    refine ⟨132800541435799861235574685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177067388581066481647432913 132800541435799861235574685)
    ·
      refine ⟨49800203038424947963340507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132800541435799861235574685 49800203038424947963340507)
      ·
        refine ⟨74700304557637421945010761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49800203038424947963340507 74700304557637421945010761)
        ·
          refine ⟨56025228418228066458758071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74700304557637421945010761 56025228418228066458758071)
          ·
            refine ⟨84037842627342099688137107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56025228418228066458758071 84037842627342099688137107)
            ·
              refine ⟨126056763941013149532205661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84037842627342099688137107 126056763941013149532205661)
              ·
                refine ⟨47271286477879931074577123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126056763941013149532205661 47271286477879931074577123)
                ·
                  refine ⟨70906929716819896611865685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47271286477879931074577123 70906929716819896611865685)
                  ·
                    refine ⟨830940582618983163420301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70906929716819896611865685 830940582618983163420301)
                    ·
                      rfl

theorem cell23_4854753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_4854753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854753 prefixEnd_4854753 := by exact prefixLift 4854753
  have htrace : WordTrace (prefixWord ++ tailWord_4854753) baseStart_4854753 baseEnd_4854753 := by
    simpa [prefixWord, tailWord_4854753, baseEnd_4854753] using wordTrace_append hprefix tailTrace_4854753
  have hstable : (prefixWord ++ tailWord_4854753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854753).length < 2 ^ (prefixWord ++ tailWord_4854753).sum := by decide
  have hdescent : baseEnd_4854753 < baseStart_4854753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854777 : List Nat := [1, 2, 1, 3, 1, 3, 3, 2, 1, 4, 2]
def baseStart_4854777 : Nat := 118140960795 + 4854777 * 2 ^ 59
def prefixEnd_4854777 : Nat := 4983230072969 + 3 ^ 40 * 4854777 * 2
def baseEnd_4854777 : Nat := 2492834071392657396360793

theorem tailTrace_4854777 : CollatzResearch.WordTrace tailWord_4854777 prefixEnd_4854777 2492834071392657396360793 := by
  unfold tailWord_4854777
  simp only [CollatzResearch.WordTrace]
  refine ⟨177068263932979533746306585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118045509288653022497537723 177068263932979533746306585)
  ·
    refine ⟨132801197949734650309729939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177068263932979533746306585 132801197949734650309729939)
    ·
      refine ⟨199201796924601975464594909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132801197949734650309729939 199201796924601975464594909)
      ·
        refine ⟨74700673846725740799223091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199201796924601975464594909 74700673846725740799223091)
        ·
          refine ⟨112051010770088611198834637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74700673846725740799223091 112051010770088611198834637)
          ·
            refine ⟨42019129038783229199562989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112051010770088611198834637 42019129038783229199562989)
            ·
              refine ⟨15757173389543710949836121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42019129038783229199562989 15757173389543710949836121)
              ·
                refine ⟨11817880042157783212377091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15757173389543710949836121 11817880042157783212377091)
                ·
                  refine ⟨17726820063236674818565637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11817880042157783212377091 17726820063236674818565637)
                  ·
                    refine ⟨3323778761856876528481057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17726820063236674818565637 3323778761856876528481057)
                    ·
                      refine ⟨2492834071392657396360793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3323778761856876528481057 2492834071392657396360793)
                      ·
                        rfl

theorem cell23_4854777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 4, 2].length) (baseStart_4854777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854777 prefixEnd_4854777 := by exact prefixLift 4854777
  have htrace : WordTrace (prefixWord ++ tailWord_4854777) baseStart_4854777 baseEnd_4854777 := by
    simpa [prefixWord, tailWord_4854777, baseEnd_4854777] using wordTrace_append hprefix tailTrace_4854777
  have hstable : (prefixWord ++ tailWord_4854777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854777).length < 2 ^ (prefixWord ++ tailWord_4854777).sum := by decide
  have hdescent : baseEnd_4854777 < baseStart_4854777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854780 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 2, 1, 5]
def baseStart_4854780 : Nat := 118140960795 + 4854780 * 2 ^ 59
def prefixEnd_4854780 : Nat := 4983230072969 + 3 ^ 40 * 4854780 * 2
def baseEnd_4854780 : Nat := 2492835611834620884623279

theorem tailTrace_4854780 : CollatzResearch.WordTrace tailWord_4854780 prefixEnd_4854780 2492835611834620884623279 := by
  unfold tailWord_4854780
  simp only [CollatzResearch.WordTrace]
  refine ⟨88534186675984332629332897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118045582234645776839110529 88534186675984332629332897)
  ·
    refine ⟨66400640006988249471999673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88534186675984332629332897 66400640006988249471999673)
    ·
      refine ⟨49800480005241187103999755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66400640006988249471999673 49800480005241187103999755)
      ·
        refine ⟨74700720007861780655999633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49800480005241187103999755 74700720007861780655999633)
        ·
          refine ⟨56025540005896335491999725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74700720007861780655999633 56025540005896335491999725)
          ·
            refine ⟨21009577502211125809499897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56025540005896335491999725 21009577502211125809499897)
            ·
              refine ⟨15757183126658344357124923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21009577502211125809499897 15757183126658344357124923)
              ·
                refine ⟨23635774689987516535687385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15757183126658344357124923 23635774689987516535687385)
                ·
                  refine ⟨17726831017490637401765539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23635774689987516535687385 17726831017490637401765539)
                  ·
                    refine ⟨26590246526235956102648309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17726831017490637401765539 26590246526235956102648309)
                    ·
                      refine ⟨2492835611834620884623279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26590246526235956102648309 2492835611834620884623279)
                      ·
                        rfl

theorem cell23_4854780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_4854780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854780 prefixEnd_4854780 := by exact prefixLift 4854780
  have htrace : WordTrace (prefixWord ++ tailWord_4854780) baseStart_4854780 baseEnd_4854780 := by
    simpa [prefixWord, tailWord_4854780, baseEnd_4854780] using wordTrace_append hprefix tailTrace_4854780
  have hstable : (prefixWord ++ tailWord_4854780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854780).length < 2 ^ (prefixWord ++ tailWord_4854780).sum := by decide
  have hdescent : baseEnd_4854780 < baseStart_4854780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854793 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 7]
def baseStart_4854793 : Nat := 118140960795 + 4854793 * 2 ^ 59
def prefixEnd_4854793 : Nat := 4983230072969 + 3 ^ 40 * 4854793 * 2
def baseEnd_4854793 : Nat := 2492842287083129333760719

theorem tailTrace_4854793 : CollatzResearch.WordTrace tailWord_4854793 prefixEnd_4854793 2492842287083129333760719 := by
  unfold tailWord_4854793
  simp only [CollatzResearch.WordTrace]
  refine ⟨177068847500921568478889033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118045898333947712319259355 177068847500921568478889033)
  ·
    refine ⟨132801635625691176359166775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177068847500921568478889033 132801635625691176359166775)
    ·
      refine ⟨199202453438536764538750163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132801635625691176359166775 199202453438536764538750163)
      ·
        refine ⟨298803680157805146808125245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199202453438536764538750163 298803680157805146808125245)
        ·
          refine ⟨112051380059176930053046967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 298803680157805146808125245 112051380059176930053046967)
          ·
            refine ⟨168077070088765395079570451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112051380059176930053046967 168077070088765395079570451)
            ·
              refine ⟨252115605133148092619355677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168077070088765395079570451 252115605133148092619355677)
              ·
                refine ⟨94543351924930534732258379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 252115605133148092619355677 94543351924930534732258379)
                ·
                  refine ⟨141815027887395802098387569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94543351924930534732258379 141815027887395802098387569)
                  ·
                    refine ⟨106361270915546851573790677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 141815027887395802098387569 106361270915546851573790677)
                    ·
                      refine ⟨2492842287083129333760719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 106361270915546851573790677 2492842287083129333760719)
                      ·
                        rfl

theorem cell23_4854793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_4854793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854793 prefixEnd_4854793 := by exact prefixLift 4854793
  have htrace : WordTrace (prefixWord ++ tailWord_4854793) baseStart_4854793 baseEnd_4854793 := by
    simpa [prefixWord, tailWord_4854793, baseEnd_4854793] using wordTrace_append hprefix tailTrace_4854793
  have hstable : (prefixWord ++ tailWord_4854793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854793).length < 2 ^ (prefixWord ++ tailWord_4854793).sum := by decide
  have hdescent : baseEnd_4854793 < baseStart_4854793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854803 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 8]
def baseStart_4854803 : Nat := 118140960795 + 4854803 * 2 ^ 59
def prefixEnd_4854803 : Nat := 4983230072969 + 3 ^ 40 * 4854803 * 2
def baseEnd_4854803 : Nat := 2492847421889674294635673

theorem tailTrace_4854803 : CollatzResearch.WordTrace tailWord_4854803 prefixEnd_4854803 2492847421889674294635673 := by
  unfold tailWord_4854803
  simp only [CollatzResearch.WordTrace]
  refine ⟨177069212230885340186753063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118046141487256893457835375 177069212230885340186753063)
  ·
    refine ⟨265603818346328010280129595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177069212230885340186753063 265603818346328010280129595)
    ·
      refine ⟨398405727519492015420194393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265603818346328010280129595 398405727519492015420194393)
      ·
        refine ⟨298804295639619011565145795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 398405727519492015420194393 298804295639619011565145795)
        ·
          refine ⟨448206443459428517347718693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298804295639619011565145795 448206443459428517347718693)
          ·
            refine ⟨84038708148642847002697255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 448206443459428517347718693 84038708148642847002697255)
            ·
              refine ⟨126058062222964270504045883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84038708148642847002697255 126058062222964270504045883)
              ·
                refine ⟨189087093334446405756068825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126058062222964270504045883 189087093334446405756068825)
                ·
                  refine ⟨141815320000834804317051619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189087093334446405756068825 141815320000834804317051619)
                  ·
                    refine ⟨212722980001252206475577429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 141815320000834804317051619 212722980001252206475577429)
                    ·
                      refine ⟨2492847421889674294635673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 212722980001252206475577429 2492847421889674294635673)
                      ·
                        rfl

theorem cell23_4854803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_4854803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854803 prefixEnd_4854803 := by exact prefixLift 4854803
  have htrace : WordTrace (prefixWord ++ tailWord_4854803) baseStart_4854803 baseEnd_4854803 := by
    simpa [prefixWord, tailWord_4854803, baseEnd_4854803] using wordTrace_append hprefix tailTrace_4854803
  have hstable : (prefixWord ++ tailWord_4854803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854803).length < 2 ^ (prefixWord ++ tailWord_4854803).sum := by decide
  have hdescent : baseEnd_4854803 < baseStart_4854803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854807 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 4]
def baseStart_4854807 : Nat := 118140960795 + 4854807 * 2 ^ 59
def prefixEnd_4854807 : Nat := 4983230072969 + 3 ^ 40 * 4854807 * 2
def baseEnd_4854807 : Nat := 2492849475812292278985655

theorem tailTrace_4854807 : CollatzResearch.WordTrace tailWord_4854807 prefixEnd_4854807 2492849475812292278985655 := by
  unfold tailWord_4854807
  simp only [CollatzResearch.WordTrace]
  refine ⟨177069358122870848869898675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118046238748580565913265783 177069358122870848869898675)
  ·
    refine ⟨265604037184306273304848013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177069358122870848869898675 265604037184306273304848013)
    ·
      refine ⟨99601513944114852489318005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265604037184306273304848013 99601513944114852489318005)
      ·
        refine ⟨9337641932260767420873563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99601513944114852489318005 9337641932260767420873563)
        ·
          refine ⟨14006462898391151131310345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9337641932260767420873563 14006462898391151131310345)
          ·
            refine ⟨10504847173793363348482759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14006462898391151131310345 10504847173793363348482759)
            ·
              refine ⟨15757270760690045022724139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10504847173793363348482759 15757270760690045022724139)
              ·
                refine ⟨23635906141035067534086209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15757270760690045022724139 23635906141035067534086209)
                ·
                  refine ⟨17726929605776300650564657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23635906141035067534086209 17726929605776300650564657)
                  ·
                    refine ⟨13295197204332225487923493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17726929605776300650564657 13295197204332225487923493)
                    ·
                      refine ⟨2492849475812292278985655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13295197204332225487923493 2492849475812292278985655)
                      ·
                        rfl

theorem cell23_4854807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_4854807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854807 prefixEnd_4854807 := by exact prefixLift 4854807
  have htrace : WordTrace (prefixWord ++ tailWord_4854807) baseStart_4854807 baseEnd_4854807 := by
    simpa [prefixWord, tailWord_4854807, baseEnd_4854807] using wordTrace_append hprefix tailTrace_4854807
  have hstable : (prefixWord ++ tailWord_4854807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854807).length < 2 ^ (prefixWord ++ tailWord_4854807).sum := by decide
  have hdescent : baseEnd_4854807 < baseStart_4854807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854880 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 4]
def baseStart_4854880 : Nat := 118140960795 + 4854880 * 2 ^ 59
def prefixEnd_4854880 : Nat := 4983230072969 + 3 ^ 40 * 4854880 * 2
def baseEnd_4854880 : Nat := 2492886959900070493372819

theorem tailTrace_4854880 : CollatzResearch.WordTrace tailWord_4854880 prefixEnd_4854880 2492886959900070493372819 := by
  unfold tailWord_4854880
  simp only [CollatzResearch.WordTrace]
  refine ⟨88536010325803191168653047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118048013767737588224870729 88536010325803191168653047)
  ·
    refine ⟨132804015488704786752979571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88536010325803191168653047 132804015488704786752979571)
    ·
      refine ⟨199206023233057180129469357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132804015488704786752979571 199206023233057180129469357)
      ·
        refine ⟨74702258712396442548551009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199206023233057180129469357 74702258712396442548551009)
        ·
          refine ⟨56026694034297331911413257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74702258712396442548551009 56026694034297331911413257)
          ·
            refine ⟨42020020525722998933559943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56026694034297331911413257 42020020525722998933559943)
            ·
              refine ⟨63030030788584498400339915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42020020525722998933559943 63030030788584498400339915)
              ·
                refine ⟨94545046182876747600509873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63030030788584498400339915 94545046182876747600509873)
                ·
                  refine ⟨70908784637157560700382405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94545046182876747600509873 70908784637157560700382405)
                  ·
                    refine ⟨13295397119467042631321701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70908784637157560700382405 13295397119467042631321701)
                    ·
                      refine ⟨2492886959900070493372819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13295397119467042631321701 2492886959900070493372819)
                      ·
                        rfl

theorem cell23_4854880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_4854880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854880 prefixEnd_4854880 := by exact prefixLift 4854880
  have htrace : WordTrace (prefixWord ++ tailWord_4854880) baseStart_4854880 baseEnd_4854880 := by
    simpa [prefixWord, tailWord_4854880, baseEnd_4854880] using wordTrace_append hprefix tailTrace_4854880
  have hstable : (prefixWord ++ tailWord_4854880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854880).length < 2 ^ (prefixWord ++ tailWord_4854880).sum := by decide
  have hdescent : baseEnd_4854880 < baseStart_4854880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854887 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 3]
def baseStart_4854887 : Nat := 118140960795 + 4854887 * 2 ^ 59
def prefixEnd_4854887 : Nat := 4983230072969 + 3 ^ 40 * 4854887 * 2
def baseEnd_4854887 : Nat := 2492890554264651965985287

theorem tailTrace_4854887 : CollatzResearch.WordTrace tailWord_4854887 prefixEnd_4854887 2492890554264651965985287 := by
  unfold tailWord_4854887
  simp only [CollatzResearch.WordTrace]
  refine ⟨177072275962581022532810915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118048183975054015021873943 177072275962581022532810915)
  ·
    refine ⟨265608413943871533799216373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177072275962581022532810915 265608413943871533799216373)
    ·
      refine ⟨24900788807237956293676535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 265608413943871533799216373 24900788807237956293676535)
      ·
        refine ⟨37351183210856934440514803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24900788807237956293676535 37351183210856934440514803)
        ·
          refine ⟨56026774816285401660772205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37351183210856934440514803 56026774816285401660772205)
          ·
            refine ⟨21010040556107025622789577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56026774816285401660772205 21010040556107025622789577)
            ·
              refine ⟨15757530417080269217092183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21010040556107025622789577 15757530417080269217092183)
              ·
                refine ⟨23636295625620403825638275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15757530417080269217092183 23636295625620403825638275)
                ·
                  refine ⟨35454443438430605738457413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23636295625620403825638275 35454443438430605738457413)
                  ·
                    refine ⟨6647708144705738575960765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35454443438430605738457413 6647708144705738575960765)
                    ·
                      refine ⟨2492890554264651965985287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6647708144705738575960765 2492890554264651965985287)
                      ·
                        rfl

theorem cell23_4854887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_4854887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854887 prefixEnd_4854887 := by exact prefixLift 4854887
  have htrace : WordTrace (prefixWord ++ tailWord_4854887) baseStart_4854887 baseEnd_4854887 := by
    simpa [prefixWord, tailWord_4854887, baseEnd_4854887] using wordTrace_append hprefix tailTrace_4854887
  have hstable : (prefixWord ++ tailWord_4854887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854887).length < 2 ^ (prefixWord ++ tailWord_4854887).sum := by decide
  have hdescent : baseEnd_4854887 < baseStart_4854887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854901 : List Nat := [1, 3, 4, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_4854901 : Nat := 118140960795 + 4854901 * 2 ^ 59
def prefixEnd_4854901 : Nat := 4983230072969 + 3 ^ 40 * 4854901 * 2
def baseEnd_4854901 : Nat := 2492897742993814911210223

theorem tailTrace_4854901 : CollatzResearch.WordTrace tailWord_4854901 prefixEnd_4854901 2492897742993814911210223 := by
  unfold tailWord_4854901
  simp only [CollatzResearch.WordTrace]
  refine ⟨177072786584530302923820557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118048524389686868615880371 177072786584530302923820557)
  ·
    refine ⟨66402294969198863596432709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177072786584530302923820557 66402294969198863596432709)
    ·
      refine ⟨12450430306724786924331133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66402294969198863596432709 12450430306724786924331133)
      ·
        refine ⟨4668911365021795096624175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12450430306724786924331133 4668911365021795096624175)
        ·
          refine ⟨7003367047532692644936263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4668911365021795096624175 7003367047532692644936263)
          ·
            refine ⟨10505050571299038967404395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7003367047532692644936263 10505050571299038967404395)
            ·
              refine ⟨15757575856948558451106593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10505050571299038967404395 15757575856948558451106593)
              ·
                refine ⟨11818181892711418838329945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15757575856948558451106593 11818181892711418838329945)
                ·
                  refine ⟨8863636419533564128747459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11818181892711418838329945 8863636419533564128747459)
                  ·
                    refine ⟨13295454629300346193121189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8863636419533564128747459 13295454629300346193121189)
                    ·
                      refine ⟨2492897742993814911210223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13295454629300346193121189 2492897742993814911210223)
                      ·
                        rfl

theorem cell23_4854901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_4854901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854901 prefixEnd_4854901 := by exact prefixLift 4854901
  have htrace : WordTrace (prefixWord ++ tailWord_4854901) baseStart_4854901 baseEnd_4854901 := by
    simpa [prefixWord, tailWord_4854901, baseEnd_4854901] using wordTrace_append hprefix tailTrace_4854901
  have hstable : (prefixWord ++ tailWord_4854901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854901).length < 2 ^ (prefixWord ++ tailWord_4854901).sum := by decide
  have hdescent : baseEnd_4854901 < baseStart_4854901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854961 : List Nat := [1, 2, 2, 5, 1, 1, 2, 2, 2, 3, 2]
def baseStart_4854961 : Nat := 118140960795 + 4854961 * 2 ^ 59
def prefixEnd_4854961 : Nat := 4983230072969 + 3 ^ 40 * 4854961 * 2
def baseEnd_4854961 : Nat := 2492928551833084676459947

theorem tailTrace_4854961 : CollatzResearch.WordTrace tailWord_4854961 prefixEnd_4854961 2492928551833084676459947 := by
  unfold tailWord_4854961
  simp only [CollatzResearch.WordTrace]
  refine ⟨177074974964312933171004737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118049983309541955447336491 177074974964312933171004737)
  ·
    refine ⟨132806231223234699878253553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177074974964312933171004737 132806231223234699878253553)
    ·
      refine ⟨99604673417426024908690165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132806231223234699878253553 99604673417426024908690165)
      ·
        refine ⟨9337938132883689835189703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99604673417426024908690165 9337938132883689835189703)
        ·
          refine ⟨14006907199325534752784555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9337938132883689835189703 14006907199325534752784555)
          ·
            refine ⟨21010360798988302129176833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14006907199325534752784555 21010360798988302129176833)
            ·
              refine ⟨15757770599241226596882625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21010360798988302129176833 15757770599241226596882625)
              ·
                refine ⟨11818327949430919947661969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15757770599241226596882625 11818327949430919947661969)
                ·
                  refine ⟨8863745962073189960746477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11818327949430919947661969 8863745962073189960746477)
                  ·
                    refine ⟨3323904735777446235279929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8863745962073189960746477 3323904735777446235279929)
                    ·
                      refine ⟨2492928551833084676459947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3323904735777446235279929 2492928551833084676459947)
                      ·
                        rfl

theorem cell23_4854961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_4854961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854961 prefixEnd_4854961 := by exact prefixLift 4854961
  have htrace : WordTrace (prefixWord ++ tailWord_4854961) baseStart_4854961 baseEnd_4854961 := by
    simpa [prefixWord, tailWord_4854961, baseEnd_4854961] using wordTrace_append hprefix tailTrace_4854961
  have hstable : (prefixWord ++ tailWord_4854961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854961).length < 2 ^ (prefixWord ++ tailWord_4854961).sum := by decide
  have hdescent : baseEnd_4854961 < baseStart_4854961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854974 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_4854974 : Nat := 118140960795 + 4854974 * 2 ^ 59
def prefixEnd_4854974 : Nat := 4983230072969 + 3 ^ 40 * 4854974 * 2
def baseEnd_4854974 : Nat := 2492935227081593125597387

theorem tailTrace_4854974 : CollatzResearch.WordTrace tailWord_4854974 prefixEnd_4854974 2492935227081593125597387 := by
  unfold tailWord_4854974
  simp only [CollatzResearch.WordTrace]
  refine ⟨22134431139158229548903497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118050299408843890927485317 22134431139158229548903497)
  ·
    refine ⟨16600823354368672161677623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22134431139158229548903497 16600823354368672161677623)
    ·
      refine ⟨24901235031553008242516435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16600823354368672161677623 24901235031553008242516435)
      ·
        refine ⟨37351852547329512363774653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24901235031553008242516435 37351852547329512363774653)
        ·
          refine ⟨14006944705248567136415495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37351852547329512363774653 14006944705248567136415495)
          ·
            refine ⟨21010417057872850704623243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14006944705248567136415495 21010417057872850704623243)
            ·
              refine ⟨31515625586809276056934865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21010417057872850704623243 31515625586809276056934865)
              ·
                refine ⟨23636719190106957042701149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31515625586809276056934865 23636719190106957042701149)
                ·
                  refine ⟨8863769696290108891012931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23636719190106957042701149 8863769696290108891012931)
                  ·
                    refine ⟨13295654544435163336519397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8863769696290108891012931 13295654544435163336519397)
                    ·
                      refine ⟨2492935227081593125597387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13295654544435163336519397 2492935227081593125597387)
                      ·
                        rfl

theorem cell23_4854974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_4854974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854974 prefixEnd_4854974 := by exact prefixLift 4854974
  have htrace : WordTrace (prefixWord ++ tailWord_4854974) baseStart_4854974 baseEnd_4854974 := by
    simpa [prefixWord, tailWord_4854974, baseEnd_4854974] using wordTrace_append hprefix tailTrace_4854974
  have hstable : (prefixWord ++ tailWord_4854974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854974).length < 2 ^ (prefixWord ++ tailWord_4854974).sum := by decide
  have hdescent : baseEnd_4854974 < baseStart_4854974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854984 : List Nat := [2, 1, 3, 1, 2, 1, 4, 3, 2, 4]
def baseStart_4854984 : Nat := 118140960795 + 4854984 * 2 ^ 59
def prefixEnd_4854984 : Nat := 4983230072969 + 3 ^ 40 * 4854984 * 2
def baseEnd_4854984 : Nat := 830980120629379362157447

theorem tailTrace_4854984 : CollatzResearch.WordTrace tailWord_4854984 prefixEnd_4854984 830980120629379362157447 := by
  unfold tailWord_4854984
  simp only [CollatzResearch.WordTrace]
  refine ⟨88537906921614804049546003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118050542562153072066061337 88537906921614804049546003)
  ·
    refine ⟨132806860382422206074319005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88537906921614804049546003 132806860382422206074319005)
    ·
      refine ⟨49802572643408327277869627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132806860382422206074319005 49802572643408327277869627)
      ·
        refine ⟨74703858965112490916804441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49802572643408327277869627 74703858965112490916804441)
        ·
          refine ⟨56027894223834368187603331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74703858965112490916804441 56027894223834368187603331)
          ·
            refine ⟨84041841335751552281404997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56027894223834368187603331 84041841335751552281404997)
            ·
              refine ⟨15757845250453416052763437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84041841335751552281404997 15757845250453416052763437)
              ·
                refine ⟨5909191968920031019786289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15757845250453416052763437 5909191968920031019786289)
                ·
                  refine ⟨4431893976690023264839717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5909191968920031019786289 4431893976690023264839717)
                  ·
                    refine ⟨830980120629379362157447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4431893976690023264839717 830980120629379362157447)
                    ·
                      rfl

theorem cell23_4854984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_4854984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854984 prefixEnd_4854984 := by exact prefixLift 4854984
  have htrace : WordTrace (prefixWord ++ tailWord_4854984) baseStart_4854984 baseEnd_4854984 := by
    simpa [prefixWord, tailWord_4854984, baseEnd_4854984] using wordTrace_append hprefix tailTrace_4854984
  have hstable : (prefixWord ++ tailWord_4854984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854984).length < 2 ^ (prefixWord ++ tailWord_4854984).sum := by decide
  have hdescent : baseEnd_4854984 < baseStart_4854984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4854994 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 3, 2, 3]
def baseStart_4854994 : Nat := 118140960795 + 4854994 * 2 ^ 59
def prefixEnd_4854994 : Nat := 4983230072969 + 3 ^ 40 * 4854994 * 2
def baseEnd_4854994 : Nat := 2492945496694683047347295

theorem tailTrace_4854994 : CollatzResearch.WordTrace tailWord_4854994 prefixEnd_4854994 2492945496694683047347295 := by
  unfold tailWord_4854994
  simp only [CollatzResearch.WordTrace]
  refine ⟨44269044643298344951739009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118050785715462253204637357 44269044643298344951739009)
  ·
    refine ⟨33201783482473758713804257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44269044643298344951739009 33201783482473758713804257)
    ·
      refine ⟨24901337611855319035353193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33201783482473758713804257 24901337611855319035353193)
      ·
        refine ⟨18676003208891489276514895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24901337611855319035353193 18676003208891489276514895)
        ·
          refine ⟨28014004813337233914772343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18676003208891489276514895 28014004813337233914772343)
          ·
            refine ⟨42021007220005850872158515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28014004813337233914772343 42021007220005850872158515)
            ·
              refine ⟨63031510830008776308237773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42021007220005850872158515 63031510830008776308237773)
              ·
                refine ⟨23636816561253291115589165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63031510830008776308237773 23636816561253291115589165)
                ·
                  refine ⟨8863806210469984168345937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23636816561253291115589165 8863806210469984168345937)
                  ·
                    refine ⟨6647854657852488126259453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8863806210469984168345937 6647854657852488126259453)
                    ·
                      refine ⟨2492945496694683047347295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6647854657852488126259453 2492945496694683047347295)
                      ·
                        rfl

theorem cell23_4854994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_4854994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4854994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4854994 prefixEnd_4854994 := by exact prefixLift 4854994
  have htrace : WordTrace (prefixWord ++ tailWord_4854994) baseStart_4854994 baseEnd_4854994 := by
    simpa [prefixWord, tailWord_4854994, baseEnd_4854994] using wordTrace_append hprefix tailTrace_4854994
  have hstable : (prefixWord ++ tailWord_4854994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4854994).length < 2 ^ (prefixWord ++ tailWord_4854994).sum := by decide
  have hdescent : baseEnd_4854994 < baseStart_4854994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4854994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855005 : List Nat := [1, 4, 3, 2, 3, 1, 2, 1, 1, 5]
def baseStart_4855005 : Nat := 118140960795 + 4855005 * 2 ^ 59
def prefixEnd_4855005 : Nat := 4983230072969 + 3 ^ 40 * 4855005 * 2
def baseEnd_4855005 : Nat := 830983714993960834769915

theorem tailTrace_4855005 : CollatzResearch.WordTrace tailWord_4855005 prefixEnd_4855005 830983714993960834769915 := by
  unfold tailWord_4855005
  simp only [CollatzResearch.WordTrace]
  refine ⟨177076579776153528685606469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118051053184102352457070979 177076579776153528685606469)
  ·
    refine ⟨33201858708028786628551213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177076579776153528685606469 33201858708028786628551213)
    ·
      refine ⟨12450697015510794985706705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33201858708028786628551213 12450697015510794985706705)
      ·
        refine ⟨9338022761633096239280029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12450697015510794985706705 9338022761633096239280029)
        ·
          refine ⟨3501758535612411089730011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9338022761633096239280029 3501758535612411089730011)
          ·
            refine ⟨5252637803418616634595017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3501758535612411089730011 5252637803418616634595017)
            ·
              refine ⟨3939478352563962475946263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5252637803418616634595017 3939478352563962475946263)
              ·
                refine ⟨5909217528845943713919395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3939478352563962475946263 5909217528845943713919395)
                ·
                  refine ⟨8863826293268915570879093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5909217528845943713919395 8863826293268915570879093)
                  ·
                    refine ⟨830983714993960834769915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8863826293268915570879093 830983714993960834769915)
                    ·
                      rfl

theorem cell23_4855005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_4855005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855005 prefixEnd_4855005 := by exact prefixLift 4855005
  have htrace : WordTrace (prefixWord ++ tailWord_4855005) baseStart_4855005 baseEnd_4855005 := by
    simpa [prefixWord, tailWord_4855005, baseEnd_4855005] using wordTrace_append hprefix tailTrace_4855005
  have hstable : (prefixWord ++ tailWord_4855005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855005).length < 2 ^ (prefixWord ++ tailWord_4855005).sum := by decide
  have hdescent : baseEnd_4855005 < baseStart_4855005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855008 : List Nat := [2, 1, 1, 3, 1, 4, 1, 5, 1, 2, 2]
def baseStart_4855008 : Nat := 118140960795 + 4855008 * 2 ^ 59
def prefixEnd_4855008 : Nat := 4983230072969 + 3 ^ 40 * 4855008 * 2
def baseEnd_4855008 : Nat := 2492952685423845992572231

theorem tailTrace_4855008 : CollatzResearch.WordTrace tailWord_4855008 prefixEnd_4855008 2492952685423845992572231 := by
  unfold tailWord_4855008
  simp only [CollatzResearch.WordTrace]
  refine ⟨88538344597571330098982839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118051126130095106798643785 88538344597571330098982839)
  ·
    refine ⟨132807516896356995148474259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88538344597571330098982839 132807516896356995148474259)
    ·
      refine ⟨199211275344535492722711389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132807516896356995148474259 199211275344535492722711389)
      ·
        refine ⟨74704228254200809771016771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199211275344535492722711389 74704228254200809771016771)
        ·
          refine ⟨112056342381301214656525157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74704228254200809771016771 112056342381301214656525157)
          ·
            refine ⟨21010564196493977748098467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112056342381301214656525157 21010564196493977748098467)
            ·
              refine ⟨31515846294740966622147701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21010564196493977748098467 31515846294740966622147701)
              ·
                refine ⟨2954610590131965620826347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31515846294740966622147701 2954610590131965620826347)
                ·
                  refine ⟨4431915885197948431239521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2954610590131965620826347 4431915885197948431239521)
                  ·
                    refine ⟨3323936913898461323429641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4431915885197948431239521 3323936913898461323429641)
                    ·
                      refine ⟨2492952685423845992572231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3323936913898461323429641 2492952685423845992572231)
                      ·
                        rfl

theorem cell23_4855008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 1, 2, 2].length) (baseStart_4855008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855008 prefixEnd_4855008 := by exact prefixLift 4855008
  have htrace : WordTrace (prefixWord ++ tailWord_4855008) baseStart_4855008 baseEnd_4855008 := by
    simpa [prefixWord, tailWord_4855008, baseEnd_4855008] using wordTrace_append hprefix tailTrace_4855008
  have hstable : (prefixWord ++ tailWord_4855008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855008).length < 2 ^ (prefixWord ++ tailWord_4855008).sum := by decide
  have hdescent : baseEnd_4855008 < baseStart_4855008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855041 : List Nat := [1, 2, 4, 1, 1, 5, 1, 1, 1, 3, 3]
def baseStart_4855041 : Nat := 118140960795 + 4855041 * 2 ^ 59
def prefixEnd_4855041 : Nat := 4983230072969 + 3 ^ 40 * 4855041 * 2
def baseEnd_4855041 : Nat := 2492969630285444363459579

theorem tailTrace_4855041 : CollatzResearch.WordTrace tailWord_4855041 prefixEnd_4855041 2492969630285444363459579 := by
  unfold tailWord_4855041
  simp only [CollatzResearch.WordTrace]
  refine ⟨177077892804023106833916977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118051928536015404555944651 177077892804023106833916977)
  ·
    refine ⟨132808419603017330125437733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177077892804023106833916977 132808419603017330125437733)
    ·
      refine ⟨24901578675565749398519575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132808419603017330125437733 24901578675565749398519575)
      ·
        refine ⟨37352368013348624097779363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24901578675565749398519575 37352368013348624097779363)
        ·
          refine ⟨56028552020022936146669045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37352368013348624097779363 56028552020022936146669045)
          ·
            refine ⟨5252676751877150263750223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56028552020022936146669045 5252676751877150263750223)
            ·
              refine ⟨7879015127815725395625335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5252676751877150263750223 7879015127815725395625335)
              ·
                refine ⟨11818522691723588093438003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7879015127815725395625335 11818522691723588093438003)
                ·
                  refine ⟨17727784037585382140157005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11818522691723588093438003 17727784037585382140157005)
                  ·
                    refine ⟨6647919014094518302558877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17727784037585382140157005 6647919014094518302558877)
                    ·
                      refine ⟨2492969630285444363459579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6647919014094518302558877 2492969630285444363459579)
                      ·
                        rfl

theorem cell23_4855041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_4855041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855041 prefixEnd_4855041 := by exact prefixLift 4855041
  have htrace : WordTrace (prefixWord ++ tailWord_4855041) baseStart_4855041 baseEnd_4855041 := by
    simpa [prefixWord, tailWord_4855041, baseEnd_4855041] using wordTrace_append hprefix tailTrace_4855041
  have hstable : (prefixWord ++ tailWord_4855041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855041).length < 2 ^ (prefixWord ++ tailWord_4855041).sum := by decide
  have hdescent : baseEnd_4855041 < baseStart_4855041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855051 : List Nat := [1, 1, 1, 1, 5, 3, 1, 4, 1, 3, 2]
def baseStart_4855051 : Nat := 118140960795 + 4855051 * 2 ^ 59
def prefixEnd_4855051 : Nat := 4983230072969 + 3 ^ 40 * 4855051 * 2
def baseEnd_4855051 : Nat := 2492974765091989324334533

theorem tailTrace_4855051 : CollatzResearch.WordTrace tailWord_4855051 prefixEnd_4855051 2492974765091989324334533 := by
  unfold tailWord_4855051
  simp only [CollatzResearch.WordTrace]
  refine ⟨177078257533986878541781007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118052171689324585694520671 177078257533986878541781007)
  ·
    refine ⟨265617386300980317812671511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177078257533986878541781007 265617386300980317812671511)
    ·
      refine ⟨398426079451470476719007267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265617386300980317812671511 398426079451470476719007267)
      ·
        refine ⟨597639119177205715078510901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398426079451470476719007267 597639119177205715078510901)
        ·
          refine ⟨56028667422863035788610397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 597639119177205715078510901 56028667422863035788610397)
          ·
            refine ⟨21010750283573638420728899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56028667422863035788610397 21010750283573638420728899)
            ·
              refine ⟨31516125425360457631093349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21010750283573638420728899 31516125425360457631093349)
              ·
                refine ⟨5909273517255085805830003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31516125425360457631093349 5909273517255085805830003)
                ·
                  refine ⟨8863910275882628708745005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5909273517255085805830003 8863910275882628708745005)
                  ·
                    refine ⟨3323966353455985765779377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8863910275882628708745005 3323966353455985765779377)
                    ·
                      refine ⟨2492974765091989324334533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3323966353455985765779377 2492974765091989324334533)
                      ·
                        rfl

theorem cell23_4855051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 3, 2].length) (baseStart_4855051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855051 prefixEnd_4855051 := by exact prefixLift 4855051
  have htrace : WordTrace (prefixWord ++ tailWord_4855051) baseStart_4855051 baseEnd_4855051 := by
    simpa [prefixWord, tailWord_4855051, baseEnd_4855051] using wordTrace_append hprefix tailTrace_4855051
  have hstable : (prefixWord ++ tailWord_4855051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855051).length < 2 ^ (prefixWord ++ tailWord_4855051).sum := by decide
  have hdescent : baseEnd_4855051 < baseStart_4855051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855067 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 3]
def baseStart_4855067 : Nat := 118140960795 + 4855067 * 2 ^ 59
def prefixEnd_4855067 : Nat := 4983230072969 + 3 ^ 40 * 4855067 * 2
def baseEnd_4855067 : Nat := 2492982980782461261734459

theorem tailTrace_4855067 : CollatzResearch.WordTrace tailWord_4855067 prefixEnd_4855067 2492982980782461261734459 := by
  unfold tailWord_4855067
  simp only [CollatzResearch.WordTrace]
  refine ⟨177078841101928913274363455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118052560734619275516242303 177078841101928913274363455)
  ·
    refine ⟨265618261652893369911545183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177078841101928913274363455 265618261652893369911545183)
    ·
      refine ⟨398427392479340054867317775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265618261652893369911545183 398427392479340054867317775)
      ·
        refine ⟨597641088719010082300976663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398427392479340054867317775 597641088719010082300976663)
        ·
          refine ⟨896461633078515123451464995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597641088719010082300976663 896461633078515123451464995)
          ·
            refine ⟨1344692449617772685177197493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 896461633078515123451464995 1344692449617772685177197493)
            ·
              refine ⟨126064917151666189235362265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1344692449617772685177197493 126064917151666189235362265)
              ·
                refine ⟨94548687863749641926521699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126064917151666189235362265 94548687863749641926521699)
                ·
                  refine ⟨141823031795624462889782549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94548687863749641926521699 141823031795624462889782549)
                  ·
                    refine ⟨6647954615419896697958557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 141823031795624462889782549 6647954615419896697958557)
                    ·
                      refine ⟨2492982980782461261734459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6647954615419896697958557 2492982980782461261734459)
                      ·
                        rfl

theorem cell23_4855067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 3].length) (baseStart_4855067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855067 prefixEnd_4855067 := by exact prefixLift 4855067
  have htrace : WordTrace (prefixWord ++ tailWord_4855067) baseStart_4855067 baseEnd_4855067 := by
    simpa [prefixWord, tailWord_4855067, baseEnd_4855067] using wordTrace_append hprefix tailTrace_4855067
  have hstable : (prefixWord ++ tailWord_4855067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855067).length < 2 ^ (prefixWord ++ tailWord_4855067).sum := by decide
  have hdescent : baseEnd_4855067 < baseStart_4855067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855098 : List Nat := [3, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2]
def baseStart_4855098 : Nat := 118140960795 + 4855098 * 2 ^ 59
def prefixEnd_4855098 : Nat := 4983230072969 + 3 ^ 40 * 4855098 * 2
def baseEnd_4855098 : Nat := 2492998898682750640446817

theorem tailTrace_4855098 : CollatzResearch.WordTrace tailWord_4855098 prefixEnd_4855098 2492998898682750640446817 := by
  unfold tailWord_4855098
  simp only [CollatzResearch.WordTrace]
  refine ⟨44269992941204151392185487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118053314509877737045827965 44269992941204151392185487)
  ·
    refine ⟨66404989411806227088278231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44269992941204151392185487 66404989411806227088278231)
    ·
      refine ⟨99607484117709340632417347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66404989411806227088278231 99607484117709340632417347)
      ·
        refine ⟨149411226176564010948626021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99607484117709340632417347 149411226176564010948626021)
        ·
          refine ⟨28014604908105752052867379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149411226176564010948626021 28014604908105752052867379)
          ·
            refine ⟨42021907362158628079301069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28014604908105752052867379 42021907362158628079301069)
            ·
              refine ⟨15758215260809485529737901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42021907362158628079301069 15758215260809485529737901)
              ·
                refine ⟨5909330722803557073651713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15758215260809485529737901 5909330722803557073651713)
                ·
                  refine ⟨4431998042102667805238785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5909330722803557073651713 4431998042102667805238785)
                  ·
                    refine ⟨3323998531577000853929089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4431998042102667805238785 3323998531577000853929089)
                    ·
                      refine ⟨2492998898682750640446817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3323998531577000853929089 2492998898682750640446817)
                      ·
                        rfl

theorem cell23_4855098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2].length) (baseStart_4855098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855098 prefixEnd_4855098 := by exact prefixLift 4855098
  have htrace : WordTrace (prefixWord ++ tailWord_4855098) baseStart_4855098 baseEnd_4855098 := by
    simpa [prefixWord, tailWord_4855098, baseEnd_4855098] using wordTrace_append hprefix tailTrace_4855098
  have hstable : (prefixWord ++ tailWord_4855098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855098).length < 2 ^ (prefixWord ++ tailWord_4855098).sum := by decide
  have hdescent : baseEnd_4855098 < baseStart_4855098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855154 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 1, 3, 4]
def baseStart_4855154 : Nat := 118140960795 + 4855154 * 2 ^ 59
def prefixEnd_4855154 : Nat := 4983230072969 + 3 ^ 40 * 4855154 * 2
def baseEnd_4855154 : Nat := 2493027653599402421346559

theorem tailTrace_4855154 : CollatzResearch.WordTrace tailWord_4855154 prefixEnd_4855154 2493027653599402421346559 := by
  unfold tailWord_4855154
  simp only [CollatzResearch.WordTrace]
  refine ⟨44270503563153431783195129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118054676168409151421853677 44270503563153431783195129)
  ·
    refine ⟨33202877672365073837396347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44270503563153431783195129 33202877672365073837396347)
    ·
      refine ⟨49804316508547610756094521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33202877672365073837396347 49804316508547610756094521)
      ·
        refine ⟨37353237381410708067070891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49804316508547610756094521 37353237381410708067070891)
        ·
          refine ⟨56029856072116062100606337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37353237381410708067070891 56029856072116062100606337)
          ·
            refine ⟨42022392054087046575454753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56029856072116062100606337 42022392054087046575454753)
            ·
              refine ⟨31516794040565284931591065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42022392054087046575454753 31516794040565284931591065)
              ·
                refine ⟨23637595530423963698693299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31516794040565284931591065 23637595530423963698693299)
                ·
                  refine ⟨35456393295635945548039949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23637595530423963698693299 35456393295635945548039949)
                  ·
                    refine ⟨13296147485863479580514981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35456393295635945548039949 13296147485863479580514981)
                    ·
                      refine ⟨2493027653599402421346559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13296147485863479580514981 2493027653599402421346559)
                      ·
                        rfl

theorem cell23_4855154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_4855154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855154 prefixEnd_4855154 := by exact prefixLift 4855154
  have htrace : WordTrace (prefixWord ++ tailWord_4855154) baseStart_4855154 baseEnd_4855154 := by
    simpa [prefixWord, tailWord_4855154, baseEnd_4855154] using wordTrace_append hprefix tailTrace_4855154
  have hstable : (prefixWord ++ tailWord_4855154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855154).length < 2 ^ (prefixWord ++ tailWord_4855154).sum := by decide
  have hdescent : baseEnd_4855154 < baseStart_4855154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855167 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 6]
def baseStart_4855167 : Nat := 118140960795 + 4855167 * 2 ^ 59
def prefixEnd_4855167 : Nat := 4983230072969 + 3 ^ 40 * 4855167 * 2
def baseEnd_4855167 : Nat := 2493034328847910870483999

theorem tailTrace_4855167 : CollatzResearch.WordTrace tailWord_4855167 prefixEnd_4855167 2493034328847910870483999 := by
  unfold tailWord_4855167
  simp only [CollatzResearch.WordTrace]
  refine ⟨177082488401566630353003755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118054992267711086902002503 177082488401566630353003755)
  ·
    refine ⟨265623732602349945529505633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177082488401566630353003755 265623732602349945529505633)
    ·
      refine ⟨199217799451762459147129225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265623732602349945529505633 199217799451762459147129225)
      ·
        refine ⟨149413349588821844360346919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199217799451762459147129225 149413349588821844360346919)
        ·
          refine ⟨224120024383232766540520379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149413349588821844360346919 224120024383232766540520379)
          ·
            refine ⟨336180036574849149810780569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224120024383232766540520379 336180036574849149810780569)
            ·
              refine ⟨252135027431136862358085427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 336180036574849149810780569 252135027431136862358085427)
              ·
                refine ⟨378202541146705293537128141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252135027431136862358085427 378202541146705293537128141)
                ·
                  refine ⟨141825952930014485076423053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 378202541146705293537128141 141825952930014485076423053)
                  ·
                    refine ⟨53184732348755431903658645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 141825952930014485076423053 53184732348755431903658645)
                    ·
                      refine ⟨2493034328847910870483999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53184732348755431903658645 2493034328847910870483999)
                      ·
                        rfl

theorem cell23_4855167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_4855167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855167 prefixEnd_4855167 := by exact prefixLift 4855167
  have htrace : WordTrace (prefixWord ++ tailWord_4855167) baseStart_4855167 baseEnd_4855167 := by
    simpa [prefixWord, tailWord_4855167, baseEnd_4855167] using wordTrace_append hprefix tailTrace_4855167
  have hstable : (prefixWord ++ tailWord_4855167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855167).length < 2 ^ (prefixWord ++ tailWord_4855167).sum := by decide
  have hdescent : baseEnd_4855167 < baseStart_4855167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855171 : List Nat := [1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 4]
def baseStart_4855171 : Nat := 118140960795 + 4855171 * 2 ^ 59
def prefixEnd_4855171 : Nat := 4983230072969 + 3 ^ 40 * 4855171 * 2
def baseEnd_4855171 : Nat := 2493036382770528854833981

theorem tailTrace_4855171 : CollatzResearch.WordTrace tailWord_4855171 prefixEnd_4855171 2493036382770528854833981 := by
  unfold tailWord_4855171
  simp only [CollatzResearch.WordTrace]
  refine ⟨177082634293552139036149367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118055089529034759357432911 177082634293552139036149367)
  ·
    refine ⟨265623951440328208554224051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177082634293552139036149367 265623951440328208554224051)
    ·
      refine ⟨398435927160492312831336077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265623951440328208554224051 398435927160492312831336077)
      ·
        refine ⟨149413472685184617311751029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 398435927160492312831336077 149413472685184617311751029)
        ·
          refine ⟨14007513064236057872976659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 149413472685184617311751029 14007513064236057872976659)
          ·
            refine ⟨21011269596354086809464989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14007513064236057872976659 21011269596354086809464989)
            ·
              refine ⟨7879226098632782553549371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21011269596354086809464989 7879226098632782553549371)
              ·
                refine ⟨11818839147949173830324057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7879226098632782553549371 11818839147949173830324057)
                ·
                  refine ⟨8864129360961880372743043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11818839147949173830324057 8864129360961880372743043)
                  ·
                    refine ⟨13296194041442820559114565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8864129360961880372743043 13296194041442820559114565)
                    ·
                      refine ⟨2493036382770528854833981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13296194041442820559114565 2493036382770528854833981)
                      ·
                        rfl

theorem cell23_4855171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 4].length) (baseStart_4855171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855171 prefixEnd_4855171 := by exact prefixLift 4855171
  have htrace : WordTrace (prefixWord ++ tailWord_4855171) baseStart_4855171 baseEnd_4855171 := by
    simpa [prefixWord, tailWord_4855171, baseEnd_4855171] using wordTrace_append hprefix tailTrace_4855171
  have hstable : (prefixWord ++ tailWord_4855171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855171).length < 2 ^ (prefixWord ++ tailWord_4855171).sum := by decide
  have hdescent : baseEnd_4855171 < baseStart_4855171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855187 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 7]
def baseStart_4855187 : Nat := 118140960795 + 4855187 * 2 ^ 59
def prefixEnd_4855187 : Nat := 4983230072969 + 3 ^ 40 * 4855187 * 2
def baseEnd_4855187 : Nat := 2493044598461000792233907

theorem tailTrace_4855187 : CollatzResearch.WordTrace tailWord_4855187 prefixEnd_4855187 2493044598461000792233907 := by
  unfold tailWord_4855187
  simp only [CollatzResearch.WordTrace]
  refine ⟨177083217861494173768731815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118055478574329449179154543 177083217861494173768731815)
  ·
    refine ⟨265624826792241260653097723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177083217861494173768731815 265624826792241260653097723)
    ·
      refine ⟨398437240188361890979646585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265624826792241260653097723 398437240188361890979646585)
      ·
        refine ⟨298827930141271418234734939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 398437240188361890979646585 298827930141271418234734939)
        ·
          refine ⟨448241895211907127352102409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298827930141271418234734939 448241895211907127352102409)
          ·
            refine ⟨336181421408930345514076807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 448241895211907127352102409 336181421408930345514076807)
            ·
              refine ⟨504272132113395518271115211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336181421408930345514076807 504272132113395518271115211)
              ·
                refine ⟨756408198170093277406672817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 504272132113395518271115211 756408198170093277406672817)
                ·
                  refine ⟨567306148627569958055004613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 756408198170093277406672817 567306148627569958055004613)
                  ·
                    refine ⟨106369902867669367135313365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 567306148627569958055004613 106369902867669367135313365)
                    ·
                      refine ⟨2493044598461000792233907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 106369902867669367135313365 2493044598461000792233907)
                      ·
                        rfl

theorem cell23_4855187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_4855187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855187 prefixEnd_4855187 := by exact prefixLift 4855187
  have htrace : WordTrace (prefixWord ++ tailWord_4855187) baseStart_4855187 baseEnd_4855187 := by
    simpa [prefixWord, tailWord_4855187, baseEnd_4855187] using wordTrace_append hprefix tailTrace_4855187
  have hstable : (prefixWord ++ tailWord_4855187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855187).length < 2 ^ (prefixWord ++ tailWord_4855187).sum := by decide
  have hdescent : baseEnd_4855187 < baseStart_4855187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855188 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 2, 4, 2]
def baseStart_4855188 : Nat := 118140960795 + 4855188 * 2 ^ 59
def prefixEnd_4855188 : Nat := 4983230072969 + 3 ^ 40 * 4855188 * 2
def baseEnd_4855188 : Nat := 2493045111941655288321403

theorem tailTrace_4855188 : CollatzResearch.WordTrace tailWord_4855188 prefixEnd_4855188 2493045111941655288321403 := by
  unfold tailWord_4855188
  simp only [CollatzResearch.WordTrace]
  refine ⟨88541627167245275469759109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118055502889660367293012145 88541627167245275469759109)
  ·
    refine ⟨16601555093858489150579833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88541627167245275469759109 16601555093858489150579833)
    ·
      refine ⟨12451166320393866862934875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16601555093858489150579833 12451166320393866862934875)
      ·
        refine ⟨18676749480590800294402313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12451166320393866862934875 18676749480590800294402313)
        ·
          refine ⟨14007562110443100220801735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18676749480590800294402313 14007562110443100220801735)
          ·
            refine ⟨21011343165664650331202603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14007562110443100220801735 21011343165664650331202603)
            ·
              refine ⟨31517014748496975496803905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21011343165664650331202603 31517014748496975496803905)
              ·
                refine ⟨23637761061372731622602929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31517014748496975496803905 23637761061372731622602929)
                ·
                  refine ⟨17728320796029548716952197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23637761061372731622602929 17728320796029548716952197)
                  ·
                    refine ⟨3324060149255540384428537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17728320796029548716952197 3324060149255540384428537)
                    ·
                      refine ⟨2493045111941655288321403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3324060149255540384428537 2493045111941655288321403)
                      ·
                        rfl

theorem cell23_4855188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_4855188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855188 prefixEnd_4855188 := by exact prefixLift 4855188
  have htrace : WordTrace (prefixWord ++ tailWord_4855188) baseStart_4855188 baseEnd_4855188 := by
    simpa [prefixWord, tailWord_4855188, baseEnd_4855188] using wordTrace_append hprefix tailTrace_4855188
  have hstable : (prefixWord ++ tailWord_4855188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855188).length < 2 ^ (prefixWord ++ tailWord_4855188).sum := by decide
  have hdescent : baseEnd_4855188 < baseStart_4855188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855194 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 8]
def baseStart_4855194 : Nat := 118140960795 + 4855194 * 2 ^ 59
def prefixEnd_4855194 : Nat := 4983230072969 + 3 ^ 40 * 4855194 * 2
def baseEnd_4855194 : Nat := 277005354758398029427375

theorem tailTrace_4855194 : CollatzResearch.WordTrace tailWord_4855194 prefixEnd_4855194 277005354758398029427375 := by
  unfold tailWord_4855194
  simp only [CollatzResearch.WordTrace]
  refine ⟨44270868293117203491059159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118055648781645875976157757 44270868293117203491059159)
  ·
    refine ⟨66406302439675805236588739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44270868293117203491059159 66406302439675805236588739)
    ·
      refine ⟨99609453659513707854883109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66406302439675805236588739 99609453659513707854883109)
      ·
        refine ⟨18676772561158820222790583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99609453659513707854883109 18676772561158820222790583)
        ·
          refine ⟨28015158841738230334185875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18676772561158820222790583 28015158841738230334185875)
          ·
            refine ⟨42022738262607345501278813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28015158841738230334185875 42022738262607345501278813)
            ·
              refine ⟨15758526848477754562979555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42022738262607345501278813 15758526848477754562979555)
              ·
                refine ⟨23637790272716631844469333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15758526848477754562979555 23637790272716631844469333)
                ·
                  refine ⟨277005354758398029427375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23637790272716631844469333 277005354758398029427375)
                  ·
                    rfl

theorem cell23_4855194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 8].length) (baseStart_4855194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855194 prefixEnd_4855194 := by exact prefixLift 4855194
  have htrace : WordTrace (prefixWord ++ tailWord_4855194) baseStart_4855194 baseEnd_4855194 := by
    simpa [prefixWord, tailWord_4855194, baseEnd_4855194] using wordTrace_append hprefix tailTrace_4855194
  have hstable : (prefixWord ++ tailWord_4855194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855194).length < 2 ^ (prefixWord ++ tailWord_4855194).sum := by decide
  have hdescent : baseEnd_4855194 < baseStart_4855194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855224 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 3, 5]
def baseStart_4855224 : Nat := 118140960795 + 4855224 * 2 ^ 59
def prefixEnd_4855224 : Nat := 4983230072969 + 3 ^ 40 * 4855224 * 2
def baseEnd_4855224 : Nat := 831021199081739049157079

theorem tailTrace_4855224 : CollatzResearch.WordTrace tailWord_4855224 prefixEnd_4855224 831021199081739049157079 := by
  unfold tailWord_4855224
  simp only [CollatzResearch.WordTrace]
  refine ⟨88542283681180064543914363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118056378241573419391885817 88542283681180064543914363)
  ·
    refine ⟨132813425521770096815871545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88542283681180064543914363 132813425521770096815871545)
    ·
      refine ⟨99610069141327572611903659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132813425521770096815871545 99610069141327572611903659)
      ·
        refine ⟨149415103711991358917855489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99610069141327572611903659 149415103711991358917855489)
        ·
          refine ⟨112061327783993519188391617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149415103711991358917855489 112061327783993519188391617)
          ·
            refine ⟨84045995837995139391293713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112061327783993519188391617 84045995837995139391293713)
            ·
              refine ⟨63034496878496354543470285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84045995837995139391293713 63034496878496354543470285)
              ·
                refine ⟨23637936329436132953801357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63034496878496354543470285 23637936329436132953801357)
                ·
                  refine ⟨8864226123538549857675509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23637936329436132953801357 8864226123538549857675509)
                  ·
                    refine ⟨831021199081739049157079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8864226123538549857675509 831021199081739049157079)
                    ·
                      rfl

theorem cell23_4855224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_4855224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855224 prefixEnd_4855224 := by exact prefixLift 4855224
  have htrace : WordTrace (prefixWord ++ tailWord_4855224) baseStart_4855224 baseEnd_4855224 := by
    simpa [prefixWord, tailWord_4855224, baseEnd_4855224] using wordTrace_append hprefix tailTrace_4855224
  have hstable : (prefixWord ++ tailWord_4855224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855224).length < 2 ^ (prefixWord ++ tailWord_4855224).sum := by decide
  have hdescent : baseEnd_4855224 < baseStart_4855224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855231 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 6, 3, 2]
def baseStart_4855231 : Nat := 118140960795 + 4855231 * 2 ^ 59
def prefixEnd_4855231 : Nat := 4983230072969 + 3 ^ 40 * 4855231 * 2
def baseEnd_4855231 : Nat := 2493067191609798620083705

theorem tailTrace_4855231 : CollatzResearch.WordTrace tailWord_4855231 prefixEnd_4855231 2493067191609798620083705 := by
  unfold tailWord_4855231
  simp only [CollatzResearch.WordTrace]
  refine ⟨177084822673334769283333547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118056548448889846188889031 177084822673334769283333547)
  ·
    refine ⟨265627234010002153925000321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177084822673334769283333547 265627234010002153925000321)
    ·
      refine ⟨199220425507501615443750241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265627234010002153925000321 199220425507501615443750241)
      ·
        refine ⟨149415319130626211582812681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199220425507501615443750241 149415319130626211582812681)
        ·
          refine ⟨112061489347969658687109511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149415319130626211582812681 112061489347969658687109511)
          ·
            refine ⟨168092234021954488030664267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112061489347969658687109511 168092234021954488030664267)
            ·
              refine ⟨252138351032931732045996401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168092234021954488030664267 252138351032931732045996401)
              ·
                refine ⟨189103763274698799034497301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252138351032931732045996401 189103763274698799034497301)
                ·
                  refine ⟨8864238903501506204742061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 189103763274698799034497301 8864238903501506204742061)
                  ·
                    refine ⟨3324089588813064826778273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8864238903501506204742061 3324089588813064826778273)
                    ·
                      refine ⟨2493067191609798620083705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3324089588813064826778273 2493067191609798620083705)
                      ·
                        rfl

theorem cell23_4855231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 3, 2].length) (baseStart_4855231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855231 prefixEnd_4855231 := by exact prefixLift 4855231
  have htrace : WordTrace (prefixWord ++ tailWord_4855231) baseStart_4855231 baseEnd_4855231 := by
    simpa [prefixWord, tailWord_4855231, baseEnd_4855231] using wordTrace_append hprefix tailTrace_4855231
  have hstable : (prefixWord ++ tailWord_4855231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855231).length < 2 ^ (prefixWord ++ tailWord_4855231).sum := by decide
  have hdescent : baseEnd_4855231 < baseStart_4855231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855264 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 5]
def baseStart_4855264 : Nat := 118140960795 + 4855264 * 2 ^ 59
def prefixEnd_4855264 : Nat := 4983230072969 + 3 ^ 40 * 4855264 * 2
def baseEnd_4855264 : Nat := 2493084136471396990971053

theorem tailTrace_4855264 : CollatzResearch.WordTrace tailWord_4855264 prefixEnd_4855264 2493084136471396990971053 := by
  unfold tailWord_4855264
  simp only [CollatzResearch.WordTrace]
  refine ⟨88543013141107607959642423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118057350854810143946189897 88543013141107607959642423)
  ·
    refine ⟨132814519711661411939463635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88543013141107607959642423 132814519711661411939463635)
    ·
      refine ⟨199221779567492117909195453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132814519711661411939463635 199221779567492117909195453)
      ·
        refine ⟨74708167337809544215948295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199221779567492117909195453 74708167337809544215948295)
        ·
          refine ⟨112062251006714316323922443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74708167337809544215948295 112062251006714316323922443)
          ·
            refine ⟨168093376510071474485883665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112062251006714316323922443 168093376510071474485883665)
            ·
              refine ⟨126070032382553605864412749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168093376510071474485883665 126070032382553605864412749)
              ·
                refine ⟨47276262143457602199154781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126070032382553605864412749 47276262143457602199154781)
                ·
                  refine ⟨17728598303796600824683043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47276262143457602199154781 17728598303796600824683043)
                  ·
                    refine ⟨26592897455694901237024565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17728598303796600824683043 26592897455694901237024565)
                    ·
                      refine ⟨2493084136471396990971053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26592897455694901237024565 2493084136471396990971053)
                      ·
                        rfl

theorem cell23_4855264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_4855264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855264 prefixEnd_4855264 := by exact prefixLift 4855264
  have htrace : WordTrace (prefixWord ++ tailWord_4855264) baseStart_4855264 baseEnd_4855264 := by
    simpa [prefixWord, tailWord_4855264, baseEnd_4855264] using wordTrace_append hprefix tailTrace_4855264
  have hstable : (prefixWord ++ tailWord_4855264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855264).length < 2 ^ (prefixWord ++ tailWord_4855264).sum := by decide
  have hdescent : baseEnd_4855264 < baseStart_4855264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855321 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 1, 9, 2]
def baseStart_4855321 : Nat := 118140960795 + 4855321 * 2 ^ 59
def prefixEnd_4855321 : Nat := 4983230072969 + 3 ^ 40 * 4855321 * 2
def baseEnd_4855321 : Nat := 2493113404868703267958291

theorem tailTrace_4855321 : CollatzResearch.WordTrace tailWord_4855321 prefixEnd_4855321 2493113404868703267958291 := by
  unfold tailWord_4855321
  simp only [CollatzResearch.WordTrace]
  refine ⟨177088105243008714654109817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118058736828672476436073211 177088105243008714654109817)
  ·
    refine ⟨132816078932256535990582363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177088105243008714654109817 132816078932256535990582363)
    ·
      refine ⟨199224118398384803985873545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132816078932256535990582363 199224118398384803985873545)
      ·
        refine ⟨149418088798788602989405159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199224118398384803985873545 149418088798788602989405159)
        ·
          refine ⟨224127133198182904484107739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149418088798788602989405159 224127133198182904484107739)
          ·
            refine ⟨336190699797274356726161609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224127133198182904484107739 336190699797274356726161609)
            ·
              refine ⟨252143024847955767544621207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 336190699797274356726161609 252143024847955767544621207)
              ·
                refine ⟨378214537271933651316931811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252143024847955767544621207 378214537271933651316931811)
                ·
                  refine ⟨567321805907900476975397717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 378214537271933651316931811 567321805907900476975397717)
                  ·
                    refine ⟨3324151206491604357277721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 567321805907900476975397717 3324151206491604357277721)
                    ·
                      refine ⟨2493113404868703267958291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3324151206491604357277721 2493113404868703267958291)
                      ·
                        rfl

theorem cell23_4855321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 9, 2].length) (baseStart_4855321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855321 prefixEnd_4855321 := by exact prefixLift 4855321
  have htrace : WordTrace (prefixWord ++ tailWord_4855321) baseStart_4855321 baseEnd_4855321 := by
    simpa [prefixWord, tailWord_4855321, baseEnd_4855321] using wordTrace_append hprefix tailTrace_4855321
  have hstable : (prefixWord ++ tailWord_4855321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855321).length < 2 ^ (prefixWord ++ tailWord_4855321).sum := by decide
  have hdescent : baseEnd_4855321 < baseStart_4855321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855328 : List Nat := [2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 3]
def baseStart_4855328 : Nat := 118140960795 + 4855328 * 2 ^ 59
def prefixEnd_4855328 : Nat := 4983230072969 + 3 ^ 40 * 4855328 * 2
def baseEnd_4855328 : Nat := 2493116999233284740570759

theorem tailTrace_4855328 : CollatzResearch.WordTrace tailWord_4855328 prefixEnd_4855328 2493116999233284740570759 := by
  unfold tailWord_4855328
  simp only [CollatzResearch.WordTrace]
  refine ⟨88544180276991677424807319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118058907035988903233076425 88544180276991677424807319)
  ·
    refine ⟨132816270415487516137210979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88544180276991677424807319 132816270415487516137210979)
    ·
      refine ⟨199224405623231274205816469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132816270415487516137210979 199224405623231274205816469)
      ·
        refine ⟨9338644013588965978397647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 199224405623231274205816469 9338644013588965978397647)
        ·
          refine ⟨14007966020383448967596471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9338644013588965978397647 14007966020383448967596471)
          ·
            refine ⟨21011949030575173451394707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14007966020383448967596471 21011949030575173451394707)
            ·
              refine ⟨31517923545862760177092061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21011949030575173451394707 31517923545862760177092061)
              ·
                refine ⟨11819221329698535066409523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31517923545862760177092061 11819221329698535066409523)
                ·
                  refine ⟨17728831994547802599614285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11819221329698535066409523 17728831994547802599614285)
                  ·
                    refine ⟨6648311997955425974855357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17728831994547802599614285 6648311997955425974855357)
                    ·
                      refine ⟨2493116999233284740570759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6648311997955425974855357 2493116999233284740570759)
                      ·
                        rfl

theorem cell23_4855328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_4855328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855328 prefixEnd_4855328 := by exact prefixLift 4855328
  have htrace : WordTrace (prefixWord ++ tailWord_4855328) baseStart_4855328 baseEnd_4855328 := by
    simpa [prefixWord, tailWord_4855328, baseEnd_4855328] using wordTrace_append hprefix tailTrace_4855328
  have hstable : (prefixWord ++ tailWord_4855328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855328).length < 2 ^ (prefixWord ++ tailWord_4855328).sum := by decide
  have hdescent : baseEnd_4855328 < baseStart_4855328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855344 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 3, 8]
def baseStart_4855344 : Nat := 118140960795 + 4855344 * 2 ^ 59
def prefixEnd_4855344 : Nat := 4983230072969 + 3 ^ 40 * 4855344 * 2
def baseEnd_4855344 : Nat := 831041738307918892656895

theorem tailTrace_4855344 : CollatzResearch.WordTrace tailWord_4855344 prefixEnd_4855344 831041738307918892656895 := by
  unfold tailWord_4855344
  simp only [CollatzResearch.WordTrace]
  refine ⟨88544472060962694791098543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118059296081283593054798057 88544472060962694791098543)
  ·
    refine ⟨132816708091444042186647815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88544472060962694791098543 132816708091444042186647815)
    ·
      refine ⟨199225062137166063279971723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132816708091444042186647815 199225062137166063279971723)
      ·
        refine ⟨298837593205749094919957585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199225062137166063279971723 298837593205749094919957585)
        ·
          refine ⟨224128194904311821189968189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298837593205749094919957585 224128194904311821189968189)
          ·
            refine ⟨84048073089116932946238071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224128194904311821189968189 84048073089116932946238071)
            ·
              refine ⟨126072109633675399419357107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84048073089116932946238071 126072109633675399419357107)
              ·
                refine ⟨189108164450513099129035661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126072109633675399419357107 189108164450513099129035661)
                ·
                  refine ⟨70915561668942412173388373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189108164450513099129035661 70915561668942412173388373)
                  ·
                    refine ⟨831041738307918892656895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70915561668942412173388373 831041738307918892656895)
                    ·
                      rfl

theorem cell23_4855344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 8].length) (baseStart_4855344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855344 prefixEnd_4855344 := by exact prefixLift 4855344
  have htrace : WordTrace (prefixWord ++ tailWord_4855344) baseStart_4855344 baseEnd_4855344 := by
    simpa [prefixWord, tailWord_4855344, baseEnd_4855344] using wordTrace_append hprefix tailTrace_4855344
  have hstable : (prefixWord ++ tailWord_4855344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855344).length < 2 ^ (prefixWord ++ tailWord_4855344).sum := by decide
  have hdescent : baseEnd_4855344 < baseStart_4855344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855361 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 4, 6]
def baseStart_4855361 : Nat := 118140960795 + 4855361 * 2 ^ 59
def prefixEnd_4855361 : Nat := 4983230072969 + 3 ^ 40 * 4855361 * 2
def baseEnd_4855361 : Nat := 831044648031627703819369

theorem tailTrace_4855361 : CollatzResearch.WordTrace tailWord_4855361 prefixEnd_4855361 831044648031627703819369 := by
  unfold tailWord_4855361
  simp only [CollatzResearch.WordTrace]
  refine ⟨177089564162863801485565937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118059709441909200990377291 177089564162863801485565937)
  ·
    refine ⟨132817173122147851114174453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177089564162863801485565937 132817173122147851114174453)
    ·
      refine ⟨12451609980201361041953855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 132817173122147851114174453 12451609980201361041953855)
      ·
        refine ⟨18677414970302041562930783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12451609980201361041953855 18677414970302041562930783)
        ·
          refine ⟨28016122455453062344396175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18677414970302041562930783 28016122455453062344396175)
          ·
            refine ⟨42024183683179593516594263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28016122455453062344396175 42024183683179593516594263)
            ·
              refine ⟨63036275524769390274891395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42024183683179593516594263 63036275524769390274891395)
              ·
                refine ⟨94554413287154085412337093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63036275524769390274891395 94554413287154085412337093)
                ·
                  refine ⟨17728952491341391014813205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94554413287154085412337093 17728952491341391014813205)
                  ·
                    refine ⟨831044648031627703819369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17728952491341391014813205 831044648031627703819369)
                    ·
                      rfl

theorem cell23_4855361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_4855361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855361 prefixEnd_4855361 := by exact prefixLift 4855361
  have htrace : WordTrace (prefixWord ++ tailWord_4855361) baseStart_4855361 baseEnd_4855361 := by
    simpa [prefixWord, tailWord_4855361, baseEnd_4855361] using wordTrace_append hprefix tailTrace_4855361
  have hstable : (prefixWord ++ tailWord_4855361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855361).length < 2 ^ (prefixWord ++ tailWord_4855361).sum := by decide
  have hdescent : baseEnd_4855361 < baseStart_4855361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855385 : List Nat := [1, 2, 1, 2, 2, 1, 1, 7, 2, 2, 2]
def baseStart_4855385 : Nat := 118140960795 + 4855385 * 2 ^ 59
def prefixEnd_4855385 : Nat := 4983230072969 + 3 ^ 40 * 4855385 * 2
def baseEnd_4855385 : Nat := 2493146267630591017557997

theorem tailTrace_4855385 : CollatzResearch.WordTrace tailWord_4855385 prefixEnd_4855385 2493146267630591017557997 := by
  unfold tailWord_4855385
  simp only [CollatzResearch.WordTrace]
  refine ⟨177090439514776853584439609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118060293009851235722959739 177090439514776853584439609)
  ·
    refine ⟨132817829636082640188329707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177090439514776853584439609 132817829636082640188329707)
    ·
      refine ⟨199226744454123960282494561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132817829636082640188329707 199226744454123960282494561)
      ·
        refine ⟨149420058340592970211870921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199226744454123960282494561 149420058340592970211870921)
        ·
          refine ⟨112065043755444727658903191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149420058340592970211870921 112065043755444727658903191)
          ·
            refine ⟨168097565633167091488354787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112065043755444727658903191 168097565633167091488354787)
            ·
              refine ⟨252146348449750637232532181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168097565633167091488354787 252146348449750637232532181)
              ·
                refine ⟨5909680041791030560137473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 252146348449750637232532181 5909680041791030560137473)
                ·
                  refine ⟨4432260031343272920103105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5909680041791030560137473 4432260031343272920103105)
                  ·
                    refine ⟨3324195023507454690077329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4432260031343272920103105 3324195023507454690077329)
                    ·
                      refine ⟨2493146267630591017557997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3324195023507454690077329 2493146267630591017557997)
                      ·
                        rfl

theorem cell23_4855385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 2, 2].length) (baseStart_4855385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855385 prefixEnd_4855385 := by exact prefixLift 4855385
  have htrace : WordTrace (prefixWord ++ tailWord_4855385) baseStart_4855385 baseEnd_4855385 := by
    simpa [prefixWord, tailWord_4855385, baseEnd_4855385] using wordTrace_append hprefix tailTrace_4855385
  have hstable : (prefixWord ++ tailWord_4855385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855385).length < 2 ^ (prefixWord ++ tailWord_4855385).sum := by decide
  have hdescent : baseEnd_4855385 < baseStart_4855385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855401 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 1, 5, 3]
def baseStart_4855401 : Nat := 118140960795 + 4855401 * 2 ^ 59
def prefixEnd_4855401 : Nat := 4983230072969 + 3 ^ 40 * 4855401 * 2
def baseEnd_4855401 : Nat := 2493154483321062954957923

theorem tailTrace_4855401 : CollatzResearch.WordTrace tailWord_4855401 prefixEnd_4855401 2493154483321062954957923 := by
  unfold tailWord_4855401
  simp only [CollatzResearch.WordTrace]
  refine ⟨177091023082718888317022057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118060682055145925544681371 177091023082718888317022057)
  ·
    refine ⟨132818267312039166237766543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177091023082718888317022057 132818267312039166237766543)
    ·
      refine ⟨199227400968058749356649815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132818267312039166237766543 199227400968058749356649815)
      ·
        refine ⟨298841101452088124034974723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199227400968058749356649815 298841101452088124034974723)
        ·
          refine ⟨448261652178132186052462085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298841101452088124034974723 448261652178132186052462085)
          ·
            refine ⟨84049059783399784884836641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 448261652178132186052462085 84049059783399784884836641)
            ·
              refine ⟨63036794837549838663627481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84049059783399784884836641 63036794837549838663627481)
              ·
                refine ⟨47277596128162378997720611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63036794837549838663627481 47277596128162378997720611)
                ·
                  refine ⟨70916394192243568496580917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47277596128162378997720611 70916394192243568496580917)
                  ·
                    refine ⟨6648411955522834546554461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70916394192243568496580917 6648411955522834546554461)
                    ·
                      refine ⟨2493154483321062954957923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6648411955522834546554461 2493154483321062954957923)
                      ·
                        rfl

theorem cell23_4855401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 5, 3].length) (baseStart_4855401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855401 prefixEnd_4855401 := by exact prefixLift 4855401
  have htrace : WordTrace (prefixWord ++ tailWord_4855401) baseStart_4855401 baseEnd_4855401 := by
    simpa [prefixWord, tailWord_4855401, baseEnd_4855401] using wordTrace_append hprefix tailTrace_4855401
  have hstable : (prefixWord ++ tailWord_4855401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855401).length < 2 ^ (prefixWord ++ tailWord_4855401).sum := by decide
  have hdescent : baseEnd_4855401 < baseStart_4855401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855431 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 7]
def baseStart_4855431 : Nat := 118140960795 + 4855431 * 2 ^ 59
def prefixEnd_4855431 : Nat := 4983230072969 + 3 ^ 40 * 4855431 * 2
def baseEnd_4855431 : Nat := 2493169887740697837582785

theorem tailTrace_4855431 : CollatzResearch.WordTrace tailWord_4855431 prefixEnd_4855431 2493169887740697837582785 := by
  unfold tailWord_4855431
  simp only [CollatzResearch.WordTrace]
  refine ⟨177092117272610203440614147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118061411515073468960409431 177092117272610203440614147)
  ·
    refine ⟨265638175908915305160921221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177092117272610203440614147 265638175908915305160921221)
    ·
      refine ⟨49807157982921619717672729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 265638175908915305160921221 49807157982921619717672729)
      ·
        refine ⟨37355368487191214788254547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49807157982921619717672729 37355368487191214788254547)
        ·
          refine ⟨56033052730786822182381821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37355368487191214788254547 56033052730786822182381821)
          ·
            refine ⟨21012394774045058318393183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56033052730786822182381821 21012394774045058318393183)
            ·
              refine ⟨31518592161067587477589775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21012394774045058318393183 31518592161067587477589775)
              ·
                refine ⟨47277888241601381216384663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31518592161067587477589775 47277888241601381216384663)
                ·
                  refine ⟨70916832362402071824576995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47277888241601381216384663 70916832362402071824576995)
                  ·
                    refine ⟨106375248543603107736865493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70916832362402071824576995 106375248543603107736865493)
                    ·
                      refine ⟨2493169887740697837582785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 106375248543603107736865493 2493169887740697837582785)
                      ·
                        rfl

theorem cell23_4855431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_4855431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855431 prefixEnd_4855431 := by exact prefixLift 4855431
  have htrace : WordTrace (prefixWord ++ tailWord_4855431) baseStart_4855431 baseEnd_4855431 := by
    simpa [prefixWord, tailWord_4855431, baseEnd_4855431] using wordTrace_append hprefix tailTrace_4855431
  have hstable : (prefixWord ++ tailWord_4855431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855431).length < 2 ^ (prefixWord ++ tailWord_4855431).sum := by decide
  have hdescent : baseEnd_4855431 < baseStart_4855431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855441 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 4]
def baseStart_4855441 : Nat := 118140960795 + 4855441 * 2 ^ 59
def prefixEnd_4855441 : Nat := 4983230072969 + 3 ^ 40 * 4855441 * 2
def baseEnd_4855441 : Nat := 2493175022547242798457739

theorem tailTrace_4855441 : CollatzResearch.WordTrace tailWord_4855441 prefixEnd_4855441 2493175022547242798457739 := by
  unfold tailWord_4855441
  simp only [CollatzResearch.WordTrace]
  refine ⟨177092482002573975148478177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118061654668382650098985451 177092482002573975148478177)
  ·
    refine ⟨132819361501930481361358633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177092482002573975148478177 132819361501930481361358633)
    ·
      refine ⟨99614521126447861021018975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132819361501930481361358633 99614521126447861021018975)
      ·
        refine ⟨149421781689671791531528463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99614521126447861021018975 149421781689671791531528463)
        ·
          refine ⟨224132672534507687297292695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149421781689671791531528463 224132672534507687297292695)
          ·
            refine ⟨336199008801761530945939043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224132672534507687297292695 336199008801761530945939043)
            ·
              refine ⟨504298513202642296418908565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336199008801761530945939043 504298513202642296418908565)
              ·
                refine ⟨23638992806373857644636339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 504298513202642296418908565 23638992806373857644636339)
                ·
                  refine ⟨35458489209560786466954509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23638992806373857644636339 35458489209560786466954509)
                  ·
                    refine ⟨13296933453585294925107941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35458489209560786466954509 13296933453585294925107941)
                    ·
                      refine ⟨2493175022547242798457739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13296933453585294925107941 2493175022547242798457739)
                      ·
                        rfl

theorem cell23_4855441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_4855441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855441 prefixEnd_4855441 := by exact prefixLift 4855441
  have htrace : WordTrace (prefixWord ++ tailWord_4855441) baseStart_4855441 baseEnd_4855441 := by
    simpa [prefixWord, tailWord_4855441, baseEnd_4855441] using wordTrace_append hprefix tailTrace_4855441
  have hstable : (prefixWord ++ tailWord_4855441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855441).length < 2 ^ (prefixWord ++ tailWord_4855441).sum := by decide
  have hdescent : baseEnd_4855441 < baseStart_4855441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855471 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 6]
def baseStart_4855471 : Nat := 118140960795 + 4855471 * 2 ^ 59
def prefixEnd_4855471 : Nat := 4983230072969 + 3 ^ 40 * 4855471 * 2
def baseEnd_4855471 : Nat := 2493190426966877681082601

theorem tailTrace_4855471 : CollatzResearch.WordTrace tailWord_4855471 prefixEnd_4855471 2493190426966877681082601 := by
  unfold tailWord_4855471
  simp only [CollatzResearch.WordTrace]
  refine ⟨177093576192465290272070267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118062384128310193514713511 177093576192465290272070267)
  ·
    refine ⟨265640364288697935408105401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177093576192465290272070267 265640364288697935408105401)
    ·
      refine ⟨199230273216523451556079051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265640364288697935408105401 199230273216523451556079051)
      ·
        refine ⟨298845409824785177334118577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199230273216523451556079051 298845409824785177334118577)
        ·
          refine ⟨224134057368588883000588933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298845409824785177334118577 224134057368588883000588933)
          ·
            refine ⟨42025135756610415562610425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 224134057368588883000588933 42025135756610415562610425)
            ·
              refine ⟨31518851817457811671957819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42025135756610415562610425 31518851817457811671957819)
              ·
                refine ⟨47278277726186717507936729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31518851817457811671957819 47278277726186717507936729)
                ·
                  refine ⟨35458708294640038130952547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47278277726186717507936729 35458708294640038130952547)
                  ·
                    refine ⟨53188062441960057196428821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35458708294640038130952547 53188062441960057196428821)
                    ·
                      refine ⟨2493190426966877681082601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53188062441960057196428821 2493190426966877681082601)
                      ·
                        rfl

theorem cell23_4855471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_4855471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855471 prefixEnd_4855471 := by exact prefixLift 4855471
  have htrace : WordTrace (prefixWord ++ tailWord_4855471) baseStart_4855471 baseEnd_4855471 := by
    simpa [prefixWord, tailWord_4855471, baseEnd_4855471] using wordTrace_append hprefix tailTrace_4855471
  have hstable : (prefixWord ++ tailWord_4855471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855471).length < 2 ^ (prefixWord ++ tailWord_4855471).sum := by decide
  have hdescent : baseEnd_4855471 < baseStart_4855471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855481 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 8]
def baseStart_4855481 : Nat := 118140960795 + 4855481 * 2 ^ 59
def prefixEnd_4855481 : Nat := 4983230072969 + 3 ^ 40 * 4855481 * 2
def baseEnd_4855481 : Nat := 277021729085935849106395

theorem tailTrace_4855481 : CollatzResearch.WordTrace tailWord_4855481 prefixEnd_4855481 277021729085935849106395 := by
  unfold tailWord_4855481
  simp only [CollatzResearch.WordTrace]
  refine ⟨177093940922429061979934297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118062627281619374653289531 177093940922429061979934297)
  ·
    refine ⟨132820455691821796484950723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177093940922429061979934297 132820455691821796484950723)
    ·
      refine ⟨199230683537732694727426085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132820455691821796484950723 199230683537732694727426085)
      ·
        refine ⟨37355753163324880261392391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199230683537732694727426085 37355753163324880261392391)
        ·
          refine ⟨56033629744987320392088587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37355753163324880261392391 56033629744987320392088587)
          ·
            refine ⟨84050444617480980588132881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56033629744987320392088587 84050444617480980588132881)
            ·
              refine ⟨63037833463110735441099661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84050444617480980588132881 63037833463110735441099661)
              ·
                refine ⟨23639187548666525790412373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63037833463110735441099661 23639187548666525790412373)
                ·
                  refine ⟨277021729085935849106395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23639187548666525790412373 277021729085935849106395)
                  ·
                    rfl

theorem cell23_4855481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 8].length) (baseStart_4855481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855481 prefixEnd_4855481 := by exact prefixLift 4855481
  have htrace : WordTrace (prefixWord ++ tailWord_4855481) baseStart_4855481 baseEnd_4855481 := by
    simpa [prefixWord, tailWord_4855481, baseEnd_4855481] using wordTrace_append hprefix tailTrace_4855481
  have hstable : (prefixWord ++ tailWord_4855481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855481).length < 2 ^ (prefixWord ++ tailWord_4855481).sum := by decide
  have hdescent : baseEnd_4855481 < baseStart_4855481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855525 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 5, 1, 3]
def baseStart_4855525 : Nat := 118140960795 + 4855525 * 2 ^ 59
def prefixEnd_4855525 : Nat := 4983230072969 + 3 ^ 40 * 4855525 * 2
def baseEnd_4855525 : Nat := 2493218154922220469807353

theorem tailTrace_4855525 : CollatzResearch.WordTrace tailWord_4855525 prefixEnd_4855525 2493218154922220469807353 := by
  unfold tailWord_4855525
  simp only [CollatzResearch.WordTrace]
  refine ⟨177095545734269657494536029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118063697156179771663024019 177095545734269657494536029)
  ·
    refine ⟨66410829650351121560451011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177095545734269657494536029 66410829650351121560451011)
    ·
      refine ⟨99616244475526682340676517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66410829650351121560451011 99616244475526682340676517)
      ·
        refine ⟨18678045839161252938876847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99616244475526682340676517 18678045839161252938876847)
        ·
          refine ⟨28017068758741879408315271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18678045839161252938876847 28017068758741879408315271)
          ·
            refine ⟨42025603138112819112472907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28017068758741879408315271 42025603138112819112472907)
            ·
              refine ⟨63038404707169228668709361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42025603138112819112472907 63038404707169228668709361)
              ·
                refine ⟨47278803530376921501532021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63038404707169228668709361 47278803530376921501532021)
                ·
                  refine ⟨4432387830972836390768627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47278803530376921501532021 4432387830972836390768627)
                  ·
                    refine ⟨6648581746459254586152941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4432387830972836390768627 6648581746459254586152941)
                    ·
                      refine ⟨2493218154922220469807353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6648581746459254586152941 2493218154922220469807353)
                      ·
                        rfl

theorem cell23_4855525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_4855525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855525 prefixEnd_4855525 := by exact prefixLift 4855525
  have htrace : WordTrace (prefixWord ++ tailWord_4855525) baseStart_4855525 baseEnd_4855525 := by
    simpa [prefixWord, tailWord_4855525, baseEnd_4855525] using wordTrace_append hprefix tailTrace_4855525
  have hstable : (prefixWord ++ tailWord_4855525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855525).length < 2 ^ (prefixWord ++ tailWord_4855525).sum := by decide
  have hdescent : baseEnd_4855525 < baseStart_4855525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855535 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 4, 3, 2]
def baseStart_4855535 : Nat := 118140960795 + 4855535 * 2 ^ 59
def prefixEnd_4855535 : Nat := 4983230072969 + 3 ^ 40 * 4855535 * 2
def baseEnd_4855535 : Nat := 2493223289728765430682307

theorem tailTrace_4855535 : CollatzResearch.WordTrace tailWord_4855535 prefixEnd_4855535 2493223289728765430682307 := by
  unfold tailWord_4855535
  simp only [CollatzResearch.WordTrace]
  refine ⟨177095910464233429202400059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118063940309488952801600039 177095910464233429202400059)
  ·
    refine ⟨265643865696350143803600089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177095910464233429202400059 265643865696350143803600089)
    ·
      refine ⟨199232899272262607852700067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265643865696350143803600089 199232899272262607852700067)
      ·
        refine ⟨298849348908393911779050101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199232899272262607852700067 298849348908393911779050101)
        ·
          refine ⟨28017126460161929229285947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 298849348908393911779050101 28017126460161929229285947)
          ·
            refine ⟨42025689690242893843928921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28017126460161929229285947 42025689690242893843928921)
            ·
              refine ⟨31519267267682170382946691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42025689690242893843928921 31519267267682170382946691)
              ·
                refine ⟨47278900901523255574420037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31519267267682170382946691 47278900901523255574420037)
                ·
                  refine ⟨8864793919035610420203757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47278900901523255574420037 8864793919035610420203757)
                  ·
                    refine ⟨3324297719638353907576409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8864793919035610420203757 3324297719638353907576409)
                    ·
                      refine ⟨2493223289728765430682307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3324297719638353907576409 2493223289728765430682307)
                      ·
                        rfl

theorem cell23_4855535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 3, 2].length) (baseStart_4855535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855535 prefixEnd_4855535 := by exact prefixLift 4855535
  have htrace : WordTrace (prefixWord ++ tailWord_4855535) baseStart_4855535 baseEnd_4855535 := by
    simpa [prefixWord, tailWord_4855535, baseEnd_4855535] using wordTrace_append hprefix tailTrace_4855535
  have hstable : (prefixWord ++ tailWord_4855535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855535).length < 2 ^ (prefixWord ++ tailWord_4855535).sum := by decide
  have hdescent : baseEnd_4855535 < baseStart_4855535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855542 : List Nat := [5, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3]
def baseStart_4855542 : Nat := 118140960795 + 4855542 * 2 ^ 59
def prefixEnd_4855542 : Nat := 4983230072969 + 3 ^ 40 * 4855542 * 2
def baseEnd_4855542 : Nat := 2493226884093346903294775

theorem tailTrace_4855542 : CollatzResearch.WordTrace tailWord_4855542 prefixEnd_4855542 2493226884093346903294775 := by
  unfold tailWord_4855542
  simp only [CollatzResearch.WordTrace]
  refine ⟨11068510360950504337369055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118064110516805379598603253 11068510360950504337369055)
  ·
    refine ⟨16602765541425756506053583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11068510360950504337369055 16602765541425756506053583)
    ·
      refine ⟨24904148312138634759080375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16602765541425756506053583 24904148312138634759080375)
      ·
        refine ⟨37356222468207952138620563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24904148312138634759080375 37356222468207952138620563)
        ·
          refine ⟨56034333702311928207930845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37356222468207952138620563 56034333702311928207930845)
          ·
            refine ⟨21012875138366973077974067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56034333702311928207930845 21012875138366973077974067)
            ·
              refine ⟨31519312707550459616961101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21012875138366973077974067 31519312707550459616961101)
              ·
                refine ⟨11819742265331422356360413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31519312707550459616961101 11819742265331422356360413)
                ·
                  refine ⟨4432403349499283383635155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11819742265331422356360413 4432403349499283383635155)
                  ·
                    refine ⟨6648605024248925075452733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4432403349499283383635155 6648605024248925075452733)
                    ·
                      refine ⟨2493226884093346903294775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6648605024248925075452733 2493226884093346903294775)
                      ·
                        rfl

theorem cell23_4855542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_4855542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855542 prefixEnd_4855542 := by exact prefixLift 4855542
  have htrace : WordTrace (prefixWord ++ tailWord_4855542) baseStart_4855542 baseEnd_4855542 := by
    simpa [prefixWord, tailWord_4855542, baseEnd_4855542] using wordTrace_append hprefix tailTrace_4855542
  have hstable : (prefixWord ++ tailWord_4855542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855542).length < 2 ^ (prefixWord ++ tailWord_4855542).sum := by decide
  have hdescent : baseEnd_4855542 < baseStart_4855542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855575 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 4, 4]
def baseStart_4855575 : Nat := 118140960795 + 4855575 * 2 ^ 59
def prefixEnd_4855575 : Nat := 4983230072969 + 3 ^ 40 * 4855575 * 2
def baseEnd_4855575 : Nat := 831081276318315091394041

theorem tailTrace_4855575 : CollatzResearch.WordTrace tailWord_4855575 prefixEnd_4855575 831081276318315091394041 := by
  unfold tailWord_4855575
  simp only [CollatzResearch.WordTrace]
  refine ⟨177097369384088516033856179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118064912922725677355904119 177097369384088516033856179)
  ·
    refine ⟨265646054076132774050784269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177097369384088516033856179 265646054076132774050784269)
    ·
      refine ⟨99617270278549790269044101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265646054076132774050784269 99617270278549790269044101)
      ·
        refine ⟨18678238177228085675445769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99617270278549790269044101 18678238177228085675445769)
        ·
          refine ⟨14008678632921064256584327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18678238177228085675445769 14008678632921064256584327)
          ·
            refine ⟨21013017949381596384876491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14008678632921064256584327 21013017949381596384876491)
            ·
              refine ⟨31519526924072394577314737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21013017949381596384876491 31519526924072394577314737)
              ·
                refine ⟨23639645193054295932986053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31519526924072394577314737 23639645193054295932986053)
                ·
                  refine ⟨4432433473697680487434885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23639645193054295932986053 4432433473697680487434885)
                  ·
                    refine ⟨831081276318315091394041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4432433473697680487434885 831081276318315091394041)
                    ·
                      rfl

theorem cell23_4855575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 4].length) (baseStart_4855575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855575 prefixEnd_4855575 := by exact prefixLift 4855575
  have htrace : WordTrace (prefixWord ++ tailWord_4855575) baseStart_4855575 baseEnd_4855575 := by
    simpa [prefixWord, tailWord_4855575, baseEnd_4855575] using wordTrace_append hprefix tailTrace_4855575
  have hstable : (prefixWord ++ tailWord_4855575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855575).length < 2 ^ (prefixWord ++ tailWord_4855575).sum := by decide
  have hdescent : baseEnd_4855575 < baseStart_4855575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855585 : List Nat := [1, 2, 3, 2, 1, 4, 2, 1, 1, 1, 5]
def baseStart_4855585 : Nat := 118140960795 + 4855585 * 2 ^ 59
def prefixEnd_4855585 : Nat := 4983230072969 + 3 ^ 40 * 4855585 * 2
def baseEnd_4855585 : Nat := 2493248963761490235057077

theorem tailTrace_4855585 : CollatzResearch.WordTrace tailWord_4855585 prefixEnd_4855585 2493248963761490235057077 := by
  unfold tailWord_4855585
  simp only [CollatzResearch.WordTrace]
  refine ⟨177097734114052287741720209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118065156076034858494480139 177097734114052287741720209)
  ·
    refine ⟨132823300585539215806290157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177097734114052287741720209 132823300585539215806290157)
    ·
      refine ⟨49808737719577205927358809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132823300585539215806290157 49808737719577205927358809)
      ·
        refine ⟨37356553289682904445519107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49808737719577205927358809 37356553289682904445519107)
        ·
          refine ⟨56034829934524356668278661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37356553289682904445519107 56034829934524356668278661)
          ·
            refine ⟨10506530612723316875302249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56034829934524356668278661 10506530612723316875302249)
            ·
              refine ⟨7879897959542487656476687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10506530612723316875302249 7879897959542487656476687)
              ·
                refine ⟨11819846939313731484715031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7879897959542487656476687 11819846939313731484715031)
                ·
                  refine ⟨17729770408970597227072547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11819846939313731484715031 17729770408970597227072547)
                  ·
                    refine ⟨26594655613455895840608821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17729770408970597227072547 26594655613455895840608821)
                    ·
                      refine ⟨2493248963761490235057077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26594655613455895840608821 2493248963761490235057077)
                      ·
                        rfl

theorem cell23_4855585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_4855585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855585 prefixEnd_4855585 := by exact prefixLift 4855585
  have htrace : WordTrace (prefixWord ++ tailWord_4855585) baseStart_4855585 baseEnd_4855585 := by
    simpa [prefixWord, tailWord_4855585, baseEnd_4855585] using wordTrace_append hprefix tailTrace_4855585
  have hstable : (prefixWord ++ tailWord_4855585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855585).length < 2 ^ (prefixWord ++ tailWord_4855585).sum := by decide
  have hdescent : baseEnd_4855585 < baseStart_4855585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855588 : List Nat := [2, 3, 1, 3, 2, 1, 11]
def baseStart_4855588 : Nat := 118140960795 + 4855588 * 2 ^ 59
def prefixEnd_4855588 : Nat := 4983230072969 + 3 ^ 40 * 4855588 * 2
def baseEnd_4855588 : Nat := 30780870422264860781723

theorem tailTrace_4855588 : CollatzResearch.WordTrace tailWord_4855588 prefixEnd_4855588 30780870422264860781723 := by
  unfold tailWord_4855588
  simp only [CollatzResearch.WordTrace]
  refine ⟨88548921766520709627039709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118065229022027612836052945 88548921766520709627039709)
  ·
    refine ⟨33205845662445266110139891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88548921766520709627039709 33205845662445266110139891)
    ·
      refine ⟨49808768493667899165209837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33205845662445266110139891 49808768493667899165209837)
      ·
        refine ⟨18678288185125462186953689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49808768493667899165209837 18678288185125462186953689)
        ·
          refine ⟨14008716138844096640215267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18678288185125462186953689 14008716138844096640215267)
          ·
            refine ⟨21013074208266144960322901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14008716138844096640215267 21013074208266144960322901)
            ·
              refine ⟨30780870422264860781723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 21013074208266144960322901 30780870422264860781723)
              ·
                rfl

theorem cell23_4855588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 11].length) (baseStart_4855588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855588 prefixEnd_4855588 := by exact prefixLift 4855588
  have htrace : WordTrace (prefixWord ++ tailWord_4855588) baseStart_4855588 baseEnd_4855588 := by
    simpa [prefixWord, tailWord_4855588, baseEnd_4855588] using wordTrace_append hprefix tailTrace_4855588
  have hstable : (prefixWord ++ tailWord_4855588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855588).length < 2 ^ (prefixWord ++ tailWord_4855588).sum := by decide
  have hdescent : baseEnd_4855588 < baseStart_4855588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855605 : List Nat := [1, 3, 3, 1, 4, 1, 2, 8]
def baseStart_4855605 : Nat := 118140960795 + 4855605 * 2 ^ 59
def prefixEnd_4855605 : Nat := 4983230072969 + 3 ^ 40 * 4855605 * 2
def baseEnd_4855605 : Nat := 92342934569428894696555

theorem tailTrace_4855605 : CollatzResearch.WordTrace tailWord_4855605 prefixEnd_4855605 92342934569428894696555 := by
  unfold tailWord_4855605
  simp only [CollatzResearch.WordTrace]
  refine ⟨177098463573979831157448269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118065642382653220771632179 177098463573979831157448269)
  ·
    refine ⟨66411923840242436684043101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177098463573979831157448269 66411923840242436684043101)
    ·
      refine ⟨24904471440090913756516163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66411923840242436684043101 24904471440090913756516163)
      ·
        refine ⟨37356707160136370634774245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24904471440090913756516163 37356707160136370634774245)
        ·
          refine ⟨7004382592525569494020171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37356707160136370634774245 7004382592525569494020171)
          ·
            refine ⟨10506573888788354241030257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7004382592525569494020171 10506573888788354241030257)
            ·
              refine ⟨7879930416591265680772693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10506573888788354241030257 7879930416591265680772693)
              ·
                refine ⟨92342934569428894696555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7879930416591265680772693 92342934569428894696555)
                ·
                  rfl

theorem cell23_4855605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 8].length) (baseStart_4855605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855605 prefixEnd_4855605 := by exact prefixLift 4855605
  have htrace : WordTrace (prefixWord ++ tailWord_4855605) baseStart_4855605 baseEnd_4855605 := by
    simpa [prefixWord, tailWord_4855605, baseEnd_4855605] using wordTrace_append hprefix tailTrace_4855605
  have hstable : (prefixWord ++ tailWord_4855605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855605).length < 2 ^ (prefixWord ++ tailWord_4855605).sum := by decide
  have hdescent : baseEnd_4855605 < baseStart_4855605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855609 : List Nat := [1, 2, 1, 7, 1, 1, 1, 3, 2, 4]
def baseStart_4855609 : Nat := 118140960795 + 4855609 * 2 ^ 59
def prefixEnd_4855609 : Nat := 4983230072969 + 3 ^ 40 * 4855609 * 2
def baseEnd_4855609 : Nat := 831087095765732713718989

theorem tailTrace_4855609 : CollatzResearch.WordTrace tailWord_4855609 prefixEnd_4855609 831087095765732713718989 := by
  unfold tailWord_4855609
  simp only [CollatzResearch.WordTrace]
  refine ⟨177098609465965339840593881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118065739643976893227062587 177098609465965339840593881)
  ·
    refine ⟨132823957099474004880445411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177098609465965339840593881 132823957099474004880445411)
    ·
      refine ⟨199235935649211007320668117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132823957099474004880445411 199235935649211007320668117)
      ·
        refine ⟨4669592241778382984078159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 199235935649211007320668117 4669592241778382984078159)
        ·
          refine ⟨7004388362667574476117239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4669592241778382984078159 7004388362667574476117239)
          ·
            refine ⟨10506582544001361714175859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7004388362667574476117239 10506582544001361714175859)
            ·
              refine ⟨15759873816002042571263789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10506582544001361714175859 15759873816002042571263789)
              ·
                refine ⟨5909952681000765964223921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15759873816002042571263789 5909952681000765964223921)
                ·
                  refine ⟨4432464510750574473167941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5909952681000765964223921 4432464510750574473167941)
                  ·
                    refine ⟨831087095765732713718989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4432464510750574473167941 831087095765732713718989)
                    ·
                      rfl

theorem cell23_4855609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 4].length) (baseStart_4855609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855609 prefixEnd_4855609 := by exact prefixLift 4855609
  have htrace : WordTrace (prefixWord ++ tailWord_4855609) baseStart_4855609 baseEnd_4855609 := by
    simpa [prefixWord, tailWord_4855609, baseEnd_4855609] using wordTrace_append hprefix tailTrace_4855609
  have hstable : (prefixWord ++ tailWord_4855609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855609).length < 2 ^ (prefixWord ++ tailWord_4855609).sum := by decide
  have hdescent : baseEnd_4855609 < baseStart_4855609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855622 : List Nat := [6, 1, 1, 2, 1, 1, 2, 9]
def baseStart_4855622 : Nat := 118140960795 + 4855622 * 2 ^ 59
def prefixEnd_4855622 : Nat := 4983230072969 + 3 ^ 40 * 4855622 * 2
def baseEnd_4855622 : Nat := 92343257872063207047941

theorem tailTrace_4855622 : CollatzResearch.WordTrace tailWord_4855622 prefixEnd_4855622 92343257872063207047941 := by
  unfold tailWord_4855622
  simp only [CollatzResearch.WordTrace]
  refine ⟨5534346362966195095650535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 118066055743278828707211413 5534346362966195095650535)
  ·
    refine ⟨8301519544449292643475803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5534346362966195095650535 8301519544449292643475803)
    ·
      refine ⟨12452279316673938965213705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8301519544449292643475803 12452279316673938965213705)
      ·
        refine ⟨9339209487505454223910279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12452279316673938965213705 9339209487505454223910279)
        ·
          refine ⟨14008814231258181335865419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9339209487505454223910279 14008814231258181335865419)
          ·
            refine ⟨21013221346887272003798129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14008814231258181335865419 21013221346887272003798129)
            ·
              refine ⟨15759916010165454002848597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21013221346887272003798129 15759916010165454002848597)
              ·
                refine ⟨92343257872063207047941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15759916010165454002848597 92343257872063207047941)
                ·
                  rfl

theorem cell23_4855622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_4855622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855622 prefixEnd_4855622 := by exact prefixLift 4855622
  have htrace : WordTrace (prefixWord ++ tailWord_4855622) baseStart_4855622 baseEnd_4855622 := by
    simpa [prefixWord, tailWord_4855622, baseEnd_4855622] using wordTrace_append hprefix tailTrace_4855622
  have hstable : (prefixWord ++ tailWord_4855622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855622).length < 2 ^ (prefixWord ++ tailWord_4855622).sum := by decide
  have hdescent : baseEnd_4855622 < baseStart_4855622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855650 : List Nat := [3, 3, 2, 1, 2, 3, 2, 2, 1, 2, 2]
def baseStart_4855650 : Nat := 118140960795 + 4855650 * 2 ^ 59
def prefixEnd_4855650 : Nat := 4983230072969 + 3 ^ 40 * 4855650 * 2
def baseEnd_4855650 : Nat := 2493282340004032480744279

theorem tailTrace_4855650 : CollatzResearch.WordTrace tailWord_4855650 prefixEnd_4855650 2493282340004032480744279 := by
  unfold tailWord_4855650
  simp only [CollatzResearch.WordTrace]
  refine ⟨44275026214704200960709101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118066736572544535895224269 44275026214704200960709101)
  ·
    refine ⟨16603134830514075360265913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44275026214704200960709101 16603134830514075360265913)
    ·
      refine ⟨12452351122885556520199435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16603134830514075360265913 12452351122885556520199435)
      ·
        refine ⟨18678526684328334780299153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12452351122885556520199435 18678526684328334780299153)
        ·
          refine ⟨14008895013246251085224365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18678526684328334780299153 14008895013246251085224365)
          ·
            refine ⟨5253335629967344156959137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14008895013246251085224365 5253335629967344156959137)
            ·
              refine ⟨3940001722475508117719353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5253335629967344156959137 3940001722475508117719353)
              ·
                refine ⟨2955001291856631088289515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3940001722475508117719353 2955001291856631088289515)
                ·
                  refine ⟨4432501937784946632434273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2955001291856631088289515 4432501937784946632434273)
                  ·
                    refine ⟨3324376453338709974325705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4432501937784946632434273 3324376453338709974325705)
                    ·
                      refine ⟨2493282340004032480744279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3324376453338709974325705 2493282340004032480744279)
                      ·
                        rfl

theorem cell23_4855650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_4855650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855650 prefixEnd_4855650 := by exact prefixLift 4855650
  have htrace : WordTrace (prefixWord ++ tailWord_4855650) baseStart_4855650 baseEnd_4855650 := by
    simpa [prefixWord, tailWord_4855650, baseEnd_4855650] using wordTrace_append hprefix tailTrace_4855650
  have hstable : (prefixWord ++ tailWord_4855650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855650).length < 2 ^ (prefixWord ++ tailWord_4855650).sum := by decide
  have hdescent : baseEnd_4855650 < baseStart_4855650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855705 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 2, 3, 3]
def baseStart_4855705 : Nat := 118140960795 + 4855705 * 2 ^ 59
def prefixEnd_4855705 : Nat := 4983230072969 + 3 ^ 40 * 4855705 * 2
def baseEnd_4855705 : Nat := 2493310581440029765556525

theorem tailTrace_4855705 : CollatzResearch.WordTrace tailWord_4855705 prefixEnd_4855705 2493310581440029765556525 := by
  unfold tailWord_4855705
  simp only [CollatzResearch.WordTrace]
  refine ⟨177102110873617548236088569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118068073915745032157392379 177102110873617548236088569)
  ·
    refine ⟨132826583155213161177066427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177102110873617548236088569 132826583155213161177066427)
    ·
      refine ⟨199239874732819741765599641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132826583155213161177066427 199239874732819741765599641)
      ·
        refine ⟨149429906049614806324199731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199239874732819741765599641 149429906049614806324199731)
        ·
          refine ⟨224144859074422209486299597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149429906049614806324199731 224144859074422209486299597)
          ·
            refine ⟨84054322152908328557362349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224144859074422209486299597 84054322152908328557362349)
            ·
              refine ⟨31520370807340623209010881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84054322152908328557362349 31520370807340623209010881)
              ·
                refine ⟨23640278105505467406758161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31520370807340623209010881 23640278105505467406758161)
                ·
                  refine ⟨17730208579129100555068621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23640278105505467406758161 17730208579129100555068621)
                  ·
                    refine ⟨6648828217173412708150733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17730208579129100555068621 6648828217173412708150733)
                    ·
                      refine ⟨2493310581440029765556525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6648828217173412708150733 2493310581440029765556525)
                      ·
                        rfl

theorem cell23_4855705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 3, 3].length) (baseStart_4855705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855705 prefixEnd_4855705 := by exact prefixLift 4855705
  have htrace : WordTrace (prefixWord ++ tailWord_4855705) baseStart_4855705 baseEnd_4855705 := by
    simpa [prefixWord, tailWord_4855705, baseEnd_4855705] using wordTrace_append hprefix tailTrace_4855705
  have hstable : (prefixWord ++ tailWord_4855705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855705).length < 2 ^ (prefixWord ++ tailWord_4855705).sum := by decide
  have hdescent : baseEnd_4855705 < baseStart_4855705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855706 : List Nat := [3, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2]
def baseStart_4855706 : Nat := 118140960795 + 4855706 * 2 ^ 59
def prefixEnd_4855706 : Nat := 4983230072969 + 3 ^ 40 * 4855706 * 2
def baseEnd_4855706 : Nat := 2493311094920684261644021

theorem tailTrace_4855706 : CollatzResearch.WordTrace tailWord_4855706 prefixEnd_4855706 2493311094920684261644021 := by
  unfold tailWord_4855706
  simp only [CollatzResearch.WordTrace]
  refine ⟨44275536836653481351718743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118068098231075950271249981 44275536836653481351718743)
  ·
    refine ⟨66413305254980222027578115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44275536836653481351718743 66413305254980222027578115)
    ·
      refine ⟨99619957882470333041367173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66413305254980222027578115 99619957882470333041367173)
      ·
        refine ⟨18678742102963187445256345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99619957882470333041367173 18678742102963187445256345)
        ·
          refine ⟨14009056577222390583942259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18678742102963187445256345 14009056577222390583942259)
          ·
            refine ⟨21013584865833585875913389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14009056577222390583942259 21013584865833585875913389)
            ·
              refine ⟨7880094324687594703467521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21013584865833585875913389 7880094324687594703467521)
              ·
                refine ⟨5910070743515696027600641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7880094324687594703467521 5910070743515696027600641)
                ·
                  refine ⟨4432553057636772020700481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5910070743515696027600641 4432553057636772020700481)
                  ·
                    refine ⟨3324414793227579015525361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4432553057636772020700481 3324414793227579015525361)
                    ·
                      refine ⟨2493311094920684261644021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3324414793227579015525361 2493311094920684261644021)
                      ·
                        rfl

theorem cell23_4855706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_4855706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855706 prefixEnd_4855706 := by exact prefixLift 4855706
  have htrace : WordTrace (prefixWord ++ tailWord_4855706) baseStart_4855706 baseEnd_4855706 := by
    simpa [prefixWord, tailWord_4855706, baseEnd_4855706] using wordTrace_append hprefix tailTrace_4855706
  have hstable : (prefixWord ++ tailWord_4855706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855706).length < 2 ^ (prefixWord ++ tailWord_4855706).sum := by decide
  have hdescent : baseEnd_4855706 < baseStart_4855706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855795 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 3]
def baseStart_4855795 : Nat := 118140960795 + 4855795 * 2 ^ 59
def prefixEnd_4855795 : Nat := 4983230072969 + 3 ^ 40 * 4855795 * 2
def baseEnd_4855795 : Nat := 2493356794698934413431111

theorem tailTrace_4855795 : CollatzResearch.WordTrace tailWord_4855795 prefixEnd_4855795 2493356794698934413431111 := by
  unfold tailWord_4855795
  simp only [CollatzResearch.WordTrace]
  refine ⟨177105393443291493606864839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118070262295527662404576559 177105393443291493606864839)
  ·
    refine ⟨265658090164937240410297259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177105393443291493606864839 265658090164937240410297259)
    ·
      refine ⟨398487135247405860615445889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265658090164937240410297259 398487135247405860615445889)
      ·
        refine ⟨298865351435554395461584417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 398487135247405860615445889 298865351435554395461584417)
        ·
          refine ⟨224149013576665796596188313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298865351435554395461584417 224149013576665796596188313)
          ·
            refine ⟨168111760182499347447141235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224149013576665796596188313 168111760182499347447141235)
            ·
              refine ⟨252167640273749021170711853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168111760182499347447141235 252167640273749021170711853)
              ·
                refine ⟨94562865102655882939016945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 252167640273749021170711853 94562865102655882939016945)
                ·
                  refine ⟨70922148826991912204262709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94562865102655882939016945 70922148826991912204262709)
                  ·
                    refine ⟨6648951452530491769149629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70922148826991912204262709 6648951452530491769149629)
                    ·
                      refine ⟨2493356794698934413431111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6648951452530491769149629 2493356794698934413431111)
                      ·
                        rfl

theorem cell23_4855795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 3].length) (baseStart_4855795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855795 prefixEnd_4855795 := by exact prefixLift 4855795
  have htrace : WordTrace (prefixWord ++ tailWord_4855795) baseStart_4855795 baseEnd_4855795 := by
    simpa [prefixWord, tailWord_4855795, baseEnd_4855795] using wordTrace_append hprefix tailTrace_4855795
  have hstable : (prefixWord ++ tailWord_4855795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855795).length < 2 ^ (prefixWord ++ tailWord_4855795).sum := by decide
  have hdescent : baseEnd_4855795 < baseStart_4855795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855814 : List Nat := [6, 2, 1, 2, 2, 1, 2, 2, 5]
def baseStart_4855814 : Nat := 118140960795 + 4855814 * 2 ^ 59
def prefixEnd_4855814 : Nat := 4983230072969 + 3 ^ 40 * 4855814 * 2
def baseEnd_4855814 : Nat := 277040727870152204343725

theorem tailTrace_4855814 : CollatzResearch.WordTrace tailWord_4855814 prefixEnd_4855814 277040727870152204343725 := by
  unfold tailWord_4855814
  simp only [CollatzResearch.WordTrace]
  refine ⟨5534565200944458120368953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 118070724286815106567870997 5534565200944458120368953)
  ·
    refine ⟨4150923900708343590276715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5534565200944458120368953 4150923900708343590276715)
    ·
      refine ⟨6226385851062515385415073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4150923900708343590276715 6226385851062515385415073)
      ·
        refine ⟨4669789388296886539061305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6226385851062515385415073 4669789388296886539061305)
        ·
          refine ⟨3502342041222664904295979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4669789388296886539061305 3502342041222664904295979)
          ·
            refine ⟨5253513061833997356443969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3502342041222664904295979 5253513061833997356443969)
            ·
              refine ⟨3940134796375498017332977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5253513061833997356443969 3940134796375498017332977)
              ·
                refine ⟨2955101097281623512999733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3940134796375498017332977 2955101097281623512999733)
                ·
                  refine ⟨277040727870152204343725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2955101097281623512999733 277040727870152204343725)
                  ·
                    rfl

theorem cell23_4855814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_4855814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855814 prefixEnd_4855814 := by exact prefixLift 4855814
  have htrace : WordTrace (prefixWord ++ tailWord_4855814) baseStart_4855814 baseEnd_4855814 := by
    simpa [prefixWord, tailWord_4855814, baseEnd_4855814] using wordTrace_append hprefix tailTrace_4855814
  have hstable : (prefixWord ++ tailWord_4855814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855814).length < 2 ^ (prefixWord ++ tailWord_4855814).sum := by decide
  have hdescent : baseEnd_4855814 < baseStart_4855814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855852 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 1, 8, 2]
def baseStart_4855852 : Nat := 118140960795 + 4855852 * 2 ^ 59
def prefixEnd_4855852 : Nat := 4983230072969 + 3 ^ 40 * 4855852 * 2
def baseEnd_4855852 : Nat := 2493386063096240690418349

theorem tailTrace_4855852 : CollatzResearch.WordTrace tailWord_4855852 prefixEnd_4855852 2493386063096240690418349 := by
  unfold tailWord_4855852
  simp only [CollatzResearch.WordTrace]
  refine ⟨88553736202042496170844905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118071648269389994894459873 88553736202042496170844905)
  ·
    refine ⟨66415302151531872128133679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88553736202042496170844905 66415302151531872128133679)
    ·
      refine ⟨99622953227297808192200519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66415302151531872128133679 99622953227297808192200519)
      ·
        refine ⟨149434429840946712288300779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99622953227297808192200519 149434429840946712288300779)
        ·
          refine ⟨224151644761420068432451169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149434429840946712288300779 224151644761420068432451169)
          ·
            refine ⟨168113733571065051324338377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224151644761420068432451169 168113733571065051324338377)
            ·
              refine ⟨126085300178298788493253783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168113733571065051324338377 126085300178298788493253783)
              ·
                refine ⟨189127950267448182739880675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126085300178298788493253783 189127950267448182739880675)
                ·
                  refine ⟨283691925401172274109821013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189127950267448182739880675 283691925401172274109821013)
                  ·
                    refine ⟨3324514750794987587224465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 283691925401172274109821013 3324514750794987587224465)
                    ·
                      refine ⟨2493386063096240690418349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3324514750794987587224465 2493386063096240690418349)
                      ·
                        rfl

theorem cell23_4855852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 8, 2].length) (baseStart_4855852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855852 prefixEnd_4855852 := by exact prefixLift 4855852
  have htrace : WordTrace (prefixWord ++ tailWord_4855852) baseStart_4855852 baseEnd_4855852 := by
    simpa [prefixWord, tailWord_4855852, baseEnd_4855852] using wordTrace_append hprefix tailTrace_4855852
  have hstable : (prefixWord ++ tailWord_4855852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855852).length < 2 ^ (prefixWord ++ tailWord_4855852).sum := by decide
  have hdescent : baseEnd_4855852 < baseStart_4855852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855855 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 5]
def baseStart_4855855 : Nat := 118140960795 + 4855855 * 2 ^ 59
def prefixEnd_4855855 : Nat := 4983230072969 + 3 ^ 40 * 4855855 * 2
def baseEnd_4855855 : Nat := 2493387603538204178680835

theorem tailTrace_4855855 : CollatzResearch.WordTrace tailWord_4855855 prefixEnd_4855855 2493387603538204178680835 := by
  unfold tailWord_4855855
  simp only [CollatzResearch.WordTrace]
  refine ⟨177107581823074123854049019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118071721215382749236032679 177107581823074123854049019)
  ·
    refine ⟨265661372734611185781073529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177107581823074123854049019 265661372734611185781073529)
    ·
      refine ⟨199246029550958389335805147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265661372734611185781073529 199246029550958389335805147)
      ·
        refine ⟨298869044326437584003707721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199246029550958389335805147 298869044326437584003707721)
        ·
          refine ⟨224151783244828188002780791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298869044326437584003707721 224151783244828188002780791)
          ·
            refine ⟨336227674867242282004171187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224151783244828188002780791 336227674867242282004171187)
            ·
              refine ⟨504341512300863423006256781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336227674867242282004171187 504341512300863423006256781)
              ·
                refine ⟨189128067112823783627346293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 504341512300863423006256781 189128067112823783627346293)
                ·
                  refine ⟨17730756291827229715063715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 189128067112823783627346293 17730756291827229715063715)
                  ·
                    refine ⟨26596134437740844572595573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17730756291827229715063715 26596134437740844572595573)
                    ·
                      refine ⟨2493387603538204178680835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26596134437740844572595573 2493387603538204178680835)
                      ·
                        rfl

theorem cell23_4855855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 5].length) (baseStart_4855855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855855 prefixEnd_4855855 := by exact prefixLift 4855855
  have htrace : WordTrace (prefixWord ++ tailWord_4855855) baseStart_4855855 baseEnd_4855855 := by
    simpa [prefixWord, tailWord_4855855, baseEnd_4855855] using wordTrace_append hprefix tailTrace_4855855
  have hstable : (prefixWord ++ tailWord_4855855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855855).length < 2 ^ (prefixWord ++ tailWord_4855855).sum := by decide
  have hdescent : baseEnd_4855855 < baseStart_4855855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855856 : List Nat := [2, 1, 1, 1, 2, 7, 1, 1, 2, 3, 2]
def baseStart_4855856 : Nat := 118140960795 + 4855856 * 2 ^ 59
def prefixEnd_4855856 : Nat := 4983230072969 + 3 ^ 40 * 4855856 * 2
def baseEnd_4855856 : Nat := 2493388117018858674768331

theorem tailTrace_4855856 : CollatzResearch.WordTrace tailWord_4855856 prefixEnd_4855856 2493388117018858674768331 := by
  unfold tailWord_4855856
  simp only [CollatzResearch.WordTrace]
  refine ⟨88553809148035250512417711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118071745530713667349890281 88553809148035250512417711)
  ·
    refine ⟨132830713722052875768626567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88553809148035250512417711 132830713722052875768626567)
    ·
      refine ⟨199246070583079313652939851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132830713722052875768626567 199246070583079313652939851)
      ·
        refine ⟨298869105874618970479409777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199246070583079313652939851 298869105874618970479409777)
        ·
          refine ⟨224151829405964227859557333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298869105874618970479409777 224151829405964227859557333)
          ·
            refine ⟨5253558501702286590458375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 224151829405964227859557333 5253558501702286590458375)
            ·
              refine ⟨7880337752553429885687563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5253558501702286590458375 7880337752553429885687563)
              ·
                refine ⟨11820506628830144828531345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7880337752553429885687563 11820506628830144828531345)
                ·
                  refine ⟨8865379971622608621398509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11820506628830144828531345 8865379971622608621398509)
                  ·
                    refine ⟨3324517489358478233024441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8865379971622608621398509 3324517489358478233024441)
                    ·
                      refine ⟨2493388117018858674768331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3324517489358478233024441 2493388117018858674768331)
                      ·
                        rfl

theorem cell23_4855856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 2, 3, 2].length) (baseStart_4855856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855856 prefixEnd_4855856 := by exact prefixLift 4855856
  have htrace : WordTrace (prefixWord ++ tailWord_4855856) baseStart_4855856 baseEnd_4855856 := by
    simpa [prefixWord, tailWord_4855856, baseEnd_4855856] using wordTrace_append hprefix tailTrace_4855856
  have hstable : (prefixWord ++ tailWord_4855856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855856).length < 2 ^ (prefixWord ++ tailWord_4855856).sum := by decide
  have hdescent : baseEnd_4855856 < baseStart_4855856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855869 : List Nat := [1, 4, 1, 3, 1, 1, 3, 3, 1, 1, 4]
def baseStart_4855869 : Nat := 118140960795 + 4855869 * 2 ^ 59
def prefixEnd_4855869 : Nat := 4983230072969 + 3 ^ 40 * 4855869 * 2
def baseEnd_4855869 : Nat := 2493394792267367123905771

theorem tailTrace_4855869 : CollatzResearch.WordTrace tailWord_4855869 prefixEnd_4855869 2493394792267367123905771 := by
  unfold tailWord_4855869
  simp only [CollatzResearch.WordTrace]
  refine ⟨177108092445023404245058661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118072061630015602830039107 177108092445023404245058661)
  ·
    refine ⟨33207767333441888295948499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177108092445023404245058661 33207767333441888295948499)
    ·
      refine ⟨49811651000162832443922749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33207767333441888295948499 49811651000162832443922749)
      ·
        refine ⟨18679369125061062166471031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49811651000162832443922749 18679369125061062166471031)
        ·
          refine ⟨28019053687591593249706547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18679369125061062166471031 28019053687591593249706547)
          ·
            refine ⟨42028580531387389874559821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28019053687591593249706547 42028580531387389874559821)
            ·
              refine ⟨15760717699270271202959933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42028580531387389874559821 15760717699270271202959933)
              ·
                refine ⟨5910269137226351701109975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15760717699270271202959933 5910269137226351701109975)
                ·
                  refine ⟨8865403705839527551664963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5910269137226351701109975 8865403705839527551664963)
                  ·
                    refine ⟨13298105558759291327497445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8865403705839527551664963 13298105558759291327497445)
                    ·
                      refine ⟨2493394792267367123905771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13298105558759291327497445 2493394792267367123905771)
                      ·
                        rfl

theorem cell23_4855869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_4855869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855869 prefixEnd_4855869 := by exact prefixLift 4855869
  have htrace : WordTrace (prefixWord ++ tailWord_4855869) baseStart_4855869 baseEnd_4855869 := by
    simpa [prefixWord, tailWord_4855869, baseEnd_4855869] using wordTrace_append hprefix tailTrace_4855869
  have hstable : (prefixWord ++ tailWord_4855869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855869).length < 2 ^ (prefixWord ++ tailWord_4855869).sum := by decide
  have hdescent : baseEnd_4855869 < baseStart_4855869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855886 : List Nat := [4, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2]
def baseStart_4855886 : Nat := 118140960795 + 4855886 * 2 ^ 59
def prefixEnd_4855886 : Nat := 4983230072969 + 3 ^ 40 * 4855886 * 2
def baseEnd_4855886 : Nat := 2493403521438493557393193

theorem tailTrace_4855886 : CollatzResearch.WordTrace tailWord_4855886 prefixEnd_4855886 2493403521438493557393193 := by
  unfold tailWord_4855886
  simp only [CollatzResearch.WordTrace]
  refine ⟨22138589060745227018553439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118072474990641210765618341 22138589060745227018553439)
  ·
    refine ⟨33207883591117840527830159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22138589060745227018553439 33207883591117840527830159)
    ·
      refine ⟨49811825386676760791745239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33207883591117840527830159 49811825386676760791745239)
      ·
        refine ⟨74717738080015141187617859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49811825386676760791745239 74717738080015141187617859)
        ·
          refine ⟨112076607120022711781426789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74717738080015141187617859 112076607120022711781426789)
          ·
            refine ⟨21014363835004258459017523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112076607120022711781426789 21014363835004258459017523)
            ·
              refine ⟨31521545752506387688526285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21014363835004258459017523 31521545752506387688526285)
              ·
                refine ⟨11820579657189895383197357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31521545752506387688526285 11820579657189895383197357)
                ·
                  refine ⟨4432717371446210768699009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11820579657189895383197357 4432717371446210768699009)
                  ·
                    refine ⟨3324538028584658076524257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4432717371446210768699009 3324538028584658076524257)
                    ·
                      refine ⟨2493403521438493557393193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3324538028584658076524257 2493403521438493557393193)
                      ·
                        rfl

theorem cell23_4855886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2].length) (baseStart_4855886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855886 prefixEnd_4855886 := by exact prefixLift 4855886
  have htrace : WordTrace (prefixWord ++ tailWord_4855886) baseStart_4855886 baseEnd_4855886 := by
    simpa [prefixWord, tailWord_4855886, baseEnd_4855886] using wordTrace_append hprefix tailTrace_4855886
  have hstable : (prefixWord ++ tailWord_4855886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855886).length < 2 ^ (prefixWord ++ tailWord_4855886).sum := by decide
  have hdescent : baseEnd_4855886 < baseStart_4855886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855896 : List Nat := [2, 1, 2, 2, 1, 5, 3, 1, 2, 4]
def baseStart_4855896 : Nat := 118140960795 + 4855896 * 2 ^ 59
def prefixEnd_4855896 : Nat := 4983230072969 + 3 ^ 40 * 4855896 * 2
def baseEnd_4855896 : Nat := 831136218748346172756049

theorem tailTrace_4855896 : CollatzResearch.WordTrace tailWord_4855896 prefixEnd_4855896 831136218748346172756049 := by
  unfold tailWord_4855896
  simp only [CollatzResearch.WordTrace]
  refine ⟨88554538607962793928145771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118072718143950391904194361 88554538607962793928145771)
  ·
    refine ⟨132831807911944190892218657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88554538607962793928145771 132831807911944190892218657)
    ·
      refine ⟨99623855933958143169163993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132831807911944190892218657 99623855933958143169163993)
      ·
        refine ⟨74717891950468607376872995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99623855933958143169163993 74717891950468607376872995)
        ·
          refine ⟨112076837925702911065309493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74717891950468607376872995 112076837925702911065309493)
          ·
            refine ⟨10507203555534647912372765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112076837925702911065309493 10507203555534647912372765)
            ·
              refine ⟨3940201333325492967139787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10507203555534647912372765 3940201333325492967139787)
              ·
                refine ⟨5910301999988239450709681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3940201333325492967139787 5910301999988239450709681)
                ·
                  refine ⟨4432726499991179588032261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5910301999988239450709681 4432726499991179588032261)
                  ·
                    refine ⟨831136218748346172756049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4432726499991179588032261 831136218748346172756049)
                    ·
                      rfl

theorem cell23_4855896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 2, 4].length) (baseStart_4855896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855896 prefixEnd_4855896 := by exact prefixLift 4855896
  have htrace : WordTrace (prefixWord ++ tailWord_4855896) baseStart_4855896 baseEnd_4855896 := by
    simpa [prefixWord, tailWord_4855896, baseEnd_4855896] using wordTrace_append hprefix tailTrace_4855896
  have hstable : (prefixWord ++ tailWord_4855896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855896).length < 2 ^ (prefixWord ++ tailWord_4855896).sum := by decide
  have hdescent : baseEnd_4855896 < baseStart_4855896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855909 : List Nat := [1, 3, 1, 3, 2, 4, 2, 7]
def baseStart_4855909 : Nat := 118140960795 + 4855909 * 2 ^ 59
def prefixEnd_4855909 : Nat := 4983230072969 + 3 ^ 40 * 4855909 * 2
def baseEnd_4855909 : Nat := 92348715981242480274281

theorem tailTrace_4855909 : CollatzResearch.WordTrace tailWord_4855909 prefixEnd_4855909 92348715981242480274281 := by
  unfold tailWord_4855909
  simp only [CollatzResearch.WordTrace]
  refine ⟨177109551364878491076514781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118073034243252327384343187 177109551364878491076514781)
  ·
    refine ⟨66416081761829434153693043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177109551364878491076514781 66416081761829434153693043)
    ·
      refine ⟨99624122642744151230539565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66416081761829434153693043 99624122642744151230539565)
      ·
        refine ⟨37359045991029056711452337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99624122642744151230539565 37359045991029056711452337)
        ·
          refine ⟨28019284493271792533589253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37359045991029056711452337 28019284493271792533589253)
          ·
            refine ⟨5253615842488461100047985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28019284493271792533589253 5253615842488461100047985)
            ·
              refine ⟨3940211881866345825035989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5253615842488461100047985 3940211881866345825035989)
              ·
                refine ⟨92348715981242480274281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3940211881866345825035989 92348715981242480274281)
                ·
                  rfl

theorem cell23_4855909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 7].length) (baseStart_4855909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855909 prefixEnd_4855909 := by exact prefixLift 4855909
  have htrace : WordTrace (prefixWord ++ tailWord_4855909) baseStart_4855909 baseEnd_4855909 := by
    simpa [prefixWord, tailWord_4855909, baseEnd_4855909] using wordTrace_append hprefix tailTrace_4855909
  have hstable : (prefixWord ++ tailWord_4855909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855909).length < 2 ^ (prefixWord ++ tailWord_4855909).sum := by decide
  have hdescent : baseEnd_4855909 < baseStart_4855909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855919 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 4, 1, 3]
def baseStart_4855919 : Nat := 118140960795 + 4855919 * 2 ^ 59
def prefixEnd_4855919 : Nat := 4983230072969 + 3 ^ 40 * 4855919 * 2
def baseEnd_4855919 : Nat := 2493420466300091928280541

theorem tailTrace_4855919 : CollatzResearch.WordTrace tailWord_4855919 prefixEnd_4855919 2493420466300091928280541 := by
  unfold tailWord_4855919
  simp only [CollatzResearch.WordTrace]
  refine ⟨177109916094842262784378811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118073277396561508522919207 177109916094842262784378811)
  ·
    refine ⟨265664874142263394176568217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177109916094842262784378811 265664874142263394176568217)
    ·
      refine ⟨199248655606697545632426163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265664874142263394176568217 199248655606697545632426163)
      ·
        refine ⟨298872983410046318448639245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199248655606697545632426163 298872983410046318448639245)
        ·
          refine ⟨112077368778767369418239717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 298872983410046318448639245 112077368778767369418239717)
          ·
            refine ⟨21014506646018881765919947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112077368778767369418239717 21014506646018881765919947)
            ·
              refine ⟨31521759969028322648879921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21014506646018881765919947 31521759969028322648879921)
              ·
                refine ⟨23641319976771241986659941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31521759969028322648879921 23641319976771241986659941)
                ·
                  refine ⟨4432747495644607872498739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23641319976771241986659941 4432747495644607872498739)
                  ·
                    refine ⟨6649121243466911808748109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4432747495644607872498739 6649121243466911808748109)
                    ·
                      refine ⟨2493420466300091928280541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6649121243466911808748109 2493420466300091928280541)
                      ·
                        rfl

theorem cell23_4855919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 1, 3].length) (baseStart_4855919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855919 prefixEnd_4855919 := by exact prefixLift 4855919
  have htrace : WordTrace (prefixWord ++ tailWord_4855919) baseStart_4855919 baseEnd_4855919 := by
    simpa [prefixWord, tailWord_4855919, baseEnd_4855919] using wordTrace_append hprefix tailTrace_4855919
  have hstable : (prefixWord ++ tailWord_4855919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855919).length < 2 ^ (prefixWord ++ tailWord_4855919).sum := by decide
  have hdescent : baseEnd_4855919 < baseStart_4855919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855920 : List Nat := [2, 1, 1, 1, 5, 4, 1, 3, 1, 2, 2]
def baseStart_4855920 : Nat := 118140960795 + 4855920 * 2 ^ 59
def prefixEnd_4855920 : Nat := 4983230072969 + 3 ^ 40 * 4855920 * 2
def baseEnd_4855920 : Nat := 2493420979780746424368037

theorem tailTrace_4855920 : CollatzResearch.WordTrace tailWord_4855920 prefixEnd_4855920 2493420979780746424368037 := by
  unfold tailWord_4855920
  simp only [CollatzResearch.WordTrace]
  refine ⟨88554976283919319977582607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118073301711892426636776809 88554976283919319977582607)
  ·
    refine ⟨132832464425878979966373911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88554976283919319977582607 132832464425878979966373911)
    ·
      refine ⟨199248696638818469949560867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132832464425878979966373911 199248696638818469949560867)
      ·
        refine ⟨298873044958227704924341301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199248696638818469949560867 298873044958227704924341301)
        ·
          refine ⟨28019347964833847336656997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 298873044958227704924341301 28019347964833847336656997)
          ·
            refine ⟨5253627743406346375623187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28019347964833847336656997 5253627743406346375623187)
            ·
              refine ⟨7880441615109519563434781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5253627743406346375623187 7880441615109519563434781)
              ·
                refine ⟨2955165605666069836288043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7880441615109519563434781 2955165605666069836288043)
                ·
                  refine ⟨4432748408499104754432065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2955165605666069836288043 4432748408499104754432065)
                  ·
                    refine ⟨3324561306374328565824049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4432748408499104754432065 3324561306374328565824049)
                    ·
                      refine ⟨2493420979780746424368037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3324561306374328565824049 2493420979780746424368037)
                      ·
                        rfl

theorem cell23_4855920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 1, 2, 2].length) (baseStart_4855920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855920 prefixEnd_4855920 := by exact prefixLift 4855920
  have htrace : WordTrace (prefixWord ++ tailWord_4855920) baseStart_4855920 baseEnd_4855920 := by
    simpa [prefixWord, tailWord_4855920, baseEnd_4855920] using wordTrace_append hprefix tailTrace_4855920
  have hstable : (prefixWord ++ tailWord_4855920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855920).length < 2 ^ (prefixWord ++ tailWord_4855920).sum := by decide
  have hdescent : baseEnd_4855920 < baseStart_4855920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855937 : List Nat := [1, 2, 4, 2, 3, 1, 3, 2, 1, 2, 2]
def baseStart_4855937 : Nat := 118140960795 + 4855937 * 2 ^ 59
def prefixEnd_4855937 : Nat := 4983230072969 + 3 ^ 40 * 4855937 * 2
def baseEnd_4855937 : Nat := 2493429708951872857855459

theorem tailTrace_4855937 : CollatzResearch.WordTrace tailWord_4855937 prefixEnd_4855937 2493429708951872857855459 := by
  unfold tailWord_4855937
  simp only [CollatzResearch.WordTrace]
  refine ⟨177110572608777051858534065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118073715072518034572356043 177110572608777051858534065)
  ·
    refine ⟨132832929456582788893900549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177110572608777051858534065 132832929456582788893900549)
    ·
      refine ⟨24906174273109272917606353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132832929456582788893900549 24906174273109272917606353)
      ·
        refine ⟨18679630704831954688204765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24906174273109272917606353 18679630704831954688204765)
        ·
          refine ⟨7004861514311983008076787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18679630704831954688204765 7004861514311983008076787)
          ·
            refine ⟨10507292271467974512115181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7004861514311983008076787 10507292271467974512115181)
            ·
              refine ⟨3940234601800490442043193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10507292271467974512115181 3940234601800490442043193)
              ·
                refine ⟨2955175951350367831532395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3940234601800490442043193 2955175951350367831532395)
                ·
                  refine ⟨4432763927025551747298593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2955175951350367831532395 4432763927025551747298593)
                  ·
                    refine ⟨3324572945269163810473945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4432763927025551747298593 3324572945269163810473945)
                    ·
                      refine ⟨2493429708951872857855459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3324572945269163810473945 2493429708951872857855459)
                      ·
                        rfl

theorem cell23_4855937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_4855937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855937 prefixEnd_4855937 := by exact prefixLift 4855937
  have htrace : WordTrace (prefixWord ++ tailWord_4855937) baseStart_4855937 baseEnd_4855937 := by
    simpa [prefixWord, tailWord_4855937, baseEnd_4855937] using wordTrace_append hprefix tailTrace_4855937
  have hstable : (prefixWord ++ tailWord_4855937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855937).length < 2 ^ (prefixWord ++ tailWord_4855937).sum := by decide
  have hdescent : baseEnd_4855937 < baseStart_4855937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855988 : List Nat := [2, 5, 3, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_4855988 : Nat := 118140960795 + 4855988 * 2 ^ 59
def prefixEnd_4855988 : Nat := 4983230072969 + 3 ^ 40 * 4855988 * 2
def baseEnd_4855988 : Nat := 2493455896465252158317725

theorem tailTrace_4855988 : CollatzResearch.WordTrace tailWord_4855988 prefixEnd_4855988 2493455896465252158317725 := by
  unfold tailWord_4855988
  simp only [CollatzResearch.WordTrace]
  refine ⟨88556216365796143784320309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118074955154394858379093745 88556216365796143784320309)
  ·
    refine ⟨8302145284293388479780029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88556216365796143784320309 8302145284293388479780029)
    ·
      refine ⟨3113304481610020679917511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8302145284293388479780029 3113304481610020679917511)
      ·
        refine ⟨4669956722415031019876267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3113304481610020679917511 4669956722415031019876267)
        ·
          refine ⟨7004935083622546529814401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4669956722415031019876267 7004935083622546529814401)
          ·
            refine ⟨5253701312716909897360801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7004935083622546529814401 5253701312716909897360801)
            ·
              refine ⟨3940275984537682423020601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5253701312716909897360801 3940275984537682423020601)
              ·
                refine ⟨2955206988403261817265451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3940275984537682423020601 2955206988403261817265451)
                ·
                  refine ⟨4432810482604892725898177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2955206988403261817265451 4432810482604892725898177)
                  ·
                    refine ⟨3324607861953669544423633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4432810482604892725898177 3324607861953669544423633)
                    ·
                      refine ⟨2493455896465252158317725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3324607861953669544423633 2493455896465252158317725)
                      ·
                        rfl

theorem cell23_4855988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_4855988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855988 prefixEnd_4855988 := by exact prefixLift 4855988
  have htrace : WordTrace (prefixWord ++ tailWord_4855988) baseStart_4855988 baseEnd_4855988 := by
    simpa [prefixWord, tailWord_4855988, baseEnd_4855988] using wordTrace_append hprefix tailTrace_4855988
  have hstable : (prefixWord ++ tailWord_4855988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855988).length < 2 ^ (prefixWord ++ tailWord_4855988).sum := by decide
  have hdescent : baseEnd_4855988 < baseStart_4855988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4855993 : List Nat := [1, 2, 1, 4, 1, 2, 4, 2, 2, 2, 2]
def baseStart_4855993 : Nat := 118140960795 + 4855993 * 2 ^ 59
def prefixEnd_4855993 : Nat := 4983230072969 + 3 ^ 40 * 4855993 * 2
def baseEnd_4855993 : Nat := 2493458463868524638755201

theorem tailTrace_4855993 : CollatzResearch.WordTrace tailWord_4855993 prefixEnd_4855993 2493458463868524638755201 := by
  unfold tailWord_4855993
  simp only [CollatzResearch.WordTrace]
  refine ⟨177112615096574173422572633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118075076731049448948381755 177112615096574173422572633)
  ·
    refine ⟨132834461322430630066929475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177112615096574173422572633 132834461322430630066929475)
    ·
      refine ⟨199251691983645945100394213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132834461322430630066929475 199251691983645945100394213)
      ·
        refine ⟨37359692246933614706323915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199251691983645945100394213 37359692246933614706323915)
        ·
          refine ⟨56039538370400422059485873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37359692246933614706323915 56039538370400422059485873)
          ·
            refine ⟨42029653777800316544614405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56039538370400422059485873 42029653777800316544614405)
            ·
              refine ⟨7880560083337559352115201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42029653777800316544614405 7880560083337559352115201)
              ·
                refine ⟨5910420062503169514086401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7880560083337559352115201 5910420062503169514086401)
                ·
                  refine ⟨4432815046877377135564801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5910420062503169514086401 4432815046877377135564801)
                  ·
                    refine ⟨3324611285158032851673601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4432815046877377135564801 3324611285158032851673601)
                    ·
                      refine ⟨2493458463868524638755201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3324611285158032851673601 2493458463868524638755201)
                      ·
                        rfl

theorem cell23_4855993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_4855993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4855993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4855993 prefixEnd_4855993 := by exact prefixLift 4855993
  have htrace : WordTrace (prefixWord ++ tailWord_4855993) baseStart_4855993 baseEnd_4855993 := by
    simpa [prefixWord, tailWord_4855993, baseEnd_4855993] using wordTrace_append hprefix tailTrace_4855993
  have hstable : (prefixWord ++ tailWord_4855993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4855993).length < 2 ^ (prefixWord ++ tailWord_4855993).sum := by decide
  have hdescent : baseEnd_4855993 < baseStart_4855993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4855993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856049 : List Nat := [1, 2, 2, 2, 2, 1, 2, 4, 2, 1, 4]
def baseStart_4856049 : Nat := 118140960795 + 4856049 * 2 ^ 59
def prefixEnd_4856049 : Nat := 4983230072969 + 3 ^ 40 * 4856049 * 2
def baseEnd_4856049 : Nat := 2493487218785176419654943

theorem tailTrace_4856049 : CollatzResearch.WordTrace tailWord_4856049 prefixEnd_4856049 2493487218785176419654943 := by
  unfold tailWord_4856049
  simp only [CollatzResearch.WordTrace]
  refine ⟨177114657584371294986611201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118076438389580863324407467 177114657584371294986611201)
  ·
    refine ⟨132835993188278471239958401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177114657584371294986611201 132835993188278471239958401)
    ·
      refine ⟨99626994891208853429968801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132835993188278471239958401 99626994891208853429968801)
      ·
        refine ⟨74720246168406640072476601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99626994891208853429968801 74720246168406640072476601)
        ·
          refine ⟨56040184626304980054357451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74720246168406640072476601 56040184626304980054357451)
          ·
            refine ⟨84060276939457470081536177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56040184626304980054357451 84060276939457470081536177)
            ·
              refine ⟨63045207704593102561152133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84060276939457470081536177 63045207704593102561152133)
              ·
                refine ⟨11820976444611206730216025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63045207704593102561152133 11820976444611206730216025)
                ·
                  refine ⟨8865732333458405047662019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11820976444611206730216025 8865732333458405047662019)
                  ·
                    refine ⟨13298598500187607571493029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8865732333458405047662019 13298598500187607571493029)
                    ·
                      refine ⟨2493487218785176419654943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13298598500187607571493029 2493487218785176419654943)
                      ·
                        rfl

theorem cell23_4856049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_4856049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856049 prefixEnd_4856049 := by exact prefixLift 4856049
  have htrace : WordTrace (prefixWord ++ tailWord_4856049) baseStart_4856049 baseEnd_4856049 := by
    simpa [prefixWord, tailWord_4856049, baseEnd_4856049] using wordTrace_append hprefix tailTrace_4856049
  have hstable : (prefixWord ++ tailWord_4856049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856049).length < 2 ^ (prefixWord ++ tailWord_4856049).sum := by decide
  have hdescent : baseEnd_4856049 < baseStart_4856049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856066 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_4856066 : Nat := 118140960795 + 4856066 * 2 ^ 59
def prefixEnd_4856066 : Nat := 4983230072969 + 3 ^ 40 * 4856066 * 2
def baseEnd_4856066 : Nat := 2493495947956302853142365

theorem tailTrace_4856066 : CollatzResearch.WordTrace tailWord_4856066 prefixEnd_4856066 2493495947956302853142365 := by
  unfold tailWord_4856066
  simp only [CollatzResearch.WordTrace]
  refine ⟨44278819406327426722495013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118076851750206471259986701 44278819406327426722495013)
  ·
    refine ⟨8302278638686392510467815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44278819406327426722495013 8302278638686392510467815)
    ·
      refine ⟨12453417958029588765701723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8302278638686392510467815 12453417958029588765701723)
      ·
        refine ⟨18680126937044383148552585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12453417958029588765701723 18680126937044383148552585)
        ·
          refine ⟨14010095202783287361414439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18680126937044383148552585 14010095202783287361414439)
          ·
            refine ⟨21015142804174931042121659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14010095202783287361414439 21015142804174931042121659)
            ·
              refine ⟨31522714206262396563182489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21015142804174931042121659 31522714206262396563182489)
              ·
                refine ⟨23642035654696797422386867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31522714206262396563182489 23642035654696797422386867)
                ·
                  refine ⟨35463053482045196133580301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23642035654696797422386867 35463053482045196133580301)
                  ·
                    refine ⟨13298645055766948550092613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35463053482045196133580301 13298645055766948550092613)
                    ·
                      refine ⟨2493495947956302853142365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13298645055766948550092613 2493495947956302853142365)
                      ·
                        rfl

theorem cell23_4856066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_4856066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856066 prefixEnd_4856066 := by exact prefixLift 4856066
  have htrace : WordTrace (prefixWord ++ tailWord_4856066) baseStart_4856066 baseEnd_4856066 := by
    simpa [prefixWord, tailWord_4856066, baseEnd_4856066] using wordTrace_append hprefix tailTrace_4856066
  have hstable : (prefixWord ++ tailWord_4856066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856066).length < 2 ^ (prefixWord ++ tailWord_4856066).sum := by decide
  have hdescent : baseEnd_4856066 < baseStart_4856066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856069 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 6, 2, 3]
def baseStart_4856069 : Nat := 118140960795 + 4856069 * 2 ^ 59
def prefixEnd_4856069 : Nat := 4983230072969 + 3 ^ 40 * 4856069 * 2
def baseEnd_4856069 : Nat := 2493497488398266341404851

theorem tailTrace_4856069 : CollatzResearch.WordTrace tailWord_4856069 prefixEnd_4856069 2493497488398266341404851 := by
  unfold tailWord_4856069
  simp only [CollatzResearch.WordTrace]
  refine ⟨177115387044298838402339261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118076924696199225601559507 177115387044298838402339261)
  ·
    refine ⟨66418270141612064400877223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177115387044298838402339261 66418270141612064400877223)
    ·
      refine ⟨99627405212418096601315835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66418270141612064400877223 99627405212418096601315835)
      ·
        refine ⟨149441107818627144901973753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99627405212418096601315835 149441107818627144901973753)
        ·
          refine ⟨112080830863970358676480315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149441107818627144901973753 112080830863970358676480315)
          ·
            refine ⟨168121246295955538014720473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112080830863970358676480315 168121246295955538014720473)
            ·
              refine ⟨126090934721966653511040355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168121246295955538014720473 126090934721966653511040355)
              ·
                refine ⟨189136402082949980266560533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126090934721966653511040355 189136402082949980266560533)
                ·
                  refine ⟨8865768847638280324995025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 189136402082949980266560533 8865768847638280324995025)
                  ·
                    refine ⟨6649326635728710243746269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8865768847638280324995025 6649326635728710243746269)
                    ·
                      refine ⟨2493497488398266341404851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6649326635728710243746269 2493497488398266341404851)
                      ·
                        rfl

theorem cell23_4856069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 2, 3].length) (baseStart_4856069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856069 prefixEnd_4856069 := by exact prefixLift 4856069
  have htrace : WordTrace (prefixWord ++ tailWord_4856069) baseStart_4856069 baseEnd_4856069 := by
    simpa [prefixWord, tailWord_4856069, baseEnd_4856069] using wordTrace_append hprefix tailTrace_4856069
  have hstable : (prefixWord ++ tailWord_4856069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856069).length < 2 ^ (prefixWord ++ tailWord_4856069).sum := by decide
  have hdescent : baseEnd_4856069 < baseStart_4856069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856136 : List Nat := [2, 1, 3, 1, 1, 2, 5, 2, 1, 5]
def baseStart_4856136 : Nat := 118140960795 + 4856136 * 2 ^ 59
def prefixEnd_4856136 : Nat := 4983230072969 + 3 ^ 40 * 4856136 * 2
def baseEnd_4856136 : Nat := 831177297200705859755681

theorem tailTrace_4856136 : CollatzResearch.WordTrace tailWord_4856136 prefixEnd_4856136 831177297200705859755681 := by
  unfold tailWord_4856136
  simp only [CollatzResearch.WordTrace]
  refine ⟨88558915367528054422514131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118078553823370739230018841 88558915367528054422514131)
  ·
    refine ⟨132838373051292081633771197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88558915367528054422514131 132838373051292081633771197)
    ·
      refine ⟨49814389894234530612664199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132838373051292081633771197 49814389894234530612664199)
      ·
        refine ⟨74721584841351795918996299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49814389894234530612664199 74721584841351795918996299)
        ·
          refine ⟨112082377262027693878494449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74721584841351795918996299 112082377262027693878494449)
          ·
            refine ⟨84061782946520770408870837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112082377262027693878494449 84061782946520770408870837)
            ·
              refine ⟨7880792151236322225831641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84061782946520770408870837 7880792151236322225831641)
              ·
                refine ⟨5910594113427241669373731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7880792151236322225831641 5910594113427241669373731)
                ·
                  refine ⟨8865891170140862504060597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5910594113427241669373731 8865891170140862504060597)
                  ·
                    refine ⟨831177297200705859755681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8865891170140862504060597 831177297200705859755681)
                    ·
                      rfl

theorem cell23_4856136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_4856136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856136 prefixEnd_4856136 := by exact prefixLift 4856136
  have htrace : WordTrace (prefixWord ++ tailWord_4856136) baseStart_4856136 baseEnd_4856136 := by
    simpa [prefixWord, tailWord_4856136, baseEnd_4856136] using wordTrace_append hprefix tailTrace_4856136
  have hstable : (prefixWord ++ tailWord_4856136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856136).length < 2 ^ (prefixWord ++ tailWord_4856136).sum := by decide
  have hdescent : baseEnd_4856136 < baseStart_4856136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856167 : List Nat := [1, 1, 5, 1, 3, 1, 4, 2, 1, 1, 3]
def baseStart_4856167 : Nat := 118140960795 + 4856167 * 2 ^ 59
def prefixEnd_4856167 : Nat := 4983230072969 + 3 ^ 40 * 4856167 * 2
def baseEnd_4856167 : Nat := 2493547809502406957979401

theorem tailTrace_4856167 : CollatzResearch.WordTrace tailWord_4856167 prefixEnd_4856167 2493547809502406957979401 := by
  unfold tailWord_4856167
  simp only [CollatzResearch.WordTrace]
  refine ⟨177118961397943801139406755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118079307598629200759604503 177118961397943801139406755)
  ·
    refine ⟨265678442096915701709110133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177118961397943801139406755 265678442096915701709110133)
    ·
      refine ⟨24907353946585847035229075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 265678442096915701709110133 24907353946585847035229075)
      ·
        refine ⟨37361030919878770552843613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24907353946585847035229075 37361030919878770552843613)
        ·
          refine ⟨14010386594954538957316355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37361030919878770552843613 14010386594954538957316355)
          ·
            refine ⟨21015579892431808435974533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14010386594954538957316355 21015579892431808435974533)
            ·
              refine ⟨3940421229830964081745225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21015579892431808435974533 3940421229830964081745225)
              ·
                refine ⟨2955315922373223061308919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3940421229830964081745225 2955315922373223061308919)
                ·
                  refine ⟨4432973883559834591963379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2955315922373223061308919 4432973883559834591963379)
                  ·
                    refine ⟨6649460825339751887945069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4432973883559834591963379 6649460825339751887945069)
                    ·
                      refine ⟨2493547809502406957979401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6649460825339751887945069 2493547809502406957979401)
                      ·
                        rfl

theorem cell23_4856167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_4856167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856167 prefixEnd_4856167 := by exact prefixLift 4856167
  have htrace : WordTrace (prefixWord ++ tailWord_4856167) baseStart_4856167 baseEnd_4856167 := by
    simpa [prefixWord, tailWord_4856167, baseEnd_4856167] using wordTrace_append hprefix tailTrace_4856167
  have hstable : (prefixWord ++ tailWord_4856167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856167).length < 2 ^ (prefixWord ++ tailWord_4856167).sum := by decide
  have hdescent : baseEnd_4856167 < baseStart_4856167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856169 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 3, 2, 4]
def baseStart_4856169 : Nat := 118140960795 + 4856169 * 2 ^ 59
def prefixEnd_4856169 : Nat := 4983230072969 + 3 ^ 40 * 4856169 * 2
def baseEnd_4856169 : Nat := 2493548836463715950154391

theorem tailTrace_4856169 : CollatzResearch.WordTrace tailWord_4856169 prefixEnd_4856169 2493548836463715950154391 := by
  unfold tailWord_4856169
  simp only [CollatzResearch.WordTrace]
  refine ⟨177119034343936555480979561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118079356229291036987319707 177119034343936555480979561)
  ·
    refine ⟨132839275757952416610734671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177119034343936555480979561 132839275757952416610734671)
    ·
      refine ⟨199258913636928624916102007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132839275757952416610734671 199258913636928624916102007)
      ·
        refine ⟨298888370455392937374153011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199258913636928624916102007 298888370455392937374153011)
        ·
          refine ⟨448332555683089406061229517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298888370455392937374153011 448332555683089406061229517)
          ·
            refine ⟨168124708381158527272961069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 448332555683089406061229517 168124708381158527272961069)
            ·
              refine ⟨63046765642934447727360401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168124708381158527272961069 63046765642934447727360401)
              ·
                refine ⟨47285074232200835795520301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63046765642934447727360401 47285074232200835795520301)
                ·
                  refine ⟨17731902837075313423320113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47285074232200835795520301 17731902837075313423320113)
                  ·
                    refine ⟨13298927127806485067490085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17731902837075313423320113 13298927127806485067490085)
                    ·
                      refine ⟨2493548836463715950154391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13298927127806485067490085 2493548836463715950154391)
                      ·
                        rfl

theorem cell23_4856169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 2, 4].length) (baseStart_4856169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856169 prefixEnd_4856169 := by exact prefixLift 4856169
  have htrace : WordTrace (prefixWord ++ tailWord_4856169) baseStart_4856169 baseEnd_4856169 := by
    simpa [prefixWord, tailWord_4856169, baseEnd_4856169] using wordTrace_append hprefix tailTrace_4856169
  have hstable : (prefixWord ++ tailWord_4856169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856169).length < 2 ^ (prefixWord ++ tailWord_4856169).sum := by decide
  have hdescent : baseEnd_4856169 < baseStart_4856169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856176 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 3]
def baseStart_4856176 : Nat := 118140960795 + 4856176 * 2 ^ 59
def prefixEnd_4856176 : Nat := 4983230072969 + 3 ^ 40 * 4856176 * 2
def baseEnd_4856176 : Nat := 2493552430828297422766859

theorem tailTrace_4856176 : CollatzResearch.WordTrace tailWord_4856176 prefixEnd_4856176 2493552430828297422766859 := by
  unfold tailWord_4856176
  simp only [CollatzResearch.WordTrace]
  refine ⟨88559644827455597838242191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118079526436607463784322921 88559644827455597838242191)
  ·
    refine ⟨132839467241183396757363287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88559644827455597838242191 132839467241183396757363287)
    ·
      refine ⟨199259200861775095136044931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132839467241183396757363287 199259200861775095136044931)
      ·
        refine ⟨298888801292662642704067397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199259200861775095136044931 298888801292662642704067397)
        ·
          refine ⟨56041650242374245507012637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 298888801292662642704067397 56041650242374245507012637)
          ·
            refine ⟨21015618840890342065129739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56041650242374245507012637 21015618840890342065129739)
            ·
              refine ⟨31523428261335513097694609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21015618840890342065129739 31523428261335513097694609)
              ·
                refine ⟨23642571196001634823270957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31523428261335513097694609 23642571196001634823270957)
                ·
                  refine ⟨8865964198500613058726609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23642571196001634823270957 8865964198500613058726609)
                  ·
                    refine ⟨6649473148875459794044957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8865964198500613058726609 6649473148875459794044957)
                    ·
                      refine ⟨2493552430828297422766859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6649473148875459794044957 2493552430828297422766859)
                      ·
                        rfl

theorem cell23_4856176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 3].length) (baseStart_4856176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856176 prefixEnd_4856176 := by exact prefixLift 4856176
  have htrace : WordTrace (prefixWord ++ tailWord_4856176) baseStart_4856176 baseEnd_4856176 := by
    simpa [prefixWord, tailWord_4856176, baseEnd_4856176] using wordTrace_append hprefix tailTrace_4856176
  have hstable : (prefixWord ++ tailWord_4856176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856176).length < 2 ^ (prefixWord ++ tailWord_4856176).sum := by decide
  have hdescent : baseEnd_4856176 < baseStart_4856176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856193 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 3, 2, 3]
def baseStart_4856193 : Nat := 118140960795 + 4856193 * 2 ^ 59
def prefixEnd_4856193 : Nat := 4983230072969 + 3 ^ 40 * 4856193 * 2
def baseEnd_4856193 : Nat := 2493561159999423856254281

theorem tailTrace_4856193 : CollatzResearch.WordTrace tailWord_4856193 prefixEnd_4856193 2493561159999423856254281 := by
  unfold tailWord_4856193
  simp only [CollatzResearch.WordTrace]
  refine ⟨177119909695849607579853233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118079939797233071719902155 177119909695849607579853233)
  ·
    refine ⟨132839932271887205684889925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177119909695849607579853233 132839932271887205684889925)
    ·
      refine ⟨24907487300978851065916861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132839932271887205684889925 24907487300978851065916861)
      ·
        refine ⟨9340307737867069149718823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24907487300978851065916861 9340307737867069149718823)
        ·
          refine ⟨14010461606800603724578235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9340307737867069149718823 14010461606800603724578235)
          ·
            refine ⟨21015692410200905586867353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14010461606800603724578235 21015692410200905586867353)
            ·
              refine ⟨15761769307650679190150515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21015692410200905586867353 15761769307650679190150515)
              ·
                refine ⟨23642653961476018785225773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15761769307650679190150515 23642653961476018785225773)
                ·
                  refine ⟨8865995235553507044459665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23642653961476018785225773 8865995235553507044459665)
                  ·
                    refine ⟨6649496426665130283344749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8865995235553507044459665 6649496426665130283344749)
                    ·
                      refine ⟨2493561159999423856254281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6649496426665130283344749 2493561159999423856254281)
                      ·
                        rfl

theorem cell23_4856193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_4856193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856193 prefixEnd_4856193 := by exact prefixLift 4856193
  have htrace : WordTrace (prefixWord ++ tailWord_4856193) baseStart_4856193 baseEnd_4856193 := by
    simpa [prefixWord, tailWord_4856193, baseEnd_4856193] using wordTrace_append hprefix tailTrace_4856193
  have hstable : (prefixWord ++ tailWord_4856193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856193).length < 2 ^ (prefixWord ++ tailWord_4856193).sum := by decide
  have hdescent : baseEnd_4856193 < baseStart_4856193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856194 : List Nat := [3, 4, 2, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_4856194 : Nat := 118140960795 + 4856194 * 2 ^ 59
def prefixEnd_4856194 : Nat := 4983230072969 + 3 ^ 40 * 4856194 * 2
def baseEnd_4856194 : Nat := 2493561673480078352341777

theorem tailTrace_4856194 : CollatzResearch.WordTrace tailWord_4856194 prefixEnd_4856194 2493561673480078352341777 := by
  unfold tailWord_4856194
  simp only [CollatzResearch.WordTrace]
  refine ⟨44279986542211496187659909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118079964112563989833759757 44279986542211496187659909)
  ·
    refine ⟨8302497476664655535186233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44279986542211496187659909 8302497476664655535186233)
    ·
      refine ⟨6226873107498491651389675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8302497476664655535186233 6226873107498491651389675)
      ·
        refine ⟨9340309661247737477084513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6226873107498491651389675 9340309661247737477084513)
        ·
          refine ⟨7005232245935803107813385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9340309661247737477084513 7005232245935803107813385)
          ·
            refine ⟨5253924184451852330860039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7005232245935803107813385 5253924184451852330860039)
            ·
              refine ⟨7880886276677778496290059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5253924184451852330860039 7880886276677778496290059)
              ·
                refine ⟨11821329415016667744435089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7880886276677778496290059 11821329415016667744435089)
                ·
                  refine ⟨8865997061262500808326317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11821329415016667744435089 8865997061262500808326317)
                  ·
                    refine ⟨3324748897973437803122369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8865997061262500808326317 3324748897973437803122369)
                    ·
                      refine ⟨2493561673480078352341777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3324748897973437803122369 2493561673480078352341777)
                      ·
                        rfl

theorem cell23_4856194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_4856194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856194 prefixEnd_4856194 := by exact prefixLift 4856194
  have htrace : WordTrace (prefixWord ++ tailWord_4856194) baseStart_4856194 baseEnd_4856194 := by
    simpa [prefixWord, tailWord_4856194, baseEnd_4856194] using wordTrace_append hprefix tailTrace_4856194
  have hstable : (prefixWord ++ tailWord_4856194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856194).length < 2 ^ (prefixWord ++ tailWord_4856194).sum := by decide
  have hdescent : baseEnd_4856194 < baseStart_4856194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856196 : List Nat := [2, 3, 2, 1, 1, 2, 5, 7]
def baseStart_4856196 : Nat := 118140960795 + 4856196 * 2 ^ 59
def prefixEnd_4856196 : Nat := 4983230072969 + 3 ^ 40 * 4856196 * 2
def baseEnd_4856196 : Nat := 92354174090421753500621

theorem tailTrace_4856196 : CollatzResearch.WordTrace tailWord_4856196 prefixEnd_4856196 92354174090421753500621 := by
  unfold tailWord_4856196
  simp only [CollatzResearch.WordTrace]
  refine ⟨88560009557419369546106221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118080012743225826061474961 88560009557419369546106221)
  ·
    refine ⟨33210003584032263579789833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88560009557419369546106221 33210003584032263579789833)
    ·
      refine ⟨24907502688024197684842375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33210003584032263579789833 24907502688024197684842375)
      ·
        refine ⟨37361254032036296527263563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24907502688024197684842375 37361254032036296527263563)
        ·
          refine ⟨56041881048054444790895345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37361254032036296527263563 56041881048054444790895345)
          ·
            refine ⟨42031410786040833593171509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56041881048054444790895345 42031410786040833593171509)
            ·
              refine ⟨3940444761191328149359829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42031410786040833593171509 3940444761191328149359829)
              ·
                refine ⟨92354174090421753500621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3940444761191328149359829 92354174090421753500621)
                ·
                  rfl

theorem cell23_4856196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 7].length) (baseStart_4856196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856196 prefixEnd_4856196 := by exact prefixLift 4856196
  have htrace : WordTrace (prefixWord ++ tailWord_4856196) baseStart_4856196 baseEnd_4856196 := by
    simpa [prefixWord, tailWord_4856196, baseEnd_4856196] using wordTrace_append hprefix tailTrace_4856196
  have hstable : (prefixWord ++ tailWord_4856196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856196).length < 2 ^ (prefixWord ++ tailWord_4856196).sum := by decide
  have hdescent : baseEnd_4856196 < baseStart_4856196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856223 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 4, 1, 3]
def baseStart_4856223 : Nat := 118140960795 + 4856223 * 2 ^ 59
def prefixEnd_4856223 : Nat := 4983230072969 + 3 ^ 40 * 4856223 * 2
def baseEnd_4856223 : Nat := 2493576564419058738879143

theorem tailTrace_4856223 : CollatzResearch.WordTrace tailWord_4856223 prefixEnd_4856223 2493576564419058738879143 := by
  unfold tailWord_4856223
  simp only [CollatzResearch.WordTrace]
  refine ⟨177121003885740922703445323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118080669257160615135630215 177121003885740922703445323)
  ·
    refine ⟨265681505828611384055167985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177121003885740922703445323 265681505828611384055167985)
    ·
      refine ⟨199261129371458538041375989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265681505828611384055167985 199261129371458538041375989)
      ·
        refine ⟨18680730878574237941378999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 199261129371458538041375989 18680730878574237941378999)
        ·
          refine ⟨28021096317861356912068499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18680730878574237941378999 28021096317861356912068499)
          ·
            refine ⟨42031644476792035368102749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28021096317861356912068499 42031644476792035368102749)
            ·
              refine ⟨15761866678797013263038531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42031644476792035368102749 15761866678797013263038531)
              ·
                refine ⟨23642800018195519894557797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15761866678797013263038531 23642800018195519894557797)
                ·
                  refine ⟨4433025003411659980229587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23642800018195519894557797 4433025003411659980229587)
                  ·
                    refine ⟨6649537505117489970344381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4433025003411659980229587 6649537505117489970344381)
                    ·
                      refine ⟨2493576564419058738879143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6649537505117489970344381 2493576564419058738879143)
                      ·
                        rfl

theorem cell23_4856223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_4856223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856223 prefixEnd_4856223 := by exact prefixLift 4856223
  have htrace : WordTrace (prefixWord ++ tailWord_4856223) baseStart_4856223 baseEnd_4856223 := by
    simpa [prefixWord, tailWord_4856223, baseEnd_4856223] using wordTrace_append hprefix tailTrace_4856223
  have hstable : (prefixWord ++ tailWord_4856223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856223).length < 2 ^ (prefixWord ++ tailWord_4856223).sum := by decide
  have hdescent : baseEnd_4856223 < baseStart_4856223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856234 : List Nat := [3, 1, 6, 1, 2, 1, 1, 1, 1, 6]
def baseStart_4856234 : Nat := 118140960795 + 4856234 * 2 ^ 59
def prefixEnd_4856234 : Nat := 4983230072969 + 3 ^ 40 * 4856234 * 2
def baseEnd_4856234 : Nat := 831194070902086065280531

theorem tailTrace_4856234 : CollatzResearch.WordTrace tailWord_4856234 prefixEnd_4856234 831194070902086065280531 := by
  unfold tailWord_4856234
  simp only [CollatzResearch.WordTrace]
  refine ⟨44280351272175267895523939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118080936725800714388063837 44280351272175267895523939)
  ·
    refine ⟨66420526908262901843285909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44280351272175267895523939 66420526908262901843285909)
    ·
      refine ⟨3113462198824823523904027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 66420526908262901843285909 3113462198824823523904027)
      ·
        refine ⟨4670193298237235285856041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3113462198824823523904027 4670193298237235285856041)
        ·
          refine ⟨3502644973677926464392031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4670193298237235285856041 3502644973677926464392031)
          ·
            refine ⟨5253967460516889696588047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3502644973677926464392031 5253967460516889696588047)
            ·
              refine ⟨7880951190775334544882071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5253967460516889696588047 7880951190775334544882071)
              ·
                refine ⟨11821426786163001817323107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7880951190775334544882071 11821426786163001817323107)
                ·
                  refine ⟨17732140179244502725984661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11821426786163001817323107 17732140179244502725984661)
                  ·
                    refine ⟨831194070902086065280531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17732140179244502725984661 831194070902086065280531)
                    ·
                      rfl

theorem cell23_4856234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_4856234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856234 prefixEnd_4856234 := by exact prefixLift 4856234
  have htrace : WordTrace (prefixWord ++ tailWord_4856234) baseStart_4856234 baseEnd_4856234 := by
    simpa [prefixWord, tailWord_4856234, baseEnd_4856234] using wordTrace_append hprefix tailTrace_4856234
  have hstable : (prefixWord ++ tailWord_4856234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856234).length < 2 ^ (prefixWord ++ tailWord_4856234).sum := by decide
  have hdescent : baseEnd_4856234 < baseStart_4856234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856237 : List Nat := [1, 5, 2, 2, 3, 1, 1, 1, 1, 2, 4]
def baseStart_4856237 : Nat := 118140960795 + 4856237 * 2 ^ 59
def prefixEnd_4856237 : Nat := 4983230072969 + 3 ^ 40 * 4856237 * 2
def baseEnd_4856237 : Nat := 2493583753148221684104079

theorem tailTrace_4856237 : CollatzResearch.WordTrace tailWord_4856237 prefixEnd_4856237 2493583753148221684104079 := by
  unfold tailWord_4856237
  simp only [CollatzResearch.WordTrace]
  refine ⟨177121514507690203094454965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118081009671793468729636643 177121514507690203094454965)
  ·
    refine ⟨16605141985095956540105153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 177121514507690203094454965 16605141985095956540105153)
    ·
      refine ⟨12453856488821967405078865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16605141985095956540105153 12453856488821967405078865)
      ·
        refine ⟨9340392366616475553809149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12453856488821967405078865 9340392366616475553809149)
        ·
          refine ⟨3502647137481178332678431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9340392366616475553809149 3502647137481178332678431)
          ·
            refine ⟨5253970706221767499017647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3502647137481178332678431 5253970706221767499017647)
            ·
              refine ⟨7880956059332651248526471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5253970706221767499017647 7880956059332651248526471)
              ·
                refine ⟨11821434088998976872789707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7880956059332651248526471 11821434088998976872789707)
                ·
                  refine ⟨17732151133498465309184561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11821434088998976872789707 17732151133498465309184561)
                  ·
                    refine ⟨13299113350123848981888421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17732151133498465309184561 13299113350123848981888421)
                    ·
                      refine ⟨2493583753148221684104079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13299113350123848981888421 2493583753148221684104079)
                      ·
                        rfl

theorem cell23_4856237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_4856237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856237 prefixEnd_4856237 := by exact prefixLift 4856237
  have htrace : WordTrace (prefixWord ++ tailWord_4856237) baseStart_4856237 baseEnd_4856237 := by
    simpa [prefixWord, tailWord_4856237, baseEnd_4856237] using wordTrace_append hprefix tailTrace_4856237
  have hstable : (prefixWord ++ tailWord_4856237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856237).length < 2 ^ (prefixWord ++ tailWord_4856237).sum := by decide
  have hdescent : baseEnd_4856237 < baseStart_4856237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856244 : List Nat := [2, 5, 2, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_4856244 : Nat := 118140960795 + 4856244 * 2 ^ 59
def prefixEnd_4856244 : Nat := 4983230072969 + 3 ^ 40 * 4856244 * 2
def baseEnd_4856244 : Nat := 2493587347512803156716547

theorem tailTrace_4856244 : CollatzResearch.WordTrace tailWord_4856244 prefixEnd_4856244 2493587347512803156716547 := by
  unfold tailWord_4856244
  simp only [CollatzResearch.WordTrace]
  refine ⟨88560884909332421644979893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118081179879109895526639857 88560884909332421644979893)
  ·
    refine ⟨8302582960249914529216865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88560884909332421644979893 8302582960249914529216865)
    ·
      refine ⟨6226937220187435896912649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8302582960249914529216865 6226937220187435896912649)
      ·
        refine ⟨4670202915140576922684487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6226937220187435896912649 4670202915140576922684487)
        ·
          refine ⟨7005304372710865384026731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4670202915140576922684487 7005304372710865384026731)
          ·
            refine ⟨10507956559066298076040097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7005304372710865384026731 10507956559066298076040097)
            ·
              refine ⟨7880967419299723557030073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10507956559066298076040097 7880967419299723557030073)
              ·
                refine ⟨5910725564474792667772555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7880967419299723557030073 5910725564474792667772555)
                ·
                  refine ⟨8866088346712189001658833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5910725564474792667772555 8866088346712189001658833)
                  ·
                    refine ⟨6649566260034141751244125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8866088346712189001658833 6649566260034141751244125)
                    ·
                      refine ⟨2493587347512803156716547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6649566260034141751244125 2493587347512803156716547)
                      ·
                        rfl

theorem cell23_4856244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_4856244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856244 prefixEnd_4856244 := by exact prefixLift 4856244
  have htrace : WordTrace (prefixWord ++ tailWord_4856244) baseStart_4856244 baseEnd_4856244 := by
    simpa [prefixWord, tailWord_4856244, baseEnd_4856244] using wordTrace_append hprefix tailTrace_4856244
  have hstable : (prefixWord ++ tailWord_4856244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856244).length < 2 ^ (prefixWord ++ tailWord_4856244).sum := by decide
  have hdescent : baseEnd_4856244 < baseStart_4856244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856266 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 2, 1, 5]
def baseStart_4856266 : Nat := 118140960795 + 4856266 * 2 ^ 59
def prefixEnd_4856266 : Nat := 4983230072969 + 3 ^ 40 * 4856266 * 2
def baseEnd_4856266 : Nat := 2493598644087202070641445

theorem tailTrace_4856266 : CollatzResearch.WordTrace tailWord_4856266 prefixEnd_4856266 2493598644087202070641445 := by
  unfold tailWord_4856266
  simp only [CollatzResearch.WordTrace]
  refine ⟨44280643056146285261815163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118081714816390094031507101 44280643056146285261815163)
  ·
    refine ⟨66420964584219427892722745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44280643056146285261815163 66420964584219427892722745)
    ·
      refine ⟨49815723438164570919542059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66420964584219427892722745 49815723438164570919542059)
      ·
        refine ⟨74723585157246856379313089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49815723438164570919542059 74723585157246856379313089)
        ·
          refine ⟨56042688867935142284484817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74723585157246856379313089 56042688867935142284484817)
          ·
            refine ⟨42032016650951356713363613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56042688867935142284484817 42032016650951356713363613)
            ·
              refine ⟨15762006244106758767511355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42032016650951356713363613 15762006244106758767511355)
              ·
                refine ⟨23643009366160138151267033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15762006244106758767511355 23643009366160138151267033)
                ·
                  refine ⟨17732257024620103613450275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23643009366160138151267033 17732257024620103613450275)
                  ·
                    refine ⟨26598385536930155420175413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17732257024620103613450275 26598385536930155420175413)
                    ·
                      refine ⟨2493598644087202070641445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26598385536930155420175413 2493598644087202070641445)
                      ·
                        rfl

theorem cell23_4856266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_4856266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856266 prefixEnd_4856266 := by exact prefixLift 4856266
  have htrace : WordTrace (prefixWord ++ tailWord_4856266) baseStart_4856266 baseEnd_4856266 := by
    simpa [prefixWord, tailWord_4856266, baseEnd_4856266] using wordTrace_append hprefix tailTrace_4856266
  have hstable : (prefixWord ++ tailWord_4856266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856266).length < 2 ^ (prefixWord ++ tailWord_4856266).sum := by decide
  have hdescent : baseEnd_4856266 < baseStart_4856266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856280 : List Nat := [2, 1, 2, 2, 2, 1, 1, 6, 2, 2, 2]
def baseStart_4856280 : Nat := 118140960795 + 4856280 * 2 ^ 59
def prefixEnd_4856280 : Nat := 4983230072969 + 3 ^ 40 * 4856280 * 2
def baseEnd_4856280 : Nat := 2493605832816365015866381

theorem tailTrace_4856280 : CollatzResearch.WordTrace tailWord_4856280 prefixEnd_4856280 2493605832816365015866381 := by
  unfold tailWord_4856280
  simp only [CollatzResearch.WordTrace]
  refine ⟨88561541423267210719135147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118082055231022947625513529 88561541423267210719135147)
  ·
    refine ⟨132842312134900816078702721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88561541423267210719135147 132842312134900816078702721)
    ·
      refine ⟨99631734101175612059027041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132842312134900816078702721 99631734101175612059027041)
      ·
        refine ⟨74723800575881709044270281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99631734101175612059027041 74723800575881709044270281)
        ·
          refine ⟨56042850431911281783202711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74723800575881709044270281 56042850431911281783202711)
          ·
            refine ⟨84064275647866922674804067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56042850431911281783202711 84064275647866922674804067)
            ·
              refine ⟨126096413471800384012206101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84064275647866922674804067 126096413471800384012206101)
              ·
                refine ⟨5910769381490643000572161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 126096413471800384012206101 5910769381490643000572161)
                ·
                  refine ⟨4433077036117982250429121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5910769381490643000572161 4433077036117982250429121)
                  ·
                    refine ⟨3324807777088486687821841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4433077036117982250429121 3324807777088486687821841)
                    ·
                      refine ⟨2493605832816365015866381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3324807777088486687821841 2493605832816365015866381)
                      ·
                        rfl

theorem cell23_4856280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 2, 2, 2].length) (baseStart_4856280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856280 prefixEnd_4856280 := by exact prefixLift 4856280
  have htrace : WordTrace (prefixWord ++ tailWord_4856280) baseStart_4856280 baseEnd_4856280 := by
    simpa [prefixWord, tailWord_4856280, baseEnd_4856280] using wordTrace_append hprefix tailTrace_4856280
  have hstable : (prefixWord ++ tailWord_4856280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856280).length < 2 ^ (prefixWord ++ tailWord_4856280).sum := by decide
  have hdescent : baseEnd_4856280 < baseStart_4856280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856336 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 4]
def baseStart_4856336 : Nat := 118140960795 + 4856336 * 2 ^ 59
def prefixEnd_4856336 : Nat := 4983230072969 + 3 ^ 40 * 4856336 * 2
def baseEnd_4856336 : Nat := 2493634587733016796766123

theorem tailTrace_4856336 : CollatzResearch.WordTrace tailWord_4856336 prefixEnd_4856336 2493634587733016796766123 := by
  unfold tailWord_4856336
  simp only [CollatzResearch.WordTrace]
  refine ⟨88562562667165771501154431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118083416889554362001539241 88562562667165771501154431)
  ·
    refine ⟨132843844000748657251731647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88562562667165771501154431 132843844000748657251731647)
    ·
      refine ⟨199265766001122985877597471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132843844000748657251731647 199265766001122985877597471)
      ·
        refine ⟨298898649001684478816396207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199265766001122985877597471 298898649001684478816396207)
        ·
          refine ⟨448347973502526718224594311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298898649001684478816396207 448347973502526718224594311)
          ·
            refine ⟨672521960253790077336891467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448347973502526718224594311 672521960253790077336891467)
            ·
              refine ⟨1008782940380685116005337201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672521960253790077336891467 1008782940380685116005337201)
              ·
                refine ⟨756587205285513837004002901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1008782940380685116005337201 756587205285513837004002901)
                ·
                  refine ⟨8866256311939615277390659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 756587205285513837004002901 8866256311939615277390659)
                  ·
                    refine ⟨13299384467909422916085989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8866256311939615277390659 13299384467909422916085989)
                    ·
                      refine ⟨2493634587733016796766123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13299384467909422916085989 2493634587733016796766123)
                      ·
                        rfl

theorem cell23_4856336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 4].length) (baseStart_4856336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856336 prefixEnd_4856336 := by exact prefixLift 4856336
  have htrace : WordTrace (prefixWord ++ tailWord_4856336) baseStart_4856336 baseEnd_4856336 := by
    simpa [prefixWord, tailWord_4856336, baseEnd_4856336] using wordTrace_append hprefix tailTrace_4856336
  have hstable : (prefixWord ++ tailWord_4856336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856336).length < 2 ^ (prefixWord ++ tailWord_4856336).sum := by decide
  have hdescent : baseEnd_4856336 < baseStart_4856336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856373 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 1, 4, 3]
def baseStart_4856373 : Nat := 118140960795 + 4856373 * 2 ^ 59
def prefixEnd_4856373 : Nat := 4983230072969 + 3 ^ 40 * 4856373 * 2
def baseEnd_4856373 : Nat := 2493653586517233152003453

theorem tailTrace_4856373 : CollatzResearch.WordTrace tailWord_4856373 prefixEnd_4856373 2493653586517233152003453 := by
  unfold tailWord_4856373
  simp only [CollatzResearch.WordTrace]
  refine ⟨177126474835197498321405773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118084316556798332214270515 177126474835197498321405773)
  ·
    refine ⟨66422428063199061870527165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177126474835197498321405773 66422428063199061870527165)
    ·
      refine ⟨24908410523699648201447687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66422428063199061870527165 24908410523699648201447687)
      ·
        refine ⟨37362615785549472302171531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24908410523699648201447687 37362615785549472302171531)
        ·
          refine ⟨56043923678324208453257297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37362615785549472302171531 56043923678324208453257297)
          ·
            refine ⟨42032942758743156339942973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56043923678324208453257297 42032942758743156339942973)
            ·
              refine ⟨15762353534528683627478615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42032942758743156339942973 15762353534528683627478615)
              ·
                refine ⟨23643530301793025441217923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15762353534528683627478615 23643530301793025441217923)
                ·
                  refine ⟨35465295452689538161826885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23643530301793025441217923 35465295452689538161826885)
                  ·
                    refine ⟨6649742897379288405342541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35465295452689538161826885 6649742897379288405342541)
                    ·
                      refine ⟨2493653586517233152003453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6649742897379288405342541 2493653586517233152003453)
                      ·
                        rfl

theorem cell23_4856373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_4856373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856373 prefixEnd_4856373 := by exact prefixLift 4856373
  have htrace : WordTrace (prefixWord ++ tailWord_4856373) baseStart_4856373 baseEnd_4856373 := by
    simpa [prefixWord, tailWord_4856373, baseEnd_4856373] using wordTrace_append hprefix tailTrace_4856373
  have hstable : (prefixWord ++ tailWord_4856373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856373).length < 2 ^ (prefixWord ++ tailWord_4856373).sum := by decide
  have hdescent : baseEnd_4856373 < baseStart_4856373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856376 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 8]
def baseStart_4856376 : Nat := 118140960795 + 4856376 * 2 ^ 59
def prefixEnd_4856376 : Nat := 4983230072969 + 3 ^ 40 * 4856376 * 2
def baseEnd_4856376 : Nat := 277072791884355182251771

theorem tailTrace_4856376 : CollatzResearch.WordTrace tailWord_4856376 prefixEnd_4856376 277072791884355182251771 := by
  unfold tailWord_4856376
  simp only [CollatzResearch.WordTrace]
  refine ⟨88563292127093314916882491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118084389502791086555843321 88563292127093314916882491)
  ·
    refine ⟨132844938190639972375323737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88563292127093314916882491 132844938190639972375323737)
    ·
      refine ⟨99633703642979979281492803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132844938190639972375323737 99633703642979979281492803)
      ·
        refine ⟨149450555464469968922239205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99633703642979979281492803 149450555464469968922239205)
        ·
          refine ⟨28021979149588119172919851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149450555464469968922239205 28021979149588119172919851)
          ·
            refine ⟨42032968724382178759379777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28021979149588119172919851 42032968724382178759379777)
            ·
              refine ⟨31524726543286634069534833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42032968724382178759379777 31524726543286634069534833)
              ·
                refine ⟨23643544907464975552151125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31524726543286634069534833 23643544907464975552151125)
                ·
                  refine ⟨277072791884355182251771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23643544907464975552151125 277072791884355182251771)
                  ·
                    rfl

theorem cell23_4856376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 8].length) (baseStart_4856376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856376 prefixEnd_4856376 := by exact prefixLift 4856376
  have htrace : WordTrace (prefixWord ++ tailWord_4856376) baseStart_4856376 baseEnd_4856376 := by
    simpa [prefixWord, tailWord_4856376, baseEnd_4856376] using wordTrace_append hprefix tailTrace_4856376
  have hstable : (prefixWord ++ tailWord_4856376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856376).length < 2 ^ (prefixWord ++ tailWord_4856376).sum := by decide
  have hdescent : baseEnd_4856376 < baseStart_4856376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856396 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 1, 1, 8]
def baseStart_4856396 : Nat := 118140960795 + 4856396 * 2 ^ 59
def prefixEnd_4856396 : Nat := 4983230072969 + 3 ^ 40 * 4856396 * 2
def baseEnd_4856396 : Nat := 2493665396572286562015847

theorem tailTrace_4856396 : CollatzResearch.WordTrace tailWord_4856396 prefixEnd_4856396 2493665396572286562015847 := by
  unfold tailWord_4856396
  simp only [CollatzResearch.WordTrace]
  refine ⟨88563656857057086624746521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118084875809409448832995361 88563656857057086624746521)
  ·
    refine ⟨66422742642792814968559891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88563656857057086624746521 66422742642792814968559891)
    ·
      refine ⟨99634113964189222452839837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66422742642792814968559891 99634113964189222452839837)
      ·
        refine ⟨37362792736570958419814939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99634113964189222452839837 37362792736570958419814939)
        ·
          refine ⟨56044189104856437629722409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37362792736570958419814939 56044189104856437629722409)
          ·
            refine ⟨42033141828642328222291807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56044189104856437629722409 42033141828642328222291807)
            ·
              refine ⟨63049712742963492333437711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42033141828642328222291807 63049712742963492333437711)
              ·
                refine ⟨94574569114445238500156567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63049712742963492333437711 94574569114445238500156567)
                ·
                  refine ⟨141861853671667857750234851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94574569114445238500156567 141861853671667857750234851)
                  ·
                    refine ⟨212792780507501786625352277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 141861853671667857750234851 212792780507501786625352277)
                    ·
                      refine ⟨2493665396572286562015847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 212792780507501786625352277 2493665396572286562015847)
                      ·
                        rfl

theorem cell23_4856396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_4856396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856396 prefixEnd_4856396 := by exact prefixLift 4856396
  have htrace : WordTrace (prefixWord ++ tailWord_4856396) baseStart_4856396 baseEnd_4856396 := by
    simpa [prefixWord, tailWord_4856396, baseEnd_4856396] using wordTrace_append hprefix tailTrace_4856396
  have hstable : (prefixWord ++ tailWord_4856396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856396).length < 2 ^ (prefixWord ++ tailWord_4856396).sum := by decide
  have hdescent : baseEnd_4856396 < baseStart_4856396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856397 : List Nat := [1, 6, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_4856397 : Nat := 118140960795 + 4856397 * 2 ^ 59
def prefixEnd_4856397 : Nat := 4983230072969 + 3 ^ 40 * 4856397 * 2
def baseEnd_4856397 : Nat := 831221970017647019367781

theorem tailTrace_4856397 : CollatzResearch.WordTrace tailWord_4856397 prefixEnd_4856397 831221970017647019367781 := by
  unfold tailWord_4856397
  simp only [CollatzResearch.WordTrace]
  refine ⟨177127350187110550420279445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118084900124740366946852963 177127350187110550420279445)
  ·
    refine ⟨8302844540020807050950599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 177127350187110550420279445 8302844540020807050950599)
    ·
      refine ⟨12454266810031210576425899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8302844540020807050950599 12454266810031210576425899)
      ·
        refine ⟨18681400215046815864638849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12454266810031210576425899 18681400215046815864638849)
        ·
          refine ⟨14011050161285111898479137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18681400215046815864638849 14011050161285111898479137)
          ·
            refine ⟨10508287620963833923859353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14011050161285111898479137 10508287620963833923859353)
            ·
              refine ⟨7881215715722875442894515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10508287620963833923859353 7881215715722875442894515)
              ·
                refine ⟨11821823573584313164341773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7881215715722875442894515 11821823573584313164341773)
                ·
                  refine ⟨4433183840094117436628165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11821823573584313164341773 4433183840094117436628165)
                  ·
                    refine ⟨831221970017647019367781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4433183840094117436628165 831221970017647019367781)
                    ·
                      rfl

theorem cell23_4856397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_4856397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856397 prefixEnd_4856397 := by exact prefixLift 4856397
  have htrace : WordTrace (prefixWord ++ tailWord_4856397) baseStart_4856397 baseEnd_4856397 := by
    simpa [prefixWord, tailWord_4856397, baseEnd_4856397] using wordTrace_append hprefix tailTrace_4856397
  have hstable : (prefixWord ++ tailWord_4856397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856397).length < 2 ^ (prefixWord ++ tailWord_4856397).sum := by decide
  have hdescent : baseEnd_4856397 < baseStart_4856397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856416 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 7]
def baseStart_4856416 : Nat := 118140960795 + 4856416 * 2 ^ 59
def prefixEnd_4856416 : Nat := 4983230072969 + 3 ^ 40 * 4856416 * 2
def baseEnd_4856416 : Nat := 2493675666185376483765755

theorem tailTrace_4856416 : CollatzResearch.WordTrace tailWord_4856416 prefixEnd_4856416 2493675666185376483765755 := by
  unfold tailWord_4856416
  simp only [CollatzResearch.WordTrace]
  refine ⟨88564021587020858332610551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118085362116027811110147401 88564021587020858332610551)
  ·
    refine ⟨132846032380531287498915827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88564021587020858332610551 132846032380531287498915827)
    ·
      refine ⟨199269048570796931248373741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132846032380531287498915827 199269048570796931248373741)
      ·
        refine ⟨74725893214048849218140153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199269048570796931248373741 74725893214048849218140153)
        ·
          refine ⟨56044419910536636913605115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74725893214048849218140153 56044419910536636913605115)
          ·
            refine ⟨84066629865804955370407673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56044419910536636913605115 84066629865804955370407673)
            ·
              refine ⟨63049972399353716527805755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84066629865804955370407673 63049972399353716527805755)
              ·
                refine ⟨94574958599030574791708633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63049972399353716527805755 94574958599030574791708633)
                ·
                  refine ⟨70931218949272931093781475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94574958599030574791708633 70931218949272931093781475)
                  ·
                    refine ⟨106396828423909396640672213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70931218949272931093781475 106396828423909396640672213)
                    ·
                      refine ⟨2493675666185376483765755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 106396828423909396640672213 2493675666185376483765755)
                      ·
                        rfl

theorem cell23_4856416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_4856416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856416 prefixEnd_4856416 := by exact prefixLift 4856416
  have htrace : WordTrace (prefixWord ++ tailWord_4856416) baseStart_4856416 baseEnd_4856416 := by
    simpa [prefixWord, tailWord_4856416, baseEnd_4856416] using wordTrace_append hprefix tailTrace_4856416
  have hstable : (prefixWord ++ tailWord_4856416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856416).length < 2 ^ (prefixWord ++ tailWord_4856416).sum := by decide
  have hdescent : baseEnd_4856416 < baseStart_4856416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856420 : List Nat := [2, 3, 1, 1, 2, 2, 1, 4, 3, 1, 3]
def baseStart_4856420 : Nat := 118140960795 + 4856420 * 2 ^ 59
def prefixEnd_4856420 : Nat := 4983230072969 + 3 ^ 40 * 4856420 * 2
def baseEnd_4856420 : Nat := 2493677720107994468115737

theorem tailTrace_4856420 : CollatzResearch.WordTrace tailWord_4856420 prefixEnd_4856420 2493677720107994468115737 := by
  unfold tailWord_4856420
  simp only [CollatzResearch.WordTrace]
  refine ⟨88564094533013612674183357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118085459377351483565577809 88564094533013612674183357)
  ·
    refine ⟨33211535449880104752818759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88564094533013612674183357 33211535449880104752818759)
    ·
      refine ⟨49817303174820157129228139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33211535449880104752818759 49817303174820157129228139)
      ·
        refine ⟨74725954762230235693842209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49817303174820157129228139 74725954762230235693842209)
        ·
          refine ⟨56044466071672676770381657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74725954762230235693842209 56044466071672676770381657)
          ·
            refine ⟨42033349553754507577786243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56044466071672676770381657 42033349553754507577786243)
            ·
              refine ⟨63050024330631761366679365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42033349553754507577786243 63050024330631761366679365)
              ·
                refine ⟨11821879561993455256252381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63050024330631761366679365 11821879561993455256252381)
                ·
                  refine ⟨4433204835747545721094643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11821879561993455256252381 4433204835747545721094643)
                  ·
                    refine ⟨6649807253621318581641965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4433204835747545721094643 6649807253621318581641965)
                    ·
                      refine ⟨2493677720107994468115737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6649807253621318581641965 2493677720107994468115737)
                      ·
                        rfl

theorem cell23_4856420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_4856420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856420 prefixEnd_4856420 := by exact prefixLift 4856420
  have htrace : WordTrace (prefixWord ++ tailWord_4856420) baseStart_4856420 baseEnd_4856420 := by
    simpa [prefixWord, tailWord_4856420, baseEnd_4856420] using wordTrace_append hprefix tailTrace_4856420
  have hstable : (prefixWord ++ tailWord_4856420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856420).length < 2 ^ (prefixWord ++ tailWord_4856420).sum := by decide
  have hdescent : baseEnd_4856420 < baseStart_4856420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856463 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 3]
def baseStart_4856463 : Nat := 118140960795 + 4856463 * 2 ^ 59
def prefixEnd_4856463 : Nat := 4983230072969 + 3 ^ 40 * 4856463 * 2
def baseEnd_4856463 : Nat := 2493699799776137799878039

theorem tailTrace_4856463 : CollatzResearch.WordTrace tailWord_4856463 prefixEnd_4856463 2493699799776137799878039 := by
  unfold tailWord_4856463
  simp only [CollatzResearch.WordTrace]
  refine ⟨177129757404871443692182043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118086504936580962461454695 177129757404871443692182043)
  ·
    refine ⟨265694636107307165538273065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177129757404871443692182043 265694636107307165538273065)
    ·
      refine ⟨199270977080480374153704799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265694636107307165538273065 199270977080480374153704799)
      ·
        refine ⟨298906465620720561230557199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199270977080480374153704799 298906465620720561230557199)
        ·
          refine ⟨448359698431080841845835799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298906465620720561230557199 448359698431080841845835799)
          ·
            refine ⟨672539547646621262768753699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448359698431080841845835799 672539547646621262768753699)
            ·
              refine ⟨1008809321469931894153130549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672539547646621262768753699 1008809321469931894153130549)
              ·
                refine ⟨94575873887806115076855989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1008809321469931894153130549 94575873887806115076855989)
                ·
                  refine ⟨8866488176981823288455249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94575873887806115076855989 8866488176981823288455249)
                  ·
                    refine ⟨6649866132736367466341437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8866488176981823288455249 6649866132736367466341437)
                    ·
                      refine ⟨2493699799776137799878039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6649866132736367466341437 2493699799776137799878039)
                      ·
                        rfl

theorem cell23_4856463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 3].length) (baseStart_4856463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856463 prefixEnd_4856463 := by exact prefixLift 4856463
  have htrace : WordTrace (prefixWord ++ tailWord_4856463) baseStart_4856463 baseEnd_4856463 := by
    simpa [prefixWord, tailWord_4856463, baseEnd_4856463] using wordTrace_append hprefix tailTrace_4856463
  have hstable : (prefixWord ++ tailWord_4856463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856463).length < 2 ^ (prefixWord ++ tailWord_4856463).sum := by decide
  have hdescent : baseEnd_4856463 < baseStart_4856463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856473 : List Nat := [1, 2, 1, 2, 1, 2, 4, 3, 1, 2, 4]
def baseStart_4856473 : Nat := 118140960795 + 4856473 * 2 ^ 59
def prefixEnd_4856473 : Nat := 4983230072969 + 3 ^ 40 * 4856473 * 2
def baseEnd_4856473 : Nat := 2493704934582682760752993

theorem tailTrace_4856473 : CollatzResearch.WordTrace tailWord_4856473 prefixEnd_4856473 2493704934582682760752993 := by
  unfold tailWord_4856473
  simp only [CollatzResearch.WordTrace]
  refine ⟨177130122134835215400046073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118086748089890143600030715 177130122134835215400046073)
  ·
    refine ⟨132847591601126411550034555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177130122134835215400046073 132847591601126411550034555)
    ·
      refine ⟨199271387401689617325051833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132847591601126411550034555 199271387401689617325051833)
      ·
        refine ⟨149453540551267212993788875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199271387401689617325051833 149453540551267212993788875)
        ·
          refine ⟨224180310826900819490683313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149453540551267212993788875 224180310826900819490683313)
          ·
            refine ⟨168135233120175614618012485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224180310826900819490683313 168135233120175614618012485)
            ·
              refine ⟨31525356210032927740877341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 168135233120175614618012485 31525356210032927740877341)
              ·
                refine ⟨11822008578762347902829003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31525356210032927740877341 11822008578762347902829003)
                ·
                  refine ⟨17733012868143521854243505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11822008578762347902829003 17733012868143521854243505)
                  ·
                    refine ⟨13299759651107641390682629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17733012868143521854243505 13299759651107641390682629)
                    ·
                      refine ⟨2493704934582682760752993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13299759651107641390682629 2493704934582682760752993)
                      ·
                        rfl

theorem cell23_4856473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_4856473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856473 prefixEnd_4856473 := by exact prefixLift 4856473
  have htrace : WordTrace (prefixWord ++ tailWord_4856473) baseStart_4856473 baseEnd_4856473 := by
    simpa [prefixWord, tailWord_4856473, baseEnd_4856473] using wordTrace_append hprefix tailTrace_4856473
  have hstable : (prefixWord ++ tailWord_4856473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856473).length < 2 ^ (prefixWord ++ tailWord_4856473).sum := by decide
  have hdescent : baseEnd_4856473 < baseStart_4856473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856474 : List Nat := [3, 1, 1, 6, 1, 2, 1, 2, 1, 5]
def baseStart_4856474 : Nat := 118140960795 + 4856474 * 2 ^ 59
def prefixEnd_4856474 : Nat := 4983230072969 + 3 ^ 40 * 4856474 * 2
def baseEnd_4856474 : Nat := 831235149354445752280163

theorem tailTrace_4856474 : CollatzResearch.WordTrace tailWord_4856474 prefixEnd_4856474 831235149354445752280163 := by
  unfold tailWord_4856474
  simp only [CollatzResearch.WordTrace]
  refine ⟨44282539651957898142708119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118086772405221061713888317 44282539651957898142708119)
  ·
    refine ⟨66423809477936847214062179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44282539651957898142708119 66423809477936847214062179)
    ·
      refine ⟨99635714216905270821093269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66423809477936847214062179 99635714216905270821093269)
      ·
        refine ⟨4670424103917434569738747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99635714216905270821093269 4670424103917434569738747)
        ·
          refine ⟨7005636155876151854608121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4670424103917434569738747 7005636155876151854608121)
          ·
            refine ⟨5254227116907113890956091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7005636155876151854608121 5254227116907113890956091)
            ·
              refine ⟨7881340675360670836434137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5254227116907113890956091 7881340675360670836434137)
              ·
                refine ⟨5911005506520503127325603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7881340675360670836434137 5911005506520503127325603)
                ·
                  refine ⟨8866508259780754690988405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5911005506520503127325603 8866508259780754690988405)
                  ·
                    refine ⟨831235149354445752280163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8866508259780754690988405 831235149354445752280163)
                    ·
                      rfl

theorem cell23_4856474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 1, 5].length) (baseStart_4856474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856474 prefixEnd_4856474 := by exact prefixLift 4856474
  have htrace : WordTrace (prefixWord ++ tailWord_4856474) baseStart_4856474 baseEnd_4856474 := by
    simpa [prefixWord, tailWord_4856474, baseEnd_4856474] using wordTrace_append hprefix tailTrace_4856474
  have hstable : (prefixWord ++ tailWord_4856474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856474).length < 2 ^ (prefixWord ++ tailWord_4856474).sum := by decide
  have hdescent : baseEnd_4856474 < baseStart_4856474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856477 : List Nat := [1, 4, 2, 1, 1, 1, 2, 4, 3, 2, 2]
def baseStart_4856477 : Nat := 118140960795 + 4856477 * 2 ^ 59
def prefixEnd_4856477 : Nat := 4983230072969 + 3 ^ 40 * 4856477 * 2
def baseEnd_4856477 : Nat := 2493706988505300745102975

theorem tailTrace_4856477 : CollatzResearch.WordTrace tailWord_4856477 prefixEnd_4856477 2493706988505300745102975 := by
  unfold tailWord_4856477
  simp only [CollatzResearch.WordTrace]
  refine ⟨177130268026820724083191685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118086845351213816055461123 177130268026820724083191685)
  ·
    refine ⟨33211925255028885765598441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177130268026820724083191685 33211925255028885765598441)
    ·
      refine ⟨24908943941271664324198831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33211925255028885765598441 24908943941271664324198831)
      ·
        refine ⟨37363415911907496486298247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24908943941271664324198831 37363415911907496486298247)
        ·
          refine ⟨56045123867861244729447371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37363415911907496486298247 56045123867861244729447371)
          ·
            refine ⟨84067685801791867094171057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56045123867861244729447371 84067685801791867094171057)
            ·
              refine ⟨63050764351343900320628293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84067685801791867094171057 63050764351343900320628293)
              ·
                refine ⟨11822018315876981310117805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63050764351343900320628293 11822018315876981310117805)
                ·
                  refine ⟨4433256868453867991294177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11822018315876981310117805 4433256868453867991294177)
                  ·
                    refine ⟨3324942651340400993470633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4433256868453867991294177 3324942651340400993470633)
                    ·
                      refine ⟨2493706988505300745102975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3324942651340400993470633 2493706988505300745102975)
                      ·
                        rfl

theorem cell23_4856477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_4856477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856477 prefixEnd_4856477 := by exact prefixLift 4856477
  have htrace : WordTrace (prefixWord ++ tailWord_4856477) baseStart_4856477 baseEnd_4856477 := by
    simpa [prefixWord, tailWord_4856477, baseEnd_4856477] using wordTrace_append hprefix tailTrace_4856477
  have hstable : (prefixWord ++ tailWord_4856477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856477).length < 2 ^ (prefixWord ++ tailWord_4856477).sum := by decide
  have hdescent : baseEnd_4856477 < baseStart_4856477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856487 : List Nat := [1, 1, 6, 3, 1, 1, 1, 2, 1, 6]
def baseStart_4856487 : Nat := 118140960795 + 4856487 * 2 ^ 59
def prefixEnd_4856487 : Nat := 4983230072969 + 3 ^ 40 * 4856487 * 2
def baseEnd_4856487 : Nat := 831237374437281901992643

theorem tailTrace_4856487 : CollatzResearch.WordTrace tailWord_4856487 prefixEnd_4856487 831237374437281901992643 := by
  unfold tailWord_4856487
  simp only [CollatzResearch.WordTrace]
  refine ⟨177130632756784495791055715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118087088504522997194037143 177130632756784495791055715)
  ·
    refine ⟨265695949135176743686583573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177130632756784495791055715 265695949135176743686583573)
    ·
      refine ⟨12454497615711409860308605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 265695949135176743686583573 12454497615711409860308605)
      ·
        refine ⟨4670436605891778697615727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12454497615711409860308605 4670436605891778697615727)
        ·
          refine ⟨7005654908837668046423591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4670436605891778697615727 7005654908837668046423591)
          ·
            refine ⟨10508482363256502069635387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7005654908837668046423591 10508482363256502069635387)
            ·
              refine ⟨15762723544884753104453081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10508482363256502069635387 15762723544884753104453081)
              ·
                refine ⟨11822042658663564828339811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15762723544884753104453081 11822042658663564828339811)
                ·
                  refine ⟨17733063987995347242509717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11822042658663564828339811 17733063987995347242509717)
                  ·
                    refine ⟨831237374437281901992643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17733063987995347242509717 831237374437281901992643)
                    ·
                      rfl

theorem cell23_4856487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_4856487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856487 prefixEnd_4856487 := by exact prefixLift 4856487
  have htrace : WordTrace (prefixWord ++ tailWord_4856487) baseStart_4856487 baseEnd_4856487 := by
    simpa [prefixWord, tailWord_4856487, baseEnd_4856487] using wordTrace_append hprefix tailTrace_4856487
  have hstable : (prefixWord ++ tailWord_4856487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856487).length < 2 ^ (prefixWord ++ tailWord_4856487).sum := by decide
  have hdescent : baseEnd_4856487 < baseStart_4856487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856510 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3]
def baseStart_4856510 : Nat := 118140960795 + 4856510 * 2 ^ 59
def prefixEnd_4856510 : Nat := 4983230072969 + 3 ^ 40 * 4856510 * 2
def baseEnd_4856510 : Nat := 2493723933366899115990323

theorem tailTrace_4856510 : CollatzResearch.WordTrace tailWord_4856510 prefixEnd_4856510 2493723933366899115990323 := by
  unfold tailWord_4856510
  simp only [CollatzResearch.WordTrace]
  refine ⟨22141433954462646339892873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118087647757134113812761989 22141433954462646339892873)
  ·
    refine ⟨16606075465846984754919655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22141433954462646339892873 16606075465846984754919655)
    ·
      refine ⟨24909113198770477132379483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16606075465846984754919655 24909113198770477132379483)
      ·
        refine ⟨37363669798155715698569225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24909113198770477132379483 37363669798155715698569225)
        ·
          refine ⟨28022752348616786773926919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37363669798155715698569225 28022752348616786773926919)
          ·
            refine ⟨42034128522925180160890379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28022752348616786773926919 42034128522925180160890379)
            ·
              refine ⟨63051192784387770241335569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42034128522925180160890379 63051192784387770241335569)
              ·
                refine ⟨47288394588290827681001677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63051192784387770241335569 47288394588290827681001677)
                ·
                  refine ⟨17733147970609060380375629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47288394588290827681001677 17733147970609060380375629)
                  ·
                    refine ⟨6649930488978397642640861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17733147970609060380375629 6649930488978397642640861)
                    ·
                      refine ⟨2493723933366899115990323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6649930488978397642640861 2493723933366899115990323)
                      ·
                        rfl

theorem cell23_4856510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_4856510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856510 prefixEnd_4856510 := by exact prefixLift 4856510
  have htrace : WordTrace (prefixWord ++ tailWord_4856510) baseStart_4856510 baseEnd_4856510 := by
    simpa [prefixWord, tailWord_4856510, baseEnd_4856510] using wordTrace_append hprefix tailTrace_4856510
  have hstable : (prefixWord ++ tailWord_4856510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856510).length < 2 ^ (prefixWord ++ tailWord_4856510).sum := by decide
  have hdescent : baseEnd_4856510 < baseStart_4856510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856511 : List Nat := [1, 1, 2, 2, 2, 4, 4, 2, 1, 2, 2]
def baseStart_4856511 : Nat := 118140960795 + 4856511 * 2 ^ 59
def prefixEnd_4856511 : Nat := 4983230072969 + 3 ^ 40 * 4856511 * 2
def baseEnd_4856511 : Nat := 2493724446847553612077819

theorem tailTrace_4856511 : CollatzResearch.WordTrace tailWord_4856511 prefixEnd_4856511 2493724446847553612077819 := by
  unfold tailWord_4856511
  simp only [CollatzResearch.WordTrace]
  refine ⟨177131508108697547889929387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118087672072465031926619591 177131508108697547889929387)
  ·
    refine ⟨265697262163046321834894081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177131508108697547889929387 265697262163046321834894081)
    ·
      refine ⟨199272946622284741376170561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265697262163046321834894081 199272946622284741376170561)
      ·
        refine ⟨149454709966713556032127921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199272946622284741376170561 149454709966713556032127921)
        ·
          refine ⟨112091032475035167024095941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149454709966713556032127921 112091032475035167024095941)
          ·
            refine ⟨21017068589069093817017989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112091032475035167024095941 21017068589069093817017989)
            ·
              refine ⟨3940700360450455090690873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21017068589069093817017989 3940700360450455090690873)
              ·
                refine ⟨2955525270337841318018155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3940700360450455090690873 2955525270337841318018155)
                ·
                  refine ⟨4433287905506761977027233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2955525270337841318018155 4433287905506761977027233)
                  ·
                    refine ⟨3324965929130071482770425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4433287905506761977027233 3324965929130071482770425)
                    ·
                      refine ⟨2493724446847553612077819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3324965929130071482770425 2493724446847553612077819)
                      ·
                        rfl

theorem cell23_4856511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 1, 2, 2].length) (baseStart_4856511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856511 prefixEnd_4856511 := by exact prefixLift 4856511
  have htrace : WordTrace (prefixWord ++ tailWord_4856511) baseStart_4856511 baseEnd_4856511 := by
    simpa [prefixWord, tailWord_4856511, baseEnd_4856511] using wordTrace_append hprefix tailTrace_4856511
  have hstable : (prefixWord ++ tailWord_4856511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856511).length < 2 ^ (prefixWord ++ tailWord_4856511).sum := by decide
  have hdescent : baseEnd_4856511 < baseStart_4856511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856537 : List Nat := [1, 2, 1, 2, 3, 2, 2, 4, 1, 3, 2]
def baseStart_4856537 : Nat := 118140960795 + 4856537 * 2 ^ 59
def prefixEnd_4856537 : Nat := 4983230072969 + 3 ^ 40 * 4856537 * 2
def baseEnd_4856537 : Nat := 2493737797344570510352699

theorem tailTrace_4856537 : CollatzResearch.WordTrace tailWord_4856537 prefixEnd_4856537 2493737797344570510352699 := by
  unfold tailWord_4856537
  simp only [CollatzResearch.WordTrace]
  refine ⟨177132456406603354330375865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118088304271068902886917243 177132456406603354330375865)
  ·
    refine ⟨132849342304952515747781899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177132456406603354330375865 132849342304952515747781899)
    ·
      refine ⟨199274013457428773621672849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132849342304952515747781899 199274013457428773621672849)
      ·
        refine ⟨149455510093071580216254637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199274013457428773621672849 149455510093071580216254637)
        ·
          refine ⟨56045816284901842581095489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149455510093071580216254637 56045816284901842581095489)
          ·
            refine ⟨42034362213676381935821617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56045816284901842581095489 42034362213676381935821617)
            ·
              refine ⟨31525771660257286451866213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42034362213676381935821617 31525771660257286451866213)
              ·
                refine ⟨5911082186298241209724915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31525771660257286451866213 5911082186298241209724915)
                ·
                  refine ⟨8866623279447361814587373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5911082186298241209724915 8866623279447361814587373)
                  ·
                    refine ⟨3324983729792760680470265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8866623279447361814587373 3324983729792760680470265)
                    ·
                      refine ⟨2493737797344570510352699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3324983729792760680470265 2493737797344570510352699)
                      ·
                        rfl

theorem cell23_4856537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 3, 2].length) (baseStart_4856537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856537 prefixEnd_4856537 := by exact prefixLift 4856537
  have htrace : WordTrace (prefixWord ++ tailWord_4856537) baseStart_4856537 baseEnd_4856537 := by
    simpa [prefixWord, tailWord_4856537, baseEnd_4856537] using wordTrace_append hprefix tailTrace_4856537
  have hstable : (prefixWord ++ tailWord_4856537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856537).length < 2 ^ (prefixWord ++ tailWord_4856537).sum := by decide
  have hdescent : baseEnd_4856537 < baseStart_4856537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856553 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 2, 1, 5]
def baseStart_4856553 : Nat := 118140960795 + 4856553 * 2 ^ 59
def prefixEnd_4856553 : Nat := 4983230072969 + 3 ^ 40 * 4856553 * 2
def baseEnd_4856553 : Nat := 2493746013035042447752625

theorem tailTrace_4856553 : CollatzResearch.WordTrace tailWord_4856553 prefixEnd_4856553 2493746013035042447752625 := by
  unfold tailWord_4856553
  simp only [CollatzResearch.WordTrace]
  refine ⟨177133039974545389062958313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118088693316363592708638875 177133039974545389062958313)
  ·
    refine ⟨132849779980909041797218735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177133039974545389062958313 132849779980909041797218735)
    ·
      refine ⟨199274669971363562695828103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132849779980909041797218735 199274669971363562695828103)
      ·
        refine ⟨298912004957045344043742155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199274669971363562695828103 298912004957045344043742155)
        ·
          refine ⟨448368007435568016065613233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298912004957045344043742155 448368007435568016065613233)
          ·
            refine ⟨336276005576676012049209925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 448368007435568016065613233 336276005576676012049209925)
            ·
              refine ⟨63051751045626752259226861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 336276005576676012049209925 63051751045626752259226861)
              ·
                refine ⟨23644406642110032097210073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63051751045626752259226861 23644406642110032097210073)
                ·
                  refine ⟨17733304981582524072907555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23644406642110032097210073 17733304981582524072907555)
                  ·
                    refine ⟨26599957472373786109361333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17733304981582524072907555 26599957472373786109361333)
                    ·
                      refine ⟨2493746013035042447752625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26599957472373786109361333 2493746013035042447752625)
                      ·
                        rfl

theorem cell23_4856553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 1, 5].length) (baseStart_4856553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856553 prefixEnd_4856553 := by exact prefixLift 4856553
  have htrace : WordTrace (prefixWord ++ tailWord_4856553) baseStart_4856553 baseEnd_4856553 := by
    simpa [prefixWord, tailWord_4856553, baseEnd_4856553] using wordTrace_append hprefix tailTrace_4856553
  have hstable : (prefixWord ++ tailWord_4856553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856553).length < 2 ^ (prefixWord ++ tailWord_4856553).sum := by decide
  have hdescent : baseEnd_4856553 < baseStart_4856553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856580 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_4856580 : Nat := 118140960795 + 4856580 * 2 ^ 59
def prefixEnd_4856580 : Nat := 4983230072969 + 3 ^ 40 * 4856580 * 2
def baseEnd_4856580 : Nat := 2493759877012713842115001

theorem tailTrace_4856580 : CollatzResearch.WordTrace tailWord_4856580 prefixEnd_4856580 2493759877012713842115001 := by
  unfold tailWord_4856580
  simp only [CollatzResearch.WordTrace]
  refine ⟨88567012372723786337095597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118089349830298381782794129 88567012372723786337095597)
  ·
    refine ⟨33212629639771419876410849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88567012372723786337095597 33212629639771419876410849)
    ·
      refine ⟨24909472229828564907308137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33212629639771419876410849 24909472229828564907308137)
      ·
        refine ⟨18682104172371423680481103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24909472229828564907308137 18682104172371423680481103)
        ·
          refine ⟨28023156258557135520721655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18682104172371423680481103 28023156258557135520721655)
          ·
            refine ⟨42034734387835703281082483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28023156258557135520721655 42034734387835703281082483)
            ·
              refine ⟨63052101581753554921623725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42034734387835703281082483 63052101581753554921623725)
              ·
                refine ⟨23644538093157583095608897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63052101581753554921623725 23644538093157583095608897)
                ·
                  refine ⟨17733403569868187321706673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23644538093157583095608897 17733403569868187321706673)
                  ·
                    refine ⟨13300052677401140491280005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17733403569868187321706673 13300052677401140491280005)
                    ·
                      refine ⟨2493759877012713842115001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13300052677401140491280005 2493759877012713842115001)
                      ·
                        rfl

theorem cell23_4856580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_4856580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856580 prefixEnd_4856580 := by exact prefixLift 4856580
  have htrace : WordTrace (prefixWord ++ tailWord_4856580) baseStart_4856580 baseEnd_4856580 := by
    simpa [prefixWord, tailWord_4856580, baseEnd_4856580] using wordTrace_append hprefix tailTrace_4856580
  have hstable : (prefixWord ++ tailWord_4856580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856580).length < 2 ^ (prefixWord ++ tailWord_4856580).sum := by decide
  have hdescent : baseEnd_4856580 < baseStart_4856580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856584 : List Nat := [2, 1, 3, 2, 2, 4, 1, 1, 1, 4, 2]
def baseStart_4856584 : Nat := 118140960795 + 4856584 * 2 ^ 59
def prefixEnd_4856584 : Nat := 4983230072969 + 3 ^ 40 * 4856584 * 2
def baseEnd_4856584 : Nat := 2493761930935331826464983

theorem tailTrace_4856584 : CollatzResearch.WordTrace tailWord_4856584 prefixEnd_4856584 2493761930935331826464983 := by
  unfold tailWord_4856584
  simp only [CollatzResearch.WordTrace]
  refine ⟨88567085318716540678668403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118089447091622054238224537 88567085318716540678668403)
  ·
    refine ⟨132850627978074811018002605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88567085318716540678668403 132850627978074811018002605)
    ·
      refine ⟨49818985491778054131750977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132850627978074811018002605 49818985491778054131750977)
      ·
        refine ⟨37364239118833540598813233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49818985491778054131750977 37364239118833540598813233)
        ·
          refine ⟨28023179339125155449109925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37364239118833540598813233 28023179339125155449109925)
          ·
            refine ⟨5254346126085966646708111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28023179339125155449109925 5254346126085966646708111)
            ·
              refine ⟨7881519189128949970062167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5254346126085966646708111 7881519189128949970062167)
              ·
                refine ⟨11822278783693424955093251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7881519189128949970062167 11822278783693424955093251)
                ·
                  refine ⟨17733418175540137432639877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11822278783693424955093251 17733418175540137432639877)
                  ·
                    refine ⟨3325015907913775768619977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17733418175540137432639877 3325015907913775768619977)
                    ·
                      refine ⟨2493761930935331826464983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3325015907913775768619977 2493761930935331826464983)
                      ·
                        rfl

theorem cell23_4856584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_4856584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856584 prefixEnd_4856584 := by exact prefixLift 4856584
  have htrace : WordTrace (prefixWord ++ tailWord_4856584) baseStart_4856584 baseEnd_4856584 := by
    simpa [prefixWord, tailWord_4856584, baseEnd_4856584] using wordTrace_append hprefix tailTrace_4856584
  have hstable : (prefixWord ++ tailWord_4856584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856584).length < 2 ^ (prefixWord ++ tailWord_4856584).sum := by decide
  have hdescent : baseEnd_4856584 < baseStart_4856584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856607 : List Nat := [1, 1, 2, 4, 2, 2, 3, 3, 5]
def baseStart_4856607 : Nat := 118140960795 + 4856607 * 2 ^ 59
def prefixEnd_4856607 : Nat := 4983230072969 + 3 ^ 40 * 4856607 * 2
def baseEnd_4856607 : Nat := 277085971221153915164153

theorem tailTrace_4856607 : CollatzResearch.WordTrace tailWord_4856607 prefixEnd_4856607 277085971221153915164153 := by
  unfold tailWord_4856607
  simp only [CollatzResearch.WordTrace]
  refine ⟨177135009516349756285424075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118090006344233170856949383 177135009516349756285424075)
  ·
    refine ⟨265702514274524634428136113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177135009516349756285424075 265702514274524634428136113)
    ·
      refine ⟨199276885705893475821102085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265702514274524634428136113 199276885705893475821102085)
      ·
        refine ⟨37364416069855026716456641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199276885705893475821102085 37364416069855026716456641)
        ·
          refine ⟨28023312052391270037342481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37364416069855026716456641 28023312052391270037342481)
          ·
            refine ⟨21017484039293452528006861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28023312052391270037342481 21017484039293452528006861)
            ·
              refine ⟨7881556514735044698002573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21017484039293452528006861 7881556514735044698002573)
              ·
                refine ⟨2955583693025641761750965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7881556514735044698002573 2955583693025641761750965)
                ·
                  refine ⟨277085971221153915164153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2955583693025641761750965 277085971221153915164153)
                  ·
                    rfl

theorem cell23_4856607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 5].length) (baseStart_4856607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856607 prefixEnd_4856607 := by exact prefixLift 4856607
  have htrace : WordTrace (prefixWord ++ tailWord_4856607) baseStart_4856607 baseEnd_4856607 := by
    simpa [prefixWord, tailWord_4856607, baseEnd_4856607] using wordTrace_append hprefix tailTrace_4856607
  have hstable : (prefixWord ++ tailWord_4856607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856607).length < 2 ^ (prefixWord ++ tailWord_4856607).sum := by decide
  have hdescent : baseEnd_4856607 < baseStart_4856607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856620 : List Nat := [2, 2, 1, 1, 1, 4, 3, 2, 2, 5]
def baseStart_4856620 : Nat := 118140960795 + 4856620 * 2 ^ 59
def prefixEnd_4856620 : Nat := 4983230072969 + 3 ^ 40 * 4856620 * 2
def baseEnd_4856620 : Nat := 831260138746297895204939

theorem tailTrace_4856620 : CollatzResearch.WordTrace tailWord_4856620 prefixEnd_4856620 831260138746297895204939 := by
  unfold tailWord_4856620
  simp only [CollatzResearch.WordTrace]
  refine ⟨88567741832651329752823657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118090322443535106337098209 88567741832651329752823657)
  ·
    refine ⟨66425806374488497314617743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88567741832651329752823657 66425806374488497314617743)
    ·
      refine ⟨99638709561732745971926615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66425806374488497314617743 99638709561732745971926615)
      ·
        refine ⟨149458064342599118957889923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99638709561732745971926615 149458064342599118957889923)
        ·
          refine ⟨224187096513898678436834885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149458064342599118957889923 224187096513898678436834885)
          ·
            refine ⟨42035080596356002206906541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 224187096513898678436834885 42035080596356002206906541)
            ·
              refine ⟨15763155223633500827589953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42035080596356002206906541 15763155223633500827589953)
              ·
                refine ⟨11822366417725125620692465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15763155223633500827589953 11822366417725125620692465)
                ·
                  refine ⟨8866774813293844215519349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11822366417725125620692465 8866774813293844215519349)
                  ·
                    refine ⟨831260138746297895204939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8866774813293844215519349 831260138746297895204939)
                    ·
                      rfl

theorem cell23_4856620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_4856620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856620 prefixEnd_4856620 := by exact prefixLift 4856620
  have htrace : WordTrace (prefixWord ++ tailWord_4856620) baseStart_4856620 baseEnd_4856620 := by
    simpa [prefixWord, tailWord_4856620, baseEnd_4856620] using wordTrace_append hprefix tailTrace_4856620
  have hstable : (prefixWord ++ tailWord_4856620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856620).length < 2 ^ (prefixWord ++ tailWord_4856620).sum := by decide
  have hdescent : baseEnd_4856620 < baseStart_4856620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856677 : List Nat := [1, 3, 1, 3, 1, 1, 4, 2, 2, 2, 3]
def baseStart_4856677 : Nat := 118140960795 + 4856677 * 2 ^ 59
def prefixEnd_4856677 : Nat := 4983230072969 + 3 ^ 40 * 4856677 * 2
def baseEnd_4856677 : Nat := 2493809684636199962602055

theorem tailTrace_4856677 : CollatzResearch.WordTrace tailWord_4856677 prefixEnd_4856677 2493809684636199962602055 := by
  unfold tailWord_4856677
  simp only [CollatzResearch.WordTrace]
  refine ⟨177137562626096158240472285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118091708417397438826981523 177137562626096158240472285)
  ·
    refine ⟨66426585984786059340177107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177137562626096158240472285 66426585984786059340177107)
    ·
      refine ⟨99639878977179089010265661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66426585984786059340177107 99639878977179089010265661)
      ·
        refine ⟨37364954616442158378849623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99639878977179089010265661 37364954616442158378849623)
        ·
          refine ⟨56047431924663237568274435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37364954616442158378849623 56047431924663237568274435)
          ·
            refine ⟨84071147886994856352411653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56047431924663237568274435 84071147886994856352411653)
            ·
              refine ⟨15763340228811535566077185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84071147886994856352411653 15763340228811535566077185)
              ·
                refine ⟨11822505171608651674557889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15763340228811535566077185 11822505171608651674557889)
                ·
                  refine ⟨8866878878706488755918417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11822505171608651674557889 8866878878706488755918417)
                  ·
                    refine ⟨6650159159029866566938813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8866878878706488755918417 6650159159029866566938813)
                    ·
                      refine ⟨2493809684636199962602055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6650159159029866566938813 2493809684636199962602055)
                      ·
                        rfl

theorem cell23_4856677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_4856677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856677 prefixEnd_4856677 := by exact prefixLift 4856677
  have htrace : WordTrace (prefixWord ++ tailWord_4856677) baseStart_4856677 baseEnd_4856677 := by
    simpa [prefixWord, tailWord_4856677, baseEnd_4856677] using wordTrace_append hprefix tailTrace_4856677
  have hstable : (prefixWord ++ tailWord_4856677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856677).length < 2 ^ (prefixWord ++ tailWord_4856677).sum := by decide
  have hdescent : baseEnd_4856677 < baseStart_4856677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856684 : List Nat := [2, 2, 1, 1, 4, 1, 3, 4, 1, 4]
def baseStart_4856684 : Nat := 118140960795 + 4856684 * 2 ^ 59
def prefixEnd_4856684 : Nat := 4983230072969 + 3 ^ 40 * 4856684 * 2
def baseEnd_4856684 : Nat := 831271093000260478404841

theorem tailTrace_4856684 : CollatzResearch.WordTrace tailWord_4856684 prefixEnd_4856684 831271093000260478404841 := by
  unfold tailWord_4856684
  simp only [CollatzResearch.WordTrace]
  refine ⟨88568908968535399217988553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118091878624713865623984737 88568908968535399217988553)
  ·
    refine ⟨66426681726401549413491415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88568908968535399217988553 66426681726401549413491415)
    ·
      refine ⟨99640022589602324120237123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66426681726401549413491415 99640022589602324120237123)
      ·
        refine ⟨149460033884403486180355685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99640022589602324120237123 149460033884403486180355685)
        ·
          refine ⟨28023756353325653658816691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149460033884403486180355685 28023756353325653658816691)
          ·
            refine ⟨42035634529988480488225037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28023756353325653658816691 42035634529988480488225037)
            ·
              refine ⟨15763362948745680183084389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42035634529988480488225037 15763362948745680183084389)
              ·
                refine ⟨2955630552889815034328323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15763362948745680183084389 2955630552889815034328323)
                ·
                  refine ⟨4433445829334722551492485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2955630552889815034328323 4433445829334722551492485)
                  ·
                    refine ⟨831271093000260478404841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4433445829334722551492485 831271093000260478404841)
                    ·
                      rfl

theorem cell23_4856684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 1, 4].length) (baseStart_4856684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856684 prefixEnd_4856684 := by exact prefixLift 4856684
  have htrace : WordTrace (prefixWord ++ tailWord_4856684) baseStart_4856684 baseEnd_4856684 := by
    simpa [prefixWord, tailWord_4856684, baseEnd_4856684] using wordTrace_append hprefix tailTrace_4856684
  have hstable : (prefixWord ++ tailWord_4856684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856684).length < 2 ^ (prefixWord ++ tailWord_4856684).sum := by decide
  have hdescent : baseEnd_4856684 < baseStart_4856684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856724 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_4856724 : Nat := 118140960795 + 4856724 * 2 ^ 59
def prefixEnd_4856724 : Nat := 4983230072969 + 3 ^ 40 * 4856724 * 2
def baseEnd_4856724 : Nat := 2493833818226961278714339

theorem tailTrace_4856724 : CollatzResearch.WordTrace tailWord_4856724 prefixEnd_4856724 2493833818226961278714339 := by
  unfold tailWord_4856724
  simp only [CollatzResearch.WordTrace]
  refine ⟨88569638428462942633716613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118092851237950590178288817 88569638428462942633716613)
  ·
    refine ⟨16606807205336801743821865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88569638428462942633716613 16606807205336801743821865)
    ·
      refine ⟨12455105404002601307866399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16606807205336801743821865 12455105404002601307866399)
      ·
        refine ⟨18682658106003901961799599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12455105404002601307866399 18682658106003901961799599)
        ·
          refine ⟨28023987159005852942699399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18682658106003901961799599 28023987159005852942699399)
          ·
            refine ⟨42035980738508779414049099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28023987159005852942699399 42035980738508779414049099)
            ·
              refine ⟨63053971107763169121073649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42035980738508779414049099 63053971107763169121073649)
              ·
                refine ⟨47290478330822376840805237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63053971107763169121073649 47290478330822376840805237)
                ·
                  refine ⟨4433482343514597828825491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47290478330822376840805237 4433482343514597828825491)
                  ·
                    refine ⟨6650223515271896743238237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4433482343514597828825491 6650223515271896743238237)
                    ·
                      refine ⟨2493833818226961278714339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6650223515271896743238237 2493833818226961278714339)
                      ·
                        rfl

theorem cell23_4856724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_4856724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856724 prefixEnd_4856724 := by exact prefixLift 4856724
  have htrace : WordTrace (prefixWord ++ tailWord_4856724) baseStart_4856724 baseEnd_4856724 := by
    simpa [prefixWord, tailWord_4856724, baseEnd_4856724] using wordTrace_append hprefix tailTrace_4856724
  have hstable : (prefixWord ++ tailWord_4856724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856724).length < 2 ^ (prefixWord ++ tailWord_4856724).sum := by decide
  have hdescent : baseEnd_4856724 < baseStart_4856724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856727 : List Nat := [1, 1, 3, 3, 1, 2, 3, 3, 1, 5]
def baseStart_4856727 : Nat := 118140960795 + 4856727 * 2 ^ 59
def prefixEnd_4856727 : Nat := 4983230072969 + 3 ^ 40 * 4856727 * 2
def baseEnd_4856727 : Nat := 831278452889641588992275

theorem tailTrace_4856727 : CollatzResearch.WordTrace tailWord_4856727 prefixEnd_4856727 831278452889641588992275 := by
  unfold tailWord_4856727
  simp only [CollatzResearch.WordTrace]
  refine ⟨177139386275915016779792435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118092924183943344519861623 177139386275915016779792435)
  ·
    refine ⟨265709079413872525169688653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177139386275915016779792435 265709079413872525169688653)
    ·
      refine ⟨99640904780202196938633245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265709079413872525169688653 99640904780202196938633245)
      ·
        refine ⟨37365339292575823851987467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99640904780202196938633245 37365339292575823851987467)
        ·
          refine ⟨56048008938863735777981201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37365339292575823851987467 56048008938863735777981201)
          ·
            refine ⟨42036006704147801833485901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56048008938863735777981201 42036006704147801833485901)
            ·
              refine ⟨15763502514055425687557213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42036006704147801833485901 15763502514055425687557213)
              ·
                refine ⟨5911313442770784632833955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15763502514055425687557213 5911313442770784632833955)
                ·
                  refine ⟨8866970164156176949250933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5911313442770784632833955 8866970164156176949250933)
                  ·
                    refine ⟨831278452889641588992275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8866970164156176949250933 831278452889641588992275)
                    ·
                      rfl

theorem cell23_4856727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 5].length) (baseStart_4856727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856727 prefixEnd_4856727 := by exact prefixLift 4856727
  have htrace : WordTrace (prefixWord ++ tailWord_4856727) baseStart_4856727 baseEnd_4856727 := by
    simpa [prefixWord, tailWord_4856727, baseEnd_4856727] using wordTrace_append hprefix tailTrace_4856727
  have hstable : (prefixWord ++ tailWord_4856727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856727).length < 2 ^ (prefixWord ++ tailWord_4856727).sum := by decide
  have hdescent : baseEnd_4856727 < baseStart_4856727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856857 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 2, 4, 3]
def baseStart_4856857 : Nat := 118140960795 + 4856857 * 2 ^ 59
def prefixEnd_4856857 : Nat := 4983230072969 + 3 ^ 40 * 4856857 * 2
def baseEnd_4856857 : Nat := 2493902111154009258351227

theorem tailTrace_4856857 : CollatzResearch.WordTrace tailWord_4856857 prefixEnd_4856857 2493902111154009258351227 := by
  unfold tailWord_4856857
  simp only [CollatzResearch.WordTrace]
  refine ⟨177144127765444048982024825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118096085176962699321349883 177144127765444048982024825)
  ·
    refine ⟨132858095824083036736518619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177144127765444048982024825 132858095824083036736518619)
    ·
      refine ⟨199287143736124555104777929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132858095824083036736518619 199287143736124555104777929)
      ·
        refine ⟨149465357802093416328583447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199287143736124555104777929 149465357802093416328583447)
        ·
          refine ⟨224198036703140124492875171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149465357802093416328583447 224198036703140124492875171)
          ·
            refine ⟨336297055054710186739312757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224198036703140124492875171 336297055054710186739312757)
            ·
              refine ⟨31527848911379080006810571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 336297055054710186739312757 31527848911379080006810571)
              ·
                refine ⟨47291773367068620010215857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31527848911379080006810571 47291773367068620010215857)
                ·
                  refine ⟨35468830025301465007661893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47291773367068620010215857 35468830025301465007661893)
                  ·
                    refine ⟨6650405629744024688936605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35468830025301465007661893 6650405629744024688936605)
                    ·
                      refine ⟨2493902111154009258351227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6650405629744024688936605 2493902111154009258351227)
                      ·
                        rfl

theorem cell23_4856857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 4, 3].length) (baseStart_4856857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856857 prefixEnd_4856857 := by exact prefixLift 4856857
  have htrace : WordTrace (prefixWord ++ tailWord_4856857) baseStart_4856857 baseEnd_4856857 := by
    simpa [prefixWord, tailWord_4856857, baseEnd_4856857] using wordTrace_append hprefix tailTrace_4856857
  have hstable : (prefixWord ++ tailWord_4856857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856857).length < 2 ^ (prefixWord ++ tailWord_4856857).sum := by decide
  have hdescent : baseEnd_4856857 < baseStart_4856857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856867 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 4]
def baseStart_4856867 : Nat := 118140960795 + 4856867 * 2 ^ 59
def prefixEnd_4856867 : Nat := 4983230072969 + 3 ^ 40 * 4856867 * 2
def baseEnd_4856867 : Nat := 2493907245960554219226181

theorem tailTrace_4856867 : CollatzResearch.WordTrace tailWord_4856867 prefixEnd_4856867 2493907245960554219226181 := by
  unfold tailWord_4856867
  simp only [CollatzResearch.WordTrace]
  refine ⟨177144492495407820689888855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118096328330271880459925903 177144492495407820689888855)
  ·
    refine ⟨265716738743111731034833283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177144492495407820689888855 265716738743111731034833283)
    ·
      refine ⟨398575108114667596552249925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265716738743111731034833283 398575108114667596552249925)
      ·
        refine ⟨74732832771500174353546861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 398575108114667596552249925 74732832771500174353546861)
        ·
          refine ⟨28024812289312565382580073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74732832771500174353546861 28024812289312565382580073)
          ·
            refine ⟨21018609216984424036935055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28024812289312565382580073 21018609216984424036935055)
            ·
              refine ⟨31527913825476636055402583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21018609216984424036935055 31527913825476636055402583)
              ·
                refine ⟨47291870738214954083103875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31527913825476636055402583 47291870738214954083103875)
                ·
                  refine ⟨70937806107322431124655813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47291870738214954083103875 70937806107322431124655813)
                  ·
                    refine ⟨13300838645122955835872965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70937806107322431124655813 13300838645122955835872965)
                    ·
                      refine ⟨2493907245960554219226181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13300838645122955835872965 2493907245960554219226181)
                      ·
                        rfl

theorem cell23_4856867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_4856867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856867 prefixEnd_4856867 := by exact prefixLift 4856867
  have htrace : WordTrace (prefixWord ++ tailWord_4856867) baseStart_4856867 baseEnd_4856867 := by
    simpa [prefixWord, tailWord_4856867, baseEnd_4856867] using wordTrace_append hprefix tailTrace_4856867
  have hstable : (prefixWord ++ tailWord_4856867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856867).length < 2 ^ (prefixWord ++ tailWord_4856867).sum := by decide
  have hdescent : baseEnd_4856867 < baseStart_4856867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856887 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 3]
def baseStart_4856887 : Nat := 118140960795 + 4856887 * 2 ^ 59
def prefixEnd_4856887 : Nat := 4983230072969 + 3 ^ 40 * 4856887 * 2
def baseEnd_4856887 : Nat := 2493917515573644140976089

theorem tailTrace_4856887 : CollatzResearch.WordTrace tailWord_4856887 prefixEnd_4856887 2493917515573644140976089 := by
  unfold tailWord_4856887
  simp only [CollatzResearch.WordTrace]
  refine ⟨177145221955335364105616915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118096814636890242737077943 177145221955335364105616915)
  ·
    refine ⟨265717832933003046158425373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177145221955335364105616915 265717832933003046158425373)
    ·
      refine ⟨99644187349876142309409515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265717832933003046158425373 99644187349876142309409515)
      ·
        refine ⟨149466281024814213464114273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99644187349876142309409515 149466281024814213464114273)
        ·
          refine ⟨112099710768610660098085705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149466281024814213464114273 112099710768610660098085705)
          ·
            refine ⟨84074783076457995073564279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112099710768610660098085705 84074783076457995073564279)
            ·
              refine ⟨126112174614686992610346419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84074783076457995073564279 126112174614686992610346419)
              ·
                refine ⟨189168261922030488915519629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126112174614686992610346419 189168261922030488915519629)
                ·
                  refine ⟨70938098220761433343319861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189168261922030488915519629 70938098220761433343319861)
                  ·
                    refine ⟨6650446708196384375936237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70938098220761433343319861 6650446708196384375936237)
                    ·
                      refine ⟨2493917515573644140976089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6650446708196384375936237 2493917515573644140976089)
                      ·
                        rfl

theorem cell23_4856887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 3].length) (baseStart_4856887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856887 prefixEnd_4856887 := by exact prefixLift 4856887
  have htrace : WordTrace (prefixWord ++ tailWord_4856887) baseStart_4856887 baseEnd_4856887 := by
    simpa [prefixWord, tailWord_4856887, baseEnd_4856887] using wordTrace_append hprefix tailTrace_4856887
  have hstable : (prefixWord ++ tailWord_4856887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856887).length < 2 ^ (prefixWord ++ tailWord_4856887).sum := by decide
  have hdescent : baseEnd_4856887 < baseStart_4856887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856917 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 1, 1, 7]
def baseStart_4856917 : Nat := 118140960795 + 4856917 * 2 ^ 59
def prefixEnd_4856917 : Nat := 4983230072969 + 3 ^ 40 * 4856917 * 2
def baseEnd_4856917 : Nat := 2493932919993279023600951

theorem tailTrace_4856917 : CollatzResearch.WordTrace tailWord_4856917 prefixEnd_4856917 2493932919993279023600951 := by
  unfold tailWord_4856917
  simp only [CollatzResearch.WordTrace]
  refine ⟨177146316145226679229209005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118097544096817786152806003 177146316145226679229209005)
  ·
    refine ⟨66429868554460004710953377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177146316145226679229209005 66429868554460004710953377)
    ·
      refine ⟨49822401415845003533215033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66429868554460004710953377 49822401415845003533215033)
      ·
        refine ⟨37366801061883752649911275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49822401415845003533215033 37366801061883752649911275)
        ·
          refine ⟨56050201592825628974866913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37366801061883752649911275 56050201592825628974866913)
          ·
            refine ⟨42037651194619221731150185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56050201592825628974866913 42037651194619221731150185)
            ·
              refine ⟨31528238395964416298362639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42037651194619221731150185 31528238395964416298362639)
              ·
                refine ⟨47292357593946624447543959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31528238395964416298362639 47292357593946624447543959)
                ·
                  refine ⟨70938536390919936671315939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47292357593946624447543959 70938536390919936671315939)
                  ·
                    refine ⟨106407804586379905006973909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70938536390919936671315939 106407804586379905006973909)
                    ·
                      refine ⟨2493932919993279023600951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 106407804586379905006973909 2493932919993279023600951)
                      ·
                        rfl

theorem cell23_4856917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_4856917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856917 prefixEnd_4856917 := by exact prefixLift 4856917
  have htrace : WordTrace (prefixWord ++ tailWord_4856917) baseStart_4856917 baseEnd_4856917 := by
    simpa [prefixWord, tailWord_4856917, baseEnd_4856917] using wordTrace_append hprefix tailTrace_4856917
  have hstable : (prefixWord ++ tailWord_4856917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856917).length < 2 ^ (prefixWord ++ tailWord_4856917).sum := by decide
  have hdescent : baseEnd_4856917 < baseStart_4856917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856927 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 4]
def baseStart_4856927 : Nat := 118140960795 + 4856927 * 2 ^ 59
def prefixEnd_4856927 : Nat := 4983230072969 + 3 ^ 40 * 4856927 * 2
def baseEnd_4856927 : Nat := 2493938054799823984475905

theorem tailTrace_4856927 : CollatzResearch.WordTrace tailWord_4856927 prefixEnd_4856927 2493938054799823984475905 := by
  unfold tailWord_4856927
  simp only [CollatzResearch.WordTrace]
  refine ⟨177146680875190450937073035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118097787250126967291382023 177146680875190450937073035)
  ·
    refine ⟨265720021312785676405609553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177146680875190450937073035 265720021312785676405609553)
    ·
      refine ⟨199290015984589257304207165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265720021312785676405609553 199290015984589257304207165)
      ·
        refine ⟨74733755994220971489077687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199290015984589257304207165 74733755994220971489077687)
        ·
          refine ⟨112100633991331457233616531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74733755994220971489077687 112100633991331457233616531)
          ·
            refine ⟨168150950986997185850424797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112100633991331457233616531 168150950986997185850424797)
            ·
              refine ⟨63056606620123944693909299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168150950986997185850424797 63056606620123944693909299)
              ·
                refine ⟨94584909930185917040863949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63056606620123944693909299 94584909930185917040863949)
                ·
                  refine ⟨35469341223819718890323981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94584909930185917040863949 35469341223819718890323981)
                  ·
                    refine ⟨13301002958932394583871493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35469341223819718890323981 13301002958932394583871493)
                    ·
                      refine ⟨2493938054799823984475905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13301002958932394583871493 2493938054799823984475905)
                      ·
                        rfl

theorem cell23_4856927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_4856927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856927 prefixEnd_4856927 := by exact prefixLift 4856927
  have htrace : WordTrace (prefixWord ++ tailWord_4856927) baseStart_4856927 baseEnd_4856927 := by
    simpa [prefixWord, tailWord_4856927, baseEnd_4856927] using wordTrace_append hprefix tailTrace_4856927
  have hstable : (prefixWord ++ tailWord_4856927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856927).length < 2 ^ (prefixWord ++ tailWord_4856927).sum := by decide
  have hdescent : baseEnd_4856927 < baseStart_4856927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856944 : List Nat := [2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 4]
def baseStart_4856944 : Nat := 118140960795 + 4856944 * 2 ^ 59
def prefixEnd_4856944 : Nat := 4983230072969 + 3 ^ 40 * 4856944 * 2
def baseEnd_4856944 : Nat := 2493946783970950417963327

theorem tailTrace_4856944 : CollatzResearch.WordTrace tailWord_4856944 prefixEnd_4856944 2493946783970950417963327 := by
  unfold tailWord_4856944
  simp only [CollatzResearch.WordTrace]
  refine ⟨88573650458064431420220943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118098200610752575226961257 88573650458064431420220943)
  ·
    refine ⟨132860475687096647130331415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88573650458064431420220943 132860475687096647130331415)
    ·
      refine ⟨199290713530644970695497123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132860475687096647130331415 199290713530644970695497123)
      ·
        refine ⟨298936070295967456043245685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199290713530644970695497123 298936070295967456043245685)
        ·
          refine ⟨28025256590246949004054283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 298936070295967456043245685 28025256590246949004054283)
          ·
            refine ⟨42037884885370423506081425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28025256590246949004054283 42037884885370423506081425)
            ·
              refine ⟨31528413664027817629561069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42037884885370423506081425 31528413664027817629561069)
              ·
                refine ⟨11823155124010431611085401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31528413664027817629561069 11823155124010431611085401)
                ·
                  refine ⟨8867366343007823708314051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11823155124010431611085401 8867366343007823708314051)
                  ·
                    refine ⟨13301049514511735562471077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8867366343007823708314051 13301049514511735562471077)
                    ·
                      refine ⟨2493946783970950417963327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13301049514511735562471077 2493946783970950417963327)
                      ·
                        rfl

theorem cell23_4856944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 4].length) (baseStart_4856944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856944 prefixEnd_4856944 := by exact prefixLift 4856944
  have htrace : WordTrace (prefixWord ++ tailWord_4856944) baseStart_4856944 baseEnd_4856944 := by
    simpa [prefixWord, tailWord_4856944, baseEnd_4856944] using wordTrace_append hprefix tailTrace_4856944
  have hstable : (prefixWord ++ tailWord_4856944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856944).length < 2 ^ (prefixWord ++ tailWord_4856944).sum := by decide
  have hdescent : baseEnd_4856944 < baseStart_4856944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856961 : List Nat := [1, 2, 4, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_4856961 : Nat := 118140960795 + 4856961 * 2 ^ 59
def prefixEnd_4856961 : Nat := 4983230072969 + 3 ^ 40 * 4856961 * 2
def baseEnd_4856961 : Nat := 2493955513142076851450749

theorem tailTrace_4856961 : CollatzResearch.WordTrace tailWord_4856961 prefixEnd_4856961 2493955513142076851450749 := by
  unfold tailWord_4856961
  simp only [CollatzResearch.WordTrace]
  refine ⟨177147920957067274743810737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118098613971378183162540491 177147920957067274743810737)
  ·
    refine ⟨132860940717800456057858053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177147920957067274743810737 132860940717800456057858053)
    ·
      refine ⟨24911426384587585510848385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132860940717800456057858053 24911426384587585510848385)
      ·
        refine ⟨18683569788440689133136289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24911426384587585510848385 18683569788440689133136289)
        ·
          refine ⟨14012677341330516849852217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18683569788440689133136289 14012677341330516849852217)
          ·
            refine ⟨10509508005997887637389163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14012677341330516849852217 10509508005997887637389163)
            ·
              refine ⟨15764262008996831456083745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10509508005997887637389163 15764262008996831456083745)
              ·
                refine ⟨11823196506747623592062809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15764262008996831456083745 11823196506747623592062809)
                ·
                  refine ⟨8867397380060717694047107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11823196506747623592062809 8867397380060717694047107)
                  ·
                    refine ⟨13301096070091076541070661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8867397380060717694047107 13301096070091076541070661)
                    ·
                      refine ⟨2493955513142076851450749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13301096070091076541070661 2493955513142076851450749)
                      ·
                        rfl

theorem cell23_4856961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_4856961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856961 prefixEnd_4856961 := by exact prefixLift 4856961
  have htrace : WordTrace (prefixWord ++ tailWord_4856961) baseStart_4856961 baseEnd_4856961 := by
    simpa [prefixWord, tailWord_4856961, baseEnd_4856961] using wordTrace_append hprefix tailTrace_4856961
  have hstable : (prefixWord ++ tailWord_4856961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856961).length < 2 ^ (prefixWord ++ tailWord_4856961).sum := by decide
  have hdescent : baseEnd_4856961 < baseStart_4856961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4856971 : List Nat := [1, 1, 1, 1, 4, 1, 1, 8, 1, 4]
def baseStart_4856971 : Nat := 118140960795 + 4856971 * 2 ^ 59
def prefixEnd_4856971 : Nat := 4983230072969 + 3 ^ 40 * 4856971 * 2
def baseEnd_4856971 : Nat := 831320215982873937441901

theorem tailTrace_4856971 : CollatzResearch.WordTrace tailWord_4856971 prefixEnd_4856971 831320215982873937441901 := by
  unfold tailWord_4856971
  simp only [CollatzResearch.WordTrace]
  refine ⟨177148285687031046451674767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118098857124687364301116511 177148285687031046451674767)
  ·
    refine ⟨265722428530546569677512151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177148285687031046451674767 265722428530546569677512151)
    ·
      refine ⟨398583642795819854516268227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265722428530546569677512151 398583642795819854516268227)
      ·
        refine ⟨597875464193729781774402341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398583642795819854516268227 597875464193729781774402341)
        ·
          refine ⟨112101649536324334082700439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 597875464193729781774402341 112101649536324334082700439)
          ·
            refine ⟨168152474304486501124050659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112101649536324334082700439 168152474304486501124050659)
            ·
              refine ⟨252228711456729751686075989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168152474304486501124050659 252228711456729751686075989)
              ·
                refine ⟨2955805212383551777571203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 252228711456729751686075989 2955805212383551777571203)
                ·
                  refine ⟨4433707818575327666356805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2955805212383551777571203 4433707818575327666356805)
                  ·
                    refine ⟨831320215982873937441901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4433707818575327666356805 831320215982873937441901)
                    ·
                      rfl

theorem cell23_4856971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 1, 4].length) (baseStart_4856971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4856971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4856971 prefixEnd_4856971 := by exact prefixLift 4856971
  have htrace : WordTrace (prefixWord ++ tailWord_4856971) baseStart_4856971 baseEnd_4856971 := by
    simpa [prefixWord, tailWord_4856971, baseEnd_4856971] using wordTrace_append hprefix tailTrace_4856971
  have hstable : (prefixWord ++ tailWord_4856971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4856971).length < 2 ^ (prefixWord ++ tailWord_4856971).sum := by decide
  have hdescent : baseEnd_4856971 < baseStart_4856971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4856971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857022 : List Nat := [4, 2, 1, 1, 3, 3, 2, 2, 1, 4]
def baseStart_4857022 : Nat := 118140960795 + 4857022 * 2 ^ 59
def prefixEnd_4857022 : Nat := 4983230072969 + 3 ^ 40 * 4857022 * 2
def baseEnd_4857022 : Nat := 831328945154000370929323

theorem tailTrace_4857022 : CollatzResearch.WordTrace tailWord_4857022 prefixEnd_4857022 831328945154000370929323 := by
  unfold tailWord_4857022
  simp only [CollatzResearch.WordTrace]
  refine ⟨22143768226230785270222665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118100097206564188107854213 22143768226230785270222665)
  ·
    refine ⟨16607826169673088952666999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22143768226230785270222665 16607826169673088952666999)
    ·
      refine ⟨24911739254509633429000499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16607826169673088952666999 24911739254509633429000499)
      ·
        refine ⟨37367608881764450143500749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24911739254509633429000499 37367608881764450143500749)
        ·
          refine ⟨14012853330661668803812781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37367608881764450143500749 14012853330661668803812781)
          ·
            refine ⟨5254819998998125801429793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14012853330661668803812781 5254819998998125801429793)
            ·
              refine ⟨3941114999248594351072345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5254819998998125801429793 3941114999248594351072345)
              ·
                refine ⟨2955836249436445763304259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3941114999248594351072345 2955836249436445763304259)
                ·
                  refine ⟨4433754374154668644956389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2955836249436445763304259 4433754374154668644956389)
                  ·
                    refine ⟨831328945154000370929323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4433754374154668644956389 831328945154000370929323)
                    ·
                      rfl

theorem cell23_4857022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_4857022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857022 prefixEnd_4857022 := by exact prefixLift 4857022
  have htrace : WordTrace (prefixWord ++ tailWord_4857022) baseStart_4857022 baseEnd_4857022 := by
    simpa [prefixWord, tailWord_4857022, baseEnd_4857022] using wordTrace_append hprefix tailTrace_4857022
  have hstable : (prefixWord ++ tailWord_4857022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857022).length < 2 ^ (prefixWord ++ tailWord_4857022).sum := by decide
  have hdescent : baseEnd_4857022 < baseStart_4857022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857068 : List Nat := [2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 4]
def baseStart_4857068 : Nat := 118140960795 + 4857068 * 2 ^ 59
def prefixEnd_4857068 : Nat := 4983230072969 + 3 ^ 40 * 4857068 * 2
def baseEnd_4857068 : Nat := 2494010455572107932812757

theorem tailTrace_4857068 : CollatzResearch.WordTrace tailWord_4857068 prefixEnd_4857068 2494010455572107932812757 := by
  unfold tailWord_4857068
  simp only [CollatzResearch.WordTrace]
  refine ⟨88575911783839816008977929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118101215711786421345303905 88575911783839816008977929)
  ·
    refine ⟨66431933837879862006733447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88575911783839816008977929 66431933837879862006733447)
    ·
      refine ⟨99647900756819793010100171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66431933837879862006733447 99647900756819793010100171)
      ·
        refine ⟨149471851135229689515150257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99647900756819793010100171 149471851135229689515150257)
        ·
          refine ⟨112103888351422267136362693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149471851135229689515150257 112103888351422267136362693)
          ·
            refine ⟨21019479065891675088068005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112103888351422267136362693 21019479065891675088068005)
            ·
              refine ⟨3941152324854689079012751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21019479065891675088068005 3941152324854689079012751)
              ·
                refine ⟨5911728487282033618519127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3941152324854689079012751 5911728487282033618519127)
                ·
                  refine ⟨8867592730923050427778691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5911728487282033618519127 8867592730923050427778691)
                  ·
                    refine ⟨13301389096384575641668037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8867592730923050427778691 13301389096384575641668037)
                    ·
                      refine ⟨2494010455572107932812757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13301389096384575641668037 2494010455572107932812757)
                      ·
                        rfl

theorem cell23_4857068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 4].length) (baseStart_4857068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857068 prefixEnd_4857068 := by exact prefixLift 4857068
  have htrace : WordTrace (prefixWord ++ tailWord_4857068) baseStart_4857068 baseEnd_4857068 := by
    simpa [prefixWord, tailWord_4857068, baseEnd_4857068] using wordTrace_append hprefix tailTrace_4857068
  have hstable : (prefixWord ++ tailWord_4857068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857068).length < 2 ^ (prefixWord ++ tailWord_4857068).sum := by decide
  have hdescent : baseEnd_4857068 < baseStart_4857068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
