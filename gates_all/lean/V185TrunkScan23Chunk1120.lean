import V185TrunkScan23Chunk1119

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6633603 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 3]
def baseStart_6633603 : Nat := 118140960795 + 6633603 * 2 ^ 59
def prefixEnd_6633603 : Nat := 4983230072969 + 3 ^ 40 * 6633603 * 2
def baseEnd_6633603 : Nat := 3406226810107314731455121

theorem tailTrace_6633603 : CollatzResearch.WordTrace tailWord_6633603 prefixEnd_6633603 3406226810107314731455121 := by
  unfold tailWord_6633603
  simp only [CollatzResearch.WordTrace]
  refine ⟨241947378186596735040409463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161298252124397823360272975 241947378186596735040409463)
  ·
    refine ⟨362921067279895102560614195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241947378186596735040409463 362921067279895102560614195)
    ·
      refine ⟨544381600919842653840921293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362921067279895102560614195 544381600919842653840921293)
      ·
        refine ⟨204143100344940995190345485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 544381600919842653840921293 204143100344940995190345485)
        ·
          refine ⟨76553662629352873196379557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204143100344940995190345485 76553662629352873196379557)
          ·
            refine ⟨14353811743003663724321167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76553662629352873196379557 14353811743003663724321167)
            ·
              refine ⟨21530717614505495586481751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14353811743003663724321167 21530717614505495586481751)
              ·
                refine ⟨32296076421758243379722627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21530717614505495586481751 32296076421758243379722627)
                ·
                  refine ⟨48444114632637365069583941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32296076421758243379722627 48444114632637365069583941)
                  ·
                    refine ⟨9083271493619505950546989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48444114632637365069583941 9083271493619505950546989)
                    ·
                      refine ⟨3406226810107314731455121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9083271493619505950546989 3406226810107314731455121)
                      ·
                        rfl

theorem cell23_6633603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 3].length) (baseStart_6633603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633603 prefixEnd_6633603 := by exact prefixLift 6633603
  have htrace : WordTrace (prefixWord ++ tailWord_6633603) baseStart_6633603 baseEnd_6633603 := by
    simpa [prefixWord, tailWord_6633603, baseEnd_6633603] using wordTrace_append hprefix tailTrace_6633603
  have hstable : (prefixWord ++ tailWord_6633603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633603).length < 2 ^ (prefixWord ++ tailWord_6633603).sum := by decide
  have hdescent : baseEnd_6633603 < baseStart_6633603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633623 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 8]
def baseStart_6633623 : Nat := 118140960795 + 6633623 * 2 ^ 59
def prefixEnd_6633623 : Nat := 4983230072969 + 3 ^ 40 * 6633623 * 2
def baseEnd_6633623 : Nat := 378470786635600517022781

theorem tailTrace_6633623 : CollatzResearch.WordTrace tailWord_6633623 prefixEnd_6633623 378470786635600517022781 := by
  unfold tailWord_6633623
  simp only [CollatzResearch.WordTrace]
  refine ⟨241948107646524278456137523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161298738431016185637425015 241948107646524278456137523)
  ·
    refine ⟨362922161469786417684206285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241948107646524278456137523 362922161469786417684206285)
    ·
      refine ⟨136095810551169906631577357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362922161469786417684206285 136095810551169906631577357)
      ·
        refine ⟨51035928956688714986841509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136095810551169906631577357 51035928956688714986841509)
        ·
          refine ⟨9569236679379134060032783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51035928956688714986841509 9569236679379134060032783)
          ·
            refine ⟨14353855019068701090049175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9569236679379134060032783 14353855019068701090049175)
            ·
              refine ⟨21530782528603051635073763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14353855019068701090049175 21530782528603051635073763)
              ·
                refine ⟨32296173792904577452610645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21530782528603051635073763 32296173792904577452610645)
                ·
                  refine ⟨378470786635600517022781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32296173792904577452610645 378470786635600517022781)
                  ·
                    rfl

theorem cell23_6633623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 8].length) (baseStart_6633623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633623 prefixEnd_6633623 := by exact prefixLift 6633623
  have htrace : WordTrace (prefixWord ++ tailWord_6633623) baseStart_6633623 baseEnd_6633623 := by
    simpa [prefixWord, tailWord_6633623, baseEnd_6633623] using wordTrace_append hprefix tailTrace_6633623
  have hstable : (prefixWord ++ tailWord_6633623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633623).length < 2 ^ (prefixWord ++ tailWord_6633623).sum := by decide
  have hdescent : baseEnd_6633623 < baseStart_6633623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633650 : List Nat := [3, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3]
def baseStart_6633650 : Nat := 118140960795 + 6633650 * 2 ^ 59
def prefixEnd_6633650 : Nat := 4983230072969 + 3 ^ 40 * 6633650 * 2
def baseEnd_6633650 : Nat := 3406250943698076047567405

theorem tailTrace_6633650 : CollatzResearch.WordTrace tailWord_6633650 prefixEnd_6633650 3406250943698076047567405 := by
  unfold tailWord_6633650
  simp only [CollatzResearch.WordTrace]
  refine ⟨60487273104356615516842601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161299394944950974711580269 60487273104356615516842601)
  ·
    refine ⟨45365454828267461637631951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60487273104356615516842601 45365454828267461637631951)
    ·
      refine ⟨68048182242401192456447927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45365454828267461637631951 68048182242401192456447927)
      ·
        refine ⟨102072273363601788684671891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68048182242401192456447927 102072273363601788684671891)
        ·
          refine ⟨153108410045402683027007837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102072273363601788684671891 153108410045402683027007837)
          ·
            refine ⟨57415653767026006135127939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153108410045402683027007837 57415653767026006135127939)
            ·
              refine ⟨86123480650539009202691909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57415653767026006135127939 86123480650539009202691909)
              ·
                refine ⟨16148152621976064225504733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86123480650539009202691909 16148152621976064225504733)
                ·
                  refine ⟨6055557233241024084564275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16148152621976064225504733 6055557233241024084564275)
                  ·
                    refine ⟨9083335849861536126846413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6055557233241024084564275 9083335849861536126846413)
                    ·
                      refine ⟨3406250943698076047567405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9083335849861536126846413 3406250943698076047567405)
                      ·
                        rfl

theorem cell23_6633650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_6633650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633650 prefixEnd_6633650 := by exact prefixLift 6633650
  have htrace : WordTrace (prefixWord ++ tailWord_6633650) baseStart_6633650 baseEnd_6633650 := by
    simpa [prefixWord, tailWord_6633650, baseEnd_6633650] using wordTrace_append hprefix tailTrace_6633650
  have hstable : (prefixWord ++ tailWord_6633650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633650).length < 2 ^ (prefixWord ++ tailWord_6633650).sum := by decide
  have hdescent : baseEnd_6633650 < baseStart_6633650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633727 : List Nat := [1, 1, 2, 2, 1, 4, 5, 1, 1, 2, 3]
def baseStart_6633727 : Nat := 118140960795 + 6633727 * 2 ^ 59
def prefixEnd_6633727 : Nat := 4983230072969 + 3 ^ 40 * 6633727 * 2
def baseEnd_6633727 : Nat := 3406290481708472246304551

theorem tailTrace_6633727 : CollatzResearch.WordTrace tailWord_6633727 prefixEnd_6633727 3406290481708472246304551 := by
  unfold tailWord_6633727
  simp only [CollatzResearch.WordTrace]
  refine ⟨241951900838147504217923435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161301267225431669478615623 241951900838147504217923435)
  ·
    refine ⟨362927851257221256326885153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241951900838147504217923435 362927851257221256326885153)
    ·
      refine ⟨272195888442915942245163865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362927851257221256326885153 272195888442915942245163865)
      ·
        refine ⟨204146916332186956683872899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272195888442915942245163865 204146916332186956683872899)
        ·
          refine ⟨306220374498280435025809349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204146916332186956683872899 306220374498280435025809349)
          ·
            refine ⟨57416320218427581567339253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 306220374498280435025809349 57416320218427581567339253)
            ·
              refine ⟨5382780020477585771938055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57416320218427581567339253 5382780020477585771938055)
              ·
                refine ⟨8074170030716378657907083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5382780020477585771938055 8074170030716378657907083)
                ·
                  refine ⟨12111255046074567986860625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8074170030716378657907083 12111255046074567986860625)
                  ·
                    refine ⟨9083441284555925990145469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12111255046074567986860625 9083441284555925990145469)
                    ·
                      refine ⟨3406290481708472246304551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9083441284555925990145469 3406290481708472246304551)
                      ·
                        rfl

theorem cell23_6633727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 1, 2, 3].length) (baseStart_6633727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633727 prefixEnd_6633727 := by exact prefixLift 6633727
  have htrace : WordTrace (prefixWord ++ tailWord_6633727) baseStart_6633727 baseEnd_6633727 := by
    simpa [prefixWord, tailWord_6633727, baseEnd_6633727] using wordTrace_append hprefix tailTrace_6633727
  have hstable : (prefixWord ++ tailWord_6633727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633727).length < 2 ^ (prefixWord ++ tailWord_6633727).sum := by decide
  have hdescent : baseEnd_6633727 < baseStart_6633727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633735 : List Nat := [1, 1, 4, 5, 2, 1, 2, 2, 1, 1, 3]
def baseStart_6633735 : Nat := 118140960795 + 6633735 * 2 ^ 59
def prefixEnd_6633735 : Nat := 4983230072969 + 3 ^ 40 * 6633735 * 2
def baseEnd_6633735 : Nat := 3406294589553708215004515

theorem tailTrace_6633735 : CollatzResearch.WordTrace tailWord_6633735 prefixEnd_6633735 3406294589553708215004515 := by
  unfold tailWord_6633735
  simp only [CollatzResearch.WordTrace]
  refine ⟨241952192622118521584214659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161301461748079014389476439 241952192622118521584214659)
  ·
    refine ⟨362928288933177782376321989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241952192622118521584214659 362928288933177782376321989)
    ·
      refine ⟨68049054174970834195560373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 362928288933177782376321989 68049054174970834195560373)
      ·
        refine ⟨6379598828903515705833785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68049054174970834195560373 6379598828903515705833785)
        ·
          refine ⟨4784699121677636779375339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6379598828903515705833785 4784699121677636779375339)
          ·
            refine ⟨7177048682516455169063009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4784699121677636779375339 7177048682516455169063009)
            ·
              refine ⟨5382786511887341376797257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7177048682516455169063009 5382786511887341376797257)
              ·
                refine ⟨4037089883915506032597943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5382786511887341376797257 4037089883915506032597943)
                ·
                  refine ⟨6055634825873259048896915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4037089883915506032597943 6055634825873259048896915)
                  ·
                    refine ⟨9083452238809888573345373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6055634825873259048896915 9083452238809888573345373)
                    ·
                      refine ⟨3406294589553708215004515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9083452238809888573345373 3406294589553708215004515)
                      ·
                        rfl

theorem cell23_6633735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_6633735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633735 prefixEnd_6633735 := by exact prefixLift 6633735
  have htrace : WordTrace (prefixWord ++ tailWord_6633735) baseStart_6633735 baseEnd_6633735 := by
    simpa [prefixWord, tailWord_6633735, baseEnd_6633735] using wordTrace_append hprefix tailTrace_6633735
  have hstable : (prefixWord ++ tailWord_6633735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633735).length < 2 ^ (prefixWord ++ tailWord_6633735).sum := by decide
  have hdescent : baseEnd_6633735 < baseStart_6633735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633763 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 4]
def baseStart_6633763 : Nat := 118140960795 + 6633763 * 2 ^ 59
def prefixEnd_6633763 : Nat := 4983230072969 + 3 ^ 40 * 6633763 * 2
def baseEnd_6633763 : Nat := 3406308967012034105454385

theorem tailTrace_6633763 : CollatzResearch.WordTrace tailWord_6633763 prefixEnd_6633763 3406308967012034105454385 := by
  unfold tailWord_6633763
  simp only [CollatzResearch.WordTrace]
  refine ⟨241953213866017082366233943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161302142577344721577489295 241953213866017082366233943)
  ·
    refine ⟨362929820799025623549350915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241953213866017082366233943 362929820799025623549350915)
    ·
      refine ⟨544394731198538435324026373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362929820799025623549350915 544394731198538435324026373)
      ·
        refine ⟨102074012099725956623254945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 544394731198538435324026373 102074012099725956623254945)
        ·
          refine ⟨76555509074794467467441209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102074012099725956623254945 76555509074794467467441209)
          ·
            refine ⟨57416631806095850600580907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76555509074794467467441209 57416631806095850600580907)
            ·
              refine ⟨86124947709143775900871361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57416631806095850600580907 86124947709143775900871361)
              ·
                refine ⟨64593710781857831925653521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86124947709143775900871361 64593710781857831925653521)
                ·
                  refine ⟨48445283086393373944240141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64593710781857831925653521 48445283086393373944240141)
                  ·
                    refine ⟨18166981157397515229090053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48445283086393373944240141 18166981157397515229090053)
                    ·
                      refine ⟨3406308967012034105454385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18166981157397515229090053 3406308967012034105454385)
                      ·
                        rfl

theorem cell23_6633763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_6633763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633763 prefixEnd_6633763 := by exact prefixLift 6633763
  have htrace : WordTrace (prefixWord ++ tailWord_6633763) baseStart_6633763 baseEnd_6633763 := by
    simpa [prefixWord, tailWord_6633763, baseEnd_6633763] using wordTrace_append hprefix tailTrace_6633763
  have hstable : (prefixWord ++ tailWord_6633763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633763).length < 2 ^ (prefixWord ++ tailWord_6633763).sum := by decide
  have hdescent : baseEnd_6633763 < baseStart_6633763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633783 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 5]
def baseStart_6633783 : Nat := 118140960795 + 6633783 * 2 ^ 59
def prefixEnd_6633783 : Nat := 4983230072969 + 3 ^ 40 * 6633783 * 2
def baseEnd_6633783 : Nat := 3406319236625124027204293

theorem tailTrace_6633783 : CollatzResearch.WordTrace tailWord_6633783 prefixEnd_6633783 3406319236625124027204293 := by
  unfold tailWord_6633783
  simp only [CollatzResearch.WordTrace]
  refine ⟨241953943325944625781962003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161302628883963083854641335 241953943325944625781962003)
  ·
    refine ⟨362930914988916938672943005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241953943325944625781962003 362930914988916938672943005)
    ·
      refine ⟨136099093120843852002353627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362930914988916938672943005 136099093120843852002353627)
      ·
        refine ⟨204148639681265778003530441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136099093120843852002353627 204148639681265778003530441)
        ·
          refine ⟨153111479760949333502647831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204148639681265778003530441 153111479760949333502647831)
          ·
            refine ⟨229667219641424000253971747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153111479760949333502647831 229667219641424000253971747)
            ·
              refine ⟨344500829462136000380957621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229667219641424000253971747 344500829462136000380957621)
              ·
                refine ⟨32296952762075250035714777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 344500829462136000380957621 32296952762075250035714777)
                ·
                  refine ⟨24222714571556437526786083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32296952762075250035714777 24222714571556437526786083)
                  ·
                    refine ⟨36334071857334656290179125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24222714571556437526786083 36334071857334656290179125)
                    ·
                      refine ⟨3406319236625124027204293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36334071857334656290179125 3406319236625124027204293)
                      ·
                        rfl

theorem cell23_6633783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_6633783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633783 prefixEnd_6633783 := by exact prefixLift 6633783
  have htrace : WordTrace (prefixWord ++ tailWord_6633783) baseStart_6633783 baseEnd_6633783 := by
    simpa [prefixWord, tailWord_6633783, baseEnd_6633783] using wordTrace_append hprefix tailTrace_6633783
  have hstable : (prefixWord ++ tailWord_6633783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633783).length < 2 ^ (prefixWord ++ tailWord_6633783).sum := by decide
  have hdescent : baseEnd_6633783 < baseStart_6633783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633784 : List Nat := [2, 1, 2, 1, 3, 1, 6, 1, 1, 3, 2]
def baseStart_6633784 : Nat := 118140960795 + 6633784 * 2 ^ 59
def prefixEnd_6633784 : Nat := 4983230072969 + 3 ^ 40 * 6633784 * 2
def baseEnd_6633784 : Nat := 3406319750105778523291789

theorem tailTrace_6633784 : CollatzResearch.WordTrace tailWord_6633784 prefixEnd_6633784 3406319750105778523291789 := by
  unfold tailWord_6633784
  simp only [CollatzResearch.WordTrace]
  refine ⟨120976989899470501476374203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161302653199294001968498937 120976989899470501476374203)
  ·
    refine ⟨181465484849205752214561305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120976989899470501476374203 181465484849205752214561305)
    ·
      refine ⟨136099113636904314160920979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181465484849205752214561305 136099113636904314160920979)
      ·
        refine ⟨204148670455356471241381469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136099113636904314160920979 204148670455356471241381469)
        ·
          refine ⟨76555751420758676715518051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204148670455356471241381469 76555751420758676715518051)
          ·
            refine ⟨114833627131138015073277077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76555751420758676715518051 114833627131138015073277077)
            ·
              refine ⟨5382826271772094456559863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114833627131138015073277077 5382826271772094456559863)
              ·
                refine ⟨8074239407658141684839795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5382826271772094456559863 8074239407658141684839795)
                ·
                  refine ⟨12111359111487212527259693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8074239407658141684839795 12111359111487212527259693)
                  ·
                    refine ⟨4541759666807704697722385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12111359111487212527259693 4541759666807704697722385)
                    ·
                      refine ⟨3406319750105778523291789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4541759666807704697722385 3406319750105778523291789)
                      ·
                        rfl

theorem cell23_6633784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 1, 3, 2].length) (baseStart_6633784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633784 prefixEnd_6633784 := by exact prefixLift 6633784
  have htrace : WordTrace (prefixWord ++ tailWord_6633784) baseStart_6633784 baseEnd_6633784 := by
    simpa [prefixWord, tailWord_6633784, baseEnd_6633784] using wordTrace_append hprefix tailTrace_6633784
  have hstable : (prefixWord ++ tailWord_6633784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633784).length < 2 ^ (prefixWord ++ tailWord_6633784).sum := by decide
  have hdescent : baseEnd_6633784 < baseStart_6633784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633790 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 2, 6]
def baseStart_6633790 : Nat := 118140960795 + 6633790 * 2 ^ 59
def prefixEnd_6633790 : Nat := 4983230072969 + 3 ^ 40 * 6633790 * 2
def baseEnd_6633790 : Nat := 1135440943663235166605587

theorem tailTrace_6633790 : CollatzResearch.WordTrace tailWord_6633790 prefixEnd_6633790 1135440943663235166605587 := by
  unfold tailWord_6633790
  simp only [CollatzResearch.WordTrace]
  refine ⟨30244274829614908247183353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161302799091279510651644549 30244274829614908247183353)
  ·
    refine ⟨22683206122211181185387515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30244274829614908247183353 22683206122211181185387515)
    ·
      refine ⟨34024809183316771778081273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22683206122211181185387515 34024809183316771778081273)
      ·
        refine ⟨25518606887487578833560955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34024809183316771778081273 25518606887487578833560955)
        ·
          refine ⟨38277910331231368250341433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25518606887487578833560955 38277910331231368250341433)
          ·
            refine ⟨28708432748423526187756075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38277910331231368250341433 28708432748423526187756075)
            ·
              refine ⟨43062649122635289281634113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28708432748423526187756075 43062649122635289281634113)
              ·
                refine ⟨32296986841976466961225585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43062649122635289281634113 32296986841976466961225585)
                ·
                  refine ⟨24222740131482350220919189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32296986841976466961225585 24222740131482350220919189)
                  ·
                    refine ⟨1135440943663235166605587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24222740131482350220919189 1135440943663235166605587)
                    ·
                      rfl

theorem cell23_6633790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_6633790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633790 prefixEnd_6633790 := by exact prefixLift 6633790
  have htrace : WordTrace (prefixWord ++ tailWord_6633790) baseStart_6633790 baseEnd_6633790 := by
    simpa [prefixWord, tailWord_6633790, baseEnd_6633790] using wordTrace_append hprefix tailTrace_6633790
  have hstable : (prefixWord ++ tailWord_6633790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633790).length < 2 ^ (prefixWord ++ tailWord_6633790).sum := by decide
  have hdescent : baseEnd_6633790 < baseStart_6633790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633810 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_6633810 : Nat := 118140960795 + 6633810 * 2 ^ 59
def prefixEnd_6633810 : Nat := 4983230072969 + 3 ^ 40 * 6633810 * 2
def baseEnd_6633810 : Nat := 3406333100602795421566669

theorem tailTrace_6633810 : CollatzResearch.WordTrace tailWord_6633810 prefixEnd_6633810 3406333100602795421566669 := by
  unfold tailWord_6633810
  simp only [CollatzResearch.WordTrace]
  refine ⟨60488732024211702348298721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161303285397897872928796589 60488732024211702348298721)
  ·
    refine ⟨45366549018158776761224041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60488732024211702348298721 45366549018158776761224041)
    ·
      refine ⟨34024911763619082570918031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45366549018158776761224041 34024911763619082570918031)
      ·
        refine ⟨51037367645428623856377047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34024911763619082570918031 51037367645428623856377047)
        ·
          refine ⟨76556051468142935784565571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51037367645428623856377047 76556051468142935784565571)
          ·
            refine ⟨114834077202214403676848357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76556051468142935784565571 114834077202214403676848357)
            ·
              refine ⟨21531389475415200689409067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114834077202214403676848357 21531389475415200689409067)
              ·
                refine ⟨32297084213122801034113601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21531389475415200689409067 32297084213122801034113601)
                ·
                  refine ⟨24222813159842100775585201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32297084213122801034113601 24222813159842100775585201)
                  ·
                    refine ⟨18167109869881575581688901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24222813159842100775585201 18167109869881575581688901)
                    ·
                      refine ⟨3406333100602795421566669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18167109869881575581688901 3406333100602795421566669)
                      ·
                        rfl

theorem cell23_6633810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_6633810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633810 prefixEnd_6633810 := by exact prefixLift 6633810
  have htrace : WordTrace (prefixWord ++ tailWord_6633810) baseStart_6633810 baseEnd_6633810 := by
    simpa [prefixWord, tailWord_6633810, baseEnd_6633810] using wordTrace_append hprefix tailTrace_6633810
  have hstable : (prefixWord ++ tailWord_6633810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633810).length < 2 ^ (prefixWord ++ tailWord_6633810).sum := by decide
  have hdescent : baseEnd_6633810 < baseStart_6633810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633833 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 1, 7]
def baseStart_6633833 : Nat := 118140960795 + 6633833 * 2 ^ 59
def prefixEnd_6633833 : Nat := 4983230072969 + 3 ^ 40 * 6633833 * 2
def baseEnd_6633833 : Nat := 1135448303552616277193021

theorem tailTrace_6633833 : CollatzResearch.WordTrace tailWord_6633833 prefixEnd_6633833 1135448303552616277193021 := by
  unfold tailWord_6633833
  simp only [CollatzResearch.WordTrace]
  refine ⟨241955766975763484321282153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161303844650508989547521435 241955766975763484321282153)
  ·
    refine ⟨181466825231822613240961615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241955766975763484321282153 181466825231822613240961615)
    ·
      refine ⟨272200237847733919861442423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181466825231822613240961615 272200237847733919861442423)
      ·
        refine ⟨408300356771600879792163635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272200237847733919861442423 408300356771600879792163635)
        ·
          refine ⟨612450535157401319688245453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408300356771600879792163635 612450535157401319688245453)
          ·
            refine ⟨229668950684025494883092045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 612450535157401319688245453 229668950684025494883092045)
            ·
              refine ⟨86125856506509560581159517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229668950684025494883092045 86125856506509560581159517)
              ·
                refine ⟨32297196189941085217934819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86125856506509560581159517 32297196189941085217934819)
                ·
                  refine ⟨48445794284911627826902229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32297196189941085217934819 48445794284911627826902229)
                  ·
                    refine ⟨1135448303552616277193021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48445794284911627826902229 1135448303552616277193021)
                    ·
                      rfl

theorem cell23_6633833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 7].length) (baseStart_6633833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633833 prefixEnd_6633833 := by exact prefixLift 6633833
  have htrace : WordTrace (prefixWord ++ tailWord_6633833) baseStart_6633833 baseEnd_6633833 := by
    simpa [prefixWord, tailWord_6633833, baseEnd_6633833] using wordTrace_append hprefix tailTrace_6633833
  have hstable : (prefixWord ++ tailWord_6633833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633833).length < 2 ^ (prefixWord ++ tailWord_6633833).sum := by decide
  have hdescent : baseEnd_6633833 < baseStart_6633833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633843 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 5]
def baseStart_6633843 : Nat := 118140960795 + 6633843 * 2 ^ 59
def prefixEnd_6633843 : Nat := 4983230072969 + 3 ^ 40 * 6633843 * 2
def baseEnd_6633843 : Nat := 3406350045464393792454017

theorem tailTrace_6633843 : CollatzResearch.WordTrace tailWord_6633843 prefixEnd_6633843 3406350045464393792454017 := by
  unfold tailWord_6633843
  simp only [CollatzResearch.WordTrace]
  refine ⟨241956131705727256029146183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161304087803818170686097455 241956131705727256029146183)
  ·
    refine ⟨362934197558590884043719275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241956131705727256029146183 362934197558590884043719275)
    ·
      refine ⟨544401296337886326065578913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362934197558590884043719275 544401296337886326065578913)
      ·
        refine ⟨408300972253414744549184185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 544401296337886326065578913 408300972253414744549184185)
        ·
          refine ⟨306225729190061058411888139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408300972253414744549184185 306225729190061058411888139)
          ·
            refine ⟨459338593785091587617832209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306225729190061058411888139 459338593785091587617832209)
            ·
              refine ⟨344503945338818690713374157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459338593785091587617832209 344503945338818690713374157)
              ·
                refine ⟨129188979502057009017515309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344503945338818690713374157 129188979502057009017515309)
                ·
                  refine ⟨48445867313271378381568241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129188979502057009017515309 48445867313271378381568241)
                  ·
                    refine ⟨36334400484953533786176181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48445867313271378381568241 36334400484953533786176181)
                    ·
                      refine ⟨3406350045464393792454017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36334400484953533786176181 3406350045464393792454017)
                      ·
                        rfl

theorem cell23_6633843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_6633843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633843 prefixEnd_6633843 := by exact prefixLift 6633843
  have htrace : WordTrace (prefixWord ++ tailWord_6633843) baseStart_6633843 baseEnd_6633843 := by
    simpa [prefixWord, tailWord_6633843, baseEnd_6633843] using wordTrace_append hprefix tailTrace_6633843
  have hstable : (prefixWord ++ tailWord_6633843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633843).length < 2 ^ (prefixWord ++ tailWord_6633843).sum := by decide
  have hdescent : baseEnd_6633843 < baseStart_6633843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633860 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_6633860 : Nat := 118140960795 + 6633860 * 2 ^ 59
def prefixEnd_6633860 : Nat := 4983230072969 + 3 ^ 40 * 6633860 * 2
def baseEnd_6633860 : Nat := 3406358774635520225941439

theorem tailTrace_6633860 : CollatzResearch.WordTrace tailWord_6633860 prefixEnd_6633860 3406358774635520225941439 := by
  unfold tailWord_6633860
  simp only [CollatzResearch.WordTrace]
  refine ⟨120978375873332833966257517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161304501164443778621676689 120978375873332833966257517)
  ·
    refine ⟨45366890952499812737346569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120978375873332833966257517 45366890952499812737346569)
    ·
      refine ⟨34025168214374859553009927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45366890952499812737346569 34025168214374859553009927)
      ·
        refine ⟨51037752321562289329514891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34025168214374859553009927 51037752321562289329514891)
        ·
          refine ⟨76556628482343433994272337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51037752321562289329514891 76556628482343433994272337)
          ·
            refine ⟨57417471361757575495704253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76556628482343433994272337 57417471361757575495704253)
            ·
              refine ⟨21531551760659090810889095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57417471361757575495704253 21531551760659090810889095)
              ·
                refine ⟨32297327640988636216333643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21531551760659090810889095 32297327640988636216333643)
                ·
                  refine ⟨48445991461482954324500465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32297327640988636216333643 48445991461482954324500465)
                  ·
                    refine ⟨36334493596112215743375349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48445991461482954324500465 36334493596112215743375349)
                    ·
                      refine ⟨3406358774635520225941439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36334493596112215743375349 3406358774635520225941439)
                      ·
                        rfl

theorem cell23_6633860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_6633860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633860 prefixEnd_6633860 := by exact prefixLift 6633860
  have htrace : WordTrace (prefixWord ++ tailWord_6633860) baseStart_6633860 baseEnd_6633860 := by
    simpa [prefixWord, tailWord_6633860, baseEnd_6633860] using wordTrace_append hprefix tailTrace_6633860
  have hstable : (prefixWord ++ tailWord_6633860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633860).length < 2 ^ (prefixWord ++ tailWord_6633860).sum := by decide
  have hdescent : baseEnd_6633860 < baseStart_6633860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633887 : List Nat := [1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 4]
def baseStart_6633887 : Nat := 118140960795 + 6633887 * 2 ^ 59
def prefixEnd_6633887 : Nat := 4983230072969 + 3 ^ 40 * 6633887 * 2
def baseEnd_6633887 : Nat := 3406372638613191620303815

theorem tailTrace_6633887 : CollatzResearch.WordTrace tailWord_6633887 prefixEnd_6633887 3406372638613191620303815 := by
  unfold tailWord_6633887
  simp only [CollatzResearch.WordTrace]
  refine ⟨241957736517567851543747915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161305157678378567695831943 241957736517567851543747915)
  ·
    refine ⟨362936604776351777315621873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241957736517567851543747915 362936604776351777315621873)
    ·
      refine ⟨272202453582263832986716405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362936604776351777315621873 272202453582263832986716405)
      ·
        refine ⟨25518980023337234342504663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 272202453582263832986716405 25518980023337234342504663)
        ·
          refine ⟨38278470035005851513756995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25518980023337234342504663 38278470035005851513756995)
          ·
            refine ⟨57417705052508777270635493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38278470035005851513756995 57417705052508777270635493)
            ·
              refine ⟨10765819697345395738244155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57417705052508777270635493 10765819697345395738244155)
              ·
                refine ⟨16148729546018093607366233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10765819697345395738244155 16148729546018093607366233)
                ·
                  refine ⟨12111547159513570205524675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16148729546018093607366233 12111547159513570205524675)
                  ·
                    refine ⟨18167320739270355308287013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12111547159513570205524675 18167320739270355308287013)
                    ·
                      refine ⟨3406372638613191620303815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18167320739270355308287013 3406372638613191620303815)
                      ·
                        rfl

theorem cell23_6633887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_6633887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633887 prefixEnd_6633887 := by exact prefixLift 6633887
  have htrace : WordTrace (prefixWord ++ tailWord_6633887) baseStart_6633887 baseEnd_6633887 := by
    simpa [prefixWord, tailWord_6633887, baseEnd_6633887] using wordTrace_append hprefix tailTrace_6633887
  have hstable : (prefixWord ++ tailWord_6633887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633887).length < 2 ^ (prefixWord ++ tailWord_6633887).sum := by decide
  have hdescent : baseEnd_6633887 < baseStart_6633887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633920 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 3]
def baseStart_6633920 : Nat := 118140960795 + 6633920 * 2 ^ 59
def prefixEnd_6633920 : Nat := 4983230072969 + 3 ^ 40 * 6633920 * 2
def baseEnd_6633920 : Nat := 3406389583474789991191163

theorem tailTrace_6633920 : CollatzResearch.WordTrace tailWord_6633920 prefixEnd_6633920 3406389583474789991191163 := by
  unfold tailWord_6633920
  simp only [CollatzResearch.WordTrace]
  refine ⟨120979470063224149089849607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161305960084298865453132809 120979470063224149089849607)
  ·
    refine ⟨181469205094836223634774411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120979470063224149089849607 181469205094836223634774411)
    ·
      refine ⟨272203807642254335452161617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181469205094836223634774411 272203807642254335452161617)
      ·
        refine ⟨204152855731690751589121213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272203807642254335452161617 204152855731690751589121213)
        ·
          refine ⟨76557320899384031845920455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204152855731690751589121213 76557320899384031845920455)
          ·
            refine ⟨114835981349076047768880683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76557320899384031845920455 114835981349076047768880683)
            ·
              refine ⟨172253972023614071653321025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114835981349076047768880683 172253972023614071653321025)
              ·
                refine ⟨129190479017710553739990769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172253972023614071653321025 129190479017710553739990769)
                ·
                  refine ⟨96892859263282915304993077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129190479017710553739990769 96892859263282915304993077)
                  ·
                    refine ⟨9083705555932773309843101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96892859263282915304993077 9083705555932773309843101)
                    ·
                      refine ⟨3406389583474789991191163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9083705555932773309843101 3406389583474789991191163)
                      ·
                        rfl

theorem cell23_6633920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 3].length) (baseStart_6633920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633920 prefixEnd_6633920 := by exact prefixLift 6633920
  have htrace : WordTrace (prefixWord ++ tailWord_6633920) baseStart_6633920 baseEnd_6633920 := by
    simpa [prefixWord, tailWord_6633920, baseEnd_6633920] using wordTrace_append hprefix tailTrace_6633920
  have hstable : (prefixWord ++ tailWord_6633920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633920).length < 2 ^ (prefixWord ++ tailWord_6633920).sum := by decide
  have hdescent : baseEnd_6633920 < baseStart_6633920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633938 : List Nat := [3, 2, 2, 4, 2, 1, 1, 1, 2, 1, 4]
def baseStart_6633938 : Nat := 118140960795 + 6633938 * 2 ^ 59
def prefixEnd_6633938 : Nat := 4983230072969 + 3 ^ 40 * 6633938 * 2
def baseEnd_6633938 : Nat := 3406398826126570920766081

theorem tailTrace_6633938 : CollatzResearch.WordTrace tailWord_6633938 prefixEnd_6633938 3406398826126570920766081 := by
  unfold tailWord_6633938
  simp only [CollatzResearch.WordTrace]
  refine ⟨60489899160095771813463617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161306397760255391502569645 60489899160095771813463617)
  ·
    refine ⟨45367424370071828860097713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60489899160095771813463617 45367424370071828860097713)
    ·
      refine ⟨34025568277553871645073285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45367424370071828860097713 34025568277553871645073285)
      ·
        refine ⟨6379794052041350933451241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34025568277553871645073285 6379794052041350933451241)
        ·
          refine ⟨4784845539031013200088431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6379794052041350933451241 4784845539031013200088431)
          ·
            refine ⟨7177268308546519800132647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4784845539031013200088431 7177268308546519800132647)
            ·
              refine ⟨10765902462819779700198971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7177268308546519800132647 10765902462819779700198971)
              ·
                refine ⟨16148853694229669550298457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10765902462819779700198971 16148853694229669550298457)
                ·
                  refine ⟨12111640270672252162723843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16148853694229669550298457 12111640270672252162723843)
                  ·
                    refine ⟨18167460406008378244085765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12111640270672252162723843 18167460406008378244085765)
                    ·
                      refine ⟨3406398826126570920766081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18167460406008378244085765 3406398826126570920766081)
                      ·
                        rfl

theorem cell23_6633938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_6633938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633938 prefixEnd_6633938 := by exact prefixLift 6633938
  have htrace : WordTrace (prefixWord ++ tailWord_6633938) baseStart_6633938 baseEnd_6633938 := by
    simpa [prefixWord, tailWord_6633938, baseEnd_6633938] using wordTrace_append hprefix tailTrace_6633938
  have hstable : (prefixWord ++ tailWord_6633938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633938).length < 2 ^ (prefixWord ++ tailWord_6633938).sum := by decide
  have hdescent : baseEnd_6633938 < baseStart_6633938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633994 : List Nat := [3, 1, 2, 2, 2, 1, 4, 2, 1, 1, 4]
def baseStart_6633994 : Nat := 118140960795 + 6633994 * 2 ^ 59
def prefixEnd_6633994 : Nat := 4983230072969 + 3 ^ 40 * 6633994 * 2
def baseEnd_6633994 : Nat := 3406427581043222701665823

theorem tailTrace_6633994 : CollatzResearch.WordTrace tailWord_6633994 prefixEnd_6633994 3406427581043222701665823 := by
  unfold tailWord_6633994
  simp only [CollatzResearch.WordTrace]
  refine ⟨60490409782045052204473259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161307759418786805878595357 60490409782045052204473259)
  ·
    refine ⟨90735614673067578306709889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60490409782045052204473259 90735614673067578306709889)
    ·
      refine ⟨68051711004800683730032417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90735614673067578306709889 68051711004800683730032417)
      ·
        refine ⟨51038783253600512797524313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68051711004800683730032417 51038783253600512797524313)
        ·
          refine ⟨38279087440200384598143235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51038783253600512797524313 38279087440200384598143235)
          ·
            refine ⟨57418631160300576897214853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38279087440200384598143235 57418631160300576897214853)
            ·
              refine ⟨10765993342556358168227785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57418631160300576897214853 10765993342556358168227785)
              ·
                refine ⟨8074495006917268626170839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10765993342556358168227785 8074495006917268626170839)
                ·
                  refine ⟨12111742510375902939256259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8074495006917268626170839 12111742510375902939256259)
                  ·
                    refine ⟨18167613765563854408884389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12111742510375902939256259 18167613765563854408884389)
                    ·
                      refine ⟨3406427581043222701665823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18167613765563854408884389 3406427581043222701665823)
                      ·
                        rfl

theorem cell23_6633994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_6633994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633994 prefixEnd_6633994 := by exact prefixLift 6633994
  have htrace : WordTrace (prefixWord ++ tailWord_6633994) baseStart_6633994 baseEnd_6633994 := by
    simpa [prefixWord, tailWord_6633994, baseEnd_6633994] using wordTrace_append hprefix tailTrace_6633994
  have hstable : (prefixWord ++ tailWord_6633994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633994).length < 2 ^ (prefixWord ++ tailWord_6633994).sum := by decide
  have hdescent : baseEnd_6633994 < baseStart_6633994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634038 : List Nat := [5, 1, 2, 1, 2, 1, 4, 1, 2, 4]
def baseStart_6634038 : Nat := 118140960795 + 6634038 * 2 ^ 59
def prefixEnd_6634038 : Nat := 4983230072969 + 3 ^ 40 * 6634038 * 2
def baseEnd_6634038 : Nat := 1135483391397340176505207

theorem tailTrace_6634038 : CollatzResearch.WordTrace tailWord_6634038 prefixEnd_6634038 1135483391397340176505207 := by
  unfold tailWord_6634038
  simp only [CollatzResearch.WordTrace]
  refine ⟨15122702746251300270780923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161308829293347202888329845 15122702746251300270780923)
  ·
    refine ⟨22684054119376950406171385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15122702746251300270780923 22684054119376950406171385)
    ·
      refine ⟨17013040589532712804628539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22684054119376950406171385 17013040589532712804628539)
      ·
        refine ⟨25519560884299069206942809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17013040589532712804628539 25519560884299069206942809)
        ·
          refine ⟨19139670663224301905207107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25519560884299069206942809 19139670663224301905207107)
          ·
            refine ⟨28709505994836452857810661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19139670663224301905207107 28709505994836452857810661)
            ·
              refine ⟨5383032374031834910839499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28709505994836452857810661 5383032374031834910839499)
              ·
                refine ⟨8074548561047752366259249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5383032374031834910839499 8074548561047752366259249)
                ·
                  refine ⟨6055911420785814274694437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8074548561047752366259249 6055911420785814274694437)
                  ·
                    refine ⟨1135483391397340176505207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6055911420785814274694437 1135483391397340176505207)
                    ·
                      rfl

theorem cell23_6634038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_6634038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634038 prefixEnd_6634038 := by exact prefixLift 6634038
  have htrace : WordTrace (prefixWord ++ tailWord_6634038) baseStart_6634038 baseEnd_6634038 := by
    simpa [prefixWord, tailWord_6634038, baseEnd_6634038] using wordTrace_append hprefix tailTrace_6634038
  have hstable : (prefixWord ++ tailWord_6634038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634038).length < 2 ^ (prefixWord ++ tailWord_6634038).sum := by decide
  have hdescent : baseEnd_6634038 < baseStart_6634038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634061 : List Nat := [1, 6, 1, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_6634061 : Nat := 118140960795 + 6634061 * 2 ^ 59
def prefixEnd_6634061 : Nat := 4983230072969 + 3 ^ 40 * 6634061 * 2
def baseEnd_6634061 : Nat := 3406461984247073939528015

theorem tailTrace_6634061 : CollatzResearch.WordTrace tailWord_6634061 prefixEnd_6634061 3406461984247073939528015 := by
  unfold tailWord_6634061
  simp only [CollatzResearch.WordTrace]
  refine ⟨241964082818937479260582037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161309388545958319507054691 241964082818937479260582037)
  ·
    refine ⟨11342066382137694340339783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 241964082818937479260582037 11342066382137694340339783)
    ·
      refine ⟨17013099573206541510509675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11342066382137694340339783 17013099573206541510509675)
      ·
        refine ⟨25519649359809812265764513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17013099573206541510509675 25519649359809812265764513)
        ·
          refine ⟨19139737019857359199323385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25519649359809812265764513 19139737019857359199323385)
          ·
            refine ⟨14354802764893019399492539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19139737019857359199323385 14354802764893019399492539)
            ·
              refine ⟨21532204147339529099238809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14354802764893019399492539 21532204147339529099238809)
              ·
                refine ⟨16149153110504646824429107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21532204147339529099238809 16149153110504646824429107)
                ·
                  refine ⟨24223729665756970236643661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16149153110504646824429107 24223729665756970236643661)
                  ·
                    refine ⟨9083898624658863838741373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24223729665756970236643661 9083898624658863838741373)
                    ·
                      refine ⟨3406461984247073939528015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9083898624658863838741373 3406461984247073939528015)
                      ·
                        rfl

theorem cell23_6634061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_6634061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634061 prefixEnd_6634061 := by exact prefixLift 6634061
  have htrace : WordTrace (prefixWord ++ tailWord_6634061) baseStart_6634061 baseEnd_6634061 := by
    simpa [prefixWord, tailWord_6634061, baseEnd_6634061] using wordTrace_append hprefix tailTrace_6634061
  have hstable : (prefixWord ++ tailWord_6634061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634061).length < 2 ^ (prefixWord ++ tailWord_6634061).sum := by decide
  have hdescent : baseEnd_6634061 < baseStart_6634061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634084 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 3, 4, 2]
def baseStart_6634084 : Nat := 118140960795 + 6634084 * 2 ^ 59
def prefixEnd_6634084 : Nat := 4983230072969 + 3 ^ 40 * 6634084 * 2
def baseEnd_6634084 : Nat := 3406473794302127349540409

theorem tailTrace_6634084 : CollatzResearch.WordTrace tailWord_6634084 prefixEnd_6634084 3406473794302127349540409 := by
  unfold tailWord_6634084
  simp only [CollatzResearch.WordTrace]
  refine ⟨120982460848927077094334653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161309947798569436125779537 120982460848927077094334653)
  ·
    refine ⟨45368422818347653910375495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120982460848927077094334653 45368422818347653910375495)
    ·
      refine ⟨68052634227521480865563243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45368422818347653910375495 68052634227521480865563243)
      ·
        refine ⟨102078951341282221298344865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68052634227521480865563243 102078951341282221298344865)
        ·
          refine ⟨76559213505961665973758649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102078951341282221298344865 76559213505961665973758649)
          ·
            refine ⟨57419410129471249480318987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76559213505961665973758649 57419410129471249480318987)
            ·
              refine ⟨86129115194206874220478481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57419410129471249480318987 86129115194206874220478481)
              ·
                refine ⟨64596836395655155665358861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86129115194206874220478481 64596836395655155665358861)
                ·
                  refine ⟨24223813648370683374509573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64596836395655155665358861 24223813648370683374509573)
                  ·
                    refine ⟨4541965059069503132720545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24223813648370683374509573 4541965059069503132720545)
                    ·
                      refine ⟨3406473794302127349540409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4541965059069503132720545 3406473794302127349540409)
                      ·
                        rfl

theorem cell23_6634084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 3, 4, 2].length) (baseStart_6634084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634084 prefixEnd_6634084 := by exact prefixLift 6634084
  have htrace : WordTrace (prefixWord ++ tailWord_6634084) baseStart_6634084 baseEnd_6634084 := by
    simpa [prefixWord, tailWord_6634084, baseEnd_6634084] using wordTrace_append hprefix tailTrace_6634084
  have hstable : (prefixWord ++ tailWord_6634084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634084).length < 2 ^ (prefixWord ++ tailWord_6634084).sum := by decide
  have hdescent : baseEnd_6634084 < baseStart_6634084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634094 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 2, 6]
def baseStart_6634094 : Nat := 118140960795 + 6634094 * 2 ^ 59
def prefixEnd_6634094 : Nat := 4983230072969 + 3 ^ 40 * 6634094 * 2
def baseEnd_6634094 : Nat := 1135492976369557436805121

theorem tailTrace_6634094 : CollatzResearch.WordTrace tailWord_6634094 prefixEnd_6634094 1135492976369557436805121 := by
  unfold tailWord_6634094
  simp only [CollatzResearch.WordTrace]
  refine ⟨30245660803477240737066667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161310190951878617264355557 30245660803477240737066667)
  ·
    refine ⟨45368491205215861105600001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30245660803477240737066667 45368491205215861105600001)
    ·
      refine ⟨34026368403911895829200001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45368491205215861105600001 34026368403911895829200001)
      ·
        refine ⟨25519776302933921871900001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34026368403911895829200001 25519776302933921871900001)
        ·
          refine ⟨19139832227200441403925001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25519776302933921871900001 19139832227200441403925001)
          ·
            refine ⟨14354874170400331052943751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19139832227200441403925001 14354874170400331052943751)
            ·
              refine ⟨21532311255600496579415627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14354874170400331052943751 21532311255600496579415627)
              ·
                refine ⟨32298466883400744869123441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21532311255600496579415627 32298466883400744869123441)
                ·
                  refine ⟨24223850162550558651842581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32298466883400744869123441 24223850162550558651842581)
                  ·
                    refine ⟨1135492976369557436805121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24223850162550558651842581 1135492976369557436805121)
                    ·
                      rfl

theorem cell23_6634094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_6634094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634094 prefixEnd_6634094 := by exact prefixLift 6634094
  have htrace : WordTrace (prefixWord ++ tailWord_6634094) baseStart_6634094 baseEnd_6634094 := by
    simpa [prefixWord, tailWord_6634094, baseEnd_6634094] using wordTrace_append hprefix tailTrace_6634094
  have hstable : (prefixWord ++ tailWord_6634094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634094).length < 2 ^ (prefixWord ++ tailWord_6634094).sum := by decide
  have hdescent : baseEnd_6634094 < baseStart_6634094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634122 : List Nat := [3, 1, 2, 3, 4, 1, 2, 1, 1, 3, 2]
def baseStart_6634122 : Nat := 118140960795 + 6634122 * 2 ^ 59
def prefixEnd_6634122 : Nat := 4983230072969 + 3 ^ 40 * 6634122 * 2
def baseEnd_6634122 : Nat := 3406493306566998200865235

theorem tailTrace_6634122 : CollatzResearch.WordTrace tailWord_6634122 prefixEnd_6634122 3406493306566998200865235 := by
  unfold tailWord_6634122
  simp only [CollatzResearch.WordTrace]
  refine ⟨60491576917929121669638155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161310871781144324452368413 60491576917929121669638155)
  ·
    refine ⟨90737365376893682504457233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60491576917929121669638155 90737365376893682504457233)
    ·
      refine ⟨68053024032670261878342925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90737365376893682504457233 68053024032670261878342925)
      ·
        refine ⟨25519884012251348204378597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68053024032670261878342925 25519884012251348204378597)
        ·
          refine ⟨4784978252297127788320987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25519884012251348204378597 4784978252297127788320987)
          ·
            refine ⟨7177467378445691682481481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4784978252297127788320987 7177467378445691682481481)
            ·
              refine ⟨5383100533834268761861111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7177467378445691682481481 5383100533834268761861111)
              ·
                refine ⟨8074650800751403142791667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5383100533834268761861111 8074650800751403142791667)
                ·
                  refine ⟨12111976201127104714187501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8074650800751403142791667 12111976201127104714187501)
                  ·
                    refine ⟨4541991075422664267820313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12111976201127104714187501 4541991075422664267820313)
                    ·
                      refine ⟨3406493306566998200865235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4541991075422664267820313 3406493306566998200865235)
                      ·
                        rfl

theorem cell23_6634122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_6634122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634122 prefixEnd_6634122 := by exact prefixLift 6634122
  have htrace : WordTrace (prefixWord ++ tailWord_6634122) baseStart_6634122 baseEnd_6634122 := by
    simpa [prefixWord, tailWord_6634122, baseEnd_6634122] using wordTrace_append hprefix tailTrace_6634122
  have hstable : (prefixWord ++ tailWord_6634122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634122).length < 2 ^ (prefixWord ++ tailWord_6634122).sum := by decide
  have hdescent : baseEnd_6634122 < baseStart_6634122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634137 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 4, 5]
def baseStart_6634137 : Nat := 118140960795 + 6634137 * 2 ^ 59
def prefixEnd_6634137 : Nat := 4983230072969 + 3 ^ 40 * 6634137 * 2
def baseEnd_6634137 : Nat := 1135500336258938547392555

theorem tailTrace_6634137 : CollatzResearch.WordTrace tailWord_6634137 prefixEnd_6634137 1135500336258938547392555 := by
  unfold tailWord_6634137
  simp only [CollatzResearch.WordTrace]
  refine ⟨241966854766662144240348665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161311236511108096160232443 241966854766662144240348665)
  ·
    refine ⟨181475141074996608180261499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241966854766662144240348665 181475141074996608180261499)
    ·
      refine ⟨272212711612494912270392249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181475141074996608180261499 272212711612494912270392249)
      ·
        refine ⟨204159533709371184202794187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272212711612494912270392249 204159533709371184202794187)
        ·
          refine ⟨306239300564056776304191281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204159533709371184202794187 306239300564056776304191281)
          ·
            refine ⟨229679475423042582228143461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306239300564056776304191281 229679475423042582228143461)
            ·
              refine ⟨43064901641820484167776899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229679475423042582228143461 43064901641820484167776899)
              ·
                refine ⟨64597352462730726251665349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43064901641820484167776899 64597352462730726251665349)
                ·
                  refine ⟨12112003586762011172187253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64597352462730726251665349 12112003586762011172187253)
                  ·
                    refine ⟨1135500336258938547392555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12112003586762011172187253 1135500336258938547392555)
                    ·
                      rfl

theorem cell23_6634137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 5].length) (baseStart_6634137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634137 prefixEnd_6634137 := by exact prefixLift 6634137
  have htrace : WordTrace (prefixWord ++ tailWord_6634137) baseStart_6634137 baseEnd_6634137 := by
    simpa [prefixWord, tailWord_6634137, baseEnd_6634137] using wordTrace_append hprefix tailTrace_6634137
  have hstable : (prefixWord ++ tailWord_6634137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634137).length < 2 ^ (prefixWord ++ tailWord_6634137).sum := by decide
  have hdescent : baseEnd_6634137 < baseStart_6634137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634174 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_6634174 : Nat := 118140960795 + 6634174 * 2 ^ 59
def prefixEnd_6634174 : Nat := 4983230072969 + 3 ^ 40 * 6634174 * 2
def baseEnd_6634174 : Nat := 3406520007561031997414995

theorem tailTrace_6634174 : CollatzResearch.WordTrace tailWord_6634174 prefixEnd_6634174 3406520007561031997414995 := by
  unfold tailWord_6634174
  simp only [CollatzResearch.WordTrace]
  refine ⟨30246025533441012444930697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161312136178352066372963717 30246025533441012444930697)
  ·
    refine ⟨22684519150080759333698023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30246025533441012444930697 22684519150080759333698023)
    ·
      refine ⟨34026778725121139000547035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22684519150080759333698023 34026778725121139000547035)
      ·
        refine ⟨51040168087681708500820553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34026778725121139000547035 51040168087681708500820553)
        ·
          refine ⟨38280126065761281375615415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51040168087681708500820553 38280126065761281375615415)
          ·
            refine ⟨57420189098641922063423123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38280126065761281375615415 57420189098641922063423123)
            ·
              refine ⟨86130283647962883095134685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57420189098641922063423123 86130283647962883095134685)
              ·
                refine ⟨32298856367986081160675507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86130283647962883095134685 32298856367986081160675507)
                ·
                  refine ⟨48448284551979121741013261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32298856367986081160675507 48448284551979121741013261)
                  ·
                    refine ⟨18168106706992170652879973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48448284551979121741013261 18168106706992170652879973)
                    ·
                      refine ⟨3406520007561031997414995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18168106706992170652879973 3406520007561031997414995)
                      ·
                        rfl

theorem cell23_6634174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_6634174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634174 prefixEnd_6634174 := by exact prefixLift 6634174
  have htrace : WordTrace (prefixWord ++ tailWord_6634174) baseStart_6634174 baseEnd_6634174 := by
    simpa [prefixWord, tailWord_6634174, baseEnd_6634174] using wordTrace_append hprefix tailTrace_6634174
  have hstable : (prefixWord ++ tailWord_6634174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634174).length < 2 ^ (prefixWord ++ tailWord_6634174).sum := by decide
  have hdescent : baseEnd_6634174 < baseStart_6634174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634217 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 1, 2, 6]
def baseStart_6634217 : Nat := 118140960795 + 6634217 * 2 ^ 59
def prefixEnd_6634217 : Nat := 4983230072969 + 3 ^ 40 * 6634217 * 2
def baseEnd_6634217 : Nat := 3406542087229175329177297

theorem tailTrace_6634217 : CollatzResearch.WordTrace tailWord_6634217 prefixEnd_6634217 3406542087229175329177297 := by
  unfold tailWord_6634217
  simp only [CollatzResearch.WordTrace]
  refine ⟨241969772606372317903260905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161313181737581545268840603 241969772606372317903260905)
  ·
    refine ⟨181477329454779238427445679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241969772606372317903260905 181477329454779238427445679)
    ·
      refine ⟨272215994182168857641168519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181477329454779238427445679 272215994182168857641168519)
      ·
        refine ⟨408323991273253286461752779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272215994182168857641168519 408323991273253286461752779)
        ·
          refine ⟨612485986909879929692629169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408323991273253286461752779 612485986909879929692629169)
          ·
            refine ⟨459364490182409947269471877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 612485986909879929692629169 459364490182409947269471877)
            ·
              refine ⟨86130841909201865113025977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 459364490182409947269471877 86130841909201865113025977)
              ·
                refine ⟨64598131431901398834769483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86130841909201865113025977 64598131431901398834769483)
                ·
                  refine ⟨96897197147852098252154225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64598131431901398834769483 96897197147852098252154225)
                  ·
                    refine ⟨72672897860889073689115669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96897197147852098252154225 72672897860889073689115669)
                    ·
                      refine ⟨3406542087229175329177297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72672897860889073689115669 3406542087229175329177297)
                      ·
                        rfl

theorem cell23_6634217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_6634217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634217 prefixEnd_6634217 := by exact prefixLift 6634217
  have htrace : WordTrace (prefixWord ++ tailWord_6634217) baseStart_6634217 baseEnd_6634217 := by
    simpa [prefixWord, tailWord_6634217, baseEnd_6634217] using wordTrace_append hprefix tailTrace_6634217
  have hstable : (prefixWord ++ tailWord_6634217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634217).length < 2 ^ (prefixWord ++ tailWord_6634217).sum := by decide
  have hdescent : baseEnd_6634217 < baseStart_6634217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634298 : List Nat := [3, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4]
def baseStart_6634298 : Nat := 118140960795 + 6634298 * 2 ^ 59
def prefixEnd_6634298 : Nat := 4983230072969 + 3 ^ 40 * 6634298 * 2
def baseEnd_6634298 : Nat := 3406583679162189512264425

theorem tailTrace_6634298 : CollatzResearch.WordTrace tailWord_6634298 prefixEnd_6634298 3406583679162189512264425 := by
  unfold tailWord_6634298
  simp only [CollatzResearch.WordTrace]
  refine ⟨60493181729769717184239887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161315151279385912491306365 60493181729769717184239887)
  ·
    refine ⟨90739772594654575776359831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60493181729769717184239887 90739772594654575776359831)
    ·
      refine ⟨136109658891981863664539747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90739772594654575776359831 136109658891981863664539747)
      ·
        refine ⟨204164488337972795496809621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136109658891981863664539747 204164488337972795496809621)
        ·
          refine ⟨9570210390842474788912951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 204164488337972795496809621 9570210390842474788912951)
          ·
            refine ⟨14355315586263712183369427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9570210390842474788912951 14355315586263712183369427)
            ·
              refine ⟨21532973379395568275054141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14355315586263712183369427 21532973379395568275054141)
              ·
                refine ⟨8074865017273338103145303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21532973379395568275054141 8074865017273338103145303)
                ·
                  refine ⟨12112297525910007154717955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8074865017273338103145303 12112297525910007154717955)
                  ·
                    refine ⟨18168446288865010732076933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12112297525910007154717955 18168446288865010732076933)
                    ·
                      refine ⟨3406583679162189512264425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18168446288865010732076933 3406583679162189512264425)
                      ·
                        rfl

theorem cell23_6634298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4].length) (baseStart_6634298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634298 prefixEnd_6634298 := by exact prefixLift 6634298
  have htrace : WordTrace (prefixWord ++ tailWord_6634298) baseStart_6634298 baseEnd_6634298 := by
    simpa [prefixWord, tailWord_6634298, baseEnd_6634298] using wordTrace_append hprefix tailTrace_6634298
  have hstable : (prefixWord ++ tailWord_6634298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634298).length < 2 ^ (prefixWord ++ tailWord_6634298).sum := by decide
  have hdescent : baseEnd_6634298 < baseStart_6634298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634364 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 4, 6]
def baseStart_6634364 : Nat := 118140960795 + 6634364 * 2 ^ 59
def prefixEnd_6634364 : Nat := 4983230072969 + 3 ^ 40 * 6634364 * 2
def baseEnd_6634364 : Nat := 1135539189628462084679707

theorem tailTrace_6634364 : CollatzResearch.WordTrace tailWord_6634364 prefixEnd_6634364 1135539189628462084679707 := by
  unfold tailWord_6634364
  simp only [CollatzResearch.WordTrace]
  refine ⟨120987567068419881004431073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161316756091226508005908097 120987567068419881004431073)
  ·
    refine ⟨90740675301314910753323305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120987567068419881004431073 90740675301314910753323305)
    ·
      refine ⟨68055506475986183064992479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90740675301314910753323305 68055506475986183064992479)
      ·
        refine ⟨102083259713979274597488719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68055506475986183064992479 102083259713979274597488719)
        ·
          refine ⟨153124889570968911896233079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102083259713979274597488719 153124889570968911896233079)
          ·
            refine ⟨229687334356453367844349619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153124889570968911896233079 229687334356453367844349619)
            ·
              refine ⟨344531001534680051766524429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229687334356453367844349619 344531001534680051766524429)
              ·
                refine ⟨129199125575505019412446661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344531001534680051766524429 129199125575505019412446661)
                ·
                  refine ⟨24224836045407191139833749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129199125575505019412446661 24224836045407191139833749)
                  ·
                    refine ⟨1135539189628462084679707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24224836045407191139833749 1135539189628462084679707)
                    ·
                      rfl

theorem cell23_6634364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_6634364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634364 prefixEnd_6634364 := by exact prefixLift 6634364
  have htrace : WordTrace (prefixWord ++ tailWord_6634364) baseStart_6634364 baseEnd_6634364 := by
    simpa [prefixWord, tailWord_6634364, baseEnd_6634364] using wordTrace_append hprefix tailTrace_6634364
  have hstable : (prefixWord ++ tailWord_6634364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634364).length < 2 ^ (prefixWord ++ tailWord_6634364).sum := by decide
  have hdescent : baseEnd_6634364 < baseStart_6634364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634366 : List Nat := [4, 2, 3, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_6634366 : Nat := 118140960795 + 6634366 * 2 ^ 59
def prefixEnd_6634366 : Nat := 4983230072969 + 3 ^ 40 * 6634366 * 2
def baseEnd_6634366 : Nat := 3406618595846695246214113

theorem tailTrace_6634366 : CollatzResearch.WordTrace tailWord_6634366 prefixEnd_6634366 3406618595846695246214113 := by
  unfold tailWord_6634366
  simp only [CollatzResearch.WordTrace]
  refine ⟨30246900885354064543804369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161316804721888344233623301 30246900885354064543804369)
  ·
    refine ⟨22685175664015548407853277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30246900885354064543804369 22685175664015548407853277)
    ·
      refine ⟨8506940874005830652944979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22685175664015548407853277 8506940874005830652944979)
      ·
        refine ⟨12760411311008745979417469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8506940874005830652944979 12760411311008745979417469)
        ·
          refine ⟨4785154241628279742281551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12760411311008745979417469 4785154241628279742281551)
          ·
            refine ⟨7177731362442419613422327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4785154241628279742281551 7177731362442419613422327)
            ·
              refine ⟨10766597043663629420133491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7177731362442419613422327 10766597043663629420133491)
              ·
                refine ⟨16149895565495444130200237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10766597043663629420133491 16149895565495444130200237)
                ·
                  refine ⟨6056210837060791548825089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16149895565495444130200237 6056210837060791548825089)
                  ·
                    refine ⟨4542158127795593661618817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6056210837060791548825089 4542158127795593661618817)
                    ·
                      refine ⟨3406618595846695246214113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4542158127795593661618817 3406618595846695246214113)
                      ·
                        rfl

theorem cell23_6634366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_6634366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634366 prefixEnd_6634366 := by exact prefixLift 6634366
  have htrace : WordTrace (prefixWord ++ tailWord_6634366) baseStart_6634366 baseEnd_6634366 := by
    simpa [prefixWord, tailWord_6634366, baseEnd_6634366] using wordTrace_append hprefix tailTrace_6634366
  have hstable : (prefixWord ++ tailWord_6634366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634366).length < 2 ^ (prefixWord ++ tailWord_6634366).sum := by decide
  have hdescent : baseEnd_6634366 < baseStart_6634366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634458 : List Nat := [3, 1, 1, 2, 4, 1, 3, 1, 2, 5]
def baseStart_6634458 : Nat := 118140960795 + 6634458 * 2 ^ 59
def prefixEnd_6634458 : Nat := 4983230072969 + 3 ^ 40 * 6634458 * 2
def baseEnd_6634458 : Nat := 1135555278688969628754563

theorem tailTrace_6634458 : CollatzResearch.WordTrace tailWord_6634458 prefixEnd_6634458 1135555278688969628754563 := by
  unfold tailWord_6634458
  simp only [CollatzResearch.WordTrace]
  refine ⟨60494640649624804015696007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161319041732332810708522685 60494640649624804015696007)
  ·
    refine ⟨90741960974437206023544011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60494640649624804015696007 90741960974437206023544011)
    ·
      refine ⟨136112941461655809035316017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90741960974437206023544011 136112941461655809035316017)
      ·
        refine ⟨102084706096241856776487013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136112941461655809035316017 102084706096241856776487013)
        ·
          refine ⟨19140882393045348145591315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102084706096241856776487013 19140882393045348145591315)
          ·
            refine ⟨28711323589568022218386973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19140882393045348145591315 28711323589568022218386973)
            ·
              refine ⟨10766746346088008331895115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28711323589568022218386973 10766746346088008331895115)
              ·
                refine ⟨16150119519132012497842673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10766746346088008331895115 16150119519132012497842673)
                ·
                  refine ⟨12112589639349009373382005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16150119519132012497842673 12112589639349009373382005)
                  ·
                    refine ⟨1135555278688969628754563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12112589639349009373382005 1135555278688969628754563)
                    ·
                      rfl

theorem cell23_6634458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 2, 5].length) (baseStart_6634458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634458 prefixEnd_6634458 := by exact prefixLift 6634458
  have htrace : WordTrace (prefixWord ++ tailWord_6634458) baseStart_6634458 baseEnd_6634458 := by
    simpa [prefixWord, tailWord_6634458, baseEnd_6634458] using wordTrace_append hprefix tailTrace_6634458
  have hstable : (prefixWord ++ tailWord_6634458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634458).length < 2 ^ (prefixWord ++ tailWord_6634458).sum := by decide
  have hdescent : baseEnd_6634458 < baseStart_6634458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634551 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 4]
def baseStart_6634551 : Nat := 118140960795 + 6634551 * 2 ^ 59
def prefixEnd_6634551 : Nat := 4983230072969 + 3 ^ 40 * 6634551 * 2
def baseEnd_6634551 : Nat := 3406713589767777022400761

theorem tailTrace_6634551 : CollatzResearch.WordTrace tailWord_6634551 prefixEnd_6634551 3406713589767777022400761 := by
  unfold tailWord_6634551
  simp only [CollatzResearch.WordTrace]
  refine ⟨241981954587162292945919507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161321303058108195297279671 241981954587162292945919507)
  ·
    refine ⟨362972931880743439418879261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241981954587162292945919507 362972931880743439418879261)
    ·
      refine ⟨136114849455278789782079723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362972931880743439418879261 136114849455278789782079723)
      ·
        refine ⟨204172274182918184673119585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136114849455278789782079723 204172274182918184673119585)
        ·
          refine ⟨153129205637188638504839689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204172274182918184673119585 153129205637188638504839689)
          ·
            refine ⟨114846904227891478878629767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153129205637188638504839689 114846904227891478878629767)
            ·
              refine ⟨172270356341837218317944651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114846904227891478878629767 172270356341837218317944651)
              ·
                refine ⟨258405534512755827476916977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172270356341837218317944651 258405534512755827476916977)
                ·
                  refine ⟨193804150884566870607687733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258405534512755827476916977 193804150884566870607687733)
                  ·
                    refine ⟨18169139145428144119470725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 193804150884566870607687733 18169139145428144119470725)
                    ·
                      refine ⟨3406713589767777022400761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18169139145428144119470725 3406713589767777022400761)
                      ·
                        rfl

theorem cell23_6634551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_6634551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634551 prefixEnd_6634551 := by exact prefixLift 6634551
  have htrace : WordTrace (prefixWord ++ tailWord_6634551) baseStart_6634551 baseEnd_6634551 := by
    simpa [prefixWord, tailWord_6634551, baseEnd_6634551] using wordTrace_append hprefix tailTrace_6634551
  have hstable : (prefixWord ++ tailWord_6634551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634551).length < 2 ^ (prefixWord ++ tailWord_6634551).sum := by decide
  have hdescent : baseEnd_6634551 < baseStart_6634551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634568 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 3, 1, 4]
def baseStart_6634568 : Nat := 118140960795 + 6634568 * 2 ^ 59
def prefixEnd_6634568 : Nat := 4983230072969 + 3 ^ 40 * 6634568 * 2
def baseEnd_6634568 : Nat := 3406722318938903455888183

theorem tailTrace_6634568 : CollatzResearch.WordTrace tailWord_6634568 prefixEnd_6634568 3406722318938903455888183 := by
  unfold tailWord_6634568
  simp only [CollatzResearch.WordTrace]
  refine ⟨120991287314050352424644179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161321716418733803232858905 120991287314050352424644179)
  ·
    refine ⟨181486930971075528636966269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120991287314050352424644179 181486930971075528636966269)
    ·
      refine ⟨68057599114153323238862351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181486930971075528636966269 68057599114153323238862351)
      ·
        refine ⟨102086398671229984858293527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68057599114153323238862351 102086398671229984858293527)
        ·
          refine ⟨153129598006844977287440291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102086398671229984858293527 153129598006844977287440291)
          ·
            refine ⟨229694397010267465931160437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153129598006844977287440291 229694397010267465931160437)
            ·
              refine ⟨21533849719712574931046291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 229694397010267465931160437 21533849719712574931046291)
              ·
                refine ⟨32300774579568862396569437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21533849719712574931046291 32300774579568862396569437)
                ·
                  refine ⟨12112790467338323398713539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32300774579568862396569437 12112790467338323398713539)
                  ·
                    refine ⟨18169185701007485098070309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12112790467338323398713539 18169185701007485098070309)
                    ·
                      refine ⟨3406722318938903455888183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18169185701007485098070309 3406722318938903455888183)
                      ·
                        rfl

theorem cell23_6634568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_6634568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634568 prefixEnd_6634568 := by exact prefixLift 6634568
  have htrace : WordTrace (prefixWord ++ tailWord_6634568) baseStart_6634568 baseEnd_6634568 := by
    simpa [prefixWord, tailWord_6634568, baseEnd_6634568] using wordTrace_append hprefix tailTrace_6634568
  have hstable : (prefixWord ++ tailWord_6634568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634568).length < 2 ^ (prefixWord ++ tailWord_6634568).sum := by decide
  have hdescent : baseEnd_6634568 < baseStart_6634568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634578 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 3, 6]
def baseStart_6634578 : Nat := 118140960795 + 6634578 * 2 ^ 59
def prefixEnd_6634578 : Nat := 4983230072969 + 3 ^ 40 * 6634578 * 2
def baseEnd_6634578 : Nat := 1135575817915149472254379

theorem tailTrace_6634578 : CollatzResearch.WordTrace tailWord_6634578 prefixEnd_6634578 1135575817915149472254379 := by
  unfold tailWord_6634578
  simp only [CollatzResearch.WordTrace]
  refine ⟨60495734839516119139288097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161321959572042984371434925 60495734839516119139288097)
  ·
    refine ⟨45371801129637089354466073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60495734839516119139288097 45371801129637089354466073)
    ·
      refine ⟨34028850847227817015849555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45371801129637089354466073 34028850847227817015849555)
      ·
        refine ⟨51043276270841725523774333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34028850847227817015849555 51043276270841725523774333)
        ·
          refine ⟨19141228601565647071415375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51043276270841725523774333 19141228601565647071415375)
          ·
            refine ⟨28711842902348470607123063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19141228601565647071415375 28711842902348470607123063)
            ·
              refine ⟨43067764353522705910684595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28711842902348470607123063 43067764353522705910684595)
              ·
                refine ⟨64601646530284058866026893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43067764353522705910684595 64601646530284058866026893)
                ·
                  refine ⟨24225617448856522074760085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64601646530284058866026893 24225617448856522074760085)
                  ·
                    refine ⟨1135575817915149472254379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24225617448856522074760085 1135575817915149472254379)
                    ·
                      rfl

theorem cell23_6634578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_6634578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634578 prefixEnd_6634578 := by exact prefixLift 6634578
  have htrace : WordTrace (prefixWord ++ tailWord_6634578) baseStart_6634578 baseEnd_6634578 := by
    simpa [prefixWord, tailWord_6634578, baseEnd_6634578] using wordTrace_append hprefix tailTrace_6634578
  have hstable : (prefixWord ++ tailWord_6634578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634578).length < 2 ^ (prefixWord ++ tailWord_6634578).sum := by decide
  have hdescent : baseEnd_6634578 < baseStart_6634578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634585 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 7, 2, 2]
def baseStart_6634585 : Nat := 118140960795 + 6634585 * 2 ^ 59
def prefixEnd_6634585 : Nat := 4983230072969 + 3 ^ 40 * 6634585 * 2
def baseEnd_6634585 : Nat := 3406731048110029889375605

theorem tailTrace_6634585 : CollatzResearch.WordTrace tailWord_6634585 prefixEnd_6634585 3406731048110029889375605 := by
  unfold tailWord_6634585
  simp only [CollatzResearch.WordTrace]
  refine ⟨241983194669039116752657209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161322129779359411168438139 241983194669039116752657209)
  ·
    refine ⟨181487396001779337564492907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241983194669039116752657209 181487396001779337564492907)
    ·
      refine ⟨272231094002669006346739361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181487396001779337564492907 272231094002669006346739361)
      ·
        refine ⟨204173320502001754760054521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272231094002669006346739361 204173320502001754760054521)
        ·
          refine ⟨153129990376501316070040891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204173320502001754760054521 153129990376501316070040891)
          ·
            refine ⟨229694985564751974105061337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153129990376501316070040891 229694985564751974105061337)
            ·
              refine ⟨172271239173563980578796003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229694985564751974105061337 172271239173563980578796003)
              ·
                refine ⟨258406858760345970868194005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172271239173563980578796003 258406858760345970868194005)
                ·
                  refine ⟨6056410752195608692223297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 258406858760345970868194005 6056410752195608692223297)
                  ·
                    refine ⟨4542308064146706519167473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6056410752195608692223297 4542308064146706519167473)
                    ·
                      refine ⟨3406731048110029889375605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4542308064146706519167473 3406731048110029889375605)
                      ·
                        rfl

theorem cell23_6634585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 2, 2].length) (baseStart_6634585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634585 prefixEnd_6634585 := by exact prefixLift 6634585
  have htrace : WordTrace (prefixWord ++ tailWord_6634585) baseStart_6634585 baseEnd_6634585 := by
    simpa [prefixWord, tailWord_6634585, baseEnd_6634585] using wordTrace_append hprefix tailTrace_6634585
  have hstable : (prefixWord ++ tailWord_6634585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634585).length < 2 ^ (prefixWord ++ tailWord_6634585).sum := by decide
  have hdescent : baseEnd_6634585 < baseStart_6634585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634605 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 3, 2, 3]
def baseStart_6634605 : Nat := 118140960795 + 6634605 * 2 ^ 59
def prefixEnd_6634605 : Nat := 4983230072969 + 3 ^ 40 * 6634605 * 2
def baseEnd_6634605 : Nat := 3406741317723119811125513

theorem tailTrace_6634605 : CollatzResearch.WordTrace tailWord_6634605 prefixEnd_6634605 3406741317723119811125513 := by
  unfold tailWord_6634605
  simp only [CollatzResearch.WordTrace]
  refine ⟨241983924128966660168385269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161322616085977773445590179 241983924128966660168385269)
  ·
    refine ⟨22685992887090624390786119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 241983924128966660168385269 22685992887090624390786119)
    ·
      refine ⟨34028989330635936586179179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22685992887090624390786119 34028989330635936586179179)
      ·
        refine ⟨51043483995953904879268769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34028989330635936586179179 51043483995953904879268769)
        ·
          refine ⟨38282612996965428659451577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51043483995953904879268769 38282612996965428659451577)
          ·
            refine ⟨28711959747724071494588683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38282612996965428659451577 28711959747724071494588683)
            ·
              refine ⟨43067939621586107241883025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28711959747724071494588683 43067939621586107241883025)
              ·
                refine ⟨32300954716189580431412269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43067939621586107241883025 32300954716189580431412269)
                ·
                  refine ⟨12112858018571092661779601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32300954716189580431412269 12112858018571092661779601)
                  ·
                    refine ⟨9084643513928319496334701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12112858018571092661779601 9084643513928319496334701)
                    ·
                      refine ⟨3406741317723119811125513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9084643513928319496334701 3406741317723119811125513)
                      ·
                        rfl

theorem cell23_6634605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_6634605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634605 prefixEnd_6634605 := by exact prefixLift 6634605
  have htrace : WordTrace (prefixWord ++ tailWord_6634605) baseStart_6634605 baseEnd_6634605 := by
    simpa [prefixWord, tailWord_6634605, baseEnd_6634605] using wordTrace_append hprefix tailTrace_6634605
  have hstable : (prefixWord ++ tailWord_6634605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634605).length < 2 ^ (prefixWord ++ tailWord_6634605).sum := by decide
  have hdescent : baseEnd_6634605 < baseStart_6634605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634625 : List Nat := [1, 2, 4, 2, 2, 2, 3, 7]
def baseStart_6634625 : Nat := 118140960795 + 6634625 * 2 ^ 59
def prefixEnd_6634625 : Nat := 4983230072969 + 3 ^ 40 * 6634625 * 2
def baseEnd_6634625 : Nat := 126175984716155916032423

theorem tailTrace_6634625 : CollatzResearch.WordTrace tailWord_6634625 prefixEnd_6634625 126175984716155916032423 := by
  unfold tailWord_6634625
  simp only [CollatzResearch.WordTrace]
  refine ⟨241984653588894203584113329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161323102392596135722742219 241984653588894203584113329)
  ·
    refine ⟨181488490191670652688084997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241984653588894203584113329 181488490191670652688084997)
    ·
      refine ⟨34029091910938247379015937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181488490191670652688084997 34029091910938247379015937)
      ·
        refine ⟨25521818933203685534261953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34029091910938247379015937 25521818933203685534261953)
        ·
          refine ⟨19141364199902764150696465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25521818933203685534261953 19141364199902764150696465)
          ·
            refine ⟨14356023149927073113022349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19141364199902764150696465 14356023149927073113022349)
            ·
              refine ⟨5383508681222652417383381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14356023149927073113022349 5383508681222652417383381)
              ·
                refine ⟨126175984716155916032423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5383508681222652417383381 126175984716155916032423)
                ·
                  rfl

theorem cell23_6634625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 7].length) (baseStart_6634625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634625 prefixEnd_6634625 := by exact prefixLift 6634625
  have htrace : WordTrace (prefixWord ++ tailWord_6634625) baseStart_6634625 baseEnd_6634625 := by
    simpa [prefixWord, tailWord_6634625, baseEnd_6634625] using wordTrace_append hprefix tailTrace_6634625
  have hstable : (prefixWord ++ tailWord_6634625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634625).length < 2 ^ (prefixWord ++ tailWord_6634625).sum := by decide
  have hdescent : baseEnd_6634625 < baseStart_6634625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634645 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 5, 3, 2]
def baseStart_6634645 : Nat := 118140960795 + 6634645 * 2 ^ 59
def prefixEnd_6634645 : Nat := 4983230072969 + 3 ^ 40 * 6634645 * 2
def baseEnd_6634645 : Nat := 3406761856949299654625329

theorem tailTrace_6634645 : CollatzResearch.WordTrace tailWord_6634645 prefixEnd_6634645 3406761856949299654625329 := by
  unfold tailWord_6634645
  simp only [CollatzResearch.WordTrace]
  refine ⟨241985383048821746999841389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161323588699214497999894259 241985383048821746999841389)
  ·
    refine ⟨90744518643308155124940521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241985383048821746999841389 90744518643308155124940521)
    ·
      refine ⟨68058388982481116343705391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90744518643308155124940521 68058388982481116343705391)
      ·
        refine ⟨102087583473721674515558087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68058388982481116343705391 102087583473721674515558087)
        ·
          refine ⟨153131375210582511773337131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102087583473721674515558087 153131375210582511773337131)
          ·
            refine ⟨229697062815873767660005697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153131375210582511773337131 229697062815873767660005697)
            ·
              refine ⟨172272797111905325745004273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229697062815873767660005697 172272797111905325745004273)
              ·
                refine ⟨129204597833928994308753205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172272797111905325745004273 129204597833928994308753205)
                ·
                  refine ⟨12112931046930843216445613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129204597833928994308753205 12112931046930843216445613)
                  ·
                    refine ⟨4542349142599066206167105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12112931046930843216445613 4542349142599066206167105)
                    ·
                      refine ⟨3406761856949299654625329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4542349142599066206167105 3406761856949299654625329)
                      ·
                        rfl

theorem cell23_6634645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 3, 2].length) (baseStart_6634645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634645 prefixEnd_6634645 := by exact prefixLift 6634645
  have htrace : WordTrace (prefixWord ++ tailWord_6634645) baseStart_6634645 baseEnd_6634645 := by
    simpa [prefixWord, tailWord_6634645, baseEnd_6634645] using wordTrace_append hprefix tailTrace_6634645
  have hstable : (prefixWord ++ tailWord_6634645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634645).length < 2 ^ (prefixWord ++ tailWord_6634645).sum := by decide
  have hdescent : baseEnd_6634645 < baseStart_6634645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634652 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 4, 1, 3]
def baseStart_6634652 : Nat := 118140960795 + 6634652 * 2 ^ 59
def prefixEnd_6634652 : Nat := 4983230072969 + 3 ^ 40 * 6634652 * 2
def baseEnd_6634652 : Nat := 3406765451313881127237797

theorem tailTrace_6634652 : CollatzResearch.WordTrace tailWord_6634652 prefixEnd_6634652 3406765451313881127237797 := by
  unfold tailWord_6634652
  simp only [CollatzResearch.WordTrace]
  refine ⟨120992819179898193597673105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161323758906530924796897473 120992819179898193597673105)
  ·
    refine ⟨90744614384923645198254829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120992819179898193597673105 90744614384923645198254829)
    ·
      refine ⟨34029230394346366949345561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90744614384923645198254829 34029230394346366949345561)
      ·
        refine ⟨25521922795759775212009171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34029230394346366949345561 25521922795759775212009171)
        ·
          refine ⟨38282884193639662818013757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25521922795759775212009171 38282884193639662818013757)
          ·
            refine ⟨14356081572614873556755159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38282884193639662818013757 14356081572614873556755159)
            ·
              refine ⟨21534122358922310335132739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14356081572614873556755159 21534122358922310335132739)
              ·
                refine ⟨32301183538383465502699109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21534122358922310335132739 32301183538383465502699109)
                ·
                  refine ⟨6056471913446899781756083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32301183538383465502699109 6056471913446899781756083)
                  ·
                    refine ⟨9084707870170349672634125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6056471913446899781756083 9084707870170349672634125)
                    ·
                      refine ⟨3406765451313881127237797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9084707870170349672634125 3406765451313881127237797)
                      ·
                        rfl

theorem cell23_6634652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_6634652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634652 prefixEnd_6634652 := by exact prefixLift 6634652
  have htrace : WordTrace (prefixWord ++ tailWord_6634652) baseStart_6634652 baseEnd_6634652 := by
    simpa [prefixWord, tailWord_6634652, baseEnd_6634652] using wordTrace_append hprefix tailTrace_6634652
  have hstable : (prefixWord ++ tailWord_6634652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634652).length < 2 ^ (prefixWord ++ tailWord_6634652).sum := by decide
  have hdescent : baseEnd_6634652 < baseStart_6634652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634669 : List Nat := [1, 5, 2, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_6634669 : Nat := 118140960795 + 6634669 * 2 ^ 59
def prefixEnd_6634669 : Nat := 4983230072969 + 3 ^ 40 * 6634669 * 2
def baseEnd_6634669 : Nat := 3406774180485007560725219

theorem tailTrace_6634669 : CollatzResearch.WordTrace tailWord_6634669 prefixEnd_6634669 3406774180485007560725219 := by
  unfold tailWord_6634669
  simp only [CollatzResearch.WordTrace]
  refine ⟨241986258400734799098715061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161324172267156532732476707 241986258400734799098715061)
  ·
    refine ⟨22686211725068887415504537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 241986258400734799098715061 22686211725068887415504537)
    ·
      refine ⟨17014658793801665561628403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22686211725068887415504537 17014658793801665561628403)
      ·
        refine ⟨25521988190702498342442605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17014658793801665561628403 25521988190702498342442605)
        ·
          refine ⟨9570745571513436878415977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25521988190702498342442605 9570745571513436878415977)
          ·
            refine ⟨7178059178635077658811983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9570745571513436878415977 7178059178635077658811983)
            ·
              refine ⟨10767088767952616488217975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7178059178635077658811983 10767088767952616488217975)
              ·
                refine ⟨16150633151928924732326963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10767088767952616488217975 16150633151928924732326963)
                ·
                  refine ⟨24225949727893387098490445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16150633151928924732326963 24225949727893387098490445)
                  ·
                    refine ⟨9084731147960020161933917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24225949727893387098490445 9084731147960020161933917)
                    ·
                      refine ⟨3406774180485007560725219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9084731147960020161933917 3406774180485007560725219)
                      ·
                        rfl

theorem cell23_6634669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_6634669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634669 prefixEnd_6634669 := by exact prefixLift 6634669
  have htrace : WordTrace (prefixWord ++ tailWord_6634669) baseStart_6634669 baseEnd_6634669 := by
    simpa [prefixWord, tailWord_6634669, baseEnd_6634669] using wordTrace_append hprefix tailTrace_6634669
  have hstable : (prefixWord ++ tailWord_6634669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634669).length < 2 ^ (prefixWord ++ tailWord_6634669).sum := by decide
  have hdescent : baseEnd_6634669 < baseStart_6634669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634709 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 4, 2, 2]
def baseStart_6634709 : Nat := 118140960795 + 6634709 * 2 ^ 59
def prefixEnd_6634709 : Nat := 4983230072969 + 3 ^ 40 * 6634709 * 2
def baseEnd_6634709 : Nat := 3406794719711187404225035

theorem tailTrace_6634709 : CollatzResearch.WordTrace tailWord_6634709 prefixEnd_6634709 3406794719711187404225035 := by
  unfold tailWord_6634709
  simp only [CollatzResearch.WordTrace]
  refine ⟨241987717320589885930171181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161325144880393257286780787 241987717320589885930171181)
  ·
    refine ⟨90745393995221207223814193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241987717320589885930171181 90745393995221207223814193)
    ·
      refine ⟨68059045496415905417860645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90745393995221207223814193 68059045496415905417860645)
      ·
        refine ⟨12761071030577982265848871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68059045496415905417860645 12761071030577982265848871)
        ·
          refine ⟨19141606545866973398773307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12761071030577982265848871 19141606545866973398773307)
          ·
            refine ⟨28712409818800460098159961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19141606545866973398773307 28712409818800460098159961)
            ·
              refine ⟨21534307364100345073619971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28712409818800460098159961 21534307364100345073619971)
              ·
                refine ⟨32301461046150517610429957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21534307364100345073619971 32301461046150517610429957)
                ·
                  refine ⟨6056523946153222051955617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32301461046150517610429957 6056523946153222051955617)
                  ·
                    refine ⟨4542392959614916538966713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6056523946153222051955617 4542392959614916538966713)
                    ·
                      refine ⟨3406794719711187404225035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4542392959614916538966713 3406794719711187404225035)
                      ·
                        rfl

theorem cell23_6634709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_6634709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634709 prefixEnd_6634709 := by exact prefixLift 6634709
  have htrace : WordTrace (prefixWord ++ tailWord_6634709) baseStart_6634709 baseEnd_6634709 := by
    simpa [prefixWord, tailWord_6634709, baseEnd_6634709] using wordTrace_append hprefix tailTrace_6634709
  have hstable : (prefixWord ++ tailWord_6634709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634709).length < 2 ^ (prefixWord ++ tailWord_6634709).sum := by decide
  have hdescent : baseEnd_6634709 < baseStart_6634709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634745 : List Nat := [1, 2, 1, 3, 1, 1, 6, 1, 2, 5]
def baseStart_6634745 : Nat := 118140960795 + 6634745 * 2 ^ 59
def prefixEnd_6634745 : Nat := 4983230072969 + 3 ^ 40 * 6634745 * 2
def baseEnd_6634745 : Nat := 1135604401671583087791623

theorem tailTrace_6634745 : CollatzResearch.WordTrace tailWord_6634745 prefixEnd_6634745 1135604401671583087791623 := by
  unfold tailWord_6634745
  simp only [CollatzResearch.WordTrace]
  refine ⟨241989030348459464078481689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161326020232306309385654459 241989030348459464078481689)
  ·
    refine ⟨181491772761344598058861267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241989030348459464078481689 181491772761344598058861267)
    ·
      refine ⟨272237659142016897088291901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181491772761344598058861267 272237659142016897088291901)
      ·
        refine ⟨102089122178256336408109463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272237659142016897088291901 102089122178256336408109463)
        ·
          refine ⟨153133683267384504612164195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102089122178256336408109463 153133683267384504612164195)
          ·
            refine ⟨229700524901076756918246293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153133683267384504612164195 229700524901076756918246293)
            ·
              refine ⟨10767212104737972980542795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 229700524901076756918246293 10767212104737972980542795)
              ·
                refine ⟨16150818157106959470814193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10767212104737972980542795 16150818157106959470814193)
                ·
                  refine ⟨12113113617830219603110645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16150818157106959470814193 12113113617830219603110645)
                  ·
                    refine ⟨1135604401671583087791623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12113113617830219603110645 1135604401671583087791623)
                    ·
                      rfl

theorem cell23_6634745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 5].length) (baseStart_6634745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634745 prefixEnd_6634745 := by exact prefixLift 6634745
  have htrace : WordTrace (prefixWord ++ tailWord_6634745) baseStart_6634745 baseEnd_6634745 := by
    simpa [prefixWord, tailWord_6634745, baseEnd_6634745] using wordTrace_append hprefix tailTrace_6634745
  have hstable : (prefixWord ++ tailWord_6634745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634745).length < 2 ^ (prefixWord ++ tailWord_6634745).sum := by decide
  have hdescent : baseEnd_6634745 < baseStart_6634745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634785 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 1, 4, 3]
def baseStart_6634785 : Nat := 118140960795 + 6634785 * 2 ^ 59
def prefixEnd_6634785 : Nat := 4983230072969 + 3 ^ 40 * 6634785 * 2
def baseEnd_6634785 : Nat := 3406833744240929106874685

theorem tailTrace_6634785 : CollatzResearch.WordTrace tailWord_6634785 prefixEnd_6634785 3406833744240929106874685 := by
  unfold tailWord_6634785
  simp only [CollatzResearch.WordTrace]
  refine ⟨241990489268314550909937809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161326992845543033939958539 241990489268314550909937809)
  ·
    refine ⟨181492866951235913182453357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241990489268314550909937809 181492866951235913182453357)
    ·
      refine ⟨68059825106713467443420009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181492866951235913182453357 68059825106713467443420009)
      ·
        refine ⟨51044868830035100582565007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68059825106713467443420009 51044868830035100582565007)
        ·
          refine ⟨76567303245052650873847511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51044868830035100582565007 76567303245052650873847511)
          ·
            refine ⟨114850954867578976310771267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76567303245052650873847511 114850954867578976310771267)
            ·
              refine ⟨172276432301368464466156901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114850954867578976310771267 172276432301368464466156901)
              ·
                refine ⟨32301831056506587087404419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172276432301368464466156901 32301831056506587087404419)
                ·
                  refine ⟨48452746584759880631106629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32301831056506587087404419 48452746584759880631106629)
                  ·
                    refine ⟨9084889984642477618332493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48452746584759880631106629 9084889984642477618332493)
                    ·
                      refine ⟨3406833744240929106874685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9084889984642477618332493 3406833744240929106874685)
                      ·
                        rfl

theorem cell23_6634785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_6634785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634785 prefixEnd_6634785 := by exact prefixLift 6634785
  have htrace : WordTrace (prefixWord ++ tailWord_6634785) baseStart_6634785 baseEnd_6634785 := by
    simpa [prefixWord, tailWord_6634785, baseEnd_6634785] using wordTrace_append hprefix tailTrace_6634785
  have hstable : (prefixWord ++ tailWord_6634785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634785).length < 2 ^ (prefixWord ++ tailWord_6634785).sum := by decide
  have hdescent : baseEnd_6634785 < baseStart_6634785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634792 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 5, 4]
def baseStart_6634792 : Nat := 118140960795 + 6634792 * 2 ^ 59
def prefixEnd_6634792 : Nat := 4983230072969 + 3 ^ 40 * 6634792 * 2
def baseEnd_6634792 : Nat := 1135612446201836859829051

theorem tailTrace_6634792 : CollatzResearch.WordTrace tailWord_6634792 prefixEnd_6634792 1135612446201836859829051 := by
  unfold tailWord_6634792
  simp only [CollatzResearch.WordTrace]
  refine ⟨120995372289644595552721315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161327163052859460736961753 120995372289644595552721315)
  ·
    refine ⟨181493058434466893329081973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120995372289644595552721315 181493058434466893329081973)
    ·
      refine ⟨17014974228231271249601435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181493058434466893329081973 17014974228231271249601435)
      ·
        refine ⟨25522461342346906874402153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17014974228231271249601435 25522461342346906874402153)
        ·
          refine ⟨19141846006760180155801615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25522461342346906874402153 19141846006760180155801615)
          ·
            refine ⟨28712769010140270233702423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19141846006760180155801615 28712769010140270233702423)
            ·
              refine ⟨43069153515210405350553635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28712769010140270233702423 43069153515210405350553635)
              ·
                refine ⟨64603730272815608025830453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43069153515210405350553635 64603730272815608025830453)
                ·
                  refine ⟨6056599713076463252421605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64603730272815608025830453 6056599713076463252421605)
                  ·
                    refine ⟨1135612446201836859829051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6056599713076463252421605 1135612446201836859829051)
                    ·
                      rfl

theorem cell23_6634792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_6634792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634792 prefixEnd_6634792 := by exact prefixLift 6634792
  have htrace : WordTrace (prefixWord ++ tailWord_6634792) baseStart_6634792 baseEnd_6634792 := by
    simpa [prefixWord, tailWord_6634792, baseEnd_6634792] using wordTrace_append hprefix tailTrace_6634792
  have hstable : (prefixWord ++ tailWord_6634792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634792).length < 2 ^ (prefixWord ++ tailWord_6634792).sum := by decide
  have hdescent : baseEnd_6634792 < baseStart_6634792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634802 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3]
def baseStart_6634802 : Nat := 118140960795 + 6634802 * 2 ^ 59
def prefixEnd_6634802 : Nat := 4983230072969 + 3 ^ 40 * 6634802 * 2
def baseEnd_6634802 : Nat := 3406842473412055540362107

theorem tailTrace_6634802 : CollatzResearch.WordTrace tailWord_6634802 prefixEnd_6634802 3406842473412055540362107 := by
  unfold tailWord_6634802
  simp only [CollatzResearch.WordTrace]
  refine ⟨60497777327313240703326665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161327406206168641875537773 60497777327313240703326665)
  ·
    refine ⟨45373332995484930527494999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60497777327313240703326665 45373332995484930527494999)
    ·
      refine ⟨68059999493227395791242499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45373332995484930527494999 68059999493227395791242499)
      ·
        refine ⟨102089999239841093686863749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68059999493227395791242499 102089999239841093686863749)
        ·
          refine ⟨19141874857470205066286953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102089999239841093686863749 19141874857470205066286953)
          ·
            refine ⟨14356406143102653799715215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19141874857470205066286953 14356406143102653799715215)
            ·
              refine ⟨21534609214653980699572823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14356406143102653799715215 21534609214653980699572823)
              ·
                refine ⟨32301913821980971049359235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21534609214653980699572823 32301913821980971049359235)
                ·
                  refine ⟨48452870732971456574038853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32301913821980971049359235 48452870732971456574038853)
                  ·
                    refine ⟨9084913262432148107632285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48452870732971456574038853 9084913262432148107632285)
                    ·
                      refine ⟨3406842473412055540362107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9084913262432148107632285 3406842473412055540362107)
                      ·
                        rfl

theorem cell23_6634802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_6634802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634802 prefixEnd_6634802 := by exact prefixLift 6634802
  have htrace : WordTrace (prefixWord ++ tailWord_6634802) baseStart_6634802 baseEnd_6634802 := by
    simpa [prefixWord, tailWord_6634802, baseEnd_6634802] using wordTrace_append hprefix tailTrace_6634802
  have hstable : (prefixWord ++ tailWord_6634802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634802).length < 2 ^ (prefixWord ++ tailWord_6634802).sum := by decide
  have hdescent : baseEnd_6634802 < baseStart_6634802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634842 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2]
def baseStart_6634842 : Nat := 118140960795 + 6634842 * 2 ^ 59
def prefixEnd_6634842 : Nat := 4983230072969 + 3 ^ 40 * 6634842 * 2
def baseEnd_6634842 : Nat := 3406863012638235383861923

theorem tailTrace_6634842 : CollatzResearch.WordTrace tailWord_6634842 prefixEnd_6634842 3406863012638235383861923 := by
  unfold tailWord_6634842
  simp only [CollatzResearch.WordTrace]
  refine ⟨60498142057277012411190695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161328378819405366429841853 60498142057277012411190695)
  ·
    refine ⟨90747213085915518616786043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60498142057277012411190695 90747213085915518616786043)
    ·
      refine ⟨136120819628873277925179065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90747213085915518616786043 136120819628873277925179065)
      ·
        refine ⟨102090614721654958443884299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136120819628873277925179065 102090614721654958443884299)
        ·
          refine ⟨153135922082482437665826449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102090614721654958443884299 153135922082482437665826449)
          ·
            refine ⟨114851941561861828249369837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153135922082482437665826449 114851941561861828249369837)
            ·
              refine ⟨43069478085698185593513689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114851941561861828249369837 43069478085698185593513689)
              ·
                refine ⟨32302108564273639195135267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43069478085698185593513689 32302108564273639195135267)
                ·
                  refine ⟨48453162846410458792702901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32302108564273639195135267 48453162846410458792702901)
                  ·
                    refine ⟨4542484016850980511815897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48453162846410458792702901 4542484016850980511815897)
                    ·
                      refine ⟨3406863012638235383861923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4542484016850980511815897 3406863012638235383861923)
                      ·
                        rfl

theorem cell23_6634842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2].length) (baseStart_6634842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634842 prefixEnd_6634842 := by exact prefixLift 6634842
  have htrace : WordTrace (prefixWord ++ tailWord_6634842) baseStart_6634842 baseEnd_6634842 := by
    simpa [prefixWord, tailWord_6634842, baseEnd_6634842] using wordTrace_append hprefix tailTrace_6634842
  have hstable : (prefixWord ++ tailWord_6634842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634842).length < 2 ^ (prefixWord ++ tailWord_6634842).sum := by decide
  have hdescent : baseEnd_6634842 < baseStart_6634842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634852 : List Nat := [2, 3, 1, 1, 3, 2, 1, 4, 1, 5]
def baseStart_6634852 : Nat := 118140960795 + 6634852 * 2 ^ 59
def prefixEnd_6634852 : Nat := 4983230072969 + 3 ^ 40 * 6634852 * 2
def baseEnd_6634852 : Nat := 1135622715814926781578959

theorem tailTrace_6634852 : CollatzResearch.WordTrace tailWord_6634852 prefixEnd_6634852 1135622715814926781578959 := by
  unfold tailWord_6634852
  simp only [CollatzResearch.WordTrace]
  refine ⟨120996466479535910676313405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161328621972714547568417873 120996466479535910676313405)
  ·
    refine ⟨45373674929825966503617527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120996466479535910676313405 45373674929825966503617527)
    ·
      refine ⟨68060512394738949755426291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45373674929825966503617527 68060512394738949755426291)
      ·
        refine ⟨102090768592108424633139437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68060512394738949755426291 102090768592108424633139437)
        ·
          refine ⟨38284038222040659237427289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102090768592108424633139437 38284038222040659237427289)
          ·
            refine ⟨28713028666530494428070467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38284038222040659237427289 28713028666530494428070467)
            ·
              refine ⟨43069542999795741642105701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28713028666530494428070467 43069542999795741642105701)
              ·
                refine ⟨8075539312461701557894819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43069542999795741642105701 8075539312461701557894819)
                ·
                  refine ⟨12113308968692552336842229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8075539312461701557894819 12113308968692552336842229)
                  ·
                    refine ⟨1135622715814926781578959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12113308968692552336842229 1135622715814926781578959)
                    ·
                      rfl

theorem cell23_6634852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_6634852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634852 prefixEnd_6634852 := by exact prefixLift 6634852
  have htrace : WordTrace (prefixWord ++ tailWord_6634852) baseStart_6634852 baseEnd_6634852 := by
    simpa [prefixWord, tailWord_6634852, baseEnd_6634852] using wordTrace_append hprefix tailTrace_6634852
  have hstable : (prefixWord ++ tailWord_6634852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634852).length < 2 ^ (prefixWord ++ tailWord_6634852).sum := by decide
  have hdescent : baseEnd_6634852 < baseStart_6634852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634865 : List Nat := [1, 2, 2, 2, 1, 2, 2, 4, 1, 6]
def baseStart_6634865 : Nat := 118140960795 + 6634865 * 2 ^ 59
def prefixEnd_6634865 : Nat := 4983230072969 + 3 ^ 40 * 6634865 * 2
def baseEnd_6634865 : Nat := 1135624940897762931291439

theorem tailTrace_6634865 : CollatzResearch.WordTrace tailWord_6634865 prefixEnd_6634865 1135624940897762931291439 := by
  unfold tailWord_6634865
  simp only [CollatzResearch.WordTrace]
  refine ⟨241993407108024724572850049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161328938072016483048566699 241993407108024724572850049)
  ·
    refine ⟨181495055331018543429637537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241993407108024724572850049 181495055331018543429637537)
    ·
      refine ⟨136121291498263907572228153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181495055331018543429637537 136121291498263907572228153)
      ·
        refine ⟨102090968623697930679171115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136121291498263907572228153 102090968623697930679171115)
        ·
          refine ⟨153136452935546896018756673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102090968623697930679171115 153136452935546896018756673)
          ·
            refine ⟨114852339701660172014067505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153136452935546896018756673 114852339701660172014067505)
            ·
              refine ⟨86139254776245129010550629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114852339701660172014067505 86139254776245129010550629)
              ·
                refine ⟨16151110270545961689478243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86139254776245129010550629 16151110270545961689478243)
                ·
                  refine ⟨24226665405818942534217365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16151110270545961689478243 24226665405818942534217365)
                  ·
                    refine ⟨1135624940897762931291439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24226665405818942534217365 1135624940897762931291439)
                    ·
                      rfl

theorem cell23_6634865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_6634865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634865 prefixEnd_6634865 := by exact prefixLift 6634865
  have htrace : WordTrace (prefixWord ++ tailWord_6634865) baseStart_6634865 baseEnd_6634865 := by
    simpa [prefixWord, tailWord_6634865, baseEnd_6634865] using wordTrace_append hprefix tailTrace_6634865
  have hstable : (prefixWord ++ tailWord_6634865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634865).length < 2 ^ (prefixWord ++ tailWord_6634865).sum := by decide
  have hdescent : baseEnd_6634865 < baseStart_6634865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634883 : List Nat := [1, 1, 1, 3, 5, 2, 3, 2, 1, 1, 3]
def baseStart_6634883 : Nat := 118140960795 + 6634883 * 2 ^ 59
def prefixEnd_6634883 : Nat := 4983230072969 + 3 ^ 40 * 6634883 * 2
def baseEnd_6634883 : Nat := 3406884065345069723449235

theorem tailTrace_6634883 : CollatzResearch.WordTrace tailWord_6634883 prefixEnd_6634883 3406884065345069723449235 := by
  unfold tailWord_6634883
  simp only [CollatzResearch.WordTrace]
  refine ⟨241994063621959513647005303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161329375747973009098003535 241994063621959513647005303)
  ·
    refine ⟨362991095432939270470507955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241994063621959513647005303 362991095432939270470507955)
    ·
      refine ⟨544486643149408905705761933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362991095432939270470507955 544486643149408905705761933)
      ·
        refine ⟨204182491181028339639660725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 544486643149408905705761933 204182491181028339639660725)
        ·
          refine ⟨19142108548221406841218193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 204182491181028339639660725 19142108548221406841218193)
          ·
            refine ⟨14356581411166055130913645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19142108548221406841218193 14356581411166055130913645)
            ·
              refine ⟨5383718029187270674092617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14356581411166055130913645 5383718029187270674092617)
              ·
                refine ⟨4037788521890453005569463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5383718029187270674092617 4037788521890453005569463)
                ·
                  refine ⟨6056682782835679508354195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4037788521890453005569463 6056682782835679508354195)
                  ·
                    refine ⟨9085024174253519262531293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6056682782835679508354195 9085024174253519262531293)
                    ·
                      refine ⟨3406884065345069723449235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9085024174253519262531293 3406884065345069723449235)
                      ·
                        rfl

theorem cell23_6634883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 1, 1, 3].length) (baseStart_6634883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634883 prefixEnd_6634883 := by exact prefixLift 6634883
  have htrace : WordTrace (prefixWord ++ tailWord_6634883) baseStart_6634883 baseEnd_6634883 := by
    simpa [prefixWord, tailWord_6634883, baseEnd_6634883] using wordTrace_append hprefix tailTrace_6634883
  have hstable : (prefixWord ++ tailWord_6634883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634883).length < 2 ^ (prefixWord ++ tailWord_6634883).sum := by decide
  have hdescent : baseEnd_6634883 < baseStart_6634883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634885 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 1, 1, 6]
def baseStart_6634885 : Nat := 118140960795 + 6634885 * 2 ^ 59
def prefixEnd_6634885 : Nat := 4983230072969 + 3 ^ 40 * 6634885 * 2
def baseEnd_6634885 : Nat := 3406885092306378715624225

theorem tailTrace_6634885 : CollatzResearch.WordTrace tailWord_6634885 prefixEnd_6634885 3406885092306378715624225 := by
  unfold tailWord_6634885
  simp only [CollatzResearch.WordTrace]
  refine ⟨241994136567952267988578109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161329424378634845325718739 241994136567952267988578109)
  ·
    refine ⟨90747801212982100495716791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241994136567952267988578109 90747801212982100495716791)
    ·
      refine ⟨136121701819473150743575187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90747801212982100495716791 136121701819473150743575187)
      ·
        refine ⟨204182552729209726115362781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136121701819473150743575187 204182552729209726115362781)
        ·
          refine ⟨76568457273453647293261043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204182552729209726115362781 76568457273453647293261043)
          ·
            refine ⟨114852685910180470939891565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76568457273453647293261043 114852685910180470939891565)
            ·
              refine ⟨43069757216317676602459337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114852685910180470939891565 43069757216317676602459337)
              ·
                refine ⟨32302317912238257451844503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43069757216317676602459337 32302317912238257451844503)
                ·
                  refine ⟨48453476868357386177766755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32302317912238257451844503 48453476868357386177766755)
                  ·
                    refine ⟨72680215302536079266650133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48453476868357386177766755 72680215302536079266650133)
                    ·
                      refine ⟨3406885092306378715624225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72680215302536079266650133 3406885092306378715624225)
                      ·
                        rfl

theorem cell23_6634885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_6634885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634885 prefixEnd_6634885 := by exact prefixLift 6634885
  have htrace : WordTrace (prefixWord ++ tailWord_6634885) baseStart_6634885 baseEnd_6634885 := by
    simpa [prefixWord, tailWord_6634885, baseEnd_6634885] using wordTrace_append hprefix tailTrace_6634885
  have hstable : (prefixWord ++ tailWord_6634885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634885).length < 2 ^ (prefixWord ++ tailWord_6634885).sum := by decide
  have hdescent : baseEnd_6634885 < baseStart_6634885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634892 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 3, 2, 3]
def baseStart_6634892 : Nat := 118140960795 + 6634892 * 2 ^ 59
def prefixEnd_6634892 : Nat := 4983230072969 + 3 ^ 40 * 6634892 * 2
def baseEnd_6634892 : Nat := 3406888686670960188236693

theorem tailTrace_6634892 : CollatzResearch.WordTrace tailWord_6634892 prefixEnd_6634892 3406888686670960188236693 := by
  unfold tailWord_6634892
  simp only [CollatzResearch.WordTrace]
  refine ⟨120997195939463454092041465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161329594585951272122721953 120997195939463454092041465)
  ·
    refine ⟨90747896954597590569031099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120997195939463454092041465 90747896954597590569031099)
    ·
      refine ⟨136121845431896385853546649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90747896954597590569031099 136121845431896385853546649)
      ·
        refine ⟨102091384073922289390159987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136121845431896385853546649 102091384073922289390159987)
        ·
          refine ⟨153137076110883434085239981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102091384073922289390159987 153137076110883434085239981)
          ·
            refine ⟨57426403541581287781964993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153137076110883434085239981 57426403541581287781964993)
            ·
              refine ⟨43069802656185965836473745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57426403541581287781964993 43069802656185965836473745)
              ·
                refine ⟨32302351992139474377355309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43069802656185965836473745 32302351992139474377355309)
                ·
                  refine ⟨12113381997052302891508241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32302351992139474377355309 12113381997052302891508241)
                  ·
                    refine ⟨9085036497789227168631181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12113381997052302891508241 9085036497789227168631181)
                    ·
                      refine ⟨3406888686670960188236693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9085036497789227168631181 3406888686670960188236693)
                      ·
                        rfl

theorem cell23_6634892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_6634892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634892 prefixEnd_6634892 := by exact prefixLift 6634892
  have htrace : WordTrace (prefixWord ++ tailWord_6634892) baseStart_6634892 baseEnd_6634892 := by
    simpa [prefixWord, tailWord_6634892, baseEnd_6634892] using wordTrace_append hprefix tailTrace_6634892
  have hstable : (prefixWord ++ tailWord_6634892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634892).length < 2 ^ (prefixWord ++ tailWord_6634892).sum := by decide
  have hdescent : baseEnd_6634892 < baseStart_6634892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634909 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 3, 2, 3]
def baseStart_6634909 : Nat := 118140960795 + 6634909 * 2 ^ 59
def prefixEnd_6634909 : Nat := 4983230072969 + 3 ^ 40 * 6634909 * 2
def baseEnd_6634909 : Nat := 3406897415842086621724115

theorem tailTrace_6634909 : CollatzResearch.WordTrace tailWord_6634909 prefixEnd_6634909 3406897415842086621724115 := by
  unfold tailWord_6634909
  simp only [CollatzResearch.WordTrace]
  refine ⟨241995011919865320087451781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161330007946576880058301187 241995011919865320087451781)
  ·
    refine ⟨45374064734974747516397209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241995011919865320087451781 45374064734974747516397209)
    ·
      refine ⟨34030548551231060637297907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45374064734974747516397209 34030548551231060637297907)
      ·
        refine ⟨51045822826846590955946861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34030548551231060637297907 51045822826846590955946861)
        ·
          refine ⟨19142183560067471608480073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51045822826846590955946861 19142183560067471608480073)
          ·
            refine ⟨14356637670050603706360055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19142183560067471608480073 14356637670050603706360055)
            ·
              refine ⟨21534956505075905559540083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14356637670050603706360055 21534956505075905559540083)
              ·
                refine ⟨32302434757613858339310125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21534956505075905559540083 32302434757613858339310125)
                ·
                  refine ⟨12113413034105196877241297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32302434757613858339310125 12113413034105196877241297)
                  ·
                    refine ⟨9085059775578897657930973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12113413034105196877241297 9085059775578897657930973)
                    ·
                      refine ⟨3406897415842086621724115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9085059775578897657930973 3406897415842086621724115)
                      ·
                        rfl

theorem cell23_6634909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_6634909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634909 prefixEnd_6634909 := by exact prefixLift 6634909
  have htrace : WordTrace (prefixWord ++ tailWord_6634909) baseStart_6634909 baseEnd_6634909 := by
    simpa [prefixWord, tailWord_6634909, baseEnd_6634909] using wordTrace_append hprefix tailTrace_6634909
  have hstable : (prefixWord ++ tailWord_6634909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634909).length < 2 ^ (prefixWord ++ tailWord_6634909).sum := by decide
  have hdescent : baseEnd_6634909 < baseStart_6634909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634940 : List Nat := [2, 2, 2, 4, 2, 1, 1, 4, 1, 2, 2]
def baseStart_6634940 : Nat := 118140960795 + 6634940 * 2 ^ 59
def prefixEnd_6634940 : Nat := 4983230072969 + 3 ^ 40 * 6634940 * 2
def baseEnd_6634940 : Nat := 3406913333742376000436473

theorem tailTrace_6634940 : CollatzResearch.WordTrace tailWord_6634940 prefixEnd_6634940 3406913333742376000436473 := by
  unfold tailWord_6634940
  simp only [CollatzResearch.WordTrace]
  refine ⟨120998071291376506190915137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161330761721835341587886849 120998071291376506190915137)
  ·
    refine ⟨90748553468532379643186353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120998071291376506190915137 90748553468532379643186353)
    ·
      refine ⟨68061415101399284732389765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90748553468532379643186353 68061415101399284732389765)
      ·
        refine ⟨12761515331512365887323081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68061415101399284732389765 12761515331512365887323081)
        ·
          refine ⟨9571136498634274415492311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12761515331512365887323081 9571136498634274415492311)
          ·
            refine ⟨14356704747951411623238467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9571136498634274415492311 14356704747951411623238467)
            ·
              refine ⟨21535057121927117434857701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14356704747951411623238467 21535057121927117434857701)
              ·
                refine ⟨4037823210361334519035819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21535057121927117434857701 4037823210361334519035819)
                ·
                  refine ⟨6056734815542001778553729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4037823210361334519035819 6056734815542001778553729)
                  ·
                    refine ⟨4542551111656501333915297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6056734815542001778553729 4542551111656501333915297)
                    ·
                      refine ⟨3406913333742376000436473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4542551111656501333915297 3406913333742376000436473)
                      ·
                        rfl

theorem cell23_6634940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_6634940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634940 prefixEnd_6634940 := by exact prefixLift 6634940
  have htrace : WordTrace (prefixWord ++ tailWord_6634940) baseStart_6634940 baseEnd_6634940 := by
    simpa [prefixWord, tailWord_6634940, baseEnd_6634940] using wordTrace_append hprefix tailTrace_6634940
  have hstable : (prefixWord ++ tailWord_6634940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634940).length < 2 ^ (prefixWord ++ tailWord_6634940).sum := by decide
  have hdescent : baseEnd_6634940 < baseStart_6634940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634955 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 1, 8]
def baseStart_6634955 : Nat := 118140960795 + 6634955 * 2 ^ 59
def prefixEnd_6634955 : Nat := 4983230072969 + 3 ^ 40 * 6634955 * 2
def baseEnd_6634955 : Nat := 1135640345317397813916301

theorem tailTrace_6634955 : CollatzResearch.WordTrace tailWord_6634955 prefixEnd_6634955 1135640345317397813916301 := by
  unfold tailWord_6634955
  simp only [CollatzResearch.WordTrace]
  refine ⟨241996689677698669943626319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161331126451799113295750879 241996689677698669943626319)
  ·
    refine ⟨362995034516548004915439479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241996689677698669943626319 362995034516548004915439479)
    ·
      refine ⟨544492551774822007373159219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362995034516548004915439479 544492551774822007373159219)
      ·
        refine ⟨816738827662233011059738829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544492551774822007373159219 816738827662233011059738829)
        ·
          refine ⟨306277060373337379147402061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 816738827662233011059738829 306277060373337379147402061)
          ·
            refine ⟨114853897640001517180275773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306277060373337379147402061 114853897640001517180275773)
            ·
              refine ⟨43070211615000568942603415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114853897640001517180275773 43070211615000568942603415)
              ·
                refine ⟨64605317422500853413905123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43070211615000568942603415 64605317422500853413905123)
                ·
                  refine ⟨96907976133751280120857685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64605317422500853413905123 96907976133751280120857685)
                  ·
                    refine ⟨1135640345317397813916301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96907976133751280120857685 1135640345317397813916301)
                    ·
                      rfl

theorem cell23_6634955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 8].length) (baseStart_6634955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634955 prefixEnd_6634955 := by exact prefixLift 6634955
  have htrace : WordTrace (prefixWord ++ tailWord_6634955) baseStart_6634955 baseEnd_6634955 := by
    simpa [prefixWord, tailWord_6634955, baseEnd_6634955] using wordTrace_append hprefix tailTrace_6634955
  have hstable : (prefixWord ++ tailWord_6634955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634955).length < 2 ^ (prefixWord ++ tailWord_6634955).sum := by decide
  have hdescent : baseEnd_6634955 < baseStart_6634955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634956 : List Nat := [2, 2, 1, 4, 2, 1, 2, 3, 2, 1, 3]
def baseStart_6634956 : Nat := 118140960795 + 6634956 * 2 ^ 59
def prefixEnd_6634956 : Nat := 4983230072969 + 3 ^ 40 * 6634956 * 2
def baseEnd_6634956 : Nat := 3406921549432847937836399

theorem tailTrace_6634956 : CollatzResearch.WordTrace tailWord_6634956 prefixEnd_6634956 3406921549432847937836399 := by
  unfold tailWord_6634956
  simp only [CollatzResearch.WordTrace]
  refine ⟨120998363075347523557206361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161331150767130031409608481 120998363075347523557206361)
  ·
    refine ⟨90748772306510642667904771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120998363075347523557206361 90748772306510642667904771)
    ·
      refine ⟨136123158459765964001857157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90748772306510642667904771 136123158459765964001857157)
      ·
        refine ⟨25523092211206118250348217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136123158459765964001857157 25523092211206118250348217)
        ·
          refine ⟨19142319158404588687761163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25523092211206118250348217 19142319158404588687761163)
          ·
            refine ⟨28713478737606883031641745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19142319158404588687761163 28713478737606883031641745)
            ·
              refine ⟨21535109053205162273731309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28713478737606883031641745 21535109053205162273731309)
              ·
                refine ⟨8075665894951935852649241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21535109053205162273731309 8075665894951935852649241)
                ·
                  refine ⟨6056749421213951889486931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8075665894951935852649241 6056749421213951889486931)
                  ·
                    refine ⟨9085124131820927834230397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6056749421213951889486931 9085124131820927834230397)
                    ·
                      refine ⟨3406921549432847937836399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9085124131820927834230397 3406921549432847937836399)
                      ·
                        rfl

theorem cell23_6634956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_6634956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634956 prefixEnd_6634956 := by exact prefixLift 6634956
  have htrace : WordTrace (prefixWord ++ tailWord_6634956) baseStart_6634956 baseEnd_6634956 := by
    simpa [prefixWord, tailWord_6634956, baseEnd_6634956] using wordTrace_append hprefix tailTrace_6634956
  have hstable : (prefixWord ++ tailWord_6634956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634956).length < 2 ^ (prefixWord ++ tailWord_6634956).sum := by decide
  have hdescent : baseEnd_6634956 < baseStart_6634956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634983 : List Nat := [1, 1, 5, 2, 1, 2, 4, 1, 1, 3, 2]
def baseStart_6634983 : Nat := 118140960795 + 6634983 * 2 ^ 59
def prefixEnd_6634983 : Nat := 4983230072969 + 3 ^ 40 * 6634983 * 2
def baseEnd_6634983 : Nat := 3406935413410519332198775

theorem tailTrace_6634983 : CollatzResearch.WordTrace tailWord_6634983 prefixEnd_6634983 3406935413410519332198775 := by
  unfold tailWord_6634983
  simp only [CollatzResearch.WordTrace]
  refine ⟨241997710921597230725645603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161331807281064820483763735 241997710921597230725645603)
  ·
    refine ⟨362996566382395846088468405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241997710921597230725645603 362996566382395846088468405)
    ·
      refine ⟨34030928098349610570793913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 362996566382395846088468405 34030928098349610570793913)
      ·
        refine ⟨25523196073762207928095435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34030928098349610570793913 25523196073762207928095435)
        ·
          refine ⟨38284794110643311892143153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25523196073762207928095435 38284794110643311892143153)
          ·
            refine ⟨28713595582982483919107365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38284794110643311892143153 28713595582982483919107365)
            ·
              refine ⟨5383799171809215734832631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28713595582982483919107365 5383799171809215734832631)
              ·
                refine ⟨8075698757713823602248947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5383799171809215734832631 8075698757713823602248947)
                ·
                  refine ⟨12113548136570735403373421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8075698757713823602248947 12113548136570735403373421)
                  ·
                    refine ⟨4542580551214025776265033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12113548136570735403373421 4542580551214025776265033)
                    ·
                      refine ⟨3406935413410519332198775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4542580551214025776265033 3406935413410519332198775)
                      ·
                        rfl

theorem cell23_6634983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_6634983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634983 prefixEnd_6634983 := by exact prefixLift 6634983
  have htrace : WordTrace (prefixWord ++ tailWord_6634983) baseStart_6634983 baseEnd_6634983 := by
    simpa [prefixWord, tailWord_6634983, baseEnd_6634983] using wordTrace_append hprefix tailTrace_6634983
  have hstable : (prefixWord ++ tailWord_6634983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634983).length < 2 ^ (prefixWord ++ tailWord_6634983).sum := by decide
  have hdescent : baseEnd_6634983 < baseStart_6634983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634992 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 4]
def baseStart_6634992 : Nat := 118140960795 + 6634992 * 2 ^ 59
def prefixEnd_6634992 : Nat := 4983230072969 + 3 ^ 40 * 6634992 * 2
def baseEnd_6634992 : Nat := 3406940034736409796986233

theorem tailTrace_6634992 : CollatzResearch.WordTrace tailWord_6634992 prefixEnd_6634992 3406940034736409796986233 := by
  unfold tailWord_6634992
  simp only [CollatzResearch.WordTrace]
  refine ⟨120999019589282312631361615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161332026119043083508482153 120999019589282312631361615)
  ·
    refine ⟨181498529383923468947042423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120999019589282312631361615 181498529383923468947042423)
    ·
      refine ⟨272247794075885203420563635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181498529383923468947042423 272247794075885203420563635)
      ·
        refine ⟨408371691113827805130845453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272247794075885203420563635 408371691113827805130845453)
        ·
          refine ⟨153139384167685426924067045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 408371691113827805130845453 153139384167685426924067045)
          ·
            refine ⟨28713634531441017548262571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153139384167685426924067045 28713634531441017548262571)
            ·
              refine ⟨43070451797161526322393857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28713634531441017548262571 43070451797161526322393857)
              ·
                refine ⟨32302838847871144741795393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43070451797161526322393857 32302838847871144741795393)
                ·
                  refine ⟨24227129135903358556346545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32302838847871144741795393 24227129135903358556346545)
                  ·
                    refine ⟨18170346851927518917259909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24227129135903358556346545 18170346851927518917259909)
                    ·
                      refine ⟨3406940034736409796986233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18170346851927518917259909 3406940034736409796986233)
                      ·
                        rfl

theorem cell23_6634992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 4].length) (baseStart_6634992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634992 prefixEnd_6634992 := by exact prefixLift 6634992
  have htrace : WordTrace (prefixWord ++ tailWord_6634992) baseStart_6634992 baseEnd_6634992 := by
    simpa [prefixWord, tailWord_6634992, baseEnd_6634992] using wordTrace_append hprefix tailTrace_6634992
  have hstable : (prefixWord ++ tailWord_6634992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634992).length < 2 ^ (prefixWord ++ tailWord_6634992).sum := by decide
  have hdescent : baseEnd_6634992 < baseStart_6634992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6634995 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 9]
def baseStart_6634995 : Nat := 118140960795 + 6634995 * 2 ^ 59
def prefixEnd_6634995 : Nat := 4983230072969 + 3 ^ 40 * 6634995 * 2
def baseEnd_6634995 : Nat := 3406941575178373285248719

theorem tailTrace_6634995 : CollatzResearch.WordTrace tailWord_6634995 prefixEnd_6634995 3406941575178373285248719 := by
  unfold tailWord_6634995
  simp only [CollatzResearch.WordTrace]
  refine ⟨241998148597553756775082439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161332099065035837850054959 241998148597553756775082439)
  ·
    refine ⟨362997222896330635162623659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241998148597553756775082439 362997222896330635162623659)
    ·
      refine ⟨544495834344495952743935489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362997222896330635162623659 544495834344495952743935489)
      ·
        refine ⟨408371875758371964557951617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 544495834344495952743935489 408371875758371964557951617)
        ·
          refine ⟨306278906818778973418463713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408371875758371964557951617 306278906818778973418463713)
          ·
            refine ⟨229709180114084230063847785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306278906818778973418463713 229709180114084230063847785)
            ·
              refine ⟨172281885085563172547885839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229709180114084230063847785 172281885085563172547885839)
              ·
                refine ⟨258422827628344758821828759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172281885085563172547885839 258422827628344758821828759)
                ·
                  refine ⟨387634241442517138232743139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258422827628344758821828759 387634241442517138232743139)
                  ·
                    refine ⟨581451362163775707349114709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 387634241442517138232743139 581451362163775707349114709)
                    ·
                      refine ⟨3406941575178373285248719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 581451362163775707349114709 3406941575178373285248719)
                      ·
                        rfl

theorem cell23_6634995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_6634995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6634995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6634995 prefixEnd_6634995 := by exact prefixLift 6634995
  have htrace : WordTrace (prefixWord ++ tailWord_6634995) baseStart_6634995 baseEnd_6634995 := by
    simpa [prefixWord, tailWord_6634995, baseEnd_6634995] using wordTrace_append hprefix tailTrace_6634995
  have hstable : (prefixWord ++ tailWord_6634995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6634995).length < 2 ^ (prefixWord ++ tailWord_6634995).sum := by decide
  have hdescent : baseEnd_6634995 < baseStart_6634995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6634995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635002 : List Nat := [3, 1, 1, 1, 1, 2, 6, 1, 7]
def baseStart_6635002 : Nat := 118140960795 + 6635002 * 2 ^ 59
def prefixEnd_6635002 : Nat := 4983230072969 + 3 ^ 40 * 6635002 * 2
def baseEnd_6635002 : Nat := 378549463282550528651243

theorem tailTrace_6635002 : CollatzResearch.WordTrace tailWord_6635002 prefixEnd_6635002 378549463282550528651243 := by
  unfold tailWord_6635002
  simp only [CollatzResearch.WordTrace]
  refine ⟨60499600977132099242646815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161332269272352264647058173 60499600977132099242646815)
  ·
    refine ⟨90749401465698148863970223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60499600977132099242646815 90749401465698148863970223)
    ·
      refine ⟨136124102198547223295955335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90749401465698148863970223 136124102198547223295955335)
      ·
        refine ⟨204186153297820834943933003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136124102198547223295955335 204186153297820834943933003)
        ·
          refine ⟨306279229946731252415899505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204186153297820834943933003 306279229946731252415899505)
          ·
            refine ⟨229709422460048439311924629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306279229946731252415899505 229709422460048439311924629)
            ·
              refine ⟨10767629177814770592746467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 229709422460048439311924629 10767629177814770592746467)
              ·
                refine ⟨16151443766722155889119701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10767629177814770592746467 16151443766722155889119701)
                ·
                  refine ⟨378549463282550528651243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16151443766722155889119701 378549463282550528651243)
                  ·
                    rfl

theorem cell23_6635002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 7].length) (baseStart_6635002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635002 prefixEnd_6635002 := by exact prefixLift 6635002
  have htrace : WordTrace (prefixWord ++ tailWord_6635002) baseStart_6635002 baseEnd_6635002 := by
    simpa [prefixWord, tailWord_6635002, baseEnd_6635002] using wordTrace_append hprefix tailTrace_6635002
  have hstable : (prefixWord ++ tailWord_6635002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635002).length < 2 ^ (prefixWord ++ tailWord_6635002).sum := by decide
  have hdescent : baseEnd_6635002 < baseStart_6635002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635096 : List Nat := [2, 1, 2, 2, 1, 2, 1, 7, 1, 4]
def baseStart_6635096 : Nat := 118140960795 + 6635096 * 2 ^ 59
def prefixEnd_6635096 : Nat := 4983230072969 + 3 ^ 40 * 6635096 * 2
def baseEnd_6635096 : Nat := 1135664478908159130028585

theorem tailTrace_6635096 : CollatzResearch.WordTrace tailWord_6635096 prefixEnd_6635096 1135664478908159130028585 := by
  unfold tailWord_6635096
  simp only [CollatzResearch.WordTrace]
  refine ⟨121000916185093925512254571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161334554913458567349672761 121000916185093925512254571)
  ·
    refine ⟨181501374277640888268381857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121000916185093925512254571 181501374277640888268381857)
    ·
      refine ⟨136126030708230666201286393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181501374277640888268381857 136126030708230666201286393)
      ·
        refine ⟨102094523031172999650964795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136126030708230666201286393 102094523031172999650964795)
        ·
          refine ⟨153141784546759499476447193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102094523031172999650964795 153141784546759499476447193)
          ·
            refine ⟨114856338410069624607335395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153141784546759499476447193 114856338410069624607335395)
            ·
              refine ⟨172284507615104436911003093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114856338410069624607335395 172284507615104436911003093)
              ·
                refine ⟨4037918147229010240101635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 172284507615104436911003093 4037918147229010240101635)
                ·
                  refine ⟨6056877220843515360152453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4037918147229010240101635 6056877220843515360152453)
                  ·
                    refine ⟨1135664478908159130028585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6056877220843515360152453 1135664478908159130028585)
                    ·
                      rfl

theorem cell23_6635096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 1, 4].length) (baseStart_6635096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635096 prefixEnd_6635096 := by exact prefixLift 6635096
  have htrace : WordTrace (prefixWord ++ tailWord_6635096) baseStart_6635096 baseEnd_6635096 := by
    simpa [prefixWord, tailWord_6635096, baseEnd_6635096] using wordTrace_append hprefix tailTrace_6635096
  have hstable : (prefixWord ++ tailWord_6635096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635096).length < 2 ^ (prefixWord ++ tailWord_6635096).sum := by decide
  have hdescent : baseEnd_6635096 < baseStart_6635096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635109 : List Nat := [1, 3, 1, 3, 3, 1, 1, 4, 6]
def baseStart_6635109 : Nat := 118140960795 + 6635109 * 2 ^ 59
def prefixEnd_6635109 : Nat := 4983230072969 + 3 ^ 40 * 6635109 * 2
def baseEnd_6635109 : Nat := 378555567996998426580355

theorem tailTrace_6635109 : CollatzResearch.WordTrace tailWord_6635109 prefixEnd_6635109 378555567996998426580355 := by
  unfold tailWord_6635109
  simp only [CollatzResearch.WordTrace]
  refine ⟨242002306519140754244732381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161334871012760502829821587 242002306519140754244732381)
  ·
    refine ⟨90750864944677782841774643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242002306519140754244732381 90750864944677782841774643)
    ·
      refine ⟨136126297417016674262661965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90750864944677782841774643 136126297417016674262661965)
      ·
        refine ⟨51047361531381252848498237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136126297417016674262661965 51047361531381252848498237)
        ·
          refine ⟨19142760574267969818186839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51047361531381252848498237 19142760574267969818186839)
          ·
            refine ⟨28714140861401954727280259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19142760574267969818186839 28714140861401954727280259)
            ·
              refine ⟨43071211292102932090920389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28714140861401954727280259 43071211292102932090920389)
              ·
                refine ⟨8075852117269299767047573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43071211292102932090920389 8075852117269299767047573)
                ·
                  refine ⟨378555567996998426580355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8075852117269299767047573 378555567996998426580355)
                  ·
                    rfl

theorem cell23_6635109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 6].length) (baseStart_6635109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635109 prefixEnd_6635109 := by exact prefixLift 6635109
  have htrace : WordTrace (prefixWord ++ tailWord_6635109) baseStart_6635109 baseEnd_6635109 := by
    simpa [prefixWord, tailWord_6635109, baseEnd_6635109] using wordTrace_append hprefix tailTrace_6635109
  have hstable : (prefixWord ++ tailWord_6635109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635109).length < 2 ^ (prefixWord ++ tailWord_6635109).sum := by decide
  have hdescent : baseEnd_6635109 < baseStart_6635109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635113 : List Nat := [1, 2, 1, 1, 1, 4, 6, 2, 1, 4]
def baseStart_6635113 : Nat := 118140960795 + 6635113 * 2 ^ 59
def prefixEnd_6635113 : Nat := 4983230072969 + 3 ^ 40 * 6635113 * 2
def baseEnd_6635113 : Nat := 1135667388631867941191059

theorem tailTrace_6635113 : CollatzResearch.WordTrace tailWord_6635113 prefixEnd_6635113 1135667388631867941191059 := by
  unfold tailWord_6635113
  simp only [CollatzResearch.WordTrace]
  refine ⟨242002452411126262927877993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161334968274084175285251995 242002452411126262927877993)
  ·
    refine ⟨181501839308344697195908495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242002452411126262927877993 181501839308344697195908495)
    ·
      refine ⟨272252758962517045793862743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181501839308344697195908495 272252758962517045793862743)
      ·
        refine ⟨408379138443775568690794115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272252758962517045793862743 408379138443775568690794115)
        ·
          refine ⟨612568707665663353036191173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408379138443775568690794115 612568707665663353036191173)
          ·
            refine ⟨114856632687311878694285845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 612568707665663353036191173 114856632687311878694285845)
            ·
              refine ⟨5383904657217744313794649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114856632687311878694285845 5383904657217744313794649)
              ·
                refine ⟨4037928492913308235345987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5383904657217744313794649 4037928492913308235345987)
                ·
                  refine ⟨6056892739369962353018981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4037928492913308235345987 6056892739369962353018981)
                  ·
                    refine ⟨1135667388631867941191059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6056892739369962353018981 1135667388631867941191059)
                    ·
                      rfl

theorem cell23_6635113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 1, 4].length) (baseStart_6635113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635113 prefixEnd_6635113 := by exact prefixLift 6635113
  have htrace : WordTrace (prefixWord ++ tailWord_6635113) baseStart_6635113 baseEnd_6635113 := by
    simpa [prefixWord, tailWord_6635113, baseEnd_6635113] using wordTrace_append hprefix tailTrace_6635113
  have hstable : (prefixWord ++ tailWord_6635113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635113).length < 2 ^ (prefixWord ++ tailWord_6635113).sum := by decide
  have hdescent : baseEnd_6635113 < baseStart_6635113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635126 : List Nat := [5, 1, 1, 2, 2, 1, 2, 3, 6]
def baseStart_6635126 : Nat := 118140960795 + 6635126 * 2 ^ 59
def prefixEnd_6635126 : Nat := 4983230072969 + 3 ^ 40 * 6635126 * 2
def baseEnd_6635126 : Nat := 378556537904901363634513

theorem tailTrace_6635126 : CollatzResearch.WordTrace tailWord_6635126 prefixEnd_6635126 378556537904901363634513 := by
  unfold tailWord_6635126
  simp only [CollatzResearch.WordTrace]
  refine ⟨15125182910004947884256327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161335284373386110765400821 15125182910004947884256327)
  ·
    refine ⟨22687774365007421826384491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15125182910004947884256327 22687774365007421826384491)
    ·
      refine ⟨34031661547511132739576737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22687774365007421826384491 34031661547511132739576737)
      ·
        refine ⟨25523746160633349554682553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34031661547511132739576737 25523746160633349554682553)
        ·
          refine ⟨19142809620475012166011915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25523746160633349554682553 19142809620475012166011915)
          ·
            refine ⟨28714214430712518249017873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19142809620475012166011915 28714214430712518249017873)
            ·
              refine ⟨21535660823034388686763405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28714214430712518249017873 21535660823034388686763405)
              ·
                refine ⟨8075872808637895757536277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21535660823034388686763405 8075872808637895757536277)
                ·
                  refine ⟨378556537904901363634513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8075872808637895757536277 378556537904901363634513)
                  ·
                    rfl

theorem cell23_6635126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_6635126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635126 prefixEnd_6635126 := by exact prefixLift 6635126
  have htrace : WordTrace (prefixWord ++ tailWord_6635126) baseStart_6635126 baseEnd_6635126 := by
    simpa [prefixWord, tailWord_6635126, baseEnd_6635126] using wordTrace_append hprefix tailTrace_6635126
  have hstable : (prefixWord ++ tailWord_6635126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635126).length < 2 ^ (prefixWord ++ tailWord_6635126).sum := by decide
  have hdescent : baseEnd_6635126 < baseStart_6635126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635132 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 1, 3, 7]
def baseStart_6635132 : Nat := 118140960795 + 6635132 * 2 ^ 59
def prefixEnd_6635132 : Nat := 4983230072969 + 3 ^ 40 * 6635132 * 2
def baseEnd_6635132 : Nat := 3407011922028039249235589

theorem tailTrace_6635132 : CollatzResearch.WordTrace tailWord_6635132 prefixEnd_6635132 3407011922028039249235589 := by
  unfold tailWord_6635132
  simp only [CollatzResearch.WordTrace]
  refine ⟨121001572699028714586409825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161335430265371619448546433 121001572699028714586409825)
  ·
    refine ⟨90751179524271535939807369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121001572699028714586409825 90751179524271535939807369)
    ·
      refine ⟨68063384643203651954855527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90751179524271535939807369 68063384643203651954855527)
      ·
        refine ⟨102095076964805477932283291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68063384643203651954855527 102095076964805477932283291)
        ·
          refine ⟨153142615447208216898424937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102095076964805477932283291 153142615447208216898424937)
          ·
            refine ⟨114856961585406162673818703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153142615447208216898424937 114856961585406162673818703)
            ·
              refine ⟨172285442378109244010728055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114856961585406162673818703 172285442378109244010728055)
              ·
                refine ⟨258428163567163866016092083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172285442378109244010728055 258428163567163866016092083)
                ·
                  refine ⟨387642245350745799024138125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258428163567163866016092083 387642245350745799024138125)
                  ·
                    refine ⟨145365842006529674634051797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 387642245350745799024138125 145365842006529674634051797)
                    ·
                      refine ⟨3407011922028039249235589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145365842006529674634051797 3407011922028039249235589)
                      ·
                        rfl

theorem cell23_6635132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_6635132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635132 prefixEnd_6635132 := by exact prefixLift 6635132
  have htrace : WordTrace (prefixWord ++ tailWord_6635132) baseStart_6635132 baseEnd_6635132 := by
    simpa [prefixWord, tailWord_6635132, baseEnd_6635132] using wordTrace_append hprefix tailTrace_6635132
  have hstable : (prefixWord ++ tailWord_6635132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635132).length < 2 ^ (prefixWord ++ tailWord_6635132).sum := by decide
  have hdescent : baseEnd_6635132 < baseStart_6635132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635136 : List Nat := [2, 1, 1, 2, 1, 4, 3, 2, 3, 1, 3]
def baseStart_6635136 : Nat := 118140960795 + 6635136 * 2 ^ 59
def prefixEnd_6635136 : Nat := 4983230072969 + 3 ^ 40 * 6635136 * 2
def baseEnd_6635136 : Nat := 3407013975950657233585571

theorem tailTrace_6635136 : CollatzResearch.WordTrace tailWord_6635136 prefixEnd_6635136 3407013975950657233585571 := by
  unfold tailWord_6635136
  simp only [CollatzResearch.WordTrace]
  refine ⟨121001645645021468927982631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161335527526695291903976841 121001645645021468927982631)
  ·
    refine ⟨181502468467532203391973947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121001645645021468927982631 181502468467532203391973947)
    ·
      refine ⟨272253702701298305087960921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181502468467532203391973947 272253702701298305087960921)
      ·
        refine ⟨204190277025973728815970691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272253702701298305087960921 204190277025973728815970691)
        ·
          refine ⟨306285415538960593223956037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204190277025973728815970691 306285415538960593223956037)
          ·
            refine ⟨57428515413555111229491757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 306285415538960593223956037 57428515413555111229491757)
            ·
              refine ⟨21535693280083166711059409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57428515413555111229491757 21535693280083166711059409)
              ·
                refine ⟨16151769960062375033294557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21535693280083166711059409 16151769960062375033294557)
                ·
                  refine ⟨6056913735023390637485459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16151769960062375033294557 6056913735023390637485459)
                  ·
                    refine ⟨9085370602535085956228189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6056913735023390637485459 9085370602535085956228189)
                    ·
                      refine ⟨3407013975950657233585571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9085370602535085956228189 3407013975950657233585571)
                      ·
                        rfl

theorem cell23_6635136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 3, 1, 3].length) (baseStart_6635136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635136 prefixEnd_6635136 := by exact prefixLift 6635136
  have htrace : WordTrace (prefixWord ++ tailWord_6635136) baseStart_6635136 baseEnd_6635136 := by
    simpa [prefixWord, tailWord_6635136, baseEnd_6635136] using wordTrace_append hprefix tailTrace_6635136
  have hstable : (prefixWord ++ tailWord_6635136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635136).length < 2 ^ (prefixWord ++ tailWord_6635136).sum := by decide
  have hdescent : baseEnd_6635136 < baseStart_6635136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635139 : List Nat := [1, 1, 1, 3, 3, 1, 1, 6, 1, 5]
def baseStart_6635139 : Nat := 118140960795 + 6635139 * 2 ^ 59
def prefixEnd_6635139 : Nat := 4983230072969 + 3 ^ 40 * 6635139 * 2
def baseEnd_6635139 : Nat := 1135671838797540240616019

theorem tailTrace_6635139 : CollatzResearch.WordTrace tailWord_6635139 prefixEnd_6635139 1135671838797540240616019 := by
  unfold tailWord_6635139
  simp only [CollatzResearch.WordTrace]
  refine ⟨242003400709032069368324471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161335600472688046245549647 242003400709032069368324471)
  ·
    refine ⟨363005101063548104052486707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242003400709032069368324471 363005101063548104052486707)
    ·
      refine ⟨544507651595322156078730061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363005101063548104052486707 544507651595322156078730061)
      ·
        refine ⟨204190369348245808529523773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 544507651595322156078730061 204190369348245808529523773)
        ·
          refine ⟨76571388505592178198571415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204190369348245808529523773 76571388505592178198571415)
          ·
            refine ⟨114857082758388267297857123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76571388505592178198571415 114857082758388267297857123)
            ·
              refine ⟨172285624137582400946785685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114857082758388267297857123 172285624137582400946785685)
              ·
                refine ⟨8075888631449175044380579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 172285624137582400946785685 8075888631449175044380579)
                ·
                  refine ⟨12113832947173762566570869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8075888631449175044380579 12113832947173762566570869)
                  ·
                    refine ⟨1135671838797540240616019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12113832947173762566570869 1135671838797540240616019)
                    ·
                      rfl

theorem cell23_6635139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 5].length) (baseStart_6635139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635139 prefixEnd_6635139 := by exact prefixLift 6635139
  have htrace : WordTrace (prefixWord ++ tailWord_6635139) baseStart_6635139 baseEnd_6635139 := by
    simpa [prefixWord, tailWord_6635139, baseEnd_6635139] using wordTrace_append hprefix tailTrace_6635139
  have hstable : (prefixWord ++ tailWord_6635139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635139).length < 2 ^ (prefixWord ++ tailWord_6635139).sum := by decide
  have hdescent : baseEnd_6635139 < baseStart_6635139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635140 : List Nat := [2, 3, 2, 1, 5, 1, 1, 1, 2, 2, 3]
def baseStart_6635140 : Nat := 118140960795 + 6635140 * 2 ^ 59
def prefixEnd_6635140 : Nat := 4983230072969 + 3 ^ 40 * 6635140 * 2
def baseEnd_6635140 : Nat := 3407016029873275217935553

theorem tailTrace_6635140 : CollatzResearch.WordTrace tailWord_6635140 prefixEnd_6635140 3407016029873275217935553 := by
  unfold tailWord_6635140
  simp only [CollatzResearch.WordTrace]
  refine ⟨121001718591014223269555437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161335624788018964359407249 121001718591014223269555437)
  ·
    refine ⟨45375644471630333726083289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121001718591014223269555437 45375644471630333726083289)
    ·
      refine ⟨34031733353722750294562467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45375644471630333726083289 34031733353722750294562467)
      ·
        refine ⟨51047600030584125441843701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34031733353722750294562467 51047600030584125441843701)
        ·
          refine ⟨4785712502867261760172847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51047600030584125441843701 4785712502867261760172847)
          ·
            refine ⟨7178568754300892640259271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4785712502867261760172847 7178568754300892640259271)
            ·
              refine ⟨10767853131451338960388907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7178568754300892640259271 10767853131451338960388907)
              ·
                refine ⟨16151779697177008440583361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10767853131451338960388907 16151779697177008440583361)
                ·
                  refine ⟨12113834772882756330437521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16151779697177008440583361 12113834772882756330437521)
                  ·
                    refine ⟨9085376079662067247828141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12113834772882756330437521 9085376079662067247828141)
                    ·
                      refine ⟨3407016029873275217935553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9085376079662067247828141 3407016029873275217935553)
                      ·
                        rfl

theorem cell23_6635140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_6635140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635140 prefixEnd_6635140 := by exact prefixLift 6635140
  have htrace : WordTrace (prefixWord ++ tailWord_6635140) baseStart_6635140 baseEnd_6635140 := by
    simpa [prefixWord, tailWord_6635140, baseEnd_6635140] using wordTrace_append hprefix tailTrace_6635140
  have hstable : (prefixWord ++ tailWord_6635140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635140).length < 2 ^ (prefixWord ++ tailWord_6635140).sum := by decide
  have hdescent : baseEnd_6635140 < baseStart_6635140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635186 : List Nat := [3, 2, 1, 1, 1, 2, 2, 5, 2, 4]
def baseStart_6635186 : Nat := 118140960795 + 6635186 * 2 ^ 59
def prefixEnd_6635186 : Nat := 4983230072969 + 3 ^ 40 * 6635186 * 2
def baseEnd_6635186 : Nat := 1135679883327794012653447

theorem tailTrace_6635186 : CollatzResearch.WordTrace tailWord_6635186 prefixEnd_6635186 1135679883327794012653447 := by
  unfold tailWord_6635186
  simp only [CollatzResearch.WordTrace]
  refine ⟨60501278734965449098821353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161336743293241197596856941 60501278734965449098821353)
  ·
    refine ⟨45375959051224086824116015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60501278734965449098821353 45375959051224086824116015)
    ·
      refine ⟨68063938576836130236174023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45375959051224086824116015 68063938576836130236174023)
      ·
        refine ⟨102095907865254195354261035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68063938576836130236174023 102095907865254195354261035)
        ·
          refine ⟨153143861797881293031391553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102095907865254195354261035 153143861797881293031391553)
          ·
            refine ⟨114857896348410969773543665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153143861797881293031391553 114857896348410969773543665)
            ·
              refine ⟨86143422261308227330157749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114857896348410969773543665 86143422261308227330157749)
              ·
                refine ⟨8075945836997646312202289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86143422261308227330157749 8075945836997646312202289)
                ·
                  refine ⟨6056959377748234734151717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8075945836997646312202289 6056959377748234734151717)
                  ·
                    refine ⟨1135679883327794012653447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6056959377748234734151717 1135679883327794012653447)
                    ·
                      rfl

theorem cell23_6635186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_6635186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635186 prefixEnd_6635186 := by exact prefixLift 6635186
  have htrace : WordTrace (prefixWord ++ tailWord_6635186) baseStart_6635186 baseEnd_6635186 := by
    simpa [prefixWord, tailWord_6635186, baseEnd_6635186] using wordTrace_append hprefix tailTrace_6635186
  have hstable : (prefixWord ++ tailWord_6635186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635186).length < 2 ^ (prefixWord ++ tailWord_6635186).sum := by decide
  have hdescent : baseEnd_6635186 < baseStart_6635186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635190 : List Nat := [5, 1, 3, 1, 1, 2, 2, 2, 1, 5]
def baseStart_6635190 : Nat := 118140960795 + 6635190 * 2 ^ 59
def prefixEnd_6635190 : Nat := 4983230072969 + 3 ^ 40 * 6635190 * 2
def baseEnd_6635190 : Nat := 1135680567968666674103441

theorem tailTrace_6635190 : CollatzResearch.WordTrace tailWord_6635190 prefixEnd_6635190 1135680567968666674103441 := by
  unfold tailWord_6635190
  simp only [CollatzResearch.WordTrace]
  refine ⟨15125328801990456567401939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161336840554564870052287349 15125328801990456567401939)
  ·
    refine ⟨22687993202985684851102909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15125328801990456567401939 22687993202985684851102909)
    ·
      refine ⟨8507997451119631819163591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22687993202985684851102909 8507997451119631819163591)
      ·
        refine ⟨12761996176679447728745387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8507997451119631819163591 12761996176679447728745387)
        ·
          refine ⟨19142994265019171593118081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12761996176679447728745387 19142994265019171593118081)
          ·
            refine ⟨14357245698764378694838561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19142994265019171593118081 14357245698764378694838561)
            ·
              refine ⟨10767934274073284021128921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14357245698764378694838561 10767934274073284021128921)
              ·
                refine ⟨8075950705554963015846691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10767934274073284021128921 8075950705554963015846691)
                ·
                  refine ⟨12113926058332444523770037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8075950705554963015846691 12113926058332444523770037)
                  ·
                    refine ⟨1135680567968666674103441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12113926058332444523770037 1135680567968666674103441)
                    ·
                      rfl

theorem cell23_6635190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_6635190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635190 prefixEnd_6635190 := by exact prefixLift 6635190
  have htrace : WordTrace (prefixWord ++ tailWord_6635190) baseStart_6635190 baseEnd_6635190 := by
    simpa [prefixWord, tailWord_6635190, baseEnd_6635190] using wordTrace_append hprefix tailTrace_6635190
  have hstable : (prefixWord ++ tailWord_6635190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635190).length < 2 ^ (prefixWord ++ tailWord_6635190).sum := by decide
  have hdescent : baseEnd_6635190 < baseStart_6635190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635193 : List Nat := [1, 2, 1, 4, 1, 1, 4, 2, 3, 2, 2]
def baseStart_6635193 : Nat := 118140960795 + 6635193 * 2 ^ 59
def prefixEnd_6635193 : Nat := 4983230072969 + 3 ^ 40 * 6635193 * 2
def baseEnd_6635193 : Nat := 3407043244347963510572809

theorem tailTrace_6635193 : CollatzResearch.WordTrace tailWord_6635193 prefixEnd_6635193 3407043244347963510572809 := by
  unfold tailWord_6635193
  simp only [CollatzResearch.WordTrace]
  refine ⟨242005370250836436590790233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161336913500557624393860155 242005370250836436590790233)
  ·
    refine ⟨181504027688127327443092675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242005370250836436590790233 181504027688127327443092675)
    ·
      refine ⟨272256041532190991164639013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181504027688127327443092675 272256041532190991164639013)
      ·
        refine ⟨51048007787285810843369815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272256041532190991164639013 51048007787285810843369815)
        ·
          refine ⟨76572011680928716265054723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51048007787285810843369815 76572011680928716265054723)
          ·
            refine ⟨114858017521393074397582085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76572011680928716265054723 114858017521393074397582085)
            ·
              refine ⟨21535878285261201449546641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114858017521393074397582085 21535878285261201449546641)
              ·
                refine ⟨16151908713945901087159981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21535878285261201449546641 16151908713945901087159981)
                ·
                  refine ⟨6056965767729712907684993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16151908713945901087159981 6056965767729712907684993)
                  ·
                    refine ⟨4542724325797284680763745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6056965767729712907684993 4542724325797284680763745)
                    ·
                      refine ⟨3407043244347963510572809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4542724325797284680763745 3407043244347963510572809)
                      ·
                        rfl

theorem cell23_6635193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_6635193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635193 prefixEnd_6635193 := by exact prefixLift 6635193
  have htrace : WordTrace (prefixWord ++ tailWord_6635193) baseStart_6635193 baseEnd_6635193 := by
    simpa [prefixWord, tailWord_6635193, baseEnd_6635193] using wordTrace_append hprefix tailTrace_6635193
  have hstable : (prefixWord ++ tailWord_6635193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635193).length < 2 ^ (prefixWord ++ tailWord_6635193).sum := by decide
  have hdescent : baseEnd_6635193 < baseStart_6635193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635213 : List Nat := [1, 6, 2, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_6635213 : Nat := 118140960795 + 6635213 * 2 ^ 59
def prefixEnd_6635213 : Nat := 4983230072969 + 3 ^ 40 * 6635213 * 2
def baseEnd_6635213 : Nat := 3407053513961053432322717

theorem tailTrace_6635213 : CollatzResearch.WordTrace tailWord_6635213 prefixEnd_6635213 3407053513961053432322717 := by
  unfold tailWord_6635213
  simp only [CollatzResearch.WordTrace]
  refine ⟨242006099710763980006518293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161337399807175986671012195 242006099710763980006518293)
  ·
    refine ⟨11344035923942061562805545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 242006099710763980006518293 11344035923942061562805545)
    ·
      refine ⟨8508026942956546172104159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11344035923942061562805545 8508026942956546172104159)
      ·
        refine ⟨12762040414434819258156239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8508026942956546172104159 12762040414434819258156239)
        ·
          refine ⟨19143060621652228887234359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12762040414434819258156239 19143060621652228887234359)
          ·
            refine ⟨28714590932478343330851539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19143060621652228887234359 28714590932478343330851539)
            ·
              refine ⟨43071886398717514996277309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28714590932478343330851539 43071886398717514996277309)
              ·
                refine ⟨16151957399519068123603991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43071886398717514996277309 16151957399519068123603991)
                ·
                  refine ⟨24227936099278602185405987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16151957399519068123603991 24227936099278602185405987)
                  ·
                    refine ⟨36341904148917903278108981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24227936099278602185405987 36341904148917903278108981)
                    ·
                      refine ⟨3407053513961053432322717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36341904148917903278108981 3407053513961053432322717)
                      ·
                        rfl

theorem cell23_6635213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_6635213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635213 prefixEnd_6635213 := by exact prefixLift 6635213
  have htrace : WordTrace (prefixWord ++ tailWord_6635213) baseStart_6635213 baseEnd_6635213 := by
    simpa [prefixWord, tailWord_6635213, baseEnd_6635213] using wordTrace_append hprefix tailTrace_6635213
  have hstable : (prefixWord ++ tailWord_6635213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635213).length < 2 ^ (prefixWord ++ tailWord_6635213).sum := by decide
  have hdescent : baseEnd_6635213 < baseStart_6635213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635296 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 4]
def baseStart_6635296 : Nat := 118140960795 + 6635296 * 2 ^ 59
def prefixEnd_6635296 : Nat := 4983230072969 + 3 ^ 40 * 6635296 * 2
def baseEnd_6635296 : Nat := 3407096132855376607584835

theorem tailTrace_6635296 : CollatzResearch.WordTrace tailWord_6635296 prefixEnd_6635296 3407096132855376607584835 := by
  unfold tailWord_6635296
  simp only [CollatzResearch.WordTrace]
  refine ⟨121004563484731642590894871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161339417979642190121193161 121004563484731642590894871)
  ·
    refine ⟨181506845227097463886342307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121004563484731642590894871 181506845227097463886342307)
    ·
      refine ⟨272260267840646195829513461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181506845227097463886342307 272260267840646195829513461)
      ·
        refine ⟨25524400110060580859016887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 272260267840646195829513461 25524400110060580859016887)
        ·
          refine ⟨38286600165090871288525331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25524400110060580859016887 38286600165090871288525331)
          ·
            refine ⟨57429900247636306932787997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38286600165090871288525331 57429900247636306932787997)
            ·
              refine ⟨21536212592863615099795499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57429900247636306932787997 21536212592863615099795499)
              ·
                refine ⟨32304318889295422649693249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21536212592863615099795499 32304318889295422649693249)
                ·
                  refine ⟨24228239166971566987269937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32304318889295422649693249 24228239166971566987269937)
                  ·
                    refine ⟨18171179375228675240452453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24228239166971566987269937 18171179375228675240452453)
                    ·
                      refine ⟨3407096132855376607584835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18171179375228675240452453 3407096132855376607584835)
                      ·
                        rfl

theorem cell23_6635296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_6635296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635296 prefixEnd_6635296 := by exact prefixLift 6635296
  have htrace : WordTrace (prefixWord ++ tailWord_6635296) baseStart_6635296 baseEnd_6635296 := by
    simpa [prefixWord, tailWord_6635296, baseEnd_6635296] using wordTrace_append hprefix tailTrace_6635296
  have hstable : (prefixWord ++ tailWord_6635296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635296).length < 2 ^ (prefixWord ++ tailWord_6635296).sum := by decide
  have hdescent : baseEnd_6635296 < baseStart_6635296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635300 : List Nat := [2, 3, 1, 3, 2, 2, 2, 1, 1, 4, 2]
def baseStart_6635300 : Nat := 118140960795 + 6635300 * 2 ^ 59
def prefixEnd_6635300 : Nat := 4983230072969 + 3 ^ 40 * 6635300 * 2
def baseEnd_6635300 : Nat := 3407098186777994591934817

theorem tailTrace_6635300 : CollatzResearch.WordTrace tailWord_6635300 prefixEnd_6635300 3407098186777994591934817 := by
  unfold tailWord_6635300
  simp only [CollatzResearch.WordTrace]
  refine ⟨121004636430724396932467677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161339515240965862576623569 121004636430724396932467677)
  ·
    refine ⟨45376738661521648849675379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121004636430724396932467677 45376738661521648849675379)
    ·
      refine ⟨68065107992282473274513069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45376738661521648849675379 68065107992282473274513069)
      ·
        refine ⟨25524415497105927477942401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68065107992282473274513069 25524415497105927477942401)
        ·
          refine ⟨19143311622829445608456801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25524415497105927477942401 19143311622829445608456801)
          ·
            refine ⟨14357483717122084206342601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19143311622829445608456801 14357483717122084206342601)
            ·
              refine ⟨10768112787841563154756951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14357483717122084206342601 10768112787841563154756951)
              ·
                refine ⟨16152169181762344732135427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10768112787841563154756951 16152169181762344732135427)
                ·
                  refine ⟨24228253772643517098203141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16152169181762344732135427 24228253772643517098203141)
                  ·
                    refine ⟨4542797582370659455913089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24228253772643517098203141 4542797582370659455913089)
                    ·
                      refine ⟨3407098186777994591934817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4542797582370659455913089 3407098186777994591934817)
                      ·
                        rfl

theorem cell23_6635300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_6635300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635300 prefixEnd_6635300 := by exact prefixLift 6635300
  have htrace : WordTrace (prefixWord ++ tailWord_6635300) baseStart_6635300 baseEnd_6635300 := by
    simpa [prefixWord, tailWord_6635300, baseEnd_6635300] using wordTrace_append hprefix tailTrace_6635300
  have hstable : (prefixWord ++ tailWord_6635300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635300).length < 2 ^ (prefixWord ++ tailWord_6635300).sum := by decide
  have hdescent : baseEnd_6635300 < baseStart_6635300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635321 : List Nat := [1, 2, 1, 7, 2, 1, 2, 1, 1, 3, 2]
def baseStart_6635321 : Nat := 118140960795 + 6635321 * 2 ^ 59
def prefixEnd_6635321 : Nat := 4983230072969 + 3 ^ 40 * 6635321 * 2
def baseEnd_6635321 : Nat := 3407108969871739009772221

theorem tailTrace_6635321 : CollatzResearch.WordTrace tailWord_6635321 prefixEnd_6635321 3407108969871739009772221 := by
  unfold tailWord_6635321
  simp only [CollatzResearch.WordTrace]
  refine ⟨242010038794372714451449817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161340025862915142967633211 242010038794372714451449817)
  ·
    refine ⟨181507529095779535838587363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242010038794372714451449817 181507529095779535838587363)
    ·
      refine ⟨272261293643669303757881045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181507529095779535838587363 272261293643669303757881045)
      ·
        refine ⟨6381124069773499306825337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 272261293643669303757881045 6381124069773499306825337)
        ·
          refine ⟨4785843052330124480119003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6381124069773499306825337 4785843052330124480119003)
          ·
            refine ⟨7178764578495186720178505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4785843052330124480119003 7178764578495186720178505)
            ·
              refine ⟨5384073433871390040133879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7178764578495186720178505 5384073433871390040133879)
              ·
                refine ⟨8076110150807085060200819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5384073433871390040133879 8076110150807085060200819)
                ·
                  refine ⟨12114165226210627590301229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8076110150807085060200819 12114165226210627590301229)
                  ·
                    refine ⟨4542811959828985346362961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12114165226210627590301229 4542811959828985346362961)
                    ·
                      refine ⟨3407108969871739009772221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4542811959828985346362961 3407108969871739009772221)
                      ·
                        rfl

theorem cell23_6635321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_6635321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635321 prefixEnd_6635321 := by exact prefixLift 6635321
  have htrace : WordTrace (prefixWord ++ tailWord_6635321) baseStart_6635321 baseEnd_6635321 := by
    simpa [prefixWord, tailWord_6635321, baseEnd_6635321] using wordTrace_append hprefix tailTrace_6635321
  have hstable : (prefixWord ++ tailWord_6635321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635321).length < 2 ^ (prefixWord ++ tailWord_6635321).sum := by decide
  have hdescent : baseEnd_6635321 < baseStart_6635321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635334 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2]
def baseStart_6635334 : Nat := 118140960795 + 6635334 * 2 ^ 59
def prefixEnd_6635334 : Nat := 4983230072969 + 3 ^ 40 * 6635334 * 2
def baseEnd_6635334 : Nat := 3407115645120247458909661

theorem tailTrace_6635334 : CollatzResearch.WordTrace tailWord_6635334 prefixEnd_6635334 3407115645120247458909661 := by
  unfold tailWord_6635334
  simp only [CollatzResearch.WordTrace]
  refine ⟨7562828529478925552239783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 161340341962217078447782037 7562828529478925552239783)
  ·
    refine ⟨11344242794218388328359675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7562828529478925552239783 11344242794218388328359675)
    ·
      refine ⟨17016364191327582492539513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11344242794218388328359675 17016364191327582492539513)
      ·
        refine ⟨12762273143495686869404635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17016364191327582492539513 12762273143495686869404635)
        ·
          refine ⟨19143409715243530304106953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12762273143495686869404635 19143409715243530304106953)
          ·
            refine ⟨14357557286432647728080215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19143409715243530304106953 14357557286432647728080215)
            ·
              refine ⟨21536335929648971592120323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14357557286432647728080215 21536335929648971592120323)
              ·
                refine ⟨32304503894473457388180485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21536335929648971592120323 32304503894473457388180485)
                ·
                  refine ⟨6057094480213773260283841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32304503894473457388180485 6057094480213773260283841)
                  ·
                    refine ⟨4542820860160329945212881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6057094480213773260283841 4542820860160329945212881)
                    ·
                      refine ⟨3407115645120247458909661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4542820860160329945212881 3407115645120247458909661)
                      ·
                        rfl

theorem cell23_6635334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_6635334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635334 prefixEnd_6635334 := by exact prefixLift 6635334
  have htrace : WordTrace (prefixWord ++ tailWord_6635334) baseStart_6635334 baseEnd_6635334 := by
    simpa [prefixWord, tailWord_6635334, baseEnd_6635334] using wordTrace_append hprefix tailTrace_6635334
  have hstable : (prefixWord ++ tailWord_6635334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635334).length < 2 ^ (prefixWord ++ tailWord_6635334).sum := by decide
  have hdescent : baseEnd_6635334 < baseStart_6635334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635373 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 1, 6, 2]
def baseStart_6635373 : Nat := 118140960795 + 6635373 * 2 ^ 59
def prefixEnd_6635373 : Nat := 4983230072969 + 3 ^ 40 * 6635373 * 2
def baseEnd_6635373 : Nat := 3407135670865772806321981

theorem tailTrace_6635373 : CollatzResearch.WordTrace tailWord_6635373 prefixEnd_6635373 3407135670865772806321981 := by
  unfold tailWord_6635373
  simp only [CollatzResearch.WordTrace]
  refine ⟨242011935390184327332342773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161341290260122884888228515 242011935390184327332342773)
  ·
    refine ⟨22688618942829780687407135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242011935390184327332342773 22688618942829780687407135)
    ·
      refine ⟨34032928414244671031110703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22688618942829780687407135 34032928414244671031110703)
      ·
        refine ⟨51049392621367006546666055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34032928414244671031110703 51049392621367006546666055)
        ·
          refine ⟨76574088932050509819999083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51049392621367006546666055 76574088932050509819999083)
          ·
            refine ⟨114861133398075764729998625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76574088932050509819999083 114861133398075764729998625)
            ·
              refine ⟨86145850048556823547498969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114861133398075764729998625 86145850048556823547498969)
              ·
                refine ⟨64609387536417617660624227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86145850048556823547498969 64609387536417617660624227)
                ·
                  refine ⟨96914081304626426490936341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64609387536417617660624227 96914081304626426490936341)
                  ·
                    refine ⟨4542847561154363741762641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 96914081304626426490936341 4542847561154363741762641)
                    ·
                      refine ⟨3407135670865772806321981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4542847561154363741762641 3407135670865772806321981)
                      ·
                        rfl

theorem cell23_6635373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_6635373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635373 prefixEnd_6635373 := by exact prefixLift 6635373
  have htrace : WordTrace (prefixWord ++ tailWord_6635373) baseStart_6635373 baseEnd_6635373 := by
    simpa [prefixWord, tailWord_6635373, baseEnd_6635373] using wordTrace_append hprefix tailTrace_6635373
  have hstable : (prefixWord ++ tailWord_6635373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635373).length < 2 ^ (prefixWord ++ tailWord_6635373).sum := by decide
  have hdescent : baseEnd_6635373 < baseStart_6635373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635390 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_6635390 : Nat := 118140960795 + 6635390 * 2 ^ 59
def prefixEnd_6635390 : Nat := 4983230072969 + 3 ^ 40 * 6635390 * 2
def baseEnd_6635390 : Nat := 3407144400036899239809403

theorem tailTrace_6635390 : CollatzResearch.WordTrace tailWord_6635390 prefixEnd_6635390 3407144400036899239809403 := by
  unfold tailWord_6635390
  simp only [CollatzResearch.WordTrace]
  refine ⟨30251569428890342404463953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161341703620748492823807749 30251569428890342404463953)
  ·
    refine ⟨22688677071667756803347965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30251569428890342404463953 22688677071667756803347965)
    ·
      refine ⟨8508253901875408801255487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22688677071667756803347965 8508253901875408801255487)
      ·
        refine ⟨12762380852813113201883231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8508253901875408801255487 12762380852813113201883231)
        ·
          refine ⟨19143571279219669802824847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12762380852813113201883231 19143571279219669802824847)
          ·
            refine ⟨28715356918829504704237271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19143571279219669802824847 28715356918829504704237271)
            ·
              refine ⟨43073035378244257056355907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28715356918829504704237271 43073035378244257056355907)
              ·
                refine ⟨64609553067366385584533861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43073035378244257056355907 64609553067366385584533861)
                ·
                  refine ⟨12114291200131197297100099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64609553067366385584533861 12114291200131197297100099)
                  ·
                    refine ⟨18171436800196795945650149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12114291200131197297100099 18171436800196795945650149)
                    ·
                      refine ⟨3407144400036899239809403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18171436800196795945650149 3407144400036899239809403)
                      ·
                        rfl

theorem cell23_6635390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_6635390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635390 prefixEnd_6635390 := by exact prefixLift 6635390
  have htrace : WordTrace (prefixWord ++ tailWord_6635390) baseStart_6635390 baseEnd_6635390 := by
    simpa [prefixWord, tailWord_6635390, baseEnd_6635390] using wordTrace_append hprefix tailTrace_6635390
  have hstable : (prefixWord ++ tailWord_6635390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635390).length < 2 ^ (prefixWord ++ tailWord_6635390).sum := by decide
  have hdescent : baseEnd_6635390 < baseStart_6635390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635396 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 8]
def baseStart_6635396 : Nat := 118140960795 + 6635396 * 2 ^ 59
def prefixEnd_6635396 : Nat := 4983230072969 + 3 ^ 40 * 6635396 * 2
def baseEnd_6635396 : Nat := 378571942324536246259375

theorem tailTrace_6635396 : CollatzResearch.WordTrace tailWord_6635396 prefixEnd_6635396 378571942324536246259375 := by
  unfold tailWord_6635396
  simp only [CollatzResearch.WordTrace]
  refine ⟨121006387134550501130215021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161341849512734001506953361 121006387134550501130215021)
  ·
    refine ⟨45377395175456437923830633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121006387134550501130215021 45377395175456437923830633)
    ·
      refine ⟨34033046381592328442872975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45377395175456437923830633 34033046381592328442872975)
      ·
        refine ⟨51049569572388492664309463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34033046381592328442872975 51049569572388492664309463)
        ·
          refine ⟨76574354358582738996464195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51049569572388492664309463 76574354358582738996464195)
          ·
            refine ⟨114861531537874108494696293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76574354358582738996464195 114861531537874108494696293)
            ·
              refine ⟨21536537163351395342755555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114861531537874108494696293 21536537163351395342755555)
              ·
                refine ⟨32304805745027093014133333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21536537163351395342755555 32304805745027093014133333)
                ·
                  refine ⟨378571942324536246259375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32304805745027093014133333 378571942324536246259375)
                  ·
                    rfl

theorem cell23_6635396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_6635396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635396 prefixEnd_6635396 := by exact prefixLift 6635396
  have htrace : WordTrace (prefixWord ++ tailWord_6635396) baseStart_6635396 baseEnd_6635396 := by
    simpa [prefixWord, tailWord_6635396, baseEnd_6635396] using wordTrace_append hprefix tailTrace_6635396
  have hstable : (prefixWord ++ tailWord_6635396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635396).length < 2 ^ (prefixWord ++ tailWord_6635396).sum := by decide
  have hdescent : baseEnd_6635396 < baseStart_6635396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635456 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 3, 6]
def baseStart_6635456 : Nat := 118140960795 + 6635456 * 2 ^ 59
def prefixEnd_6635456 : Nat := 4983230072969 + 3 ^ 40 * 6635456 * 2
def baseEnd_6635456 : Nat := 1135726096586698660528033

theorem tailTrace_6635456 : CollatzResearch.WordTrace tailWord_6635456 prefixEnd_6635456 1135726096586698660528033 := by
  unfold tailWord_6635456
  simp only [CollatzResearch.WordTrace]
  refine ⟨121007481324441816253807111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161343308432589088338409481 121007481324441816253807111)
  ·
    refine ⟨181511221986662724380710667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121007481324441816253807111 181511221986662724380710667)
    ·
      refine ⟨272266832979994086571066001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181511221986662724380710667 272266832979994086571066001)
      ·
        refine ⟨204200124734995564928299501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272266832979994086571066001 204200124734995564928299501)
        ·
          refine ⟨76575046775623336848112313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204200124734995564928299501 76575046775623336848112313)
          ·
            refine ⟨57431285081717502636084235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76575046775623336848112313 57431285081717502636084235)
            ·
              refine ⟨86146927622576253954126353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57431285081717502636084235 86146927622576253954126353)
              ·
                refine ⟨64610195716932190465594765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86146927622576253954126353 64610195716932190465594765)
                ·
                  refine ⟨24228823393849571424598037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64610195716932190465594765 24228823393849571424598037)
                  ·
                    refine ⟨1135726096586698660528033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24228823393849571424598037 1135726096586698660528033)
                    ·
                      rfl

theorem cell23_6635456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 3, 6].length) (baseStart_6635456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635456 prefixEnd_6635456 := by exact prefixLift 6635456
  have htrace : WordTrace (prefixWord ++ tailWord_6635456) baseStart_6635456 baseEnd_6635456 := by
    simpa [prefixWord, tailWord_6635456, baseEnd_6635456] using wordTrace_append hprefix tailTrace_6635456
  have hstable : (prefixWord ++ tailWord_6635456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635456).length < 2 ^ (prefixWord ++ tailWord_6635456).sum := by decide
  have hdescent : baseEnd_6635456 < baseStart_6635456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635463 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 2, 6, 2]
def baseStart_6635463 : Nat := 118140960795 + 6635463 * 2 ^ 59
def prefixEnd_6635463 : Nat := 4983230072969 + 3 ^ 40 * 6635463 * 2
def baseEnd_6635463 : Nat := 3407181884124677454196567

theorem tailTrace_6635463 : CollatzResearch.WordTrace tailWord_6635463 prefixEnd_6635463 3407181884124677454196567 := by
  unfold tailWord_6635463
  simp only [CollatzResearch.WordTrace]
  refine ⟨242015217959858272703119043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161343478639905515135412695 242015217959858272703119043)
  ·
    refine ⟨363022826939787409054678565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242015217959858272703119043 363022826939787409054678565)
    ·
      refine ⟨68066780051210139197752231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 363022826939787409054678565 68066780051210139197752231)
      ·
        refine ⟨102100170076815208796628347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68066780051210139197752231 102100170076815208796628347)
        ·
          refine ⟨153150255115222813194942521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102100170076815208796628347 153150255115222813194942521)
          ·
            refine ⟨114862691336417109896206891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153150255115222813194942521 114862691336417109896206891)
            ·
              refine ⟨172294037004625664844310337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114862691336417109896206891 172294037004625664844310337)
              ·
                refine ⟨129220527753469248633232753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172294037004625664844310337 129220527753469248633232753)
                ·
                  refine ⟨96915395815101936474924565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129220527753469248633232753 96915395815101936474924565)
                  ·
                    refine ⟨4542909178832903272262089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 96915395815101936474924565 4542909178832903272262089)
                    ·
                      refine ⟨3407181884124677454196567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4542909178832903272262089 3407181884124677454196567)
                      ·
                        rfl

theorem cell23_6635463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 6, 2].length) (baseStart_6635463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635463 prefixEnd_6635463 := by exact prefixLift 6635463
  have htrace : WordTrace (prefixWord ++ tailWord_6635463) baseStart_6635463 baseEnd_6635463 := by
    simpa [prefixWord, tailWord_6635463, baseEnd_6635463] using wordTrace_append hprefix tailTrace_6635463
  have hstable : (prefixWord ++ tailWord_6635463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635463).length < 2 ^ (prefixWord ++ tailWord_6635463).sum := by decide
  have hdescent : baseEnd_6635463 < baseStart_6635463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635524 : List Nat := [2, 3, 2, 4, 2, 1, 1, 1, 1, 6]
def baseStart_6635524 : Nat := 118140960795 + 6635524 * 2 ^ 59
def prefixEnd_6635524 : Nat := 4983230072969 + 3 ^ 40 * 6635524 * 2
def baseEnd_6635524 : Nat := 1135737735481533905177929

theorem tailTrace_6635524 : CollatzResearch.WordTrace tailWord_6635524 prefixEnd_6635524 1135737735481533905177929 := by
  unfold tailWord_6635524
  simp only [CollatzResearch.WordTrace]
  refine ⟨121008721406318640060544813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161344961875091520080726417 121008721406318640060544813)
  ·
    refine ⟨45378270527369490022704305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121008721406318640060544813 45378270527369490022704305)
    ·
      refine ⟨34033702895527117517028229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45378270527369490022704305 34033702895527117517028229)
      ·
        refine ⟨6381319292911334534442793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34033702895527117517028229 6381319292911334534442793)
        ·
          refine ⟨4785989469683500900832095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6381319292911334534442793 4785989469683500900832095)
          ·
            refine ⟨7178984204525251351248143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4785989469683500900832095 7178984204525251351248143)
            ·
              refine ⟨10768476306787877026872215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7178984204525251351248143 10768476306787877026872215)
              ·
                refine ⟨16152714460181815540308323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10768476306787877026872215 16152714460181815540308323)
                ·
                  refine ⟨24229071690272723310462485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16152714460181815540308323 24229071690272723310462485)
                  ·
                    refine ⟨1135737735481533905177929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24229071690272723310462485 1135737735481533905177929)
                    ·
                      rfl

theorem cell23_6635524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_6635524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635524 prefixEnd_6635524 := by exact prefixLift 6635524
  have htrace : WordTrace (prefixWord ++ tailWord_6635524) baseStart_6635524 baseEnd_6635524 := by
    simpa [prefixWord, tailWord_6635524, baseEnd_6635524] using wordTrace_append hprefix tailTrace_6635524
  have hstable : (prefixWord ++ tailWord_6635524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635524).length < 2 ^ (prefixWord ++ tailWord_6635524).sum := by decide
  have hdescent : baseEnd_6635524 < baseStart_6635524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635557 : List Nat := [1, 3, 1, 2, 2, 3, 2, 3, 1, 3, 2]
def baseStart_6635557 : Nat := 118140960795 + 6635557 * 2 ^ 59
def prefixEnd_6635557 : Nat := 4983230072969 + 3 ^ 40 * 6635557 * 2
def baseEnd_6635557 : Nat := 3407230151306200086421135

theorem tailTrace_6635557 : CollatzResearch.WordTrace tailWord_6635557 prefixEnd_6635557 3407230151306200086421135 := by
  unfold tailWord_6635557
  simp only [CollatzResearch.WordTrace]
  refine ⟨242018646421517726757040925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161345764281011817838027283 242018646421517726757040925)
  ·
    refine ⟨90756992408069147533890347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242018646421517726757040925 90756992408069147533890347)
    ·
      refine ⟨136135488612103721300835521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90756992408069147533890347 136135488612103721300835521)
      ·
        refine ⟨102101616459077790975626641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136135488612103721300835521 102101616459077790975626641)
        ·
          refine ⟨76576212344308343231719981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102101616459077790975626641 76576212344308343231719981)
          ·
            refine ⟨28716079629115628711894993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76576212344308343231719981 28716079629115628711894993)
            ·
              refine ⟨21537059721836721533921245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28716079629115628711894993 21537059721836721533921245)
              ·
                refine ⟨8076397395688770575220467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21537059721836721533921245 8076397395688770575220467)
                ·
                  refine ⟨12114596093533155862830701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8076397395688770575220467 12114596093533155862830701)
                  ·
                    refine ⟨4542973535074933448561513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12114596093533155862830701 4542973535074933448561513)
                    ·
                      refine ⟨3407230151306200086421135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4542973535074933448561513 3407230151306200086421135)
                      ·
                        rfl

theorem cell23_6635557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 3, 2].length) (baseStart_6635557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635557 prefixEnd_6635557 := by exact prefixLift 6635557
  have htrace : WordTrace (prefixWord ++ tailWord_6635557) baseStart_6635557 baseEnd_6635557 := by
    simpa [prefixWord, tailWord_6635557, baseEnd_6635557] using wordTrace_append hprefix tailTrace_6635557
  have hstable : (prefixWord ++ tailWord_6635557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635557).length < 2 ^ (prefixWord ++ tailWord_6635557).sum := by decide
  have hdescent : baseEnd_6635557 < baseStart_6635557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635583 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 4]
def baseStart_6635583 : Nat := 118140960795 + 6635583 * 2 ^ 59
def prefixEnd_6635583 : Nat := 4983230072969 + 3 ^ 40 * 6635583 * 2
def baseEnd_6635583 : Nat := 3407243501803216984696015

theorem tailTrace_6635583 : CollatzResearch.WordTrace tailWord_6635583 prefixEnd_6635583 3407243501803216984696015 := by
  unfold tailWord_6635583
  simp only [CollatzResearch.WordTrace]
  refine ⟨242019594719423533197487403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161346396479615688798324935 242019594719423533197487403)
  ·
    refine ⟨363029392079135299796231105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242019594719423533197487403 363029392079135299796231105)
    ·
      refine ⟨272272044059351474847173329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363029392079135299796231105 272272044059351474847173329)
      ·
        refine ⟨204204033044513606135379997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272272044059351474847173329 204204033044513606135379997)
        ·
          refine ⟨76576512391692602300767499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204204033044513606135379997 76576512391692602300767499)
          ·
            refine ⟨114864768587538903451151249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76576512391692602300767499 114864768587538903451151249)
            ·
              refine ⟨86148576440654177588363437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114864768587538903451151249 86148576440654177588363437)
              ·
                refine ⟨32305716165245316595636289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86148576440654177588363437 32305716165245316595636289)
                ·
                  refine ⟨24229287123933987446727217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32305716165245316595636289 24229287123933987446727217)
                  ·
                    refine ⟨18171965342950490585045413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24229287123933987446727217 18171965342950490585045413)
                    ·
                      refine ⟨3407243501803216984696015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18171965342950490585045413 3407243501803216984696015)
                      ·
                        rfl

theorem cell23_6635583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_6635583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635583 prefixEnd_6635583 := by exact prefixLift 6635583
  have htrace : WordTrace (prefixWord ++ tailWord_6635583) baseStart_6635583 baseEnd_6635583 := by
    simpa [prefixWord, tailWord_6635583, baseEnd_6635583] using wordTrace_append hprefix tailTrace_6635583
  have hstable : (prefixWord ++ tailWord_6635583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635583).length < 2 ^ (prefixWord ++ tailWord_6635583).sum := by decide
  have hdescent : baseEnd_6635583 < baseStart_6635583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635610 : List Nat := [3, 1, 1, 2, 1, 1, 4, 5, 5]
def baseStart_6635610 : Nat := 118140960795 + 6635610 * 2 ^ 59
def prefixEnd_6635610 : Nat := 4983230072969 + 3 ^ 40 * 6635610 * 2
def baseEnd_6635610 : Nat := 378584151753432042117599

theorem tailTrace_6635610 : CollatzResearch.WordTrace tailWord_6635610 prefixEnd_6635610 378584151753432042117599 := by
  unfold tailWord_6635610
  simp only [CollatzResearch.WordTrace]
  refine ⟨60505144872581429202180071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161347052993550477872480189 60505144872581429202180071)
  ·
    refine ⟨90757717308872143803270107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60505144872581429202180071 90757717308872143803270107)
    ·
      refine ⟨136136575963308215704905161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90757717308872143803270107 136136575963308215704905161)
      ·
        refine ⟨102102431972481161778678871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136136575963308215704905161 102102431972481161778678871)
        ·
          refine ⟨153153647958721742668018307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102102431972481161778678871 153153647958721742668018307)
          ·
            refine ⟨229730471938082614002027461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153153647958721742668018307 229730471938082614002027461)
            ·
              refine ⟨43074463488390490125380149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229730471938082614002027461 43074463488390490125380149)
              ·
                refine ⟨4038230952036608449254389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43074463488390490125380149 4038230952036608449254389)
                ·
                  refine ⟨378584151753432042117599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4038230952036608449254389 378584151753432042117599)
                  ·
                    rfl

theorem cell23_6635610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 5].length) (baseStart_6635610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635610 prefixEnd_6635610 := by exact prefixLift 6635610
  have htrace : WordTrace (prefixWord ++ tailWord_6635610) baseStart_6635610 baseEnd_6635610 := by
    simpa [prefixWord, tailWord_6635610, baseEnd_6635610] using wordTrace_append hprefix tailTrace_6635610
  have hstable : (prefixWord ++ tailWord_6635610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635610).length < 2 ^ (prefixWord ++ tailWord_6635610).sum := by decide
  have hdescent : baseEnd_6635610 < baseStart_6635610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635633 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 1, 2, 5]
def baseStart_6635633 : Nat := 118140960795 + 6635633 * 2 ^ 59
def prefixEnd_6635633 : Nat := 4983230072969 + 3 ^ 40 * 6635633 * 2
def baseEnd_6635633 : Nat := 3407269175835941789070785

theorem tailTrace_6635633 : CollatzResearch.WordTrace tailWord_6635633 prefixEnd_6635633 3407269175835941789070785 := by
  unfold tailWord_6635633
  simp only [CollatzResearch.WordTrace]
  refine ⟨242021418369242391736807553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161347612246161594491205035 242021418369242391736807553)
  ·
    refine ⟨181516063776931793802605665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242021418369242391736807553 181516063776931793802605665)
    ·
      refine ⟨136137047832698845351954249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181516063776931793802605665 136137047832698845351954249)
      ·
        refine ⟨102102785874524134013965687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136137047832698845351954249 102102785874524134013965687)
        ·
          refine ⟨153154178811786201020948531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102102785874524134013965687 153154178811786201020948531)
          ·
            refine ⟨229731268217679301531422797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153154178811786201020948531 229731268217679301531422797)
            ·
              refine ⟨86149225581629738074283549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229731268217679301531422797 86149225581629738074283549)
              ·
                refine ⟨32305959593111151777856331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86149225581629738074283549 32305959593111151777856331)
                ·
                  refine ⟨48458939389666727666784497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32305959593111151777856331 48458939389666727666784497)
                  ·
                    refine ⟨36344204542250045750088373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48458939389666727666784497 36344204542250045750088373)
                    ·
                      refine ⟨3407269175835941789070785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36344204542250045750088373 3407269175835941789070785)
                      ·
                        rfl

theorem cell23_6635633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_6635633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635633 prefixEnd_6635633 := by exact prefixLift 6635633
  have htrace : WordTrace (prefixWord ++ tailWord_6635633) baseStart_6635633 baseEnd_6635633 := by
    simpa [prefixWord, tailWord_6635633, baseEnd_6635633] using wordTrace_append hprefix tailTrace_6635633
  have hstable : (prefixWord ++ tailWord_6635633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635633).length < 2 ^ (prefixWord ++ tailWord_6635633).sum := by decide
  have hdescent : baseEnd_6635633 < baseStart_6635633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635673 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 1, 6, 4]
def baseStart_6635673 : Nat := 118140960795 + 6635673 * 2 ^ 59
def prefixEnd_6635673 : Nat := 4983230072969 + 3 ^ 40 * 6635673 * 2
def baseEnd_6635673 : Nat := 3407289715062121632570601

theorem tailTrace_6635673 : CollatzResearch.WordTrace tailWord_6635673 prefixEnd_6635673 3407289715062121632570601 := by
  unfold tailWord_6635673
  simp only [CollatzResearch.WordTrace]
  refine ⟨242022877289097478568263673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161348584859398319045509115 242022877289097478568263673)
  ·
    refine ⟨181517157966823108926197755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242022877289097478568263673 181517157966823108926197755)
    ·
      refine ⟨272275736950234663389296633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181517157966823108926197755 272275736950234663389296633)
      ·
        refine ⟨204206802712675997541972475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272275736950234663389296633 204206802712675997541972475)
        ·
          refine ⟨306310204069013996312958713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204206802712675997541972475 306310204069013996312958713)
          ·
            refine ⟨229732653051760497234719035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306310204069013996312958713 229732653051760497234719035)
            ·
              refine ⟨344598979577640745852078553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229732653051760497234719035 344598979577640745852078553)
              ·
                refine ⟨258449234683230559389058915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 344598979577640745852078553 258449234683230559389058915)
                ·
                  refine ⟨387673852024845839083588373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258449234683230559389058915 387673852024845839083588373)
                  ·
                    refine ⟨18172211813664648707043205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 387673852024845839083588373 18172211813664648707043205)
                    ·
                      refine ⟨3407289715062121632570601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18172211813664648707043205 3407289715062121632570601)
                      ·
                        rfl

theorem cell23_6635673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_6635673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635673 prefixEnd_6635673 := by exact prefixLift 6635673
  have htrace : WordTrace (prefixWord ++ tailWord_6635673) baseStart_6635673 baseEnd_6635673 := by
    simpa [prefixWord, tailWord_6635673, baseEnd_6635673] using wordTrace_append hprefix tailTrace_6635673
  have hstable : (prefixWord ++ tailWord_6635673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635673).length < 2 ^ (prefixWord ++ tailWord_6635673).sum := by decide
  have hdescent : baseEnd_6635673 < baseStart_6635673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635677 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 2, 4, 2]
def baseStart_6635677 : Nat := 118140960795 + 6635677 * 2 ^ 59
def prefixEnd_6635677 : Nat := 4983230072969 + 3 ^ 40 * 6635677 * 2
def baseEnd_6635677 : Nat := 3407291768984739616920583

theorem tailTrace_6635677 : CollatzResearch.WordTrace tailWord_6635677 prefixEnd_6635677 3407291768984739616920583 := by
  unfold tailWord_6635677
  simp only [CollatzResearch.WordTrace]
  refine ⟨242023023181082987251409285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161348682120721991500939523 242023023181082987251409285)
  ·
    refine ⟨45379316846453060109639241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242023023181082987251409285 45379316846453060109639241)
    ·
      refine ⟨34034487634839795082229431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45379316846453060109639241 34034487634839795082229431)
      ·
        refine ⟨51051731452259692623344147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34034487634839795082229431 51051731452259692623344147)
        ·
          refine ⟨76577597178389538935016221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51051731452259692623344147 76577597178389538935016221)
          ·
            refine ⟨28716598941896077100631083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76577597178389538935016221 28716598941896077100631083)
            ·
              refine ⟨43074898412844115650946625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28716598941896077100631083 43074898412844115650946625)
              ·
                refine ⟨32306173809633086738209969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43074898412844115650946625 32306173809633086738209969)
                ·
                  refine ⟨24229630357224815053657477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32306173809633086738209969 24229630357224815053657477)
                  ·
                    refine ⟨4543055691979652822560777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24229630357224815053657477 4543055691979652822560777)
                    ·
                      refine ⟨3407291768984739616920583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4543055691979652822560777 3407291768984739616920583)
                      ·
                        rfl

theorem cell23_6635677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_6635677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635677 prefixEnd_6635677 := by exact prefixLift 6635677
  have htrace : WordTrace (prefixWord ++ tailWord_6635677) baseStart_6635677 baseEnd_6635677 := by
    simpa [prefixWord, tailWord_6635677, baseEnd_6635677] using wordTrace_append hprefix tailTrace_6635677
  have hstable : (prefixWord ++ tailWord_6635677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635677).length < 2 ^ (prefixWord ++ tailWord_6635677).sum := by decide
  have hdescent : baseEnd_6635677 < baseStart_6635677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635737 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 4, 3, 2]
def baseStart_6635737 : Nat := 118140960795 + 6635737 * 2 ^ 59
def prefixEnd_6635737 : Nat := 4983230072969 + 3 ^ 40 * 6635737 * 2
def baseEnd_6635737 : Nat := 3407322577824009382170307

theorem tailTrace_6635737 : CollatzResearch.WordTrace tailWord_6635737 prefixEnd_6635737 3407322577824009382170307 := by
  unfold tailWord_6635737
  simp only [CollatzResearch.WordTrace]
  refine ⟨242025211560865617498593465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161350141040577078332395643 242025211560865617498593465)
  ·
    refine ⟨181518908670649213123945099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242025211560865617498593465 181518908670649213123945099)
    ·
      refine ⟨272278363005973819685917649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181518908670649213123945099 272278363005973819685917649)
      ·
        refine ⟨204208772254480364764438237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272278363005973819685917649 204208772254480364764438237)
        ·
          refine ⟨76578289595430136786664339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204208772254480364764438237 76578289595430136786664339)
          ·
            refine ⟨114867434393145205179996509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76578289595430136786664339 114867434393145205179996509)
            ·
              refine ⟨43075287897429451942498691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114867434393145205179996509 43075287897429451942498691)
              ·
                refine ⟨64612931846144177913748037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43075287897429451942498691 64612931846144177913748037)
                ·
                  refine ⟨12114924721152033358827757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64612931846144177913748037 12114924721152033358827757)
                  ·
                    refine ⟨4543096770432012509560409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12114924721152033358827757 4543096770432012509560409)
                    ·
                      refine ⟨3407322577824009382170307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4543096770432012509560409 3407322577824009382170307)
                      ·
                        rfl

theorem cell23_6635737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 3, 2].length) (baseStart_6635737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635737 prefixEnd_6635737 := by exact prefixLift 6635737
  have htrace : WordTrace (prefixWord ++ tailWord_6635737) baseStart_6635737 baseEnd_6635737 := by
    simpa [prefixWord, tailWord_6635737, baseEnd_6635737] using wordTrace_append hprefix tailTrace_6635737
  have hstable : (prefixWord ++ tailWord_6635737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635737).length < 2 ^ (prefixWord ++ tailWord_6635737).sum := by decide
  have hdescent : baseEnd_6635737 < baseStart_6635737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635807 : List Nat := [1, 1, 2, 4, 3, 3, 1, 8]
def baseStart_6635807 : Nat := 118140960795 + 6635807 * 2 ^ 59
def prefixEnd_6635807 : Nat := 4983230072969 + 3 ^ 40 * 6635807 * 2
def baseEnd_6635807 : Nat := 126198463758141633640555

theorem tailTrace_6635807 : CollatzResearch.WordTrace tailWord_6635807 prefixEnd_6635807 126198463758141633640555 := by
  unfold tailWord_6635807
  simp only [CollatzResearch.WordTrace]
  refine ⟨242027764670612019453641675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161351843113741346302427783 242027764670612019453641675)
  ·
    refine ⟨363041647005918029180462513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242027764670612019453641675 363041647005918029180462513)
    ·
      refine ⟨272281235254438521885346885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363041647005918029180462513 272281235254438521885346885)
      ·
        refine ⟨51052731610207222853502541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272281235254438521885346885 51052731610207222853502541)
        ·
          refine ⟨19144774353827708570063453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51052731610207222853502541 19144774353827708570063453)
          ·
            refine ⟨7179290382685390713773795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19144774353827708570063453 7179290382685390713773795)
            ·
              refine ⟨10768935574028086070660693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7179290382685390713773795 10768935574028086070660693)
              ·
                refine ⟨126198463758141633640555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10768935574028086070660693 126198463758141633640555)
                ·
                  rfl

theorem cell23_6635807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 8].length) (baseStart_6635807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635807 prefixEnd_6635807 := by exact prefixLift 6635807
  have htrace : WordTrace (prefixWord ++ tailWord_6635807) baseStart_6635807 baseEnd_6635807 := by
    simpa [prefixWord, tailWord_6635807, baseEnd_6635807] using wordTrace_append hprefix tailTrace_6635807
  have hstable : (prefixWord ++ tailWord_6635807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635807).length < 2 ^ (prefixWord ++ tailWord_6635807).sum := by decide
  have hdescent : baseEnd_6635807 < baseStart_6635807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635818 : List Nat := [3, 1, 4, 2, 2, 1, 1, 2, 3, 2, 2]
def baseStart_6635818 : Nat := 118140960795 + 6635818 * 2 ^ 59
def prefixEnd_6635818 : Nat := 4983230072969 + 3 ^ 40 * 6635818 * 2
def baseEnd_6635818 : Nat := 3407364169757023565257435

theorem tailTrace_6635818 : CollatzResearch.WordTrace tailWord_6635818 prefixEnd_6635818 3407364169757023565257435 := by
  unfold tailWord_6635818
  simp only [CollatzResearch.WordTrace]
  refine ⟨60507041468393042083073027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161352110582381445554861405 60507041468393042083073027)
  ·
    refine ⟨90760562202589563124609541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60507041468393042083073027 90760562202589563124609541)
    ·
      refine ⟨17017605412985543085864289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90760562202589563124609541 17017605412985543085864289)
      ·
        refine ⟨12763204059739157314398217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17017605412985543085864289 12763204059739157314398217)
        ·
          refine ⟨9572403044804367985798663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12763204059739157314398217 9572403044804367985798663)
          ·
            refine ⟨14358604567206551978697995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9572403044804367985798663 14358604567206551978697995)
            ·
              refine ⟨21537906850809827968046993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14358604567206551978697995 21537906850809827968046993)
              ·
                refine ⟨16153430138107370976035245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21537906850809827968046993 16153430138107370976035245)
                ·
                  refine ⟨6057536301790264116013217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16153430138107370976035245 6057536301790264116013217)
                  ·
                    refine ⟨4543152226342698087009913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6057536301790264116013217 4543152226342698087009913)
                    ·
                      refine ⟨3407364169757023565257435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4543152226342698087009913 3407364169757023565257435)
                      ·
                        rfl

theorem cell23_6635818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_6635818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635818 prefixEnd_6635818 := by exact prefixLift 6635818
  have htrace : WordTrace (prefixWord ++ tailWord_6635818) baseStart_6635818 baseEnd_6635818 := by
    simpa [prefixWord, tailWord_6635818, baseEnd_6635818] using wordTrace_append hprefix tailTrace_6635818
  have hstable : (prefixWord ++ tailWord_6635818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635818).length < 2 ^ (prefixWord ++ tailWord_6635818).sum := by decide
  have hdescent : baseEnd_6635818 < baseStart_6635818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635838 : List Nat := [4, 2, 1, 2, 1, 4, 2, 1, 1, 2, 3]
def baseStart_6635838 : Nat := 118140960795 + 6635838 * 2 ^ 59
def prefixEnd_6635838 : Nat := 4983230072969 + 3 ^ 40 * 6635838 * 2
def baseEnd_6635838 : Nat := 3407374439370113487007343

theorem tailTrace_6635838 : CollatzResearch.WordTrace tailWord_6635838 prefixEnd_6635838 3407374439370113487007343 := by
  unfold tailWord_6635838
  simp only [CollatzResearch.WordTrace]
  refine ⟨30253611916687463968502521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161352596888999807832013445 30253611916687463968502521)
  ·
    refine ⟨22690208937515597976376891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30253611916687463968502521 22690208937515597976376891)
    ·
      refine ⟨34035313406273396964565337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22690208937515597976376891 34035313406273396964565337)
      ·
        refine ⟨25526485054705047723424003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34035313406273396964565337 25526485054705047723424003)
        ·
          refine ⟨38289727582057571585136005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25526485054705047723424003 38289727582057571585136005)
          ·
            refine ⟨7179323921635794672213001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38289727582057571585136005 7179323921635794672213001)
            ·
              refine ⟨5384492941226846004159751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7179323921635794672213001 5384492941226846004159751)
              ·
                refine ⟨8076739411840269006239627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5384492941226846004159751 8076739411840269006239627)
                ·
                  refine ⟨12115109117760403509359441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8076739411840269006239627 12115109117760403509359441)
                  ·
                    refine ⟨9086331838320302632019581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12115109117760403509359441 9086331838320302632019581)
                    ·
                      refine ⟨3407374439370113487007343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9086331838320302632019581 3407374439370113487007343)
                      ·
                        rfl

theorem cell23_6635838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_6635838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635838 prefixEnd_6635838 := by exact prefixLift 6635838
  have htrace : WordTrace (prefixWord ++ tailWord_6635838) baseStart_6635838 baseEnd_6635838 := by
    simpa [prefixWord, tailWord_6635838, baseEnd_6635838] using wordTrace_append hprefix tailTrace_6635838
  have hstable : (prefixWord ++ tailWord_6635838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635838).length < 2 ^ (prefixWord ++ tailWord_6635838).sum := by decide
  have hdescent : baseEnd_6635838 < baseStart_6635838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635840 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 4]
def baseStart_6635840 : Nat := 118140960795 + 6635840 * 2 ^ 59
def prefixEnd_6635840 : Nat := 4983230072969 + 3 ^ 40 * 6635840 * 2
def baseEnd_6635840 : Nat := 3407375466331422479182333

theorem tailTrace_6635840 : CollatzResearch.WordTrace tailWord_6635840 prefixEnd_6635840 3407375466331422479182333 := by
  unfold tailWord_6635840
  simp only [CollatzResearch.WordTrace]
  refine ⟨121014484139746233044796487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161352645519661644059728649 121014484139746233044796487)
  ·
    refine ⟨181521726209619349567194731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121014484139746233044796487 181521726209619349567194731)
    ·
      refine ⟨272282589314429024350792097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181521726209619349567194731 272282589314429024350792097)
      ·
        refine ⟨204211941985821768263094073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272282589314429024350792097 204211941985821768263094073)
        ·
          refine ⟨153158956489366326197320555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204211941985821768263094073 153158956489366326197320555)
          ·
            refine ⟨229738434734049489295980833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153158956489366326197320555 229738434734049489295980833)
            ·
              refine ⟨172303826050537116971985625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229738434734049489295980833 172303826050537116971985625)
              ·
                refine ⟨129227869537902837728989219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172303826050537116971985625 129227869537902837728989219)
                ·
                  refine ⟨193841804306854256593483829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129227869537902837728989219 193841804306854256593483829)
                  ·
                    refine ⟨18172669153767586555639109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 193841804306854256593483829 18172669153767586555639109)
                    ·
                      refine ⟨3407375466331422479182333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18172669153767586555639109 3407375466331422479182333)
                      ·
                        rfl

theorem cell23_6635840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_6635840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635840 prefixEnd_6635840 := by exact prefixLift 6635840
  have htrace : WordTrace (prefixWord ++ tailWord_6635840) baseStart_6635840 baseEnd_6635840 := by
    simpa [prefixWord, tailWord_6635840, baseEnd_6635840] using wordTrace_append hprefix tailTrace_6635840
  have hstable : (prefixWord ++ tailWord_6635840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635840).length < 2 ^ (prefixWord ++ tailWord_6635840).sum := by decide
  have hdescent : baseEnd_6635840 < baseStart_6635840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635868 : List Nat := [2, 2, 4, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_6635868 : Nat := 118140960795 + 6635868 * 2 ^ 59
def prefixEnd_6635868 : Nat := 4983230072969 + 3 ^ 40 * 6635868 * 2
def baseEnd_6635868 : Nat := 3407389843789748369632205

theorem tailTrace_6635868 : CollatzResearch.WordTrace tailWord_6635868 prefixEnd_6635868 3407389843789748369632205 := by
  unfold tailWord_6635868
  simp only [CollatzResearch.WordTrace]
  refine ⟨121014994761695513435806129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161353326348927351247741505 121014994761695513435806129)
  ·
    refine ⟨90761246071271635076854597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121014994761695513435806129 90761246071271635076854597)
    ·
      refine ⟨17017733638363431576910237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90761246071271635076854597 17017733638363431576910237)
      ·
        refine ⟨6381650114386286841341339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17017733638363431576910237 6381650114386286841341339)
        ·
          refine ⟨9572475171579430262012009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6381650114386286841341339 9572475171579430262012009)
          ·
            refine ⟨7179356378684572696509007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9572475171579430262012009 7179356378684572696509007)
            ·
              refine ⟨10769034568026859044763511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7179356378684572696509007 10769034568026859044763511)
              ·
                refine ⟨16153551852040288567145267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10769034568026859044763511 16153551852040288567145267)
                ·
                  refine ⟨24230327778060432850717901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16153551852040288567145267 24230327778060432850717901)
                  ·
                    refine ⟨9086372916772662319019213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24230327778060432850717901 9086372916772662319019213)
                    ·
                      refine ⟨3407389843789748369632205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9086372916772662319019213 3407389843789748369632205)
                      ·
                        rfl

theorem cell23_6635868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_6635868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635868 prefixEnd_6635868 := by exact prefixLift 6635868
  have htrace : WordTrace (prefixWord ++ tailWord_6635868) baseStart_6635868 baseEnd_6635868 := by
    simpa [prefixWord, tailWord_6635868, baseEnd_6635868] using wordTrace_append hprefix tailTrace_6635868
  have hstable : (prefixWord ++ tailWord_6635868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635868).length < 2 ^ (prefixWord ++ tailWord_6635868).sum := by decide
  have hdescent : baseEnd_6635868 < baseStart_6635868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6635967 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 3]
def baseStart_6635967 : Nat := 118140960795 + 6635967 * 2 ^ 59
def prefixEnd_6635967 : Nat := 4983230072969 + 3 ^ 40 * 6635967 * 2
def baseEnd_6635967 : Nat := 3407440678374543482294249

theorem tailTrace_6635967 : CollatzResearch.WordTrace tailWord_6635967 prefixEnd_6635967 3407440678374543482294249 := by
  unfold tailWord_6635967
  simp only [CollatzResearch.WordTrace]
  refine ⟨242033600350032366779466155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161355733566688244519644103 242033600350032366779466155)
  ·
    refine ⟨363050400525048550169199233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242033600350032366779466155 363050400525048550169199233)
    ·
      refine ⟨272287800393786412626899425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363050400525048550169199233 272287800393786412626899425)
      ·
        refine ⟨204215850295339809470174569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272287800393786412626899425 204215850295339809470174569)
        ·
          refine ⟨153161887721504857102630927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204215850295339809470174569 153161887721504857102630927)
          ·
            refine ⟨229742831582257285653946391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153161887721504857102630927 229742831582257285653946391)
            ·
              refine ⟨344614247373385928480919587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229742831582257285653946391 344614247373385928480919587)
              ·
                refine ⟨516921371060078892721379381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344614247373385928480919587 516921371060078892721379381)
                ·
                  refine ⟨48461378536882396192629317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 516921371060078892721379381 48461378536882396192629317)
                  ·
                    refine ⟨9086508475665449286117997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48461378536882396192629317 9086508475665449286117997)
                    ·
                      refine ⟨3407440678374543482294249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9086508475665449286117997 3407440678374543482294249)
                      ·
                        rfl

theorem cell23_6635967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 3].length) (baseStart_6635967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6635967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6635967 prefixEnd_6635967 := by exact prefixLift 6635967
  have htrace : WordTrace (prefixWord ++ tailWord_6635967) baseStart_6635967 baseEnd_6635967 := by
    simpa [prefixWord, tailWord_6635967, baseEnd_6635967] using wordTrace_append hprefix tailTrace_6635967
  have hstable : (prefixWord ++ tailWord_6635967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6635967).length < 2 ^ (prefixWord ++ tailWord_6635967).sum := by decide
  have hdescent : baseEnd_6635967 < baseStart_6635967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6635967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636008 : List Nat := [2, 1, 4, 1, 1, 4, 2, 3, 1, 4]
def baseStart_6636008 : Nat := 118140960795 + 6636008 * 2 ^ 59
def prefixEnd_6636008 : Nat := 4983230072969 + 3 ^ 40 * 6636008 * 2
def baseEnd_6636008 : Nat := 1135820577027125940627187

theorem tailTrace_6636008 : CollatzResearch.WordTrace tailWord_6636008 prefixEnd_6636008 1135820577027125940627187 := by
  unfold tailWord_6636008
  simp only [CollatzResearch.WordTrace]
  refine ⟨121017547871441915390854339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161356730495255887187805785 121017547871441915390854339)
  ·
    refine ⟨181526321807162873086281509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121017547871441915390854339 181526321807162873086281509)
    ·
      refine ⟨34036185338843038703677783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181526321807162873086281509 34036185338843038703677783)
      ·
        refine ⟨51054278008264558055516675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34036185338843038703677783 51054278008264558055516675)
        ·
          refine ⟨76581417012396837083275013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51054278008264558055516675 76581417012396837083275013)
          ·
            refine ⟨14359015689824406953114065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76581417012396837083275013 14359015689824406953114065)
            ·
              refine ⟨10769261767368305214835549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14359015689824406953114065 10769261767368305214835549)
              ·
                refine ⟨4038473162763114455563331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10769261767368305214835549 4038473162763114455563331)
                ·
                  refine ⟨6057709744144671683344997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4038473162763114455563331 6057709744144671683344997)
                  ·
                    refine ⟨1135820577027125940627187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6057709744144671683344997 1135820577027125940627187)
                    ·
                      rfl

theorem cell23_6636008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_6636008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636008 prefixEnd_6636008 := by exact prefixLift 6636008
  have htrace : WordTrace (prefixWord ++ tailWord_6636008) baseStart_6636008 baseEnd_6636008 := by
    simpa [prefixWord, tailWord_6636008, baseEnd_6636008] using wordTrace_append hprefix tailTrace_6636008
  have hstable : (prefixWord ++ tailWord_6636008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636008).length < 2 ^ (prefixWord ++ tailWord_6636008).sum := by decide
  have hdescent : baseEnd_6636008 < baseStart_6636008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636021 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 8]
def baseStart_6636021 : Nat := 118140960795 + 6636021 * 2 ^ 59
def prefixEnd_6636021 : Nat := 4983230072969 + 3 ^ 40 * 6636021 * 2
def baseEnd_6636021 : Nat := 378607600703320696779889

theorem tailTrace_6636021 : CollatzResearch.WordTrace tailWord_6636021 prefixEnd_6636021 378607600703320696779889 := by
  unfold tailWord_6636021
  simp only [CollatzResearch.WordTrace]
  refine ⟨242035569891836734001931917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161357046594557822667954611 242035569891836734001931917)
  ·
    refine ⟨90763338709438775250724469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242035569891836734001931917 90763338709438775250724469)
    ·
      refine ⟨8509063004009885179755419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90763338709438775250724469 8509063004009885179755419)
      ·
        refine ⟨12763594506014827769633129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8509063004009885179755419 12763594506014827769633129)
        ·
          refine ⟨9572695879511120827224847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12763594506014827769633129 9572695879511120827224847)
          ·
            refine ⟨14359043819266681240837271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9572695879511120827224847 14359043819266681240837271)
            ·
              refine ⟨21538565728900021861255907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14359043819266681240837271 21538565728900021861255907)
              ·
                refine ⟨32307848593350032791883861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21538565728900021861255907 32307848593350032791883861)
                ·
                  refine ⟨378607600703320696779889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32307848593350032791883861 378607600703320696779889)
                  ·
                    rfl

theorem cell23_6636021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 8].length) (baseStart_6636021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636021 prefixEnd_6636021 := by exact prefixLift 6636021
  have htrace : WordTrace (prefixWord ++ tailWord_6636021) baseStart_6636021 baseEnd_6636021 := by
    simpa [prefixWord, tailWord_6636021, baseEnd_6636021] using wordTrace_append hprefix tailTrace_6636021
  have hstable : (prefixWord ++ tailWord_6636021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636021).length < 2 ^ (prefixWord ++ tailWord_6636021).sum := by decide
  have hdescent : baseEnd_6636021 < baseStart_6636021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636031 : List Nat := [1, 1, 2, 2, 1, 2, 6, 1, 3, 1, 3]
def baseStart_6636031 : Nat := 118140960795 + 6636031 * 2 ^ 59
def prefixEnd_6636031 : Nat := 4983230072969 + 3 ^ 40 * 6636031 * 2
def baseEnd_6636031 : Nat := 3407473541136431231893955

theorem tailTrace_6636031 : CollatzResearch.WordTrace tailWord_6636031 prefixEnd_6636031 3407473541136431231893955 := by
  unfold tailWord_6636031
  simp only [CollatzResearch.WordTrace]
  refine ⟨242035934621800505709795947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161357289747867003806530631 242035934621800505709795947)
  ·
    refine ⟨363053901932700758564693921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242035934621800505709795947 363053901932700758564693921)
    ·
      refine ⟨272290426449525568923520441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363053901932700758564693921 272290426449525568923520441)
      ·
        refine ⟨204217819837144176692640331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272290426449525568923520441 204217819837144176692640331)
        ·
          refine ⟨306326729755716265038960497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204217819837144176692640331 306326729755716265038960497)
          ·
            refine ⟨229745047316787198779220373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306326729755716265038960497 229745047316787198779220373)
            ·
              refine ⟨10769299092974399942775955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 229745047316787198779220373 10769299092974399942775955)
              ·
                refine ⟨16153948639461599914163933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10769299092974399942775955 16153948639461599914163933)
                ·
                  refine ⟨6057730739798099967811475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16153948639461599914163933 6057730739798099967811475)
                  ·
                    refine ⟨9086596109697149951717213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6057730739798099967811475 9086596109697149951717213)
                    ·
                      refine ⟨3407473541136431231893955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9086596109697149951717213 3407473541136431231893955)
                      ·
                        rfl

theorem cell23_6636031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 1, 3].length) (baseStart_6636031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636031 prefixEnd_6636031 := by exact prefixLift 6636031
  have htrace : WordTrace (prefixWord ++ tailWord_6636031) baseStart_6636031 baseEnd_6636031 := by
    simpa [prefixWord, tailWord_6636031, baseEnd_6636031] using wordTrace_append hprefix tailTrace_6636031
  have hstable : (prefixWord ++ tailWord_6636031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636031).length < 2 ^ (prefixWord ++ tailWord_6636031).sum := by decide
  have hdescent : baseEnd_6636031 < baseStart_6636031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636104 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 5, 3, 3]
def baseStart_6636104 : Nat := 118140960795 + 6636104 * 2 ^ 59
def prefixEnd_6636104 : Nat := 4983230072969 + 3 ^ 40 * 6636104 * 2
def baseEnd_6636104 : Nat := 3407511025224209446281119

theorem tailTrace_6636104 : CollatzResearch.WordTrace tailWord_6636104 prefixEnd_6636104 3407511025224209446281119 := by
  unfold tailWord_6636104
  simp only [CollatzResearch.WordTrace]
  refine ⟨121019298575268019588601683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161359064767024026118135577 121019298575268019588601683)
  ·
    refine ⟨181528947862902029382902525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121019298575268019588601683 181528947862902029382902525)
    ·
      refine ⟨68073355448588261018588447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181528947862902029382902525 68073355448588261018588447)
      ·
        refine ⟨102110033172882391527882671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68073355448588261018588447 102110033172882391527882671)
        ·
          refine ⟨153165049759323587291824007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102110033172882391527882671 153165049759323587291824007)
          ·
            refine ⟨229747574638985380937736011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153165049759323587291824007 229747574638985380937736011)
            ·
              refine ⟨344621361958478071406604017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229747574638985380937736011 344621361958478071406604017)
              ·
                refine ⟨258466021468858553554953013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 344621361958478071406604017 258466021468858553554953013)
                ·
                  refine ⟨24231189512705489395776845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 258466021468858553554953013 24231189512705489395776845)
                  ·
                    refine ⟨9086696067264558523416317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24231189512705489395776845 9086696067264558523416317)
                    ·
                      refine ⟨3407511025224209446281119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9086696067264558523416317 3407511025224209446281119)
                      ·
                        rfl

theorem cell23_6636104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_6636104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636104 prefixEnd_6636104 := by exact prefixLift 6636104
  have htrace : WordTrace (prefixWord ++ tailWord_6636104) baseStart_6636104 baseEnd_6636104 := by
    simpa [prefixWord, tailWord_6636104, baseEnd_6636104] using wordTrace_append hprefix tailTrace_6636104
  have hstable : (prefixWord ++ tailWord_6636104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636104).length < 2 ^ (prefixWord ++ tailWord_6636104).sum := by decide
  have hdescent : baseEnd_6636104 < baseStart_6636104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636162 : List Nat := [3, 4, 3, 1, 1, 1, 3, 7]
def baseStart_6636162 : Nat := 118140960795 + 6636162 * 2 ^ 59
def prefixEnd_6636162 : Nat := 4983230072969 + 3 ^ 40 * 6636162 * 2
def baseEnd_6636162 : Nat := 126205215077858156272439

theorem tailTrace_6636162 : CollatzResearch.WordTrace tailWord_6636162 prefixEnd_6636162 126205215077858156272439 := by
  unfold tailWord_6636162
  simp only [CollatzResearch.WordTrace]
  refine ⟨60510178146081478770703685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161360475056217276721876493 60510178146081478770703685)
  ·
    refine ⟨11345658402390277269506941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60510178146081478770703685 11345658402390277269506941)
    ·
      refine ⟨4254621900896353976065103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11345658402390277269506941 4254621900896353976065103)
      ·
        refine ⟨6381932851344530964097655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4254621900896353976065103 6381932851344530964097655)
        ·
          refine ⟨9572899277016796446146483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6381932851344530964097655 9572899277016796446146483)
          ·
            refine ⟨14359348915525194669219725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9572899277016796446146483 14359348915525194669219725)
            ·
              refine ⟨5384755843321948000957397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14359348915525194669219725 5384755843321948000957397)
              ·
                refine ⟨126205215077858156272439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5384755843321948000957397 126205215077858156272439)
                ·
                  rfl

theorem cell23_6636162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 7].length) (baseStart_6636162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636162 prefixEnd_6636162 := by exact prefixLift 6636162
  have htrace : WordTrace (prefixWord ++ tailWord_6636162) baseStart_6636162 baseEnd_6636162 := by
    simpa [prefixWord, tailWord_6636162, baseEnd_6636162] using wordTrace_append hprefix tailTrace_6636162
  have hstable : (prefixWord ++ tailWord_6636162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636162).length < 2 ^ (prefixWord ++ tailWord_6636162).sum := by decide
  have hdescent : baseEnd_6636162 < baseStart_6636162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636184 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 9]
def baseStart_6636184 : Nat := 118140960795 + 6636184 * 2 ^ 59
def prefixEnd_6636184 : Nat := 4983230072969 + 3 ^ 40 * 6636184 * 2
def baseEnd_6636184 : Nat := 378616900408507681475639

theorem tailTrace_6636184 : CollatzResearch.WordTrace tailWord_6636184 prefixEnd_6636184 378616900408507681475639 := by
  unfold tailWord_6636184
  simp only [CollatzResearch.WordTrace]
  refine ⟨121020757495123106420057803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161361009993497475226743737 121020757495123106420057803)
  ·
    refine ⟨181531136242684659630086705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121020757495123106420057803 181531136242684659630086705)
    ·
      refine ⟨136148352182013494722565029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181531136242684659630086705 136148352182013494722565029)
      ·
        refine ⟨25527816034127530260480943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136148352182013494722565029 25527816034127530260480943)
        ·
          refine ⟨38291724051191295390721415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25527816034127530260480943 38291724051191295390721415)
          ·
            refine ⟨57437586076786943086082123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38291724051191295390721415 57437586076786943086082123)
            ·
              refine ⟨86156379115180414629123185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57437586076786943086082123 86156379115180414629123185)
              ·
                refine ⟨64617284336385310971842389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86156379115180414629123185 64617284336385310971842389)
                ·
                  refine ⟨378616900408507681475639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64617284336385310971842389 378616900408507681475639)
                  ·
                    rfl

theorem cell23_6636184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 9].length) (baseStart_6636184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636184 prefixEnd_6636184 := by exact prefixLift 6636184
  have htrace : WordTrace (prefixWord ++ tailWord_6636184) baseStart_6636184 baseEnd_6636184 := by
    simpa [prefixWord, tailWord_6636184, baseEnd_6636184] using wordTrace_append hprefix tailTrace_6636184
  have hstable : (prefixWord ++ tailWord_6636184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636184).length < 2 ^ (prefixWord ++ tailWord_6636184).sum := by decide
  have hdescent : baseEnd_6636184 < baseStart_6636184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636211 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 3]
def baseStart_6636211 : Nat := 118140960795 + 6636211 * 2 ^ 59
def prefixEnd_6636211 : Nat := 4983230072969 + 3 ^ 40 * 6636211 * 2
def baseEnd_6636211 : Nat := 3407565967654240527643127

theorem tailTrace_6636211 : CollatzResearch.WordTrace tailWord_6636211 prefixEnd_6636211 3407565967654240527643127 := by
  unfold tailWord_6636211
  simp only [CollatzResearch.WordTrace]
  refine ⟨242042499761148396451348487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161361666507432264300898991 242042499761148396451348487)
  ·
    refine ⟨363063749641722594677022731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242042499761148396451348487 363063749641722594677022731)
    ·
      refine ⟨544595624462583892015534097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363063749641722594677022731 544595624462583892015534097)
      ·
        refine ⟨408446718346937919011650573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 544595624462583892015534097 408446718346937919011650573)
        ·
          refine ⟨153167519380101719629368965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 408446718346937919011650573 153167519380101719629368965)
          ·
            refine ⟨28718909883769072430506681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153167519380101719629368965 28718909883769072430506681)
            ·
              refine ⟨21539182412826804322880011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28718909883769072430506681 21539182412826804322880011)
              ·
                refine ⟨32308773619240206484320017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21539182412826804322880011 32308773619240206484320017)
                ·
                  refine ⟨24231580214430154863240013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32308773619240206484320017 24231580214430154863240013)
                  ·
                    refine ⟨9086842580411308073715005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24231580214430154863240013 9086842580411308073715005)
                    ·
                      refine ⟨3407565967654240527643127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9086842580411308073715005 3407565967654240527643127)
                      ·
                        rfl

theorem cell23_6636211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 3].length) (baseStart_6636211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636211 prefixEnd_6636211 := by exact prefixLift 6636211
  have htrace : WordTrace (prefixWord ++ tailWord_6636211) baseStart_6636211 baseEnd_6636211 := by
    simpa [prefixWord, tailWord_6636211, baseEnd_6636211] using wordTrace_append hprefix tailTrace_6636211
  have hstable : (prefixWord ++ tailWord_6636211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636211).length < 2 ^ (prefixWord ++ tailWord_6636211).sum := by decide
  have hdescent : baseEnd_6636211 < baseStart_6636211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636251 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 5, 6, 2]
def baseStart_6636251 : Nat := 118140960795 + 6636251 * 2 ^ 59
def prefixEnd_6636251 : Nat := 4983230072969 + 3 ^ 40 * 6636251 * 2
def baseEnd_6636251 : Nat := 3407586506880420371142943

theorem tailTrace_6636251 : CollatzResearch.WordTrace tailWord_6636251 prefixEnd_6636251 3407586506880420371142943 := by
  unfold tailWord_6636251
  simp only [CollatzResearch.WordTrace]
  refine ⟨242043958681003483282804607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161362639120668988855203071 242043958681003483282804607)
  ·
    refine ⟨363065938021505224924206911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242043958681003483282804607 363065938021505224924206911)
    ·
      refine ⟨544598907032257837386310367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363065938021505224924206911 544598907032257837386310367)
      ·
        refine ⟨816898360548386756079465551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544598907032257837386310367 816898360548386756079465551)
        ·
          refine ⟨1225347540822580134119198327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 816898360548386756079465551 1225347540822580134119198327)
          ·
            refine ⟨1838021311233870201178797491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1225347540822580134119198327 1838021311233870201178797491)
            ·
              refine ⟨2757031966850805301768196237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1838021311233870201178797491 2757031966850805301768196237)
              ·
                refine ⟨1033886987569051988163073589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2757031966850805301768196237 1033886987569051988163073589)
                ·
                  refine ⟨96926905084598623890288149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1033886987569051988163073589 96926905084598623890288149)
                  ·
                    refine ⟨4543448675840560494857257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 96926905084598623890288149 4543448675840560494857257)
                    ·
                      refine ⟨3407586506880420371142943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4543448675840560494857257 3407586506880420371142943)
                      ·
                        rfl

theorem cell23_6636251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 6, 2].length) (baseStart_6636251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636251 prefixEnd_6636251 := by exact prefixLift 6636251
  have htrace : WordTrace (prefixWord ++ tailWord_6636251) baseStart_6636251 baseEnd_6636251 := by
    simpa [prefixWord, tailWord_6636251, baseEnd_6636251] using wordTrace_append hprefix tailTrace_6636251
  have hstable : (prefixWord ++ tailWord_6636251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636251).length < 2 ^ (prefixWord ++ tailWord_6636251).sum := by decide
  have hdescent : baseEnd_6636251 < baseStart_6636251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636252 : List Nat := [2, 2, 5, 1, 1, 2, 3, 2, 5]
def baseStart_6636252 : Nat := 118140960795 + 6636252 * 2 ^ 59
def prefixEnd_6636252 : Nat := 4983230072969 + 3 ^ 40 * 6636252 * 2
def baseEnd_6636252 : Nat := 378620780040119429692271

theorem tailTrace_6636252 : CollatzResearch.WordTrace tailWord_6636252 prefixEnd_6636252 378620780040119429692271 := by
  unfold tailWord_6636252
  simp only [CollatzResearch.WordTrace]
  refine ⟨121021997576999930226795505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161362663435999906969060673 121021997576999930226795505)
  ·
    refine ⟨90766498182749947670096629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121021997576999930226795505 90766498182749947670096629)
    ·
      refine ⟨8509359204632807594071559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90766498182749947670096629 8509359204632807594071559)
      ·
        refine ⟨12764038806949211391107339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8509359204632807594071559 12764038806949211391107339)
        ·
          refine ⟨19146058210423817086661009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12764038806949211391107339 19146058210423817086661009)
          ·
            refine ⟨14359543657817862814995757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19146058210423817086661009 14359543657817862814995757)
            ·
              refine ⟨5384828871681698555623409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14359543657817862814995757 5384828871681698555623409)
              ·
                refine ⟨4038621653761273916717557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5384828871681698555623409 4038621653761273916717557)
                ·
                  refine ⟨378620780040119429692271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4038621653761273916717557 378620780040119429692271)
                  ·
                    rfl

theorem cell23_6636252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 5].length) (baseStart_6636252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636252 prefixEnd_6636252 := by exact prefixLift 6636252
  have htrace : WordTrace (prefixWord ++ tailWord_6636252) baseStart_6636252 baseEnd_6636252 := by
    simpa [prefixWord, tailWord_6636252, baseEnd_6636252] using wordTrace_append hprefix tailTrace_6636252
  have hstable : (prefixWord ++ tailWord_6636252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636252).length < 2 ^ (prefixWord ++ tailWord_6636252).sum := by decide
  have hdescent : baseEnd_6636252 < baseStart_6636252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636278 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 5, 4]
def baseStart_6636278 : Nat := 118140960795 + 6636278 * 2 ^ 59
def prefixEnd_6636278 : Nat := 4983230072969 + 3 ^ 40 * 6636278 * 2
def baseEnd_6636278 : Nat := 1135866790286030588501773

theorem tailTrace_6636278 : CollatzResearch.WordTrace tailWord_6636278 prefixEnd_6636278 1135866790286030588501773 := by
  unfold tailWord_6636278
  simp only [CollatzResearch.WordTrace]
  refine ⟨15127808965744104180877343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161363295634603777929358325 15127808965744104180877343)
  ·
    refine ⟨22691713448616156271316015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15127808965744104180877343 22691713448616156271316015)
    ·
      refine ⟨34037570172924234406974023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22691713448616156271316015 34037570172924234406974023)
      ·
        refine ⟨51056355259386351610461035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34037570172924234406974023 51056355259386351610461035)
        ·
          refine ⟨76584532889079527415691553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51056355259386351610461035 76584532889079527415691553)
          ·
            refine ⟨57438399666809645561768665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76584532889079527415691553 57438399666809645561768665)
            ·
              refine ⟨43078799750107234171326499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57438399666809645561768665 43078799750107234171326499)
              ·
                refine ⟨64618199625160851256989749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43078799750107234171326499 64618199625160851256989749)
                ·
                  refine ⟨6057956214858829805342789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64618199625160851256989749 6057956214858829805342789)
                  ·
                    refine ⟨1135866790286030588501773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6057956214858829805342789 1135866790286030588501773)
                    ·
                      rfl

theorem cell23_6636278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_6636278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636278 prefixEnd_6636278 := by exact prefixLift 6636278
  have htrace : WordTrace (prefixWord ++ tailWord_6636278) baseStart_6636278 baseEnd_6636278 := by
    simpa [prefixWord, tailWord_6636278, baseEnd_6636278] using wordTrace_append hprefix tailTrace_6636278
  have hstable : (prefixWord ++ tailWord_6636278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636278).length < 2 ^ (prefixWord ++ tailWord_6636278).sum := by decide
  have hdescent : baseEnd_6636278 < baseStart_6636278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636321 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 5, 5]
def baseStart_6636321 : Nat := 118140960795 + 6636321 * 2 ^ 59
def prefixEnd_6636321 : Nat := 4983230072969 + 3 ^ 40 * 6636321 * 2
def baseEnd_6636321 : Nat := 1135874150175411699089207

theorem tailTrace_6636321 : CollatzResearch.WordTrace tailWord_6636321 prefixEnd_6636321 1135874150175411699089207 := by
  unfold tailWord_6636321
  simp only [CollatzResearch.WordTrace]
  refine ⟨242046511790749885237852817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161364341193833256825235211 242046511790749885237852817)
  ·
    refine ⟨181534883843062413928389613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242046511790749885237852817 181534883843062413928389613)
    ·
      refine ⟨68075581441148405223146105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181534883843062413928389613 68075581441148405223146105)
      ·
        refine ⟨51056686080861303917359579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68075581441148405223146105 51056686080861303917359579)
        ·
          refine ⟨76585029121291955876039369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51056686080861303917359579 76585029121291955876039369)
          ·
            refine ⟨57438771840968966907029527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76585029121291955876039369 57438771840968966907029527)
            ·
              refine ⟨86158157761453450360544291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57438771840968966907029527 86158157761453450360544291)
              ·
                refine ⟨129237236642180175540816437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86158157761453450360544291 129237236642180175540816437)
                ·
                  refine ⟨12115990935204391456951541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129237236642180175540816437 12115990935204391456951541)
                  ·
                    refine ⟨1135874150175411699089207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12115990935204391456951541 1135874150175411699089207)
                    ·
                      rfl

theorem cell23_6636321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_6636321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636321 prefixEnd_6636321 := by exact prefixLift 6636321
  have htrace : WordTrace (prefixWord ++ tailWord_6636321) baseStart_6636321 baseEnd_6636321 := by
    simpa [prefixWord, tailWord_6636321, baseEnd_6636321] using wordTrace_append hprefix tailTrace_6636321
  have hstable : (prefixWord ++ tailWord_6636321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636321).length < 2 ^ (prefixWord ++ tailWord_6636321).sum := by decide
  have hdescent : baseEnd_6636321 < baseStart_6636321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636338 : List Nat := [3, 2, 1, 1, 3, 1, 2, 4, 1, 5]
def baseStart_6636338 : Nat := 118140960795 + 6636338 * 2 ^ 59
def prefixEnd_6636338 : Nat := 4983230072969 + 3 ^ 40 * 6636338 * 2
def baseEnd_6636338 : Nat := 1135877059899120510251681

theorem tailTrace_6636338 : CollatzResearch.WordTrace tailWord_6636338 prefixEnd_6636338 1135877059899120510251681 := by
  unfold tailWord_6636338
  simp only [CollatzResearch.WordTrace]
  refine ⟨60511782957922074285305417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161364754554458864760814445 60511782957922074285305417)
  ·
    refine ⟨45383837218441555713979063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60511782957922074285305417 45383837218441555713979063)
    ·
      refine ⟨68075755827662333570968595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45383837218441555713979063 68075755827662333570968595)
      ·
        refine ⟨102113633741493500356452893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68075755827662333570968595 102113633741493500356452893)
        ·
          refine ⟨38292612653060062633669835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102113633741493500356452893 38292612653060062633669835)
          ·
            refine ⟨57438918979590093950504753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38292612653060062633669835 57438918979590093950504753)
            ·
              refine ⟨43079189234692570462878565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57438918979590093950504753 43079189234692570462878565)
              ·
                refine ⟨8077347981504856961789731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43079189234692570462878565 8077347981504856961789731)
                ·
                  refine ⟨12116021972257285442684597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8077347981504856961789731 12116021972257285442684597)
                  ·
                    refine ⟨1135877059899120510251681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12116021972257285442684597 1135877059899120510251681)
                    ·
                      rfl

theorem cell23_6636338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_6636338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636338 prefixEnd_6636338 := by exact prefixLift 6636338
  have htrace : WordTrace (prefixWord ++ tailWord_6636338) baseStart_6636338 baseEnd_6636338 := by
    simpa [prefixWord, tailWord_6636338, baseEnd_6636338] using wordTrace_append hprefix tailTrace_6636338
  have hstable : (prefixWord ++ tailWord_6636338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636338).length < 2 ^ (prefixWord ++ tailWord_6636338).sum := by decide
  have hdescent : baseEnd_6636338 < baseStart_6636338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636371 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 4]
def baseStart_6636371 : Nat := 118140960795 + 6636371 * 2 ^ 59
def prefixEnd_6636371 : Nat := 4983230072969 + 3 ^ 40 * 6636371 * 2
def baseEnd_6636371 : Nat := 3407648124558959901642391

theorem tailTrace_6636371 : CollatzResearch.WordTrace tailWord_6636371 prefixEnd_6636371 3407648124558959901642391 := by
  unfold tailWord_6636371
  simp only [CollatzResearch.WordTrace]
  refine ⟨242048335440568743777172967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161365556960379162518115311 242048335440568743777172967)
  ·
    refine ⟨363072503160853115665759451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242048335440568743777172967 363072503160853115665759451)
    ·
      refine ⟨544608754741279673498639177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363072503160853115665759451 544608754741279673498639177)
      ·
        refine ⟨408456566055959755123979383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 544608754741279673498639177 408456566055959755123979383)
        ·
          refine ⟨612684849083939632685969075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408456566055959755123979383 612684849083939632685969075)
          ·
            refine ⟨919027273625909449028953613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612684849083939632685969075 919027273625909449028953613)
            ·
              refine ⟨344635227609716043385857605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 919027273625909449028953613 344635227609716043385857605)
              ·
                refine ⟨64619105176821758134848301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 344635227609716043385857605 64619105176821758134848301)
                ·
                  refine ⟨24232164441308159300568113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64619105176821758134848301 24232164441308159300568113)
                  ·
                    refine ⟨18174123330981119475426085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24232164441308159300568113 18174123330981119475426085)
                    ·
                      refine ⟨3407648124558959901642391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18174123330981119475426085 3407648124558959901642391)
                      ·
                        rfl

theorem cell23_6636371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 4].length) (baseStart_6636371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636371 prefixEnd_6636371 := by exact prefixLift 6636371
  have htrace : WordTrace (prefixWord ++ tailWord_6636371) baseStart_6636371 baseEnd_6636371 := by
    simpa [prefixWord, tailWord_6636371, baseEnd_6636371] using wordTrace_append hprefix tailTrace_6636371
  have hstable : (prefixWord ++ tailWord_6636371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636371).length < 2 ^ (prefixWord ++ tailWord_6636371).sum := by decide
  have hdescent : baseEnd_6636371 < baseStart_6636371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636378 : List Nat := [3, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5]
def baseStart_6636378 : Nat := 118140960795 + 6636378 * 2 ^ 59
def prefixEnd_6636378 : Nat := 4983230072969 + 3 ^ 40 * 6636378 * 2
def baseEnd_6636378 : Nat := 3407651718923541374254859

theorem tailTrace_6636378 : CollatzResearch.WordTrace tailWord_6636378 prefixEnd_6636378 3407651718923541374254859 := by
  unfold tailWord_6636378
  simp only [CollatzResearch.WordTrace]
  refine ⟨60512147687885845993169447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161365727167695589315118525 60512147687885845993169447)
  ·
    refine ⟨90768221531828768989754171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60512147687885845993169447 90768221531828768989754171)
    ·
      refine ⟨136152332297743153484631257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90768221531828768989754171 136152332297743153484631257)
      ·
        refine ⟨102114249223307365113473443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136152332297743153484631257 102114249223307365113473443)
        ·
          refine ⟨153171373834961047670210165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102114249223307365113473443 153171373834961047670210165)
          ·
            refine ⟨14359816297027598219082203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 153171373834961047670210165 14359816297027598219082203)
            ·
              refine ⟨21539724445541397328623305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14359816297027598219082203 21539724445541397328623305)
              ·
                refine ⟨16154793334156047996467479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21539724445541397328623305 16154793334156047996467479)
                ·
                  refine ⟨24232190001234071994701219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16154793334156047996467479 24232190001234071994701219)
                  ·
                    refine ⟨36348285001851107992051829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24232190001234071994701219 36348285001851107992051829)
                    ·
                      refine ⟨3407651718923541374254859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36348285001851107992051829 3407651718923541374254859)
                      ·
                        rfl

theorem cell23_6636378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_6636378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636378 prefixEnd_6636378 := by exact prefixLift 6636378
  have htrace : WordTrace (prefixWord ++ tailWord_6636378) baseStart_6636378 baseEnd_6636378 := by
    simpa [prefixWord, tailWord_6636378, baseEnd_6636378] using wordTrace_append hprefix tailTrace_6636378
  have hstable : (prefixWord ++ tailWord_6636378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636378).length < 2 ^ (prefixWord ++ tailWord_6636378).sum := by decide
  have hdescent : baseEnd_6636378 < baseStart_6636378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636388 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 1, 1, 6]
def baseStart_6636388 : Nat := 118140960795 + 6636388 * 2 ^ 59
def prefixEnd_6636388 : Nat := 4983230072969 + 3 ^ 40 * 6636388 * 2
def baseEnd_6636388 : Nat := 3407656853730086335129813

theorem tailTrace_6636388 : CollatzResearch.WordTrace tailWord_6636388 prefixEnd_6636388 3407656853730086335129813 := by
  unfold tailWord_6636388
  simp only [CollatzResearch.WordTrace]
  refine ⟨121024477740753577840270909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161365970321004770453694545 121024477740753577840270909)
  ·
    refine ⟨45384179152782591690101591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121024477740753577840270909 45384179152782591690101591)
    ·
      refine ⟨68076268729173887535152387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45384179152782591690101591 68076268729173887535152387)
      ·
        refine ⟨102114403093760831302728581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68076268729173887535152387 102114403093760831302728581)
        ·
          refine ⟨19146450580080155869261609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102114403093760831302728581 19146450580080155869261609)
          ·
            refine ⟨14359837935060116901946207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19146450580080155869261609 14359837935060116901946207)
            ·
              refine ⟨21539756902590175352919311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14359837935060116901946207 21539756902590175352919311)
              ·
                refine ⟨32309635353885263029378967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21539756902590175352919311 32309635353885263029378967)
                ·
                  refine ⟨48464453030827894544068451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32309635353885263029378967 48464453030827894544068451)
                  ·
                    refine ⟨72696679546241841816102677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48464453030827894544068451 72696679546241841816102677)
                    ·
                      refine ⟨3407656853730086335129813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72696679546241841816102677 3407656853730086335129813)
                      ·
                        rfl

theorem cell23_6636388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_6636388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636388 prefixEnd_6636388 := by exact prefixLift 6636388
  have htrace : WordTrace (prefixWord ++ tailWord_6636388) baseStart_6636388 baseEnd_6636388 := by
    simpa [prefixWord, tailWord_6636388, baseEnd_6636388] using wordTrace_append hprefix tailTrace_6636388
  have hstable : (prefixWord ++ tailWord_6636388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636388).length < 2 ^ (prefixWord ++ tailWord_6636388).sum := by decide
  have hdescent : baseEnd_6636388 < baseStart_6636388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636392 : List Nat := [2, 1, 4, 2, 1, 2, 2, 2, 3, 2, 2]
def baseStart_6636392 : Nat := 118140960795 + 6636392 * 2 ^ 59
def prefixEnd_6636392 : Nat := 4983230072969 + 3 ^ 40 * 6636392 * 2
def baseEnd_6636392 : Nat := 3407658907652704319479795

theorem tailTrace_6636392 : CollatzResearch.WordTrace tailWord_6636392 prefixEnd_6636392 3407658907652704319479795 := by
  unfold tailWord_6636392
  simp only [CollatzResearch.WordTrace]
  refine ⟨121024550686746332181843715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161366067582328442909124953 121024550686746332181843715)
  ·
    refine ⟨181536826030119498272765573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121024550686746332181843715 181536826030119498272765573)
    ·
      refine ⟨34038154880647405926143545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181536826030119498272765573 34038154880647405926143545)
      ·
        refine ⟨25528616160485554444607659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34038154880647405926143545 25528616160485554444607659)
        ·
          refine ⟨38292924240728331666911489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25528616160485554444607659 38292924240728331666911489)
          ·
            refine ⟨28719693180546248750183617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38292924240728331666911489 28719693180546248750183617)
            ·
              refine ⟨21539769885409686562637713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28719693180546248750183617 21539769885409686562637713)
              ·
                refine ⟨16154827414057264921978285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21539769885409686562637713 16154827414057264921978285)
                ·
                  refine ⟨6058060280271474345741857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16154827414057264921978285 6058060280271474345741857)
                  ·
                    refine ⟨4543545210203605759306393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6058060280271474345741857 4543545210203605759306393)
                    ·
                      refine ⟨3407658907652704319479795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4543545210203605759306393 3407658907652704319479795)
                      ·
                        rfl

theorem cell23_6636392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_6636392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636392 prefixEnd_6636392 := by exact prefixLift 6636392
  have htrace : WordTrace (prefixWord ++ tailWord_6636392) baseStart_6636392 baseEnd_6636392 := by
    simpa [prefixWord, tailWord_6636392, baseEnd_6636392] using wordTrace_append hprefix tailTrace_6636392
  have hstable : (prefixWord ++ tailWord_6636392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636392).length < 2 ^ (prefixWord ++ tailWord_6636392).sum := by decide
  have hdescent : baseEnd_6636392 < baseStart_6636392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636409 : List Nat := [1, 2, 1, 3, 2, 3, 3, 3, 1, 2, 2]
def baseStart_6636409 : Nat := 118140960795 + 6636409 * 2 ^ 59
def prefixEnd_6636409 : Nat := 4983230072969 + 3 ^ 40 * 6636409 * 2
def baseEnd_6636409 : Nat := 3407667636823830752967217

theorem tailTrace_6636409 : CollatzResearch.WordTrace tailWord_6636409 prefixEnd_6636409 3407667636823830752967217 := by
  unfold tailWord_6636409
  simp only [CollatzResearch.WordTrace]
  refine ⟨242049721414431076267056281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161366480942954050844704187 242049721414431076267056281)
  ·
    refine ⟨181537291060823307200292211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242049721414431076267056281 181537291060823307200292211)
    ·
      refine ⟨272305936591234960800438317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181537291060823307200292211 272305936591234960800438317)
      ·
        refine ⟨102114726221713110300164369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272305936591234960800438317 102114726221713110300164369)
        ·
          refine ⟨76586044666284832725123277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102114726221713110300164369 76586044666284832725123277)
          ·
            refine ⟨28719766749856812271921229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76586044666284832725123277 28719766749856812271921229)
            ·
              refine ⟨10769912531196304601970461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28719766749856812271921229 10769912531196304601970461)
              ·
                refine ⟨4038717199198614225738923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10769912531196304601970461 4038717199198614225738923)
                ·
                  refine ⟨6058075798797921338608385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4038717199198614225738923 6058075798797921338608385)
                  ·
                    refine ⟨4543556849098441003956289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6058075798797921338608385 4543556849098441003956289)
                    ·
                      refine ⟨3407667636823830752967217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4543556849098441003956289 3407667636823830752967217)
                      ·
                        rfl

theorem cell23_6636409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 1, 2, 2].length) (baseStart_6636409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636409 prefixEnd_6636409 := by exact prefixLift 6636409
  have htrace : WordTrace (prefixWord ++ tailWord_6636409) baseStart_6636409 baseEnd_6636409 := by
    simpa [prefixWord, tailWord_6636409, baseEnd_6636409] using wordTrace_append hprefix tailTrace_6636409
  have hstable : (prefixWord ++ tailWord_6636409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636409).length < 2 ^ (prefixWord ++ tailWord_6636409).sum := by decide
  have hdescent : baseEnd_6636409 < baseStart_6636409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636425 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 4, 1, 3]
def baseStart_6636425 : Nat := 118140960795 + 6636425 * 2 ^ 59
def prefixEnd_6636425 : Nat := 4983230072969 + 3 ^ 40 * 6636425 * 2
def baseEnd_6636425 : Nat := 3407675852514302690367143

theorem tailTrace_6636425 : CollatzResearch.WordTrace tailWord_6636425 prefixEnd_6636425 3407675852514302690367143 := by
  unfold tailWord_6636425
  simp only [CollatzResearch.WordTrace]
  refine ⟨242050304982373110999638729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161366869988248740666425819 242050304982373110999638729)
  ·
    refine ⟨181537728736779833249729047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242050304982373110999638729 181537728736779833249729047)
    ·
      refine ⟨272306593105169749874593571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181537728736779833249729047 272306593105169749874593571)
      ·
        refine ⟨408459889657754624811890357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272306593105169749874593571 408459889657754624811890357)
        ·
          refine ⟨38293114655414496076114721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 408459889657754624811890357 38293114655414496076114721)
          ·
            refine ⟨28719835991560872057086041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38293114655414496076114721 28719835991560872057086041)
            ·
              refine ⟨21539876993670654042814531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28719835991560872057086041 21539876993670654042814531)
              ·
                refine ⟨32309815490505981064221797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21539876993670654042814531 32309815490505981064221797)
                ·
                  refine ⟨6058090404469871449541587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32309815490505981064221797 6058090404469871449541587)
                  ·
                    refine ⟨9087135606704807174312381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6058090404469871449541587 9087135606704807174312381)
                    ·
                      refine ⟨3407675852514302690367143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9087135606704807174312381 3407675852514302690367143)
                      ·
                        rfl

theorem cell23_6636425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 1, 3].length) (baseStart_6636425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636425 prefixEnd_6636425 := by exact prefixLift 6636425
  have htrace : WordTrace (prefixWord ++ tailWord_6636425) baseStart_6636425 baseEnd_6636425 := by
    simpa [prefixWord, tailWord_6636425, baseEnd_6636425] using wordTrace_append hprefix tailTrace_6636425
  have hstable : (prefixWord ++ tailWord_6636425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636425).length < 2 ^ (prefixWord ++ tailWord_6636425).sum := by decide
  have hdescent : baseEnd_6636425 < baseStart_6636425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636441 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 1, 8]
def baseStart_6636441 : Nat := 118140960795 + 6636441 * 2 ^ 59
def prefixEnd_6636441 : Nat := 4983230072969 + 3 ^ 40 * 6636441 * 2
def baseEnd_6636441 : Nat := 1135894689401591542589023

theorem tailTrace_6636441 : CollatzResearch.WordTrace tailWord_6636441 prefixEnd_6636441 1135894689401591542589023 := by
  unfold tailWord_6636441
  simp only [CollatzResearch.WordTrace]
  refine ⟨242050888550315145732221177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161367259033543430488147451 242050888550315145732221177)
  ·
    refine ⟨181538166412736359299165883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242050888550315145732221177 181538166412736359299165883)
    ·
      refine ⟨272307249619104538948748825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181538166412736359299165883 272307249619104538948748825)
      ·
        refine ⟨204230437214328404211561619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272307249619104538948748825 204230437214328404211561619)
        ·
          refine ⟨306345655821492606317342429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204230437214328404211561619 306345655821492606317342429)
          ·
            refine ⟨114879620933059727369003411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306345655821492606317342429 114879620933059727369003411)
            ·
              refine ⟨172319431399589591053505117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114879620933059727369003411 172319431399589591053505117)
              ·
                refine ⟨64619786774846096645064419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172319431399589591053505117 64619786774846096645064419)
                ·
                  refine ⟨96929680162269144967596629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64619786774846096645064419 96929680162269144967596629)
                  ·
                    refine ⟨1135894689401591542589023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96929680162269144967596629 1135894689401591542589023)
                    ·
                      rfl

theorem cell23_6636441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 8].length) (baseStart_6636441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636441 prefixEnd_6636441 := by exact prefixLift 6636441
  have htrace : WordTrace (prefixWord ++ tailWord_6636441) baseStart_6636441 baseEnd_6636441 := by
    simpa [prefixWord, tailWord_6636441, baseEnd_6636441] using wordTrace_append hprefix tailTrace_6636441
  have hstable : (prefixWord ++ tailWord_6636441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636441).length < 2 ^ (prefixWord ++ tailWord_6636441).sum := by decide
  have hdescent : baseEnd_6636441 < baseStart_6636441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636469 : List Nat := [1, 3, 3, 2, 1, 1, 5, 1, 1, 3, 2]
def baseStart_6636469 : Nat := 118140960795 + 6636469 * 2 ^ 59
def prefixEnd_6636469 : Nat := 4983230072969 + 3 ^ 40 * 6636469 * 2
def baseEnd_6636469 : Nat := 3407698445663100518216941

theorem tailTrace_6636469 : CollatzResearch.WordTrace tailWord_6636469 prefixEnd_6636469 3407698445663100518216941 := by
  unfold tailWord_6636469
  simp only [CollatzResearch.WordTrace]
  refine ⟨242051909794213706514240461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161367939862809137676160307 242051909794213706514240461)
  ·
    refine ⟨90769466172830139942840173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242051909794213706514240461 90769466172830139942840173)
    ·
      refine ⟨34038549814811302478565065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90769466172830139942840173 34038549814811302478565065)
      ·
        refine ⟨25528912361108476858923799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34038549814811302478565065 25528912361108476858923799)
        ·
          refine ⟨38293368541662715288385699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25528912361108476858923799 38293368541662715288385699)
          ·
            refine ⟨57440052812494072932578549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38293368541662715288385699 57440052812494072932578549)
            ·
              refine ⟨5385004951171319337429239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57440052812494072932578549 5385004951171319337429239)
              ·
                refine ⟨8077507426756979006143859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5385004951171319337429239 8077507426756979006143859)
                ·
                  refine ⟨12116261140135468509215789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8077507426756979006143859 12116261140135468509215789)
                  ·
                    refine ⟨4543597927550800690955921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12116261140135468509215789 4543597927550800690955921)
                    ·
                      refine ⟨3407698445663100518216941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4543597927550800690955921 3407698445663100518216941)
                      ·
                        rfl

theorem cell23_6636469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_6636469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636469 prefixEnd_6636469 := by exact prefixLift 6636469
  have htrace : WordTrace (prefixWord ++ tailWord_6636469) baseStart_6636469 baseEnd_6636469 := by
    simpa [prefixWord, tailWord_6636469, baseEnd_6636469] using wordTrace_append hprefix tailTrace_6636469
  have hstable : (prefixWord ++ tailWord_6636469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636469).length < 2 ^ (prefixWord ++ tailWord_6636469).sum := by decide
  have hdescent : baseEnd_6636469 < baseStart_6636469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636522 : List Nat := [3, 1, 3, 1, 2, 3, 2, 3, 5]
def baseStart_6636522 : Nat := 118140960795 + 6636522 * 2 ^ 59
def prefixEnd_6636522 : Nat := 4983230072969 + 3 ^ 40 * 6636522 * 2
def baseEnd_6636522 : Nat := 378636184459754312317133

theorem tailTrace_6636522 : CollatzResearch.WordTrace tailWord_6636522 prefixEnd_6636522 378636184459754312317133 := by
  unfold tailWord_6636522
  simp only [CollatzResearch.WordTrace]
  refine ⟨60513460715755424141479955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161369228575347797710613213 60513460715755424141479955)
  ·
    refine ⟨90770191073633136212219933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60513460715755424141479955 90770191073633136212219933)
    ·
      refine ⟨34038821652612426079582475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90770191073633136212219933 34038821652612426079582475)
      ·
        refine ⟨51058232478918639119373713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34038821652612426079582475 51058232478918639119373713)
        ·
          refine ⟨38293674359188979339530285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51058232478918639119373713 38293674359188979339530285)
          ·
            refine ⟨14360127884695867252323857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38293674359188979339530285 14360127884695867252323857)
            ·
              refine ⟨10770095913521900439242893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14360127884695867252323857 10770095913521900439242893)
              ·
                refine ⟨4038785967570712664716085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10770095913521900439242893 4038785967570712664716085)
                ·
                  refine ⟨378636184459754312317133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4038785967570712664716085 378636184459754312317133)
                  ·
                    rfl

theorem cell23_6636522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 5].length) (baseStart_6636522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636522 prefixEnd_6636522 := by exact prefixLift 6636522
  have htrace : WordTrace (prefixWord ++ tailWord_6636522) baseStart_6636522 baseEnd_6636522 := by
    simpa [prefixWord, tailWord_6636522, baseEnd_6636522] using wordTrace_append hprefix tailTrace_6636522
  have hstable : (prefixWord ++ tailWord_6636522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636522).length < 2 ^ (prefixWord ++ tailWord_6636522).sum := by decide
  have hdescent : baseEnd_6636522 < baseStart_6636522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636575 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 3]
def baseStart_6636575 : Nat := 118140960795 + 6636575 * 2 ^ 59
def prefixEnd_6636575 : Nat := 4983230072969 + 3 ^ 40 * 6636575 * 2
def baseEnd_6636575 : Nat := 3407752874612477103491453

theorem tailTrace_6636575 : CollatzResearch.WordTrace tailWord_6636575 prefixEnd_6636575 3407752874612477103491453 := by
  unfold tailWord_6636575
  simp only [CollatzResearch.WordTrace]
  refine ⟨242055775931829686617599179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161370517287886457745066119 242055775931829686617599179)
  ·
    refine ⟨363083663897744529926398769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242055775931829686617599179 363083663897744529926398769)
    ·
      refine ⟨272312747923308397444799077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363083663897744529926398769 272312747923308397444799077)
      ·
        refine ⟨51058640235620324520899827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272312747923308397444799077 51058640235620324520899827)
        ·
          refine ⟨76587960353430486781349741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51058640235620324520899827 76587960353430486781349741)
          ·
            refine ⟨28720485132536432543006153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76587960353430486781349741 28720485132536432543006153)
            ·
              refine ⟨21540363849402324407254615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28720485132536432543006153 21540363849402324407254615)
              ·
                refine ⟨32310545774103486610881923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21540363849402324407254615 32310545774103486610881923)
                ·
                  refine ⟨48465818661155229916322885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32310545774103486610881923 48465818661155229916322885)
                  ·
                    refine ⟨9087340998966605609310541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48465818661155229916322885 9087340998966605609310541)
                    ·
                      refine ⟨3407752874612477103491453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9087340998966605609310541 3407752874612477103491453)
                      ·
                        rfl

theorem cell23_6636575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_6636575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636575 prefixEnd_6636575 := by exact prefixLift 6636575
  have htrace : WordTrace (prefixWord ++ tailWord_6636575) baseStart_6636575 baseEnd_6636575 := by
    simpa [prefixWord, tailWord_6636575, baseEnd_6636575] using wordTrace_append hprefix tailTrace_6636575
  have hstable : (prefixWord ++ tailWord_6636575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636575).length < 2 ^ (prefixWord ++ tailWord_6636575).sum := by decide
  have hdescent : baseEnd_6636575 < baseStart_6636575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636622 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3]
def baseStart_6636622 : Nat := 118140960795 + 6636622 * 2 ^ 59
def prefixEnd_6636622 : Nat := 4983230072969 + 3 ^ 40 * 6636622 * 2
def baseEnd_6636622 : Nat := 3407777008203238419603737

theorem tailTrace_6636622 : CollatzResearch.WordTrace tailWord_6636622 prefixEnd_6636622 3407777008203238419603737 := by
  unfold tailWord_6636622
  simp only [CollatzResearch.WordTrace]
  refine ⟨30257186270332426705570015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161371660108439609096373413 30257186270332426705570015)
  ·
    refine ⟨45385779405498640058355023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30257186270332426705570015 45385779405498640058355023)
    ·
      refine ⟨68078669108247960087532535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45385779405498640058355023 68078669108247960087532535)
      ·
        refine ⟨102118003662371940131298803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68078669108247960087532535 102118003662371940131298803)
        ·
          refine ⟨153177005493557910196948205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102118003662371940131298803 153177005493557910196948205)
          ·
            refine ⟨57441377060084216323855577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153177005493557910196948205 57441377060084216323855577)
            ·
              refine ⟨43081032795063162242891683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57441377060084216323855577 43081032795063162242891683)
              ·
                refine ⟨64621549192594743364337525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43081032795063162242891683 64621549192594743364337525)
                ·
                  refine ⟨6058270236805757190406643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64621549192594743364337525 6058270236805757190406643)
                  ·
                    refine ⟨9087405355208635785609965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6058270236805757190406643 9087405355208635785609965)
                    ·
                      refine ⟨3407777008203238419603737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9087405355208635785609965 3407777008203238419603737)
                      ·
                        rfl

theorem cell23_6636622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_6636622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636622 prefixEnd_6636622 := by exact prefixLift 6636622
  have htrace : WordTrace (prefixWord ++ tailWord_6636622) baseStart_6636622 baseEnd_6636622 := by
    simpa [prefixWord, tailWord_6636622, baseEnd_6636622] using wordTrace_append hprefix tailTrace_6636622
  have hstable : (prefixWord ++ tailWord_6636622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636622).length < 2 ^ (prefixWord ++ tailWord_6636622).sum := by decide
  have hdescent : baseEnd_6636622 < baseStart_6636622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636639 : List Nat := [1, 1, 2, 3, 1, 1, 4, 5, 1, 1, 3]
def baseStart_6636639 : Nat := 118140960795 + 6636639 * 2 ^ 59
def prefixEnd_6636639 : Nat := 4983230072969 + 3 ^ 40 * 6636639 * 2
def baseEnd_6636639 : Nat := 3407785737374364853091159

theorem tailTrace_6636639 : CollatzResearch.WordTrace tailWord_6636639 prefixEnd_6636639 3407785737374364853091159 := by
  unfold tailWord_6636639
  simp only [CollatzResearch.WordTrace]
  refine ⟨242058110203597825547928971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161372073469065217031952647 242058110203597825547928971)
  ·
    refine ⟨363087165305396738321893457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242058110203597825547928971 363087165305396738321893457)
    ·
      refine ⟨272315373979047553741420093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363087165305396738321893457 272315373979047553741420093)
      ·
        refine ⟨102118265242142832653032535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272315373979047553741420093 102118265242142832653032535)
        ·
          refine ⟨153177397863214248979548803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102118265242142832653032535 153177397863214248979548803)
          ·
            refine ⟨229766096794821373469323205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153177397863214248979548803 229766096794821373469323205)
            ·
              refine ⟨43081143149029007525498101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229766096794821373469323205 43081143149029007525498101)
              ·
                refine ⟨4038857170221469455515447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43081143149029007525498101 4038857170221469455515447)
                ·
                  refine ⟨6058285755332204183273171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4038857170221469455515447 6058285755332204183273171)
                  ·
                    refine ⟨9087428632998306274909757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6058285755332204183273171 9087428632998306274909757)
                    ·
                      refine ⟨3407785737374364853091159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9087428632998306274909757 3407785737374364853091159)
                      ·
                        rfl

theorem cell23_6636639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 1, 1, 3].length) (baseStart_6636639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636639 prefixEnd_6636639 := by exact prefixLift 6636639
  have htrace : WordTrace (prefixWord ++ tailWord_6636639) baseStart_6636639 baseEnd_6636639 := by
    simpa [prefixWord, tailWord_6636639, baseEnd_6636639] using wordTrace_append hprefix tailTrace_6636639
  have hstable : (prefixWord ++ tailWord_6636639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636639).length < 2 ^ (prefixWord ++ tailWord_6636639).sum := by decide
  have hdescent : baseEnd_6636639 < baseStart_6636639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636662 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_6636662 : Nat := 118140960795 + 6636662 * 2 ^ 59
def prefixEnd_6636662 : Nat := 4983230072969 + 3 ^ 40 * 6636662 * 2
def baseEnd_6636662 : Nat := 3407797547429418263103553

theorem tailTrace_6636662 : CollatzResearch.WordTrace tailWord_6636662 prefixEnd_6636662 3407797547429418263103553 := by
  unfold tailWord_6636662
  simp only [CollatzResearch.WordTrace]
  refine ⟨15128684317657156279751015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161372632721676333650677493 15128684317657156279751015)
  ·
    refine ⟨22693026476485734419626523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15128684317657156279751015 22693026476485734419626523)
    ·
      refine ⟨34039539714728601629439785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22693026476485734419626523 34039539714728601629439785)
      ·
        refine ⟨25529654786046451222079839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34039539714728601629439785 25529654786046451222079839)
        ·
          refine ⟨38294482179069676833119759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25529654786046451222079839 38294482179069676833119759)
          ·
            refine ⟨57441723268604515249679639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38294482179069676833119759 57441723268604515249679639)
            ·
              refine ⟨86162584902906772874519459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57441723268604515249679639 86162584902906772874519459)
              ·
                refine ⟨129243877354360159311779189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86162584902906772874519459 129243877354360159311779189)
                ·
                  refine ⟨12116613501971264935479299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129243877354360159311779189 12116613501971264935479299)
                  ·
                    refine ⟨18174920252956897403218949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12116613501971264935479299 18174920252956897403218949)
                    ·
                      refine ⟨3407797547429418263103553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18174920252956897403218949 3407797547429418263103553)
                      ·
                        rfl

theorem cell23_6636662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_6636662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636662 prefixEnd_6636662 := by exact prefixLift 6636662
  have htrace : WordTrace (prefixWord ++ tailWord_6636662) baseStart_6636662 baseEnd_6636662 := by
    simpa [prefixWord, tailWord_6636662, baseEnd_6636662] using wordTrace_append hprefix tailTrace_6636662
  have hstable : (prefixWord ++ tailWord_6636662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636662).length < 2 ^ (prefixWord ++ tailWord_6636662).sum := by decide
  have hdescent : baseEnd_6636662 < baseStart_6636662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636672 : List Nat := [2, 1, 1, 2, 1, 3, 4, 3, 2, 4]
def baseStart_6636672 : Nat := 118140960795 + 6636672 * 2 ^ 59
def prefixEnd_6636672 : Nat := 4983230072969 + 3 ^ 40 * 6636672 * 2
def baseEnd_6636672 : Nat := 1135934227411987741326169

theorem tailTrace_6636672 : CollatzResearch.WordTrace tailWord_6636672 prefixEnd_6636672 1135934227411987741326169 := by
  unfold tailWord_6636672
  simp only [CollatzResearch.WordTrace]
  refine ⟨121029656906239136091940135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161372875874985514789253513 121029656906239136091940135)
  ·
    refine ⟨181544485359358704137910203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121029656906239136091940135 181544485359358704137910203)
    ·
      refine ⟨272316728039038056206865305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181544485359358704137910203 272316728039038056206865305)
      ·
        refine ⟨204237546029278542155148979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272316728039038056206865305 204237546029278542155148979)
        ·
          refine ⟨306356319043917813232723469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204237546029278542155148979 306356319043917813232723469)
          ·
            refine ⟨114883619641469179962271301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306356319043917813232723469 114883619641469179962271301)
            ·
              refine ⟨21540678682775471242925869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114883619641469179962271301 21540678682775471242925869)
              ·
                refine ⟨8077754506040801716097201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21540678682775471242925869 8077754506040801716097201)
                ·
                  refine ⟨6058315879530601287072901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8077754506040801716097201 6058315879530601287072901)
                  ·
                    refine ⟨1135934227411987741326169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6058315879530601287072901 1135934227411987741326169)
                    ·
                      rfl

theorem cell23_6636672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 2, 4].length) (baseStart_6636672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636672 prefixEnd_6636672 := by exact prefixLift 6636672
  have htrace : WordTrace (prefixWord ++ tailWord_6636672) baseStart_6636672 baseEnd_6636672 := by
    simpa [prefixWord, tailWord_6636672, baseEnd_6636672] using wordTrace_append hprefix tailTrace_6636672
  have hstable : (prefixWord ++ tailWord_6636672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636672).length < 2 ^ (prefixWord ++ tailWord_6636672).sum := by decide
  have hdescent : baseEnd_6636672 < baseStart_6636672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636682 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 3, 2, 3]
def baseStart_6636682 : Nat := 118140960795 + 6636682 * 2 ^ 59
def prefixEnd_6636682 : Nat := 4983230072969 + 3 ^ 40 * 6636682 * 2
def baseEnd_6636682 : Nat := 3407807817042508184853461

theorem tailTrace_6636682 : CollatzResearch.WordTrace tailWord_6636682 prefixEnd_6636682 3407807817042508184853461 := by
  unfold tailWord_6636682
  simp only [CollatzResearch.WordTrace]
  refine ⟨60514919635610510972936075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161373119028294695927829533 60514919635610510972936075)
  ·
    refine ⟨90772379453415766459404113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60514919635610510972936075 90772379453415766459404113)
    ·
      refine ⟨68079284590061824844553085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90772379453415766459404113 68079284590061824844553085)
      ·
        refine ⟨25529731721273184316707407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68079284590061824844553085 25529731721273184316707407)
        ·
          refine ⟨38294597581909776475061111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25529731721273184316707407 38294597581909776475061111)
          ·
            refine ⟨57441896372864664712591667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38294597581909776475061111 57441896372864664712591667)
            ·
              refine ⟨86162844559296997068887501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57441896372864664712591667 86162844559296997068887501)
              ·
                refine ⟨32311066709736373900832813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86162844559296997068887501 32311066709736373900832813)
                ·
                  refine ⟨12116650016151140212812305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32311066709736373900832813 12116650016151140212812305)
                  ·
                    refine ⟨9087487512113355159609229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12116650016151140212812305 9087487512113355159609229)
                    ·
                      refine ⟨3407807817042508184853461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9087487512113355159609229 3407807817042508184853461)
                      ·
                        rfl

theorem cell23_6636682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_6636682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636682 prefixEnd_6636682 := by exact prefixLift 6636682
  have htrace : WordTrace (prefixWord ++ tailWord_6636682) baseStart_6636682 baseEnd_6636682 := by
    simpa [prefixWord, tailWord_6636682, baseEnd_6636682] using wordTrace_append hprefix tailTrace_6636682
  have hstable : (prefixWord ++ tailWord_6636682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636682).length < 2 ^ (prefixWord ++ tailWord_6636682).sum := by decide
  have hdescent : baseEnd_6636682 < baseStart_6636682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636696 : List Nat := [2, 1, 2, 4, 2, 3, 2, 1, 1, 1, 4]
def baseStart_6636696 : Nat := 118140960795 + 6636696 * 2 ^ 59
def prefixEnd_6636696 : Nat := 4983230072969 + 3 ^ 40 * 6636696 * 2
def baseEnd_6636696 : Nat := 3407815005771671130078397

theorem tailTrace_6636696 : CollatzResearch.WordTrace tailWord_6636696 prefixEnd_6636696 3407815005771671130078397 := by
  unfold tailWord_6636696
  simp only [CollatzResearch.WordTrace]
  refine ⟨121030094582195662141376971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161373459442927549521835961 121030094582195662141376971)
  ·
    refine ⟨181545141873293493212065457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121030094582195662141376971 181545141873293493212065457)
    ·
      refine ⟨136158856404970119909049093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181545141873293493212065457 136158856404970119909049093)
      ·
        refine ⟨25529785575931897482946705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136158856404970119909049093 25529785575931897482946705)
        ·
          refine ⟨19147339181948923112210029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25529785575931897482946705 19147339181948923112210029)
          ·
            refine ⟨7180252193230846167078761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19147339181948923112210029 7180252193230846167078761)
            ·
              refine ⟨5385189144923134625309071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7180252193230846167078761 5385189144923134625309071)
              ·
                refine ⟨8077783717384701937963607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5385189144923134625309071 8077783717384701937963607)
                ·
                  refine ⟨12116675576077052906945411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8077783717384701937963607 12116675576077052906945411)
                  ·
                    refine ⟨18175013364115579360418117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12116675576077052906945411 18175013364115579360418117)
                    ·
                      refine ⟨3407815005771671130078397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18175013364115579360418117 3407815005771671130078397)
                      ·
                        rfl

theorem cell23_6636696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_6636696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636696 prefixEnd_6636696 := by exact prefixLift 6636696
  have htrace : WordTrace (prefixWord ++ tailWord_6636696) baseStart_6636696 baseEnd_6636696 := by
    simpa [prefixWord, tailWord_6636696, baseEnd_6636696] using wordTrace_append hprefix tailTrace_6636696
  have hstable : (prefixWord ++ tailWord_6636696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636696).length < 2 ^ (prefixWord ++ tailWord_6636696).sum := by decide
  have hdescent : baseEnd_6636696 < baseStart_6636696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636702 : List Nat := [4, 3, 1, 1, 2, 2, 10]
def baseStart_6636702 : Nat := 118140960795 + 6636702 * 2 ^ 59
def prefixEnd_6636702 : Nat := 4983230072969 + 3 ^ 40 * 6636702 * 2
def baseEnd_6636702 : Nat := 42071828230316026007449

theorem tailTrace_6636702 : CollatzResearch.WordTrace tailWord_6636702 prefixEnd_6636702 42071828230316026007449 := by
  unfold tailWord_6636702
  simp only [CollatzResearch.WordTrace]
  refine ⟨30257551000296198413434045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161373605334913058204981573 30257551000296198413434045)
  ·
    refine ⟨11346581625111074405037767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30257551000296198413434045 11346581625111074405037767)
    ·
      refine ⟨17019872437666611607556651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11346581625111074405037767 17019872437666611607556651)
      ·
        refine ⟨25529808656499917411334977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17019872437666611607556651 25529808656499917411334977)
        ·
          refine ⟨19147356492374938058501233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25529808656499917411334977 19147356492374938058501233)
          ·
            refine ⟨14360517369281203543875925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19147356492374938058501233 14360517369281203543875925)
            ·
              refine ⟨42071828230316026007449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14360517369281203543875925 42071828230316026007449)
              ·
                rfl

theorem cell23_6636702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 10].length) (baseStart_6636702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636702 prefixEnd_6636702 := by exact prefixLift 6636702
  have htrace : WordTrace (prefixWord ++ tailWord_6636702) baseStart_6636702 baseEnd_6636702 := by
    simpa [prefixWord, tailWord_6636702, baseEnd_6636702] using wordTrace_append hprefix tailTrace_6636702
  have hstable : (prefixWord ++ tailWord_6636702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636702).length < 2 ^ (prefixWord ++ tailWord_6636702).sum := by decide
  have hdescent : baseEnd_6636702 < baseStart_6636702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636726 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_6636726 : Nat := 118140960795 + 6636726 * 2 ^ 59
def prefixEnd_6636726 : Nat := 4983230072969 + 3 ^ 40 * 6636726 * 2
def baseEnd_6636726 : Nat := 3407830410191306012703259

theorem tailTrace_6636726 : CollatzResearch.WordTrace tailWord_6636726 prefixEnd_6636726 3407830410191306012703259 := by
  unfold tailWord_6636726
  simp only [CollatzResearch.WordTrace]
  refine ⟨15128830209642664962896627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161374188902855092937564021 15128830209642664962896627)
  ·
    refine ⟨22693245314463997444344941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15128830209642664962896627 22693245314463997444344941)
    ·
      refine ⟨8509966992923999041629353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22693245314463997444344941 8509966992923999041629353)
      ·
        refine ⟨6382475244692999281222015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8509966992923999041629353 6382475244692999281222015)
        ·
          refine ⟨9573712867039498921833023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6382475244692999281222015 9573712867039498921833023)
          ·
            refine ⟨14360569300559248382749535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9573712867039498921833023 14360569300559248382749535)
            ·
              refine ⟨21540853950838872574124303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14360569300559248382749535 21540853950838872574124303)
              ·
                refine ⟨32311280926258308861186455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21540853950838872574124303 32311280926258308861186455)
                ·
                  refine ⟨48466921389387463291779683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32311280926258308861186455 48466921389387463291779683)
                  ·
                    refine ⟨72700382084081194937669525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48466921389387463291779683 72700382084081194937669525)
                    ·
                      refine ⟨3407830410191306012703259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72700382084081194937669525 3407830410191306012703259)
                      ·
                        rfl

theorem cell23_6636726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_6636726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636726 prefixEnd_6636726 := by exact prefixLift 6636726
  have htrace : WordTrace (prefixWord ++ tailWord_6636726) baseStart_6636726 baseEnd_6636726 := by
    simpa [prefixWord, tailWord_6636726, baseEnd_6636726] using wordTrace_append hprefix tailTrace_6636726
  have hstable : (prefixWord ++ tailWord_6636726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636726).length < 2 ^ (prefixWord ++ tailWord_6636726).sum := by decide
  have hdescent : baseEnd_6636726 < baseStart_6636726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636729 : List Nat := [1, 2, 1, 4, 1, 5, 1, 1, 1, 3, 3]
def baseStart_6636729 : Nat := 118140960795 + 6636729 * 2 ^ 59
def prefixEnd_6636729 : Nat := 4983230072969 + 3 ^ 40 * 6636729 * 2
def baseEnd_6636729 : Nat := 3407831950633269500965745

theorem tailTrace_6636729 : CollatzResearch.WordTrace tailWord_6636729 prefixEnd_6636729 3407831950633269500965745 := by
  unfold tailWord_6636729
  simp only [CollatzResearch.WordTrace]
  refine ⟨242061392773271770918705241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161374261848847847279136827 242061392773271770918705241)
  ·
    refine ⟨181546044579953828189028931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242061392773271770918705241 181546044579953828189028931)
    ·
      refine ⟨272319066869930742283543397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181546044579953828189028931 272319066869930742283543397)
      ·
        refine ⟨51059825038112014178164387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272319066869930742283543397 51059825038112014178164387)
        ·
          refine ⟨76589737557168021267246581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51059825038112014178164387 76589737557168021267246581)
          ·
            refine ⟨7180287895984501993804367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76589737557168021267246581 7180287895984501993804367)
            ·
              refine ⟨10770431843976752990706551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7180287895984501993804367 10770431843976752990706551)
              ·
                refine ⟨16155647765965129486059827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10770431843976752990706551 16155647765965129486059827)
                ·
                  refine ⟨24233471648947694229089741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16155647765965129486059827 24233471648947694229089741)
                  ·
                    refine ⟨9087551868355385335908653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24233471648947694229089741 9087551868355385335908653)
                    ·
                      refine ⟨3407831950633269500965745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9087551868355385335908653 3407831950633269500965745)
                      ·
                        rfl

theorem cell23_6636729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_6636729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636729 prefixEnd_6636729 := by exact prefixLift 6636729
  have htrace : WordTrace (prefixWord ++ tailWord_6636729) baseStart_6636729 baseEnd_6636729 := by
    simpa [prefixWord, tailWord_6636729, baseEnd_6636729] using wordTrace_append hprefix tailTrace_6636729
  have hstable : (prefixWord ++ tailWord_6636729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636729).length < 2 ^ (prefixWord ++ tailWord_6636729).sum := by decide
  have hdescent : baseEnd_6636729 < baseStart_6636729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636735 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 4]
def baseStart_6636735 : Nat := 118140960795 + 6636735 * 2 ^ 59
def prefixEnd_6636735 : Nat := 4983230072969 + 3 ^ 40 * 6636735 * 2
def baseEnd_6636735 : Nat := 3407835031517196477490717

theorem tailTrace_6636735 : CollatzResearch.WordTrace tailWord_6636735 prefixEnd_6636735 3407835031517196477490717 := by
  unfold tailWord_6636735
  simp only [CollatzResearch.WordTrace]
  refine ⟨242061611611250033943423659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161374407740833355962282439 242061611611250033943423659)
  ·
    refine ⟨363092417416875050915135489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242061611611250033943423659 363092417416875050915135489)
    ·
      refine ⟨272319313062656288186351617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363092417416875050915135489 272319313062656288186351617)
      ·
        refine ⟨204239484796992216139763713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272319313062656288186351617 204239484796992216139763713)
        ·
          refine ⟨153179613597744162104822785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204239484796992216139763713 153179613597744162104822785)
          ·
            refine ⟨114884710198308121578617089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153179613597744162104822785 114884710198308121578617089)
            ·
              refine ⟨86163532648731091183962817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114884710198308121578617089 86163532648731091183962817)
              ·
                refine ⟨64622649486548318387972113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86163532648731091183962817 64622649486548318387972113)
                ·
                  refine ⟨48466987114911238790979085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64622649486548318387972113 48466987114911238790979085)
                  ·
                    refine ⟨18175120168091714546617157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48466987114911238790979085 18175120168091714546617157)
                    ·
                      refine ⟨3407835031517196477490717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18175120168091714546617157 3407835031517196477490717)
                      ·
                        rfl

theorem cell23_6636735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_6636735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636735 prefixEnd_6636735 := by exact prefixLift 6636735
  have htrace : WordTrace (prefixWord ++ tailWord_6636735) baseStart_6636735 baseEnd_6636735 := by
    simpa [prefixWord, tailWord_6636735, baseEnd_6636735] using wordTrace_append hprefix tailTrace_6636735
  have hstable : (prefixWord ++ tailWord_6636735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636735).length < 2 ^ (prefixWord ++ tailWord_6636735).sum := by decide
  have hdescent : baseEnd_6636735 < baseStart_6636735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636755 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 5]
def baseStart_6636755 : Nat := 118140960795 + 6636755 * 2 ^ 59
def prefixEnd_6636755 : Nat := 4983230072969 + 3 ^ 40 * 6636755 * 2
def baseEnd_6636755 : Nat := 3407845301130286399240625

theorem tailTrace_6636755 : CollatzResearch.WordTrace tailWord_6636755 prefixEnd_6636755 3407845301130286399240625 := by
  unfold tailWord_6636755
  simp only [CollatzResearch.WordTrace]
  refine ⟨242062341071177577359151719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161374894047451718239434479 242062341071177577359151719)
  ·
    refine ⟨363093511606766366038727579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242062341071177577359151719 363093511606766366038727579)
    ·
      refine ⟨544640267410149549058091369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363093511606766366038727579 544640267410149549058091369)
      ·
        refine ⟨408480200557612161793568527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 544640267410149549058091369 408480200557612161793568527)
        ·
          refine ⟨612720300836418242690352791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408480200557612161793568527 612720300836418242690352791)
          ·
            refine ⟨919080451254627364035529187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612720300836418242690352791 919080451254627364035529187)
            ·
              refine ⟨1378620676881941046053293781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 919080451254627364035529187 1378620676881941046053293781)
              ·
                refine ⟨32311422114420493266874073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1378620676881941046053293781 32311422114420493266874073)
                ·
                  refine ⟨24233566585815369950155555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32311422114420493266874073 24233566585815369950155555)
                  ·
                    refine ⟨36350349878723054925233333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24233566585815369950155555 36350349878723054925233333)
                    ·
                      refine ⟨3407845301130286399240625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36350349878723054925233333 3407845301130286399240625)
                      ·
                        rfl

theorem cell23_6636755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 5].length) (baseStart_6636755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636755 prefixEnd_6636755 := by exact prefixLift 6636755
  have htrace : WordTrace (prefixWord ++ tailWord_6636755) baseStart_6636755 baseEnd_6636755 := by
    simpa [prefixWord, tailWord_6636755, baseEnd_6636755] using wordTrace_append hprefix tailTrace_6636755
  have hstable : (prefixWord ++ tailWord_6636755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636755).length < 2 ^ (prefixWord ++ tailWord_6636755).sum := by decide
  have hdescent : baseEnd_6636755 < baseStart_6636755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636782 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_6636782 : Nat := 118140960795 + 6636782 * 2 ^ 59
def prefixEnd_6636782 : Nat := 4983230072969 + 3 ^ 40 * 6636782 * 2
def baseEnd_6636782 : Nat := 3407859165107957793603001

theorem tailTrace_6636782 : CollatzResearch.WordTrace tailWord_6636782 prefixEnd_6636782 3407859165107957793603001 := by
  unfold tailWord_6636782
  simp only [CollatzResearch.WordTrace]
  refine ⟨30257915730259970121298075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161375550561386507313589733 30257915730259970121298075)
  ·
    refine ⟨45386873595389955181947113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30257915730259970121298075 45386873595389955181947113)
    ·
      refine ⟨34040155196542466386460335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45386873595389955181947113 34040155196542466386460335)
      ·
        refine ⟨51060232794813699579690503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34040155196542466386460335 51060232794813699579690503)
        ·
          refine ⟨76590349192220549369535755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51060232794813699579690503 76590349192220549369535755)
          ·
            refine ⟨114885523788330824054303633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76590349192220549369535755 114885523788330824054303633)
            ·
              refine ⟨86164142841248118040727725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114885523788330824054303633 86164142841248118040727725)
              ·
                refine ⟨32311553565468044265272897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86164142841248118040727725 32311553565468044265272897)
                ·
                  refine ⟨24233665174101033198954673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32311553565468044265272897 24233665174101033198954673)
                  ·
                    refine ⟨18175248880575774899216005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24233665174101033198954673 18175248880575774899216005)
                    ·
                      refine ⟨3407859165107957793603001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18175248880575774899216005 3407859165107957793603001)
                      ·
                        rfl

theorem cell23_6636782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_6636782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636782 prefixEnd_6636782 := by exact prefixLift 6636782
  have htrace : WordTrace (prefixWord ++ tailWord_6636782) baseStart_6636782 baseEnd_6636782 := by
    simpa [prefixWord, tailWord_6636782, baseEnd_6636782] using wordTrace_append hprefix tailTrace_6636782
  have hstable : (prefixWord ++ tailWord_6636782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636782).length < 2 ^ (prefixWord ++ tailWord_6636782).sum := by decide
  have hdescent : baseEnd_6636782 < baseStart_6636782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636826 : List Nat := [3, 1, 1, 3, 3, 1, 4, 2, 5]
def baseStart_6636826 : Nat := 118140960795 + 6636826 * 2 ^ 59
def prefixEnd_6636826 : Nat := 4983230072969 + 3 ^ 40 * 6636826 * 2
def baseEnd_6636826 : Nat := 378653528695195069050311

theorem tailTrace_6636826 : CollatzResearch.WordTrace tailWord_6636826 prefixEnd_6636826 378653528695195069050311 := by
  unfold tailWord_6636826
  simp only [CollatzResearch.WordTrace]
  refine ⟨60516232663480089121246583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161376620435946904323324221 60516232663480089121246583)
  ·
    refine ⟨90774348995220133681869875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60516232663480089121246583 90774348995220133681869875)
    ·
      refine ⟨136161523492830200522804813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90774348995220133681869875 136161523492830200522804813)
      ·
        refine ⟨51060571309811325196051805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136161523492830200522804813 51060571309811325196051805)
        ·
          refine ⟨19147714241179246948519427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51060571309811325196051805 19147714241179246948519427)
          ·
            refine ⟨28721571361768870422779141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19147714241179246948519427 28721571361768870422779141)
            ·
              refine ⟨5385294630331663204271089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28721571361768870422779141 5385294630331663204271089)
              ·
                refine ⟨4038970972748747403203317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5385294630331663204271089 4038970972748747403203317)
                ·
                  refine ⟨378653528695195069050311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4038970972748747403203317 378653528695195069050311)
                  ·
                    rfl

theorem cell23_6636826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 5].length) (baseStart_6636826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636826 prefixEnd_6636826 := by exact prefixLift 6636826
  have htrace : WordTrace (prefixWord ++ tailWord_6636826) baseStart_6636826 baseEnd_6636826 := by
    simpa [prefixWord, tailWord_6636826, baseEnd_6636826] using wordTrace_append hprefix tailTrace_6636826
  have hstable : (prefixWord ++ tailWord_6636826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636826).length < 2 ^ (prefixWord ++ tailWord_6636826).sum := by decide
  have hdescent : baseEnd_6636826 < baseStart_6636826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636919 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 1, 5, 2]
def baseStart_6636919 : Nat := 118140960795 + 6636919 * 2 ^ 59
def prefixEnd_6636919 : Nat := 4983230072969 + 3 ^ 40 * 6636919 * 2
def baseEnd_6636919 : Nat := 3407929511957623757589871

theorem tailTrace_6636919 : CollatzResearch.WordTrace tailWord_6636919 prefixEnd_6636919 3407929511957623757589871 := by
  unfold tailWord_6636919
  simp only [CollatzResearch.WordTrace]
  refine ⟨242068322642583433368121811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161378881761722288912081207 242068322642583433368121811)
  ·
    refine ⟨363102483963875150052182717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242068322642583433368121811 363102483963875150052182717)
    ·
      refine ⟨136163431486453181269568519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363102483963875150052182717 136163431486453181269568519)
      ·
        refine ⟨204245147229679771904352779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136163431486453181269568519 204245147229679771904352779)
        ·
          refine ⟨306367720844519657856529169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204245147229679771904352779 306367720844519657856529169)
          ·
            refine ⟨229775790633389743392396877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306367720844519657856529169 229775790633389743392396877)
            ·
              refine ⟨86165921487521153772148829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229775790633389743392396877 86165921487521153772148829)
              ·
                refine ⟨32312220557820432664555811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86165921487521153772148829 32312220557820432664555811)
                ·
                  refine ⟨48468330836730648996833717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32312220557820432664555811 48468330836730648996833717)
                  ·
                    refine ⟨4543906015943498343453161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48468330836730648996833717 4543906015943498343453161)
                    ·
                      refine ⟨3407929511957623757589871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4543906015943498343453161 3407929511957623757589871)
                      ·
                        rfl

theorem cell23_6636919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 5, 2].length) (baseStart_6636919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636919 prefixEnd_6636919 := by exact prefixLift 6636919
  have htrace : WordTrace (prefixWord ++ tailWord_6636919) baseStart_6636919 baseEnd_6636919 := by
    simpa [prefixWord, tailWord_6636919, baseEnd_6636919] using wordTrace_append hprefix tailTrace_6636919
  have hstable : (prefixWord ++ tailWord_6636919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636919).length < 2 ^ (prefixWord ++ tailWord_6636919).sum := by decide
  have hdescent : baseEnd_6636919 < baseStart_6636919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636936 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 4, 3, 2]
def baseStart_6636936 : Nat := 118140960795 + 6636936 * 2 ^ 59
def prefixEnd_6636936 : Nat := 4983230072969 + 3 ^ 40 * 6636936 * 2
def baseEnd_6636936 : Nat := 3407938241128750191077293

theorem tailTrace_6636936 : CollatzResearch.WordTrace tailWord_6636936 prefixEnd_6636936 3407938241128750191077293 := by
  unfold tailWord_6636936
  simp only [CollatzResearch.WordTrace]
  refine ⟨121034471341760922635745331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161379295122347896847660441 121034471341760922635745331)
  ·
    refine ⟨181551707012641383953617997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121034471341760922635745331 181551707012641383953617997)
    ·
      refine ⟨68081890129740518982606749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181551707012641383953617997 68081890129740518982606749)
      ·
        refine ⟨25530708798652694618477531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68081890129740518982606749 25530708798652694618477531)
        ·
          refine ⟨38296063197979041927716297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25530708798652694618477531 38296063197979041927716297)
          ·
            refine ⟨28722047398484281445787223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38296063197979041927716297 28722047398484281445787223)
            ·
              refine ⟨43083071097726422168680835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28722047398484281445787223 43083071097726422168680835)
              ·
                refine ⟨64624606646589633253021253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43083071097726422168680835 64624606646589633253021253)
                ·
                  refine ⟨12117113746235556234941485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64624606646589633253021253 12117113746235556234941485)
                  ·
                    refine ⟨4543917654838333588103057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12117113746235556234941485 4543917654838333588103057)
                    ·
                      refine ⟨3407938241128750191077293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4543917654838333588103057 3407938241128750191077293)
                      ·
                        rfl

theorem cell23_6636936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_6636936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636936 prefixEnd_6636936 := by exact prefixLift 6636936
  have htrace : WordTrace (prefixWord ++ tailWord_6636936) baseStart_6636936 baseEnd_6636936 := by
    simpa [prefixWord, tailWord_6636936, baseEnd_6636936] using wordTrace_append hprefix tailTrace_6636936
  have hstable : (prefixWord ++ tailWord_6636936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636936).length < 2 ^ (prefixWord ++ tailWord_6636936).sum := by decide
  have hdescent : baseEnd_6636936 < baseStart_6636936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636972 : List Nat := [2, 2, 1, 1, 1, 1, 6, 9]
def baseStart_6636972 : Nat := 118140960795 + 6636972 * 2 ^ 59
def prefixEnd_6636972 : Nat := 4983230072969 + 3 ^ 40 * 6636972 * 2
def baseEnd_6636972 : Nat := 126220619497493038897301

theorem tailTrace_6636972 : CollatzResearch.WordTrace tailWord_6636972 prefixEnd_6636972 126220619497493038897301 := by
  unfold tailWord_6636972
  simp only [CollatzResearch.WordTrace]
  refine ⟨121035127855695711709900585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161380170474260948946534113 121035127855695711709900585)
  ·
    refine ⟨90776345891771783782425439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121035127855695711709900585 90776345891771783782425439)
    ·
      refine ⟨136164518837657675673638159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90776345891771783782425439 136164518837657675673638159)
      ·
        refine ⟨204246778256486513510457239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136164518837657675673638159 204246778256486513510457239)
        ·
          refine ⟨306370167384729770265685859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204246778256486513510457239 306370167384729770265685859)
          ·
            refine ⟨459555251077094655398528789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306370167384729770265685859 459555251077094655398528789)
            ·
              refine ⟨21541652394238811971806037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 459555251077094655398528789 21541652394238811971806037)
              ·
                refine ⟨126220619497493038897301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21541652394238811971806037 126220619497493038897301)
                ·
                  rfl

theorem cell23_6636972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 9].length) (baseStart_6636972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636972 prefixEnd_6636972 := by exact prefixLift 6636972
  have htrace : WordTrace (prefixWord ++ tailWord_6636972) baseStart_6636972 baseEnd_6636972 := by
    simpa [prefixWord, tailWord_6636972, baseEnd_6636972] using wordTrace_append hprefix tailTrace_6636972
  have hstable : (prefixWord ++ tailWord_6636972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636972).length < 2 ^ (prefixWord ++ tailWord_6636972).sum := by decide
  have hdescent : baseEnd_6636972 < baseStart_6636972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6636999 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 3]
def baseStart_6636999 : Nat := 118140960795 + 6636999 * 2 ^ 59
def prefixEnd_6636999 : Nat := 4983230072969 + 3 ^ 40 * 6636999 * 2
def baseEnd_6636999 : Nat := 3407970590409983444589503

theorem tailTrace_6636999 : CollatzResearch.WordTrace tailWord_6636999 prefixEnd_6636999 3407970590409983444589503 := by
  unfold tailWord_6636999
  simp only [CollatzResearch.WordTrace]
  refine ⟨242071240482293607031034051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161380826988195738020689367 242071240482293607031034051)
  ·
    refine ⟨363106860723440410546551077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242071240482293607031034051 363106860723440410546551077)
    ·
      refine ⟨68082536385645076977478327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 363106860723440410546551077 68082536385645076977478327)
      ·
        refine ⟨102123804578467615466217491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68082536385645076977478327 102123804578467615466217491)
        ·
          refine ⟨153185706867701423199326237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102123804578467615466217491 153185706867701423199326237)
          ·
            refine ⟨57444640075388033699747339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153185706867701423199326237 57444640075388033699747339)
            ·
              refine ⟨86166960113082050549621009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57444640075388033699747339 86166960113082050549621009)
              ·
                refine ⟨64625220084811537912215757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86166960113082050549621009 64625220084811537912215757)
                ·
                  refine ⟨24234457531804326717080909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64625220084811537912215757 24234457531804326717080909)
                  ·
                    refine ⟨9087921574426622518905341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24234457531804326717080909 9087921574426622518905341)
                    ·
                      refine ⟨3407970590409983444589503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9087921574426622518905341 3407970590409983444589503)
                      ·
                        rfl

theorem cell23_6636999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_6636999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6636999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6636999 prefixEnd_6636999 := by exact prefixLift 6636999
  have htrace : WordTrace (prefixWord ++ tailWord_6636999) baseStart_6636999 baseEnd_6636999 := by
    simpa [prefixWord, tailWord_6636999, baseEnd_6636999] using wordTrace_append hprefix tailTrace_6636999
  have hstable : (prefixWord ++ tailWord_6636999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6636999).length < 2 ^ (prefixWord ++ tailWord_6636999).sum := by decide
  have hdescent : baseEnd_6636999 < baseStart_6636999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6636999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637000 : List Nat := [2, 1, 3, 1, 3, 1, 3, 4, 1, 2, 2]
def baseStart_6637000 : Nat := 118140960795 + 6637000 * 2 ^ 59
def prefixEnd_6637000 : Nat := 4983230072969 + 3 ^ 40 * 6637000 * 2
def baseEnd_6637000 : Nat := 3407971103890637940676999

theorem tailTrace_6637000 : CollatzResearch.WordTrace tailWord_6637000 prefixEnd_6637000 3407971103890637940676999 := by
  unfold tailWord_6637000
  simp only [CollatzResearch.WordTrace]
  refine ⟨121035638477644992100910227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161380851303526656134546969 121035638477644992100910227)
  ·
    refine ⟨181553457716467488151365341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121035638477644992100910227 181553457716467488151365341)
    ·
      refine ⟨68082546643675308056762003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181553457716467488151365341 68082546643675308056762003)
      ·
        refine ⟨102123819965512962085143005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68082546643675308056762003 102123819965512962085143005)
        ·
          refine ⟨38296432487067360781928627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102123819965512962085143005 38296432487067360781928627)
          ·
            refine ⟨57444648730601041172892941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38296432487067360781928627 57444648730601041172892941)
            ·
              refine ⟨21541743273975390439834853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57444648730601041172892941 21541743273975390439834853)
              ·
                refine ⟨4039076863870385707469035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21541743273975390439834853 4039076863870385707469035)
                ·
                  refine ⟨6058615295805578561203553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4039076863870385707469035 6058615295805578561203553)
                  ·
                    refine ⟨4543961471854183920902665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6058615295805578561203553 4543961471854183920902665)
                    ·
                      refine ⟨3407971103890637940676999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4543961471854183920902665 3407971103890637940676999)
                      ·
                        rfl

theorem cell23_6637000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 1, 2, 2].length) (baseStart_6637000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637000 prefixEnd_6637000 := by exact prefixLift 6637000
  have htrace : WordTrace (prefixWord ++ tailWord_6637000) baseStart_6637000 baseEnd_6637000 := by
    simpa [prefixWord, tailWord_6637000, baseEnd_6637000] using wordTrace_append hprefix tailTrace_6637000
  have hstable : (prefixWord ++ tailWord_6637000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637000).length < 2 ^ (prefixWord ++ tailWord_6637000).sum := by decide
  have hdescent : baseEnd_6637000 < baseStart_6637000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637037 : List Nat := [1, 5, 1, 3, 2, 2, 2, 1, 1, 2, 3]
def baseStart_6637037 : Nat := 118140960795 + 6637037 * 2 ^ 59
def prefixEnd_6637037 : Nat := 4983230072969 + 3 ^ 40 * 6637037 * 2
def baseEnd_6637037 : Nat := 3407990102674854295914329

theorem tailTrace_6637037 : CollatzResearch.WordTrace tailWord_6637037 prefixEnd_6637037 3407990102674854295914329 := by
  unfold tailWord_6637037
  simp only [CollatzResearch.WordTrace]
  refine ⟨242072626456155939520917365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161381750970770626347278243 242072626456155939520917365)
  ·
    refine ⟨22694308730264619330086003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242072626456155939520917365 22694308730264619330086003)
    ·
      refine ⟨34041463095396928995129005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22694308730264619330086003 34041463095396928995129005)
      ·
        refine ⟨12765548660773848373173377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34041463095396928995129005 12765548660773848373173377)
        ·
          refine ⟨9574161495580386279880033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12765548660773848373173377 9574161495580386279880033)
          ·
            refine ⟨7180621121685289709910025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9574161495580386279880033 7180621121685289709910025)
            ·
              refine ⟨5385465841263967282432519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7180621121685289709910025 5385465841263967282432519)
              ·
                refine ⟨8078198761895950923648779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5385465841263967282432519 8078198761895950923648779)
                ·
                  refine ⟨12117298142843926385473169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8078198761895950923648779 12117298142843926385473169)
                  ·
                    refine ⟨9087973607132944789104877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12117298142843926385473169 9087973607132944789104877)
                    ·
                      refine ⟨3407990102674854295914329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9087973607132944789104877 3407990102674854295914329)
                      ·
                        rfl

theorem cell23_6637037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_6637037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637037 prefixEnd_6637037 := by exact prefixLift 6637037
  have htrace : WordTrace (prefixWord ++ tailWord_6637037) baseStart_6637037 baseEnd_6637037 := by
    simpa [prefixWord, tailWord_6637037, baseEnd_6637037] using wordTrace_append hprefix tailTrace_6637037
  have hstable : (prefixWord ++ tailWord_6637037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637037).length < 2 ^ (prefixWord ++ tailWord_6637037).sum := by decide
  have hdescent : baseEnd_6637037 < baseStart_6637037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637059 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 3]
def baseStart_6637059 : Nat := 118140960795 + 6637059 * 2 ^ 59
def prefixEnd_6637059 : Nat := 4983230072969 + 3 ^ 40 * 6637059 * 2
def baseEnd_6637059 : Nat := 3408001399249253209839227

theorem tailTrace_6637059 : CollatzResearch.WordTrace tailWord_6637059 prefixEnd_6637059 3408001399249253209839227 := by
  unfold tailWord_6637059
  simp only [CollatzResearch.WordTrace]
  refine ⟨242073428862076237278218231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161382285908050824852145487 242073428862076237278218231)
  ·
    refine ⟨363110143293114355917327347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242073428862076237278218231 363110143293114355917327347)
    ·
      refine ⟨544665214939671533875991021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363110143293114355917327347 544665214939671533875991021)
      ·
        refine ⟨204249455602376825203496633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 544665214939671533875991021 204249455602376825203496633)
        ·
          refine ⟨153187091701782618902622475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204249455602376825203496633 153187091701782618902622475)
          ·
            refine ⟨229780637552673928353933713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153187091701782618902622475 229780637552673928353933713)
            ·
              refine ⟨172335478164505446265450285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229780637552673928353933713 172335478164505446265450285)
              ·
                refine ⟨64625804311689542349543857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172335478164505446265450285 64625804311689542349543857)
                ·
                  refine ⟨48469353233767156762157893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64625804311689542349543857 48469353233767156762157893)
                  ·
                    refine ⟨9088003731331341892904605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48469353233767156762157893 9088003731331341892904605)
                    ·
                      refine ⟨3408001399249253209839227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9088003731331341892904605 3408001399249253209839227)
                      ·
                        rfl

theorem cell23_6637059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 3].length) (baseStart_6637059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637059 prefixEnd_6637059 := by exact prefixLift 6637059
  have htrace : WordTrace (prefixWord ++ tailWord_6637059) baseStart_6637059 baseEnd_6637059 := by
    simpa [prefixWord, tailWord_6637059, baseEnd_6637059] using wordTrace_append hprefix tailTrace_6637059
  have hstable : (prefixWord ++ tailWord_6637059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637059).length < 2 ^ (prefixWord ++ tailWord_6637059).sum := by decide
  have hdescent : baseEnd_6637059 < baseStart_6637059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637119 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 7]
def baseStart_6637119 : Nat := 118140960795 + 6637119 * 2 ^ 59
def prefixEnd_6637119 : Nat := 4983230072969 + 3 ^ 40 * 6637119 * 2
def baseEnd_6637119 : Nat := 3408032208088522975088951

theorem tailTrace_6637119 : CollatzResearch.WordTrace tailWord_6637119 prefixEnd_6637119 3408032208088522975088951 := by
  unfold tailWord_6637119
  simp only [CollatzResearch.WordTrace]
  refine ⟨242075617241858867525402411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161383744827905911683601607 242075617241858867525402411)
  ·
    refine ⟨363113425862788301288103617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242075617241858867525402411 363113425862788301288103617)
    ·
      refine ⟨272335069397091225966077713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363113425862788301288103617 272335069397091225966077713)
      ·
        refine ⟨204251302047818419474558285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272335069397091225966077713 204251302047818419474558285)
        ·
          refine ⟨76594238267931907302959357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204251302047818419474558285 76594238267931907302959357)
          ·
            refine ⟨28722839350474465238609759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76594238267931907302959357 28722839350474465238609759)
            ·
              refine ⟨43084259025711697857914639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28722839350474465238609759 43084259025711697857914639)
              ·
                refine ⟨64626388538567546786871959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43084259025711697857914639 64626388538567546786871959)
                ·
                  refine ⟨96939582807851320180307939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64626388538567546786871959 96939582807851320180307939)
                  ·
                    refine ⟨145409374211776980270461909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96939582807851320180307939 145409374211776980270461909)
                    ·
                      refine ⟨3408032208088522975088951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145409374211776980270461909 3408032208088522975088951)
                      ·
                        rfl

theorem cell23_6637119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_6637119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637119 prefixEnd_6637119 := by exact prefixLift 6637119
  have htrace : WordTrace (prefixWord ++ tailWord_6637119) baseStart_6637119 baseEnd_6637119 := by
    simpa [prefixWord, tailWord_6637119, baseEnd_6637119] using wordTrace_append hprefix tailTrace_6637119
  have hstable : (prefixWord ++ tailWord_6637119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637119).length < 2 ^ (prefixWord ++ tailWord_6637119).sum := by decide
  have hdescent : baseEnd_6637119 < baseStart_6637119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637129 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 3, 3, 4]
def baseStart_6637129 : Nat := 118140960795 + 6637129 * 2 ^ 59
def prefixEnd_6637129 : Nat := 4983230072969 + 3 ^ 40 * 6637129 * 2
def baseEnd_6637129 : Nat := 3408037342895067935963905

theorem tailTrace_6637129 : CollatzResearch.WordTrace tailWord_6637129 prefixEnd_6637129 3408037342895067935963905 := by
  unfold tailWord_6637129
  simp only [CollatzResearch.WordTrace]
  refine ⟨242075981971822639233266441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161383987981215092822177627 242075981971822639233266441)
  ·
    refine ⟨181556986478866979424949831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242075981971822639233266441 181556986478866979424949831)
    ·
      refine ⟨272335479718300469137424747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181556986478866979424949831 272335479718300469137424747)
      ·
        refine ⟨408503219577450703706137121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272335479718300469137424747 408503219577450703706137121)
        ·
          refine ⟨306377414683088027779602841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408503219577450703706137121 306377414683088027779602841)
          ·
            refine ⟨229783061012316020834702131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306377414683088027779602841 229783061012316020834702131)
            ·
              refine ⟨344674591518474031252053197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229783061012316020834702131 344674591518474031252053197)
              ·
                refine ⟨129252971819427761719519949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344674591518474031252053197 129252971819427761719519949)
                ·
                  refine ⟨48469864432285410644819981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129252971819427761719519949 48469864432285410644819981)
                  ·
                    refine ⟨18176199162107028991807493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48469864432285410644819981 18176199162107028991807493)
                    ·
                      refine ⟨3408037342895067935963905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18176199162107028991807493 3408037342895067935963905)
                      ·
                        rfl

theorem cell23_6637129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 3, 4].length) (baseStart_6637129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637129 prefixEnd_6637129 := by exact prefixLift 6637129
  have htrace : WordTrace (prefixWord ++ tailWord_6637129) baseStart_6637129 baseEnd_6637129 := by
    simpa [prefixWord, tailWord_6637129, baseEnd_6637129] using wordTrace_append hprefix tailTrace_6637129
  have hstable : (prefixWord ++ tailWord_6637129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637129).length < 2 ^ (prefixWord ++ tailWord_6637129).sum := by decide
  have hdescent : baseEnd_6637129 < baseStart_6637129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637169 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 8]
def baseStart_6637169 : Nat := 118140960795 + 6637169 * 2 ^ 59
def prefixEnd_6637169 : Nat := 4983230072969 + 3 ^ 40 * 6637169 * 2
def baseEnd_6637169 : Nat := 378673098013471975495969

theorem tailTrace_6637169 : CollatzResearch.WordTrace tailWord_6637169 prefixEnd_6637169 378673098013471975495969 := by
  unfold tailWord_6637169
  simp only [CollatzResearch.WordTrace]
  refine ⟨242077440891677726064722561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161384960594451817376481707 242077440891677726064722561)
  ·
    refine ⟨181558080668758294548541921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242077440891677726064722561 181558080668758294548541921)
    ·
      refine ⟨136168560501568720911406441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181558080668758294548541921 136168560501568720911406441)
      ·
        refine ⟨102126420376176540683554831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136168560501568720911406441 102126420376176540683554831)
        ·
          refine ⟨153189630564264811025332247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102126420376176540683554831 153189630564264811025332247)
          ·
            refine ⟨229784445846397216537998371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153189630564264811025332247 229784445846397216537998371)
            ·
              refine ⟨344676668769595824806997557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229784445846397216537998371 344676668769595824806997557)
              ·
                refine ⟨32313437697149608575656021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 344676668769595824806997557 32313437697149608575656021)
                ·
                  refine ⟨378673098013471975495969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32313437697149608575656021 378673098013471975495969)
                  ·
                    rfl

theorem cell23_6637169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 8].length) (baseStart_6637169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637169 prefixEnd_6637169 := by exact prefixLift 6637169
  have htrace : WordTrace (prefixWord ++ tailWord_6637169) baseStart_6637169 baseEnd_6637169 := by
    simpa [prefixWord, tailWord_6637169, baseEnd_6637169] using wordTrace_append hprefix tailTrace_6637169
  have hstable : (prefixWord ++ tailWord_6637169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637169).length < 2 ^ (prefixWord ++ tailWord_6637169).sum := by decide
  have hdescent : baseEnd_6637169 < baseStart_6637169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637213 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 7, 1, 3]
def baseStart_6637213 : Nat := 118140960795 + 6637213 * 2 ^ 59
def prefixEnd_6637213 : Nat := 4983230072969 + 3 ^ 40 * 6637213 * 2
def baseEnd_6637213 : Nat := 3408080475270045607313519

theorem tailTrace_6637213 : CollatzResearch.WordTrace tailWord_6637213 prefixEnd_6637213 3408080475270045607313519 := by
  unfold tailWord_6637213
  simp only [CollatzResearch.WordTrace]
  refine ⟨242079045703518321579324293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161386030469012214386216195 242079045703518321579324293)
  ·
    refine ⟨45389821069409685296123305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242079045703518321579324293 45389821069409685296123305)
    ·
      refine ⟨34042365802057263972092479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45389821069409685296123305 34042365802057263972092479)
      ·
        refine ⟨51063548703085895958138719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34042365802057263972092479 51063548703085895958138719)
        ·
          refine ⟨76595323054628843937208079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51063548703085895958138719 76595323054628843937208079)
          ·
            refine ⟨114892984581943265905812119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76595323054628843937208079 114892984581943265905812119)
            ·
              refine ⟨172339476872914898858718179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114892984581943265905812119 172339476872914898858718179)
              ·
                refine ⟨258509215309372348288077269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172339476872914898858718179 258509215309372348288077269)
                ·
                  refine ⟨6058809733813414413001811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 258509215309372348288077269 6058809733813414413001811)
                  ·
                    refine ⟨9088214600720121619502717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6058809733813414413001811 9088214600720121619502717)
                    ·
                      refine ⟨3408080475270045607313519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9088214600720121619502717 3408080475270045607313519)
                      ·
                        rfl

theorem cell23_6637213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_6637213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637213 prefixEnd_6637213 := by exact prefixLift 6637213
  have htrace : WordTrace (prefixWord ++ tailWord_6637213) baseStart_6637213 baseEnd_6637213 := by
    simpa [prefixWord, tailWord_6637213, baseEnd_6637213] using wordTrace_append hprefix tailTrace_6637213
  have hstable : (prefixWord ++ tailWord_6637213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637213).length < 2 ^ (prefixWord ++ tailWord_6637213).sum := by decide
  have hdescent : baseEnd_6637213 < baseStart_6637213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637224 : List Nat := [2, 1, 7, 1, 1, 1, 2, 1, 3, 4]
def baseStart_6637224 : Nat := 118140960795 + 6637224 * 2 ^ 59
def prefixEnd_6637224 : Nat := 4983230072969 + 3 ^ 40 * 6637224 * 2
def baseEnd_6637224 : Nat := 1136028707852415021425323

theorem tailTrace_6637224 : CollatzResearch.WordTrace tailWord_6637224 prefixEnd_6637224 1136028707852415021425323 := by
  unfold tailWord_6637224
  simp only [CollatzResearch.WordTrace]
  refine ⟨121039723453239235228987363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161386297937652313638649817 121039723453239235228987363)
  ·
    refine ⟨181559585179858852843481045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121039723453239235228987363 181559585179858852843481045)
    ·
      refine ⟨4255302777652941863519087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 181559585179858852843481045 4255302777652941863519087)
      ·
        refine ⟨6382954166479412795278631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4255302777652941863519087 6382954166479412795278631)
        ·
          refine ⟨9574431249719119192917947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6382954166479412795278631 9574431249719119192917947)
          ·
            refine ⟨14361646874578678789376921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9574431249719119192917947 14361646874578678789376921)
            ·
              refine ⟨10771235155934009092032691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14361646874578678789376921 10771235155934009092032691)
              ·
                refine ⟨16156852733901013638049037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10771235155934009092032691 16156852733901013638049037)
                ·
                  refine ⟨6058819775212880114268389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16156852733901013638049037 6058819775212880114268389)
                  ·
                    refine ⟨1136028707852415021425323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6058819775212880114268389 1136028707852415021425323)
                    ·
                      rfl

theorem cell23_6637224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_6637224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637224 prefixEnd_6637224 := by exact prefixLift 6637224
  have htrace : WordTrace (prefixWord ++ tailWord_6637224) baseStart_6637224 baseEnd_6637224 := by
    simpa [prefixWord, tailWord_6637224, baseEnd_6637224] using wordTrace_append hprefix tailTrace_6637224
  have hstable : (prefixWord ++ tailWord_6637224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637224).length < 2 ^ (prefixWord ++ tailWord_6637224).sum := by decide
  have hdescent : baseEnd_6637224 < baseStart_6637224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637256 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 3, 1, 5]
def baseStart_6637256 : Nat := 118140960795 + 6637256 * 2 ^ 59
def prefixEnd_6637256 : Nat := 4983230072969 + 3 ^ 40 * 6637256 * 2
def baseEnd_6637256 : Nat := 3408102554938188939075821

theorem tailTrace_6637256 : CollatzResearch.WordTrace tailWord_6637256 prefixEnd_6637256 3408102554938188939075821 := by
  unfold tailWord_6637256
  simp only [CollatzResearch.WordTrace]
  refine ⟨121040307021181269961569811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161387076028241693282093081 121040307021181269961569811)
  ·
    refine ⟨181560460531771904942354717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121040307021181269961569811 181560460531771904942354717)
    ·
      refine ⟨68085172699414464353383019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181560460531771904942354717 68085172699414464353383019)
      ·
        refine ⟨102127759049121696530074529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68085172699414464353383019 102127759049121696530074529)
        ·
          refine ⟨76595819286841272397555897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102127759049121696530074529 76595819286841272397555897)
          ·
            refine ⟨57446864465130954298166923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76595819286841272397555897 57446864465130954298166923)
            ·
              refine ⟨86170296697696431447250385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57446864465130954298166923 86170296697696431447250385)
              ·
                refine ⟨64627722523272323585437789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86170296697696431447250385 64627722523272323585437789)
                ·
                  refine ⟨24235395946227121344539171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64627722523272323585437789 24235395946227121344539171)
                  ·
                    refine ⟨36353093919340682016808757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24235395946227121344539171 36353093919340682016808757)
                    ·
                      refine ⟨3408102554938188939075821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36353093919340682016808757 3408102554938188939075821)
                      ·
                        rfl

theorem cell23_6637256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_6637256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637256 prefixEnd_6637256 := by exact prefixLift 6637256
  have htrace : WordTrace (prefixWord ++ tailWord_6637256) baseStart_6637256 baseEnd_6637256 := by
    simpa [prefixWord, tailWord_6637256, baseEnd_6637256] using wordTrace_append hprefix tailTrace_6637256
  have hstable : (prefixWord ++ tailWord_6637256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637256).length < 2 ^ (prefixWord ++ tailWord_6637256).sum := by decide
  have hdescent : baseEnd_6637256 < baseStart_6637256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637273 : List Nat := [1, 2, 1, 2, 3, 4, 2, 1, 1, 1, 5]
def baseStart_6637273 : Nat := 118140960795 + 6637273 * 2 ^ 59
def prefixEnd_6637273 : Nat := 4983230072969 + 3 ^ 40 * 6637273 * 2
def baseEnd_6637273 : Nat := 3408111284109315372563243

theorem tailTrace_6637273 : CollatzResearch.WordTrace tailWord_6637273 prefixEnd_6637273 3408111284109315372563243 := by
  unfold tailWord_6637273
  simp only [CollatzResearch.WordTrace]
  refine ⟨242081234083300951826508473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161387489388867301217672315 242081234083300951826508473)
  ·
    refine ⟨181560925562475713869881355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242081234083300951826508473 181560925562475713869881355)
    ·
      refine ⟨272341388343713570804822033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181560925562475713869881355 272341388343713570804822033)
      ·
        refine ⟨204256041257785178103616525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272341388343713570804822033 204256041257785178103616525)
        ·
          refine ⟨76596015471669441788856197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204256041257785178103616525 76596015471669441788856197)
          ·
            refine ⟨14361752900938020335410537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76596015471669441788856197 14361752900938020335410537)
            ·
              refine ⟨10771314675703515251557903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14361752900938020335410537 10771314675703515251557903)
              ·
                refine ⟨16156972013555272877336855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10771314675703515251557903 16156972013555272877336855)
                ·
                  refine ⟨24235458020332909316005283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16156972013555272877336855 24235458020332909316005283)
                  ·
                    refine ⟨36353187030499363974007925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24235458020332909316005283 36353187030499363974007925)
                    ·
                      refine ⟨3408111284109315372563243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36353187030499363974007925 3408111284109315372563243)
                      ·
                        rfl

theorem cell23_6637273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 1, 5].length) (baseStart_6637273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637273 prefixEnd_6637273 := by exact prefixLift 6637273
  have htrace : WordTrace (prefixWord ++ tailWord_6637273) baseStart_6637273 baseEnd_6637273 := by
    simpa [prefixWord, tailWord_6637273, baseEnd_6637273] using wordTrace_append hprefix tailTrace_6637273
  have hstable : (prefixWord ++ tailWord_6637273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637273).length < 2 ^ (prefixWord ++ tailWord_6637273).sum := by decide
  have hdescent : baseEnd_6637273 < baseStart_6637273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637293 : List Nat := [1, 5, 1, 2, 1, 3, 2, 8]
def baseStart_6637293 : Nat := 118140960795 + 6637293 * 2 ^ 59
def prefixEnd_6637293 : Nat := 4983230072969 + 3 ^ 40 * 6637293 * 2
def baseEnd_6637293 : Nat := 126226724211940936826413

theorem tailTrace_6637293 : CollatzResearch.WordTrace tailWord_6637293 prefixEnd_6637293 126226724211940936826413 := by
  unfold tailWord_6637293
  simp only [CollatzResearch.WordTrace]
  refine ⟨242081963543228495242236533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161387975695485663494824355 242081963543228495242236533)
  ·
    refine ⟨22695184082177671428959675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242081963543228495242236533 22695184082177671428959675)
    ·
      refine ⟨34042776123266507143439513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22695184082177671428959675 34042776123266507143439513)
      ·
        refine ⟨25532082092449880357579635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34042776123266507143439513 25532082092449880357579635)
        ·
          refine ⟨38298123138674820536369453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25532082092449880357579635 38298123138674820536369453)
          ·
            refine ⟨14361796177003057701138545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38298123138674820536369453 14361796177003057701138545)
            ·
              refine ⟨10771347132752293275853909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14361796177003057701138545 10771347132752293275853909)
              ·
                refine ⟨126226724211940936826413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10771347132752293275853909 126226724211940936826413)
                ·
                  rfl

theorem cell23_6637293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 8].length) (baseStart_6637293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637293 prefixEnd_6637293 := by exact prefixLift 6637293
  have htrace : WordTrace (prefixWord ++ tailWord_6637293) baseStart_6637293 baseEnd_6637293 := by
    simpa [prefixWord, tailWord_6637293, baseEnd_6637293] using wordTrace_append hprefix tailTrace_6637293
  have hstable : (prefixWord ++ tailWord_6637293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637293).length < 2 ^ (prefixWord ++ tailWord_6637293).sum := by decide
  have hdescent : baseEnd_6637293 < baseStart_6637293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637297 : List Nat := [1, 2, 2, 2, 2, 5, 2, 1, 2, 4]
def baseStart_6637297 : Nat := 118140960795 + 6637297 * 2 ^ 59
def prefixEnd_6637297 : Nat := 4983230072969 + 3 ^ 40 * 6637297 * 2
def baseEnd_6637297 : Nat := 1136041202548341092887711

theorem tailTrace_6637297 : CollatzResearch.WordTrace tailWord_6637297 prefixEnd_6637297 1136041202548341092887711 := by
  unfold tailWord_6637297
  simp only [CollatzResearch.WordTrace]
  refine ⟨242082109435214003925382145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161388072956809335950254763 242082109435214003925382145)
  ·
    refine ⟨181561582076410502944036609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242082109435214003925382145 181561582076410502944036609)
    ·
      refine ⟨136171186557307877208027457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181561582076410502944036609 136171186557307877208027457)
      ·
        refine ⟨102128389917980907906020593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136171186557307877208027457 102128389917980907906020593)
        ·
          refine ⟨76596292438485680929515445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102128389917980907906020593 76596292438485680929515445)
          ·
            refine ⟨7180902416108032587142073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76596292438485680929515445 7180902416108032587142073)
            ·
              refine ⟨5385676812081024440356555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7180902416108032587142073 5385676812081024440356555)
              ·
                refine ⟨8078515218121536660534833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5385676812081024440356555 8078515218121536660534833)
                ·
                  refine ⟨6058886413591152495401125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8078515218121536660534833 6058886413591152495401125)
                  ·
                    refine ⟨1136041202548341092887711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6058886413591152495401125 1136041202548341092887711)
                    ·
                      rfl

theorem cell23_6637297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 2, 4].length) (baseStart_6637297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637297 prefixEnd_6637297 := by exact prefixLift 6637297
  have htrace : WordTrace (prefixWord ++ tailWord_6637297) baseStart_6637297 baseEnd_6637297 := by
    simpa [prefixWord, tailWord_6637297, baseEnd_6637297] using wordTrace_append hprefix tailTrace_6637297
  have hstable : (prefixWord ++ tailWord_6637297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637297).length < 2 ^ (prefixWord ++ tailWord_6637297).sum := by decide
  have hdescent : baseEnd_6637297 < baseStart_6637297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637332 : List Nat := [2, 4, 4, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_6637332 : Nat := 118140960795 + 6637332 * 2 ^ 59
def prefixEnd_6637332 : Nat := 4983230072969 + 3 ^ 40 * 6637332 * 2
def baseEnd_6637332 : Nat := 3408141579467930641725473

theorem tailTrace_6637332 : CollatzResearch.WordTrace tailWord_6637332 prefixEnd_6637332 3408141579467930641725473 := by
  unfold tailWord_6637332
  simp only [CollatzResearch.WordTrace]
  refine ⟨121041692995043602451453125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161388923993391469935270833 121041692995043602451453125)
  ·
    refine ⟨22695317436570675459647461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121041692995043602451453125 22695317436570675459647461)
    ·
      refine ⟨4255372019357001648683899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22695317436570675459647461 4255372019357001648683899)
      ·
        refine ⟨6383058029035502473025849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4255372019357001648683899 6383058029035502473025849)
        ·
          refine ⟨4787293521776626854769387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6383058029035502473025849 4787293521776626854769387)
          ·
            refine ⟨7180940282664940282154081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4787293521776626854769387 7180940282664940282154081)
            ·
              refine ⟨5385705211998705211615561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7180940282664940282154081 5385705211998705211615561)
              ·
                refine ⟨4039278908999028908711671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5385705211998705211615561 4039278908999028908711671)
                ·
                  refine ⟨6058918363498543363067507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4039278908999028908711671 6058918363498543363067507)
                  ·
                    refine ⟨9088377545247815044601261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6058918363498543363067507 9088377545247815044601261)
                    ·
                      refine ⟨3408141579467930641725473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9088377545247815044601261 3408141579467930641725473)
                      ·
                        rfl

theorem cell23_6637332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_6637332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637332 prefixEnd_6637332 := by exact prefixLift 6637332
  have htrace : WordTrace (prefixWord ++ tailWord_6637332) baseStart_6637332 baseEnd_6637332 := by
    simpa [prefixWord, tailWord_6637332, baseEnd_6637332] using wordTrace_append hprefix tailTrace_6637332
  have hstable : (prefixWord ++ tailWord_6637332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637332).length < 2 ^ (prefixWord ++ tailWord_6637332).sum := by decide
  have hdescent : baseEnd_6637332 < baseStart_6637332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637360 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 8, 2, 2]
def baseStart_6637360 : Nat := 118140960795 + 6637360 * 2 ^ 59
def prefixEnd_6637360 : Nat := 4983230072969 + 3 ^ 40 * 6637360 * 2
def baseEnd_6637360 : Nat := 3408155956926256532175343

theorem tailTrace_6637360 : CollatzResearch.WordTrace tailWord_6637360 prefixEnd_6637360 3408155956926256532175343 := by
  unfold tailWord_6637360
  simp only [CollatzResearch.WordTrace]
  refine ⟨121042203616992882842462767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161389604822657177123283689 121042203616992882842462767)
  ·
    refine ⟨181563305425489324263694151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121042203616992882842462767 181563305425489324263694151)
    ·
      refine ⟨272344958138233986395541227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181563305425489324263694151 272344958138233986395541227)
      ·
        refine ⟨408517437207350979593311841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272344958138233986395541227 408517437207350979593311841)
        ·
          refine ⟨306388077905513234694983881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408517437207350979593311841 306388077905513234694983881)
          ·
            refine ⟨229791058429134926021237911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306388077905513234694983881 229791058429134926021237911)
            ·
              refine ⟨344686587643702389031856867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229791058429134926021237911 344686587643702389031856867)
              ·
                refine ⟨517029881465553583547785301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344686587643702389031856867 517029881465553583547785301)
                ·
                  refine ⟨6058943923424456057200609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 517029881465553583547785301 6058943923424456057200609)
                  ·
                    refine ⟨4544207942568342042900457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6058943923424456057200609 4544207942568342042900457)
                    ·
                      refine ⟨3408155956926256532175343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4544207942568342042900457 3408155956926256532175343)
                      ·
                        rfl

theorem cell23_6637360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 8, 2, 2].length) (baseStart_6637360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637360 prefixEnd_6637360 := by exact prefixLift 6637360
  have htrace : WordTrace (prefixWord ++ tailWord_6637360) baseStart_6637360 baseEnd_6637360 := by
    simpa [prefixWord, tailWord_6637360, baseEnd_6637360] using wordTrace_append hprefix tailTrace_6637360
  have hstable : (prefixWord ++ tailWord_6637360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637360).length < 2 ^ (prefixWord ++ tailWord_6637360).sum := by decide
  have hdescent : baseEnd_6637360 < baseStart_6637360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637376 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 7]
def baseStart_6637376 : Nat := 118140960795 + 6637376 * 2 ^ 59
def prefixEnd_6637376 : Nat := 4983230072969 + 3 ^ 40 * 6637376 * 2
def baseEnd_6637376 : Nat := 3408164172616728469575269

theorem tailTrace_6637376 : CollatzResearch.WordTrace tailWord_6637376 prefixEnd_6637376 3408164172616728469575269 := by
  unfold tailWord_6637376
  simp only [CollatzResearch.WordTrace]
  refine ⟨121042495400963900208753991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161389993867951866945005321 121042495400963900208753991)
  ·
    refine ⟨181563743101445850313130987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121042495400963900208753991 181563743101445850313130987)
    ·
      refine ⟨272345614652168775469696481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181563743101445850313130987 272345614652168775469696481)
      ·
        refine ⟨204259210989126581602272361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272345614652168775469696481 204259210989126581602272361)
        ·
          refine ⟨153194408241844936201704271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204259210989126581602272361 153194408241844936201704271)
          ·
            refine ⟨229791612362767404302556407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153194408241844936201704271 229791612362767404302556407)
            ·
              refine ⟨344687418544151106453834611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229791612362767404302556407 344687418544151106453834611)
              ·
                refine ⟨517031127816226659680751917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344687418544151106453834611 517031127816226659680751917)
                ·
                  refine ⟨193886672931084997380281969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517031127816226659680751917 193886672931084997380281969)
                  ·
                    refine ⟨145415004698313748035211477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 193886672931084997380281969 145415004698313748035211477)
                    ·
                      refine ⟨3408164172616728469575269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145415004698313748035211477 3408164172616728469575269)
                      ·
                        rfl

theorem cell23_6637376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_6637376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637376 prefixEnd_6637376 := by exact prefixLift 6637376
  have htrace : WordTrace (prefixWord ++ tailWord_6637376) baseStart_6637376 baseEnd_6637376 := by
    simpa [prefixWord, tailWord_6637376, baseEnd_6637376] using wordTrace_append hprefix tailTrace_6637376
  have hstable : (prefixWord ++ tailWord_6637376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637376).length < 2 ^ (prefixWord ++ tailWord_6637376).sum := by decide
  have hdescent : baseEnd_6637376 < baseStart_6637376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637394 : List Nat := [3, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2]
def baseStart_6637394 : Nat := 118140960795 + 6637394 * 2 ^ 59
def prefixEnd_6637394 : Nat := 4983230072969 + 3 ^ 40 * 6637394 * 2
def baseEnd_6637394 : Nat := 3408173415268509399150187

theorem tailTrace_6637394 : CollatzResearch.WordTrace tailWord_6637394 prefixEnd_6637394 3408173415268509399150187 := by
  unfold tailWord_6637394
  simp only [CollatzResearch.WordTrace]
  refine ⟨60521411828965647372915809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161390431543908392994442157 60521411828965647372915809)
  ·
    refine ⟨45391058871724235529686857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60521411828965647372915809 45391058871724235529686857)
    ·
      refine ⟨34043294153793176647265143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45391058871724235529686857 34043294153793176647265143)
      ·
        refine ⟨51064941230689764970897715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34043294153793176647265143 51064941230689764970897715)
        ·
          refine ⟨76597411846034647456346573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51064941230689764970897715 76597411846034647456346573)
          ·
            refine ⟨28724029442262992796129965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76597411846034647456346573 28724029442262992796129965)
            ·
              refine ⟨10771511040848622298548737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28724029442262992796129965 10771511040848622298548737)
              ·
                refine ⟨8078633280636466723911553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10771511040848622298548737 8078633280636466723911553)
                ·
                  refine ⟨6058974960477350042933665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8078633280636466723911553 6058974960477350042933665)
                  ·
                    refine ⟨4544231220358012532200249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6058974960477350042933665 4544231220358012532200249)
                    ·
                      refine ⟨3408173415268509399150187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4544231220358012532200249 3408173415268509399150187)
                      ·
                        rfl

theorem cell23_6637394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_6637394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637394 prefixEnd_6637394 := by exact prefixLift 6637394
  have htrace : WordTrace (prefixWord ++ tailWord_6637394) baseStart_6637394 baseEnd_6637394 := by
    simpa [prefixWord, tailWord_6637394, baseEnd_6637394] using wordTrace_append hprefix tailTrace_6637394
  have hstable : (prefixWord ++ tailWord_6637394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637394).length < 2 ^ (prefixWord ++ tailWord_6637394).sum := by decide
  have hdescent : baseEnd_6637394 < baseStart_6637394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637411 : List Nat := [1, 1, 1, 5, 4, 1, 3, 1, 2, 2, 2]
def baseStart_6637411 : Nat := 118140960795 + 6637411 * 2 ^ 59
def prefixEnd_6637411 : Nat := 4983230072969 + 3 ^ 40 * 6637411 * 2
def baseEnd_6637411 : Nat := 3408182144439635832637609

theorem tailTrace_6637411 : CollatzResearch.WordTrace tailWord_6637411 prefixEnd_6637411 3408182144439635832637609 := by
  unfold tailWord_6637411
  simp only [CollatzResearch.WordTrace]
  refine ⟨242086267356801001395032087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161390844904534000930021391 242086267356801001395032087)
  ·
    refine ⟨363129401035201502092548131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242086267356801001395032087 363129401035201502092548131)
    ·
      refine ⟨544694101552802253138822197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363129401035201502092548131 544694101552802253138822197)
      ·
        refine ⟨51065072020575211231764581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 544694101552802253138822197 51065072020575211231764581)
        ·
          refine ⟨9574701003857852105955859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51065072020575211231764581 9574701003857852105955859)
          ·
            refine ⟨14362051505786778158933789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9574701003857852105955859 14362051505786778158933789)
            ·
              refine ⟨5385769314670041809600171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14362051505786778158933789 5385769314670041809600171)
              ·
                refine ⟨8078653972005062714400257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5385769314670041809600171 8078653972005062714400257)
                ·
                  refine ⟨6058990479003797035800193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8078653972005062714400257 6058990479003797035800193)
                  ·
                    refine ⟨4544242859252847776850145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6058990479003797035800193 4544242859252847776850145)
                    ·
                      refine ⟨3408182144439635832637609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4544242859252847776850145 3408182144439635832637609)
                      ·
                        rfl

theorem cell23_6637411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_6637411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637411 prefixEnd_6637411 := by exact prefixLift 6637411
  have htrace : WordTrace (prefixWord ++ tailWord_6637411) baseStart_6637411 baseEnd_6637411 := by
    simpa [prefixWord, tailWord_6637411, baseEnd_6637411] using wordTrace_append hprefix tailTrace_6637411
  have hstable : (prefixWord ++ tailWord_6637411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637411).length < 2 ^ (prefixWord ++ tailWord_6637411).sum := by decide
  have hdescent : baseEnd_6637411 < baseStart_6637411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637433 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 1, 3, 4]
def baseStart_6637433 : Nat := 118140960795 + 6637433 * 2 ^ 59
def prefixEnd_6637433 : Nat := 4983230072969 + 3 ^ 40 * 6637433 * 2
def baseEnd_6637433 : Nat := 3408193441014034746562507

theorem tailTrace_6637433 : CollatzResearch.WordTrace tailWord_6637433 prefixEnd_6637433 3408193441014034746562507 := by
  unfold tailWord_6637433
  simp only [CollatzResearch.WordTrace]
  refine ⟨242087069762721299152332953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161391379841814199434888635 242087069762721299152332953)
  ·
    refine ⟨181565302322040974364249715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242087069762721299152332953 181565302322040974364249715)
    ·
      refine ⟨272347953483061461546374573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181565302322040974364249715 272347953483061461546374573)
      ·
        refine ⟨102130482556148048079890465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272347953483061461546374573 102130482556148048079890465)
        ·
          refine ⟨76597861917111036059917849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102130482556148048079890465 76597861917111036059917849)
          ·
            refine ⟨57448396437833277044938387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76597861917111036059917849 57448396437833277044938387)
            ·
              refine ⟨86172594656749915567407581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57448396437833277044938387 86172594656749915567407581)
              ·
                refine ⟨32314722996281218337777843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86172594656749915567407581 32314722996281218337777843)
                ·
                  refine ⟨48472084494421827506666765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32314722996281218337777843 48472084494421827506666765)
                  ·
                    refine ⟨18177031685408185315000037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48472084494421827506666765 18177031685408185315000037)
                    ·
                      refine ⟨3408193441014034746562507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18177031685408185315000037 3408193441014034746562507)
                      ·
                        rfl

theorem cell23_6637433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_6637433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637433 prefixEnd_6637433 := by exact prefixLift 6637433
  have htrace : WordTrace (prefixWord ++ tailWord_6637433) baseStart_6637433 baseEnd_6637433 := by
    simpa [prefixWord, tailWord_6637433, baseEnd_6637433] using wordTrace_append hprefix tailTrace_6637433
  have hstable : (prefixWord ++ tailWord_6637433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637433).length < 2 ^ (prefixWord ++ tailWord_6637433).sum := by decide
  have hdescent : baseEnd_6637433 < baseStart_6637433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637462 : List Nat := [5, 3, 1, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_6637462 : Nat := 118140960795 + 6637462 * 2 ^ 59
def prefixEnd_6637462 : Nat := 4983230072969 + 3 ^ 40 * 6637462 * 2
def baseEnd_6637462 : Nat := 3408208331953015133099875

theorem tailTrace_6637462 : CollatzResearch.WordTrace tailWord_6637462 prefixEnd_6637462 3408208331953015133099875 := by
  unfold tailWord_6637462
  simp only [CollatzResearch.WordTrace]
  refine ⟨15130507967476014819071165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161392084986410824736759093 15130507967476014819071165)
  ·
    refine ⟨5673940487803505557151687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15130507967476014819071165 5673940487803505557151687)
    ·
      refine ⟨8510910731705258335727531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5673940487803505557151687 8510910731705258335727531)
      ·
        refine ⟨12766366097557887503591297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8510910731705258335727531 12766366097557887503591297)
        ·
          refine ⟨9574774573168415627693473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12766366097557887503591297 9574774573168415627693473)
          ·
            refine ⟨7181080929876311720770105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9574774573168415627693473 7181080929876311720770105)
            ·
              refine ⟨5385810697407233790577579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7181080929876311720770105 5385810697407233790577579)
              ·
                refine ⟨8078716046110850685866369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5385810697407233790577579 8078716046110850685866369)
                ·
                  refine ⟨6059037034583138014399777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8078716046110850685866369 6059037034583138014399777)
                  ·
                    refine ⟨4544277775937353510799833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6059037034583138014399777 4544277775937353510799833)
                    ·
                      refine ⟨3408208331953015133099875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4544277775937353510799833 3408208331953015133099875)
                      ·
                        rfl

theorem cell23_6637462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_6637462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637462 prefixEnd_6637462 := by exact prefixLift 6637462
  have htrace : WordTrace (prefixWord ++ tailWord_6637462) baseStart_6637462 baseEnd_6637462 := by
    simpa [prefixWord, tailWord_6637462, baseEnd_6637462] using wordTrace_append hprefix tailTrace_6637462
  have hstable : (prefixWord ++ tailWord_6637462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637462).length < 2 ^ (prefixWord ++ tailWord_6637462).sum := by decide
  have hdescent : baseEnd_6637462 < baseStart_6637462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637538 : List Nat := [3, 3, 3, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_6637538 : Nat := 118140960795 + 6637538 * 2 ^ 59
def prefixEnd_6637538 : Nat := 4983230072969 + 3 ^ 40 * 6637538 * 2
def baseEnd_6637538 : Nat := 3408247356482756835749525

theorem tailTrace_6637538 : CollatzResearch.WordTrace tailWord_6637538 prefixEnd_6637538 3408247356482756835749525 := by
  unfold tailWord_6637538
  simp only [CollatzResearch.WordTrace]
  refine ⟨60522724856835225521226317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161393932951560601389936845 60522724856835225521226317)
  ·
    refine ⟨22696021821313209570459869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60522724856835225521226317 22696021821313209570459869)
    ·
      refine ⟨8511008182992453588922451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22696021821313209570459869 8511008182992453588922451)
      ·
        refine ⟨12766512274488680383383677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8511008182992453588922451 12766512274488680383383677)
        ·
          refine ⟨4787442102933255143768879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12766512274488680383383677 4787442102933255143768879)
          ·
            refine ⟨7181163154399882715653319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4787442102933255143768879 7181163154399882715653319)
            ·
              refine ⟨10771744731599824073479979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7181163154399882715653319 10771744731599824073479979)
              ·
                refine ⟨16157617097399736110219969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10771744731599824073479979 16157617097399736110219969)
                ·
                  refine ⟨12118212823049802082664977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16157617097399736110219969 12118212823049802082664977)
                  ·
                    refine ⟨9088659617287351561998733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12118212823049802082664977 9088659617287351561998733)
                    ·
                      refine ⟨3408247356482756835749525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9088659617287351561998733 3408247356482756835749525)
                      ·
                        rfl

theorem cell23_6637538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_6637538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637538 prefixEnd_6637538 := by exact prefixLift 6637538
  have htrace : WordTrace (prefixWord ++ tailWord_6637538) baseStart_6637538 baseEnd_6637538 := by
    simpa [prefixWord, tailWord_6637538, baseEnd_6637538] using wordTrace_append hprefix tailTrace_6637538
  have hstable : (prefixWord ++ tailWord_6637538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637538).length < 2 ^ (prefixWord ++ tailWord_6637538).sum := by decide
  have hdescent : baseEnd_6637538 < baseStart_6637538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637540 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 3, 1, 4]
def baseStart_6637540 : Nat := 118140960795 + 6637540 * 2 ^ 59
def prefixEnd_6637540 : Nat := 4983230072969 + 3 ^ 40 * 6637540 * 2
def baseEnd_6637540 : Nat := 3408248383444065827924515

theorem tailTrace_6637540 : CollatzResearch.WordTrace tailWord_6637540 prefixEnd_6637540 3408248383444065827924515 := by
  unfold tailWord_6637540
  simp only [CollatzResearch.WordTrace]
  refine ⟨121045486186666828213239037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161393981582222437617652049 121045486186666828213239037)
  ·
    refine ⟨45392057320000060579964639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121045486186666828213239037 45392057320000060579964639)
    ·
      refine ⟨68088085980000090869946959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45392057320000060579964639 68088085980000090869946959)
      ·
        refine ⟨102132128970000136304920439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68088085980000090869946959 102132128970000136304920439)
        ·
          refine ⟨153198193455000204457380659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102132128970000136304920439 153198193455000204457380659)
          ·
            refine ⟨229797290182500306686070989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153198193455000204457380659 229797290182500306686070989)
            ·
              refine ⟨86173983818437615007276621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229797290182500306686070989 86173983818437615007276621)
              ·
                refine ⟨32315243931914105627728733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86173983818437615007276621 32315243931914105627728733)
                ·
                  refine ⟨12118216474467789610398275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32315243931914105627728733 12118216474467789610398275)
                  ·
                    refine ⟨18177324711701684415597413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12118216474467789610398275 18177324711701684415597413)
                    ·
                      refine ⟨3408248383444065827924515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18177324711701684415597413 3408248383444065827924515)
                      ·
                        rfl

theorem cell23_6637540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_6637540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637540 prefixEnd_6637540 := by exact prefixLift 6637540
  have htrace : WordTrace (prefixWord ++ tailWord_6637540) baseStart_6637540 baseEnd_6637540 := by
    simpa [prefixWord, tailWord_6637540, baseEnd_6637540] using wordTrace_append hprefix tailTrace_6637540
  have hstable : (prefixWord ++ tailWord_6637540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637540).length < 2 ^ (prefixWord ++ tailWord_6637540).sum := by decide
  have hdescent : baseEnd_6637540 < baseStart_6637540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637594 : List Nat := [3, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3]
def baseStart_6637594 : Nat := 118140960795 + 6637594 * 2 ^ 59
def prefixEnd_6637594 : Nat := 4983230072969 + 3 ^ 40 * 6637594 * 2
def baseEnd_6637594 : Nat := 3408276111399408616649267

theorem tailTrace_6637594 : CollatzResearch.WordTrace tailWord_6637594 prefixEnd_6637594 3408276111399408616649267 := by
  unfold tailWord_6637594
  simp only [CollatzResearch.WordTrace]
  refine ⟨60523235478784505912235959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161395294610092015765962557 60523235478784505912235959)
  ·
    refine ⟨90784853218176758868353939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60523235478784505912235959 90784853218176758868353939)
    ·
      refine ⟨136177279827265138302530909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90784853218176758868353939 136177279827265138302530909)
      ·
        refine ⟨51066479935224426863449091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136177279827265138302530909 51066479935224426863449091)
        ·
          refine ⟨76599719902836640295173637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51066479935224426863449091 76599719902836640295173637)
          ·
            refine ⟨14362447481781870055345057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76599719902836640295173637 14362447481781870055345057)
            ·
              refine ⟨10771835611336402541508793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14362447481781870055345057 10771835611336402541508793)
              ·
                refine ⟨8078876708502301906131595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10771835611336402541508793 8078876708502301906131595)
                ·
                  refine ⟨12118315062753452859197393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8078876708502301906131595 12118315062753452859197393)
                  ·
                    refine ⟨9088736297065089644398045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12118315062753452859197393 9088736297065089644398045)
                    ·
                      refine ⟨3408276111399408616649267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9088736297065089644398045 3408276111399408616649267)
                      ·
                        rfl

theorem cell23_6637594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_6637594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637594 prefixEnd_6637594 := by exact prefixLift 6637594
  have htrace : WordTrace (prefixWord ++ tailWord_6637594) baseStart_6637594 baseEnd_6637594 := by
    simpa [prefixWord, tailWord_6637594, baseEnd_6637594] using wordTrace_append hprefix tailTrace_6637594
  have hstable : (prefixWord ++ tailWord_6637594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637594).length < 2 ^ (prefixWord ++ tailWord_6637594).sum := by decide
  have hdescent : baseEnd_6637594 < baseStart_6637594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637597 : List Nat := [1, 4, 2, 2, 2, 1, 4, 7]
def baseStart_6637597 : Nat := 118140960795 + 6637597 * 2 ^ 59
def prefixEnd_6637597 : Nat := 4983230072969 + 3 ^ 40 * 6637597 * 2
def baseEnd_6637597 : Nat := 126232505623754522404139

theorem tailTrace_6637597 : CollatzResearch.WordTrace tailWord_6637597 prefixEnd_6637597 126232505623754522404139 := by
  unfold tailWord_6637597
  simp only [CollatzResearch.WordTrace]
  refine ⟨242093051334127155161303045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161395367556084770107535363 242093051334127155161303045)
  ·
    refine ⟨45392447125148841592744321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242093051334127155161303045 45392447125148841592744321)
    ·
      refine ⟨34044335343861631194558241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45392447125148841592744321 34044335343861631194558241)
      ·
        refine ⟨25533251507896223395918681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34044335343861631194558241 25533251507896223395918681)
        ·
          refine ⟨19149938630922167546939011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25533251507896223395918681 19149938630922167546939011)
          ·
            refine ⟨28724907946383251320408517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19149938630922167546939011 28724907946383251320408517)
            ·
              refine ⟨5385920239946859622576597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28724907946383251320408517 5385920239946859622576597)
              ·
                refine ⟨126232505623754522404139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5385920239946859622576597 126232505623754522404139)
                ·
                  rfl

theorem cell23_6637597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 7].length) (baseStart_6637597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637597 prefixEnd_6637597 := by exact prefixLift 6637597
  have htrace : WordTrace (prefixWord ++ tailWord_6637597) baseStart_6637597 baseEnd_6637597 := by
    simpa [prefixWord, tailWord_6637597, baseEnd_6637597] using wordTrace_append hprefix tailTrace_6637597
  have hstable : (prefixWord ++ tailWord_6637597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637597).length < 2 ^ (prefixWord ++ tailWord_6637597).sum := by decide
  have hdescent : baseEnd_6637597 < baseStart_6637597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637625 : List Nat := [1, 2, 1, 5, 3, 1, 3, 2, 1, 2, 2]
def baseStart_6637625 : Nat := 118140960795 + 6637625 * 2 ^ 59
def prefixEnd_6637625 : Nat := 4983230072969 + 3 ^ 40 * 6637625 * 2
def baseEnd_6637625 : Nat := 3408292029299697995361625

theorem tailTrace_6637625 : CollatzResearch.WordTrace tailWord_6637625 prefixEnd_6637625 3408292029299697995361625 := by
  unfold tailWord_6637625
  simp only [CollatzResearch.WordTrace]
  refine ⟨242094072578025715943322329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161396048385350477295548219 242094072578025715943322329)
  ·
    refine ⟨181570554433519286957491747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242094072578025715943322329 181570554433519286957491747)
    ·
      refine ⟨272355831650278930436237621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181570554433519286957491747 272355831650278930436237621)
      ·
        refine ⟨25533359217213649728397277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 272355831650278930436237621 25533359217213649728397277)
        ·
          refine ⟨9575009706455118648148979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25533359217213649728397277 9575009706455118648148979)
          ·
            refine ⟨14362514559682677972223469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9575009706455118648148979 14362514559682677972223469)
            ·
              refine ⟨5385942959881004239583801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14362514559682677972223469 5385942959881004239583801)
              ·
                refine ⟨4039457219910753179687851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5385942959881004239583801 4039457219910753179687851)
                ·
                  refine ⟨6059185829866129769531777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4039457219910753179687851 6059185829866129769531777)
                  ·
                    refine ⟨4544389372399597327148833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6059185829866129769531777 4544389372399597327148833)
                    ·
                      refine ⟨3408292029299697995361625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4544389372399597327148833 3408292029299697995361625)
                      ·
                        rfl

theorem cell23_6637625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_6637625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637625 prefixEnd_6637625 := by exact prefixLift 6637625
  have htrace : WordTrace (prefixWord ++ tailWord_6637625) baseStart_6637625 baseEnd_6637625 := by
    simpa [prefixWord, tailWord_6637625, baseEnd_6637625] using wordTrace_append hprefix tailTrace_6637625
  have hstable : (prefixWord ++ tailWord_6637625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637625).length < 2 ^ (prefixWord ++ tailWord_6637625).sum := by decide
  have hdescent : baseEnd_6637625 < baseStart_6637625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637664 : List Nat := [2, 1, 1, 3, 2, 4, 1, 2, 1, 4, 2]
def baseStart_6637664 : Nat := 118140960795 + 6637664 * 2 ^ 59
def prefixEnd_6637664 : Nat := 4983230072969 + 3 ^ 40 * 6637664 * 2
def baseEnd_6637664 : Nat := 3408312055045223342773945

theorem tailTrace_6637664 : CollatzResearch.WordTrace tailWord_6637664 prefixEnd_6637664 3408312055045223342773945 := by
  unfold tailWord_6637664
  simp only [CollatzResearch.WordTrace]
  refine ⟨121047747512442212801996023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161396996683256283735994697 121047747512442212801996023)
  ·
    refine ⟨181571621268663319202994035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121047747512442212801996023 181571621268663319202994035)
    ·
      refine ⟨272357431902994978804491053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181571621268663319202994035 272357431902994978804491053)
      ·
        refine ⟨102134036963623117051684145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272357431902994978804491053 102134036963623117051684145)
        ·
          refine ⟨76600527722717337788763109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102134036963623117051684145 76600527722717337788763109)
          ·
            refine ⟨14362598948009500835393083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76600527722717337788763109 14362598948009500835393083)
            ·
              refine ⟨21543898422014251253089625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14362598948009500835393083 21543898422014251253089625)
              ·
                refine ⟨16157923816510688439817219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21543898422014251253089625 16157923816510688439817219)
                ·
                  refine ⟨24236885724766032659725829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16157923816510688439817219 24236885724766032659725829)
                  ·
                    refine ⟨4544416073393631123698593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24236885724766032659725829 4544416073393631123698593)
                    ·
                      refine ⟨3408312055045223342773945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4544416073393631123698593 3408312055045223342773945)
                      ·
                        rfl

theorem cell23_6637664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 1, 4, 2].length) (baseStart_6637664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637664 prefixEnd_6637664 := by exact prefixLift 6637664
  have htrace : WordTrace (prefixWord ++ tailWord_6637664) baseStart_6637664 baseEnd_6637664 := by
    simpa [prefixWord, tailWord_6637664, baseEnd_6637664] using wordTrace_append hprefix tailTrace_6637664
  have hstable : (prefixWord ++ tailWord_6637664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637664).length < 2 ^ (prefixWord ++ tailWord_6637664).sum := by decide
  have hdescent : baseEnd_6637664 < baseStart_6637664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637677 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_6637677 : Nat := 118140960795 + 6637677 * 2 ^ 59
def prefixEnd_6637677 : Nat := 4983230072969 + 3 ^ 40 * 6637677 * 2
def baseEnd_6637677 : Nat := 3408318730293731791911385

theorem tailTrace_6637677 : CollatzResearch.WordTrace tailWord_6637677 prefixEnd_6637677 3408318730293731791911385 := by
  unfold tailWord_6637677
  simp only [CollatzResearch.WordTrace]
  refine ⟨242095969173837328824215285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161397312782558219216143523 242095969173837328824215285)
  ·
    refine ⟨22696497110047249577270183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242095969173837328824215285 22696497110047249577270183)
    ·
      refine ⟨34044745665070874365905275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22696497110047249577270183 34044745665070874365905275)
      ·
        refine ⟨51067118497606311548857913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34044745665070874365905275 51067118497606311548857913)
        ·
          refine ⟨38300338873204733661643435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51067118497606311548857913 38300338873204733661643435)
          ·
            refine ⟨57450508309807100492465153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38300338873204733661643435 57450508309807100492465153)
            ·
              refine ⟨43087881232355325369348865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57450508309807100492465153 43087881232355325369348865)
              ·
                refine ⟨32315910924266494027011649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43087881232355325369348865 32315910924266494027011649)
                ·
                  refine ⟨24236933193199870520258737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32315910924266494027011649 24236933193199870520258737)
                  ·
                    refine ⟨18177699894899902890194053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24236933193199870520258737 18177699894899902890194053)
                    ·
                      refine ⟨3408318730293731791911385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18177699894899902890194053 3408318730293731791911385)
                      ·
                        rfl

theorem cell23_6637677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_6637677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637677 prefixEnd_6637677 := by exact prefixLift 6637677
  have htrace : WordTrace (prefixWord ++ tailWord_6637677) baseStart_6637677 baseEnd_6637677 := by
    simpa [prefixWord, tailWord_6637677, baseEnd_6637677] using wordTrace_append hprefix tailTrace_6637677
  have hstable : (prefixWord ++ tailWord_6637677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637677).length < 2 ^ (prefixWord ++ tailWord_6637677).sum := by decide
  have hdescent : baseEnd_6637677 < baseStart_6637677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637681 : List Nat := [1, 2, 2, 2, 1, 1, 6, 2, 2, 2, 2]
def baseStart_6637681 : Nat := 118140960795 + 6637681 * 2 ^ 59
def prefixEnd_6637681 : Nat := 4983230072969 + 3 ^ 40 * 6637681 * 2
def baseEnd_6637681 : Nat := 3408320784216349776261367

theorem tailTrace_6637681 : CollatzResearch.WordTrace tailWord_6637681 prefixEnd_6637681 3408320784216349776261367 := by
  unfold tailWord_6637681
  simp only [CollatzResearch.WordTrace]
  refine ⟨242096115065822837507360897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161397410043881891671573931 242096115065822837507360897)
  ·
    refine ⟨181572086299367128130520673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242096115065822837507360897 181572086299367128130520673)
    ·
      refine ⟨136179064724525346097890505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181572086299367128130520673 136179064724525346097890505)
      ·
        refine ⟨102134298543394009573417879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136179064724525346097890505 102134298543394009573417879)
        ·
          refine ⟨153201447815091014360126819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102134298543394009573417879 153201447815091014360126819)
          ·
            refine ⟨229802171722636521540190229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153201447815091014360126819 229802171722636521540190229)
            ·
              refine ⟨10771976799498586947196417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 229802171722636521540190229 10771976799498586947196417)
              ·
                refine ⟨8078982599623940210397313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10771976799498586947196417 8078982599623940210397313)
                ·
                  refine ⟨6059236949717955157797985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8078982599623940210397313 6059236949717955157797985)
                  ·
                    refine ⟨4544427712288466368348489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6059236949717955157797985 4544427712288466368348489)
                    ·
                      refine ⟨3408320784216349776261367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4544427712288466368348489 3408320784216349776261367)
                      ·
                        rfl

theorem cell23_6637681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 2, 2].length) (baseStart_6637681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637681 prefixEnd_6637681 := by exact prefixLift 6637681
  have htrace : WordTrace (prefixWord ++ tailWord_6637681) baseStart_6637681 baseEnd_6637681 := by
    simpa [prefixWord, tailWord_6637681, baseEnd_6637681] using wordTrace_append hprefix tailTrace_6637681
  have hstable : (prefixWord ++ tailWord_6637681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637681).length < 2 ^ (prefixWord ++ tailWord_6637681).sum := by decide
  have hdescent : baseEnd_6637681 < baseStart_6637681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637754 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2]
def baseStart_6637754 : Nat := 118140960795 + 6637754 * 2 ^ 59
def prefixEnd_6637754 : Nat := 4983230072969 + 3 ^ 40 * 6637754 * 2
def baseEnd_6637754 : Nat := 3408358268304127990648531

theorem tailTrace_6637754 : CollatzResearch.WordTrace tailWord_6637754 prefixEnd_6637754 3408358268304127990648531 := by
  unfold tailWord_6637754
  simp only [CollatzResearch.WordTrace]
  refine ⟨60524694398639592743692079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161399185063038913983178877 60524694398639592743692079)
  ·
    refine ⟨90787041597959389115538119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60524694398639592743692079 90787041597959389115538119)
    ·
      refine ⟨136180562396939083673307179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90787041597959389115538119 136180562396939083673307179)
      ·
        refine ⟨204270843595408625509960769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136180562396939083673307179 204270843595408625509960769)
        ·
          refine ⟨153203132696556469132470577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204270843595408625509960769 153203132696556469132470577)
          ·
            refine ⟨114902349522417351849352933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153203132696556469132470577 114902349522417351849352933)
            ·
              refine ⟨21544190535453253471753675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114902349522417351849352933 21544190535453253471753675)
              ·
                refine ⟨32316285803179880207630513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21544190535453253471753675 32316285803179880207630513)
                ·
                  refine ⟨24237214352384910155722885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32316285803179880207630513 24237214352384910155722885)
                  ·
                    refine ⟨4544477691072170654198041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24237214352384910155722885 4544477691072170654198041)
                    ·
                      refine ⟨3408358268304127990648531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4544477691072170654198041 3408358268304127990648531)
                      ·
                        rfl

theorem cell23_6637754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2].length) (baseStart_6637754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637754 prefixEnd_6637754 := by exact prefixLift 6637754
  have htrace : WordTrace (prefixWord ++ tailWord_6637754) baseStart_6637754 baseEnd_6637754 := by
    simpa [prefixWord, tailWord_6637754, baseEnd_6637754] using wordTrace_append hprefix tailTrace_6637754
  have hstable : (prefixWord ++ tailWord_6637754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637754).length < 2 ^ (prefixWord ++ tailWord_6637754).sum := by decide
  have hdescent : baseEnd_6637754 < baseStart_6637754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637774 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3]
def baseStart_6637774 : Nat := 118140960795 + 6637774 * 2 ^ 59
def prefixEnd_6637774 : Nat := 4983230072969 + 3 ^ 40 * 6637774 * 2
def baseEnd_6637774 : Nat := 3408368537917217912398439

theorem tailTrace_6637774 : CollatzResearch.WordTrace tailWord_6637774 prefixEnd_6637774 3408368537917217912398439 := by
  unfold tailWord_6637774
  simp only [CollatzResearch.WordTrace]
  refine ⟨30262438381810739298812047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161399671369657276260330917 30262438381810739298812047)
  ·
    refine ⟨45393657572716108948218071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30262438381810739298812047 45393657572716108948218071)
    ·
      refine ⟨68090486359074163422327107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45393657572716108948218071 68090486359074163422327107)
      ·
        refine ⟨102135729538611245133490661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68090486359074163422327107 102135729538611245133490661)
        ·
          refine ⟨19150449288489608462529499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102135729538611245133490661 19150449288489608462529499)
          ·
            refine ⟨28725673932734412693794249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19150449288489608462529499 28725673932734412693794249)
            ·
              refine ⟨21544255449550809520345687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28725673932734412693794249 21544255449550809520345687)
              ·
                refine ⟨32316383174326214280518531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21544255449550809520345687 32316383174326214280518531)
                ·
                  refine ⟨48474574761489321420777797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32316383174326214280518531 48474574761489321420777797)
                  ·
                    refine ⟨9088982767779247766395837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48474574761489321420777797 9088982767779247766395837)
                    ·
                      refine ⟨3408368537917217912398439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9088982767779247766395837 3408368537917217912398439)
                      ·
                        rfl

theorem cell23_6637774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_6637774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637774 prefixEnd_6637774 := by exact prefixLift 6637774
  have htrace : WordTrace (prefixWord ++ tailWord_6637774) baseStart_6637774 baseEnd_6637774 := by
    simpa [prefixWord, tailWord_6637774, baseEnd_6637774] using wordTrace_append hprefix tailTrace_6637774
  have hstable : (prefixWord ++ tailWord_6637774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637774).length < 2 ^ (prefixWord ++ tailWord_6637774).sum := by decide
  have hdescent : baseEnd_6637774 < baseStart_6637774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637788 : List Nat := [2, 2, 5, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_6637788 : Nat := 118140960795 + 6637788 * 2 ^ 59
def prefixEnd_6637788 : Nat := 4983230072969 + 3 ^ 40 * 6637788 * 2
def baseEnd_6637788 : Nat := 3408375726646380857623375

theorem tailTrace_6637788 : CollatzResearch.WordTrace tailWord_6637788 prefixEnd_6637788 3408375726646380857623375 := by
  unfold tailWord_6637788
  simp only [CollatzResearch.WordTrace]
  refine ⟨121050008838217597390753009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161400011784290129854337345 121050008838217597390753009)
  ·
    refine ⟨90787506628663198043064757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121050008838217597390753009 90787506628663198043064757)
    ·
      refine ⟨8511328746437174816537321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90787506628663198043064757 8511328746437174816537321)
      ·
        refine ⟨6383496559827881112402991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8511328746437174816537321 6383496559827881112402991)
        ·
          refine ⟨9575244839741821668604487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6383496559827881112402991 9575244839741821668604487)
          ·
            refine ⟨14362867259612732502906731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9575244839741821668604487 14362867259612732502906731)
            ·
              refine ⟨21544300889419098754360097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14362867259612732502906731 21544300889419098754360097)
              ·
                refine ⟨16158225667064324065770073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21544300889419098754360097 16158225667064324065770073)
                ·
                  refine ⟨12118669250298243049327555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16158225667064324065770073 12118669250298243049327555)
                  ·
                    refine ⟨18178003875447364573991333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12118669250298243049327555 18178003875447364573991333)
                    ·
                      refine ⟨3408375726646380857623375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18178003875447364573991333 3408375726646380857623375)
                      ·
                        rfl

theorem cell23_6637788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_6637788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637788 prefixEnd_6637788 := by exact prefixLift 6637788
  have htrace : WordTrace (prefixWord ++ tailWord_6637788) baseStart_6637788 baseEnd_6637788 := by
    simpa [prefixWord, tailWord_6637788, baseEnd_6637788] using wordTrace_append hprefix tailTrace_6637788
  have hstable : (prefixWord ++ tailWord_6637788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637788).length < 2 ^ (prefixWord ++ tailWord_6637788).sum := by decide
  have hdescent : baseEnd_6637788 < baseStart_6637788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637824 : List Nat := [2, 1, 1, 2, 1, 1, 7, 2, 1, 5]
def baseStart_6637824 : Nat := 118140960795 + 6637824 * 2 ^ 59
def prefixEnd_6637824 : Nat := 4983230072969 + 3 ^ 40 * 6637824 * 2
def baseEnd_6637824 : Nat := 1136131403983314238924403

theorem tailTrace_6637824 : CollatzResearch.WordTrace tailWord_6637824 prefixEnd_6637824 1136131403983314238924403 := by
  unfold tailWord_6637824
  simp only [CollatzResearch.WordTrace]
  refine ⟨121050665352152386464908263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161400887136203181953211017 121050665352152386464908263)
  ·
    refine ⟨181575998028228579697362395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121050665352152386464908263 181575998028228579697362395)
    ·
      refine ⟨272363997042342869546043593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181575998028228579697362395 272363997042342869546043593)
      ·
        refine ⟨204272997781757152159532695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272363997042342869546043593 204272997781757152159532695)
        ·
          refine ⟨306409496672635728239299043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204272997781757152159532695 306409496672635728239299043)
          ·
            refine ⟨459614245008953592358948565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306409496672635728239299043 459614245008953592358948565)
            ·
              refine ⟨10772208867397349820912857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 459614245008953592358948565 10772208867397349820912857)
              ·
                refine ⟨8079156650548012365684643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10772208867397349820912857 8079156650548012365684643)
                ·
                  refine ⟨12118734975822018548526965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8079156650548012365684643 12118734975822018548526965)
                  ·
                    refine ⟨1136131403983314238924403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12118734975822018548526965 1136131403983314238924403)
                    ·
                      rfl

theorem cell23_6637824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 1, 5].length) (baseStart_6637824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637824 prefixEnd_6637824 := by exact prefixLift 6637824
  have htrace : WordTrace (prefixWord ++ tailWord_6637824) baseStart_6637824 baseEnd_6637824 := by
    simpa [prefixWord, tailWord_6637824, baseEnd_6637824] using wordTrace_append hprefix tailTrace_6637824
  have hstable : (prefixWord ++ tailWord_6637824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637824).length < 2 ^ (prefixWord ++ tailWord_6637824).sum := by decide
  have hdescent : baseEnd_6637824 < baseStart_6637824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637838 : List Nat := [4, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3]
def baseStart_6637838 : Nat := 118140960795 + 6637838 * 2 ^ 59
def prefixEnd_6637838 : Nat := 4983230072969 + 3 ^ 40 * 6637838 * 2
def baseEnd_6637838 : Nat := 3408401400679105661998145

theorem tailTrace_6637838 : CollatzResearch.WordTrace tailWord_6637838 prefixEnd_6637838 3408401400679105661998145 := by
  unfold tailWord_6637838
  simp only [CollatzResearch.WordTrace]
  refine ⟨30262730165781756665103271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161401227550836035547217445 30262730165781756665103271)
  ·
    refine ⟨45394095248672634997654907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30262730165781756665103271 45394095248672634997654907)
    ·
      refine ⟨68091142873008952496482361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45394095248672634997654907 68091142873008952496482361)
      ·
        refine ⟨51068357154756714372361771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68091142873008952496482361 51068357154756714372361771)
        ·
          refine ⟨76602535732135071558542657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51068357154756714372361771 76602535732135071558542657)
          ·
            refine ⟨57451901799101303668906993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76602535732135071558542657 57451901799101303668906993)
            ·
              refine ⟨43088926349325977751680245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57451901799101303668906993 43088926349325977751680245)
              ·
                refine ⟨4039586845249310414220023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43088926349325977751680245 4039586845249310414220023)
                ·
                  refine ⟨6059380267873965621330035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4039586845249310414220023 6059380267873965621330035)
                  ·
                    refine ⟨9089070401810948431995053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6059380267873965621330035 9089070401810948431995053)
                    ·
                      refine ⟨3408401400679105661998145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9089070401810948431995053 3408401400679105661998145)
                      ·
                        rfl

theorem cell23_6637838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_6637838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637838 prefixEnd_6637838 := by exact prefixLift 6637838
  have htrace : WordTrace (prefixWord ++ tailWord_6637838) baseStart_6637838 baseEnd_6637838 := by
    simpa [prefixWord, tailWord_6637838, baseEnd_6637838] using wordTrace_append hprefix tailTrace_6637838
  have hstable : (prefixWord ++ tailWord_6637838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637838).length < 2 ^ (prefixWord ++ tailWord_6637838).sum := by decide
  have hdescent : baseEnd_6637838 < baseStart_6637838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637841 : List Nat := [1, 2, 2, 1, 1, 6, 3, 1, 1, 5]
def baseStart_6637841 : Nat := 118140960795 + 6637841 * 2 ^ 59
def prefixEnd_6637841 : Nat := 4983230072969 + 3 ^ 40 * 6637841 * 2
def baseEnd_6637841 : Nat := 1136134313707023050086877

theorem tailTrace_6637841 : CollatzResearch.WordTrace tailWord_6637841 prefixEnd_6637841 1136134313707023050086877 := by
  unfold tailWord_6637841
  simp only [CollatzResearch.WordTrace]
  refine ⟨242101950745243184833185377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161401300496828789888790251 242101950745243184833185377)
  ·
    refine ⟨181576463058932388624889033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242101950745243184833185377 181576463058932388624889033)
    ·
      refine ⟨136182347294199291468666775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181576463058932388624889033 136182347294199291468666775)
      ·
        refine ⟨204273520941298937203000163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136182347294199291468666775 204273520941298937203000163)
        ·
          refine ⟨306410281411948405804500245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204273520941298937203000163 306410281411948405804500245)
          ·
            refine ⟨14362981941185081522085949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 306410281411948405804500245 14362981941185081522085949)
            ·
              refine ⟨5386118227944405570782231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14362981941185081522085949 5386118227944405570782231)
              ·
                refine ⟨8079177341916608356173347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5386118227944405570782231 8079177341916608356173347)
                ·
                  refine ⟨12118766012874912534260021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8079177341916608356173347 12118766012874912534260021)
                  ·
                    refine ⟨1136134313707023050086877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12118766012874912534260021 1136134313707023050086877)
                    ·
                      rfl

theorem cell23_6637841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 1, 5].length) (baseStart_6637841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637841 prefixEnd_6637841 := by exact prefixLift 6637841
  have htrace : WordTrace (prefixWord ++ tailWord_6637841) baseStart_6637841 baseEnd_6637841 := by
    simpa [prefixWord, tailWord_6637841, baseEnd_6637841] using wordTrace_append hprefix tailTrace_6637841
  have hstable : (prefixWord ++ tailWord_6637841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637841).length < 2 ^ (prefixWord ++ tailWord_6637841).sum := by decide
  have hdescent : baseEnd_6637841 < baseStart_6637841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637855 : List Nat := [1, 1, 2, 4, 3, 1, 4, 2, 1, 1, 3]
def baseStart_6637855 : Nat := 118140960795 + 6637855 * 2 ^ 59
def prefixEnd_6637855 : Nat := 4983230072969 + 3 ^ 40 * 6637855 * 2
def baseEnd_6637855 : Nat := 3408410129850232095485567

theorem tailTrace_6637855 : CollatzResearch.WordTrace tailWord_6637855 prefixEnd_6637855 3408410129850232095485567 := by
  unfold tailWord_6637855
  simp only [CollatzResearch.WordTrace]
  refine ⟨242102461367192465224195019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161401640911461643482796679 242102461367192465224195019)
  ·
    refine ⟨363153692050788697836292529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242102461367192465224195019 363153692050788697836292529)
    ·
      refine ⟨272365269038091523377219397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363153692050788697836292529 272365269038091523377219397)
      ·
        refine ⟨51068487944642160633228637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272365269038091523377219397 51068487944642160633228637)
        ·
          refine ⟨19150682979240810237460739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51068487944642160633228637 19150682979240810237460739)
          ·
            refine ⟨28726024468861215356191109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19150682979240810237460739 28726024468861215356191109)
            ·
              refine ⟨5386129587911477879285833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28726024468861215356191109 5386129587911477879285833)
              ·
                refine ⟨4039597190933608409464375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5386129587911477879285833 4039597190933608409464375)
                ·
                  refine ⟨6059395786400412614196563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4039597190933608409464375 6059395786400412614196563)
                  ·
                    refine ⟨9089093679600618921294845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6059395786400412614196563 9089093679600618921294845)
                    ·
                      refine ⟨3408410129850232095485567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9089093679600618921294845 3408410129850232095485567)
                      ·
                        rfl

theorem cell23_6637855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_6637855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637855 prefixEnd_6637855 := by exact prefixLift 6637855
  have htrace : WordTrace (prefixWord ++ tailWord_6637855) baseStart_6637855 baseEnd_6637855 := by
    simpa [prefixWord, tailWord_6637855, baseEnd_6637855] using wordTrace_append hprefix tailTrace_6637855
  have hstable : (prefixWord ++ tailWord_6637855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637855).length < 2 ^ (prefixWord ++ tailWord_6637855).sum := by decide
  have hdescent : baseEnd_6637855 < baseStart_6637855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637857 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 3, 1, 6]
def baseStart_6637857 : Nat := 118140960795 + 6637857 * 2 ^ 59
def prefixEnd_6637857 : Nat := 4983230072969 + 3 ^ 40 * 6637857 * 2
def baseEnd_6637857 : Nat := 3408411156811541087660557

theorem tailTrace_6637857 : CollatzResearch.WordTrace tailWord_6637857 prefixEnd_6637857 3408411156811541087660557 := by
  unfold tailWord_6637857
  simp only [CollatzResearch.WordTrace]
  refine ⟨242102534313185219565767825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161401689542123479710511883 242102534313185219565767825)
  ·
    refine ⟨181576900734888914674325869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242102534313185219565767825 181576900734888914674325869)
    ·
      refine ⟨68091337775583343002872201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181576900734888914674325869 68091337775583343002872201)
      ·
        refine ⟨51068503331687507252154151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68091337775583343002872201 51068503331687507252154151)
        ·
          refine ⟨76602754997531260878231227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51068503331687507252154151 76602754997531260878231227)
          ·
            refine ⟨114904132496296891317346841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76602754997531260878231227 114904132496296891317346841)
            ·
              refine ⟨86178099372222668488010131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114904132496296891317346841 86178099372222668488010131)
              ·
                refine ⟨129267149058334002732015197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86178099372222668488010131 129267149058334002732015197)
                ·
                  refine ⟨48475180896875251024505699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129267149058334002732015197 48475180896875251024505699)
                  ·
                    refine ⟨72712771345312876536758549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48475180896875251024505699 72712771345312876536758549)
                    ·
                      refine ⟨3408411156811541087660557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72712771345312876536758549 3408411156811541087660557)
                      ·
                        rfl

theorem cell23_6637857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_6637857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637857 prefixEnd_6637857 := by exact prefixLift 6637857
  have htrace : WordTrace (prefixWord ++ tailWord_6637857) baseStart_6637857 baseEnd_6637857 := by
    simpa [prefixWord, tailWord_6637857, baseEnd_6637857] using wordTrace_append hprefix tailTrace_6637857
  have hstable : (prefixWord ++ tailWord_6637857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637857).length < 2 ^ (prefixWord ++ tailWord_6637857).sum := by decide
  have hdescent : baseEnd_6637857 < baseStart_6637857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637881 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 3, 2, 3]
def baseStart_6637881 : Nat := 118140960795 + 6637881 * 2 ^ 59
def prefixEnd_6637881 : Nat := 4983230072969 + 3 ^ 40 * 6637881 * 2
def baseEnd_6637881 : Nat := 3408423480347248993760447

theorem tailTrace_6637881 : CollatzResearch.WordTrace tailWord_6637881 prefixEnd_6637881 3408423480347248993760447 := by
  unfold tailWord_6637881
  simp only [CollatzResearch.WordTrace]
  refine ⟨242103409665098271664641497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161402273110065514443094331 242103409665098271664641497)
  ·
    refine ⟨181577557248823703748481123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242103409665098271664641497 181577557248823703748481123)
    ·
      refine ⟨272366335873235555622721685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181577557248823703748481123 272366335873235555622721685)
      ·
        refine ⟨12767171994057916669815079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 272366335873235555622721685 12767171994057916669815079)
        ·
          refine ⟨19150757991086875004722619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12767171994057916669815079 19150757991086875004722619)
          ·
            refine ⟨28726136986630312507083929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19150757991086875004722619 28726136986630312507083929)
            ·
              refine ⟨21544602739972734380312947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28726136986630312507083929 21544602739972734380312947)
              ·
                refine ⟨32316904109959101570469421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21544602739972734380312947 32316904109959101570469421)
                ·
                  refine ⟨12118839041234663088926033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32316904109959101570469421 12118839041234663088926033)
                  ·
                    refine ⟨9089129280925997316694525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12118839041234663088926033 9089129280925997316694525)
                    ·
                      refine ⟨3408423480347248993760447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9089129280925997316694525 3408423480347248993760447)
                      ·
                        rfl

theorem cell23_6637881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_6637881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637881 prefixEnd_6637881 := by exact prefixLift 6637881
  have htrace : WordTrace (prefixWord ++ tailWord_6637881) baseStart_6637881 baseEnd_6637881 := by
    simpa [prefixWord, tailWord_6637881, baseEnd_6637881] using wordTrace_append hprefix tailTrace_6637881
  have hstable : (prefixWord ++ tailWord_6637881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637881).length < 2 ^ (prefixWord ++ tailWord_6637881).sum := by decide
  have hdescent : baseEnd_6637881 < baseStart_6637881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637884 : List Nat := [2, 2, 2, 2, 1, 2, 5, 7]
def baseStart_6637884 : Nat := 118140960795 + 6637884 * 2 ^ 59
def prefixEnd_6637884 : Nat := 4983230072969 + 3 ^ 40 * 6637884 * 2
def baseEnd_6637884 : Nat := 126237963732933795630479

theorem tailTrace_6637884 : CollatzResearch.WordTrace tailWord_6637884 prefixEnd_6637884 126237963732933795630479 := by
  unfold tailWord_6637884
  simp only [CollatzResearch.WordTrace]
  refine ⟨121051759542043701588500353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161402346056058268784667137 121051759542043701588500353)
  ·
    refine ⟨90788819656532776191375265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121051759542043701588500353 90788819656532776191375265)
    ·
      refine ⟨68091614742399582143531449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90788819656532776191375265 68091614742399582143531449)
      ·
        refine ⟨51068711056799686607648587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68091614742399582143531449 51068711056799686607648587)
        ·
          refine ⟨76603066585199529911472881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51068711056799686607648587 76603066585199529911472881)
          ·
            refine ⟨57452299938899647433604661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76603066585199529911472881 57452299938899647433604661)
            ·
              refine ⟨5386153119271841946900437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57452299938899647433604661 5386153119271841946900437)
              ·
                refine ⟨126237963732933795630479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5386153119271841946900437 126237963732933795630479)
                ·
                  rfl

theorem cell23_6637884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 7].length) (baseStart_6637884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637884 prefixEnd_6637884 := by exact prefixLift 6637884
  have htrace : WordTrace (prefixWord ++ tailWord_6637884) baseStart_6637884 baseEnd_6637884 := by
    simpa [prefixWord, tailWord_6637884, baseEnd_6637884] using wordTrace_append hprefix tailTrace_6637884
  have hstable : (prefixWord ++ tailWord_6637884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637884).length < 2 ^ (prefixWord ++ tailWord_6637884).sum := by decide
  have hdescent : baseEnd_6637884 < baseStart_6637884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637892 : List Nat := [2, 3, 4, 1, 3, 1, 2, 1, 1, 5]
def baseStart_6637892 : Nat := 118140960795 + 6637892 * 2 ^ 59
def prefixEnd_6637892 : Nat := 4983230072969 + 3 ^ 40 * 6637892 * 2
def baseEnd_6637892 : Nat := 1136143042878149483574299

theorem tailTrace_6637892 : CollatzResearch.WordTrace tailWord_6637892 prefixEnd_6637892 1136143042878149483574299 := by
  unfold tailWord_6637892
  simp only [CollatzResearch.WordTrace]
  refine ⟨121051905434029210271645965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161402540578705613695527953 121051905434029210271645965)
  ·
    refine ⟨45394464537760953851867237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121051905434029210271645965 45394464537760953851867237)
    ·
      refine ⟨8511462100830178847225107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45394464537760953851867237 8511462100830178847225107)
      ·
        refine ⟨12767193151245268270837661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8511462100830178847225107 12767193151245268270837661)
        ·
          refine ⟨4787697431716975601564123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12767193151245268270837661 4787697431716975601564123)
          ·
            refine ⟨7181546147575463402346185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4787697431716975601564123 7181546147575463402346185)
            ·
              refine ⟨5386159610681597551759639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7181546147575463402346185 5386159610681597551759639)
              ·
                refine ⟨8079239416022396327639459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5386159610681597551759639 8079239416022396327639459)
                ·
                  refine ⟨12118859124033594491459189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8079239416022396327639459 12118859124033594491459189)
                  ·
                    refine ⟨1136143042878149483574299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12118859124033594491459189 1136143042878149483574299)
                    ·
                      rfl

theorem cell23_6637892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_6637892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637892 prefixEnd_6637892 := by exact prefixLift 6637892
  have htrace : WordTrace (prefixWord ++ tailWord_6637892) baseStart_6637892 baseEnd_6637892 := by
    simpa [prefixWord, tailWord_6637892, baseEnd_6637892] using wordTrace_append hprefix tailTrace_6637892
  have hstable : (prefixWord ++ tailWord_6637892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637892).length < 2 ^ (prefixWord ++ tailWord_6637892).sum := by decide
  have hdescent : baseEnd_6637892 < baseStart_6637892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637895 : List Nat := [1, 1, 4, 1, 2, 2, 4, 3, 1, 2, 2]
def baseStart_6637895 : Nat := 118140960795 + 6637895 * 2 ^ 59
def prefixEnd_6637895 : Nat := 4983230072969 + 3 ^ 40 * 6637895 * 2
def baseEnd_6637895 : Nat := 3408430669076411938985383

theorem tailTrace_6637895 : CollatzResearch.WordTrace tailWord_6637895 prefixEnd_6637895 3408430669076411938985383 := by
  unfold tailWord_6637895
  simp only [CollatzResearch.WordTrace]
  refine ⟨242103920287047552055651139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161402613524698368037100759 242103920287047552055651139)
  ·
    refine ⟨363155880430571328083476709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242103920287047552055651139 363155880430571328083476709)
    ·
      refine ⟨68091727580732124015651883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 363155880430571328083476709 68091727580732124015651883)
      ·
        refine ⟨102137591371098186023477825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68091727580732124015651883 102137591371098186023477825)
        ·
          refine ⟨76603193528323639517608369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102137591371098186023477825 76603193528323639517608369)
          ·
            refine ⟨57452395146242729638206277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76603193528323639517608369 57452395146242729638206277)
            ·
              refine ⟨10772324089920511807163677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57452395146242729638206277 10772324089920511807163677)
              ·
                refine ⟨4039621533720191927686379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10772324089920511807163677 4039621533720191927686379)
                ·
                  refine ⟨6059432300580287891529569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4039621533720191927686379 6059432300580287891529569)
                  ·
                    refine ⟨4544574225435215918647177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6059432300580287891529569 4544574225435215918647177)
                    ·
                      refine ⟨3408430669076411938985383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4544574225435215918647177 3408430669076411938985383)
                      ·
                        rfl

theorem cell23_6637895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 1, 2, 2].length) (baseStart_6637895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637895 prefixEnd_6637895 := by exact prefixLift 6637895
  have htrace : WordTrace (prefixWord ++ tailWord_6637895) baseStart_6637895 baseEnd_6637895 := by
    simpa [prefixWord, tailWord_6637895, baseEnd_6637895] using wordTrace_append hprefix tailTrace_6637895
  have hstable : (prefixWord ++ tailWord_6637895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637895).length < 2 ^ (prefixWord ++ tailWord_6637895).sum := by decide
  have hdescent : baseEnd_6637895 < baseStart_6637895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637907 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 5]
def baseStart_6637907 : Nat := 118140960795 + 6637907 * 2 ^ 59
def prefixEnd_6637907 : Nat := 4983230072969 + 3 ^ 40 * 6637907 * 2
def baseEnd_6637907 : Nat := 3408436830844265892035327

theorem tailTrace_6637907 : CollatzResearch.WordTrace tailWord_6637907 prefixEnd_6637907 3408436830844265892035327 := by
  unfold tailWord_6637907
  simp only [CollatzResearch.WordTrace]
  refine ⟨242104357963004078105087975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161402905308669385403391983 242104357963004078105087975)
  ·
    refine ⟨363156536944506117157631963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242104357963004078105087975 363156536944506117157631963)
    ·
      refine ⟨544734805416759175736447945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363156536944506117157631963 544734805416759175736447945)
      ·
        refine ⟨408551104062569381802335959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 544734805416759175736447945 408551104062569381802335959)
        ·
          refine ⟨612826656093854072703503939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408551104062569381802335959 612826656093854072703503939)
          ·
            refine ⟨919239984140781109055255909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612826656093854072703503939 919239984140781109055255909)
            ·
              refine ⟨172357497026396457947860483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 919239984140781109055255909 172357497026396457947860483)
              ·
                refine ⟨258536245539594686921790725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172357497026396457947860483 258536245539594686921790725)
                ·
                  refine ⟨48475546038674003797835761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 258536245539594686921790725 48475546038674003797835761)
                  ·
                    refine ⟨36356659529005502848376821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48475546038674003797835761 36356659529005502848376821)
                    ·
                      refine ⟨3408436830844265892035327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36356659529005502848376821 3408436830844265892035327)
                      ·
                        rfl

theorem cell23_6637907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_6637907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637907 prefixEnd_6637907 := by exact prefixLift 6637907
  have htrace : WordTrace (prefixWord ++ tailWord_6637907) baseStart_6637907 baseEnd_6637907 := by
    simpa [prefixWord, tailWord_6637907, baseEnd_6637907] using wordTrace_append hprefix tailTrace_6637907
  have hstable : (prefixWord ++ tailWord_6637907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637907).length < 2 ^ (prefixWord ++ tailWord_6637907).sum := by decide
  have hdescent : baseEnd_6637907 < baseStart_6637907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637911 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 4, 1, 3]
def baseStart_6637911 : Nat := 118140960795 + 6637911 * 2 ^ 59
def prefixEnd_6637911 : Nat := 4983230072969 + 3 ^ 40 * 6637911 * 2
def baseEnd_6637911 : Nat := 3408438884766883876385309

theorem tailTrace_6637911 : CollatzResearch.WordTrace tailWord_6637911 prefixEnd_6637911 3408438884766883876385309 := by
  unfold tailWord_6637911
  simp only [CollatzResearch.WordTrace]
  refine ⟨242104503854989586788233587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161403002569993057858822391 242104503854989586788233587)
  ·
    refine ⟨363156755782484380182350381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242104503854989586788233587 363156755782484380182350381)
    ·
      refine ⟨136183783418431642568381393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363156755782484380182350381 136183783418431642568381393)
      ·
        refine ⟨102137837563823731926286045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136183783418431642568381393 102137837563823731926286045)
        ·
          refine ⟨38301689086433899472357267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102137837563823731926286045 38301689086433899472357267)
          ·
            refine ⟨57452533629650849208535901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38301689086433899472357267 57452533629650849208535901)
            ·
              refine ⟨21544700111119068453200963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57452533629650849208535901 21544700111119068453200963)
              ·
                refine ⟨32317050166678602679801445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21544700111119068453200963 32317050166678602679801445)
                ·
                  refine ⟨6059446906252238002462771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32317050166678602679801445 6059446906252238002462771)
                  ·
                    refine ⟨9089170359378357003694157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6059446906252238002462771 9089170359378357003694157)
                    ·
                      refine ⟨3408438884766883876385309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9089170359378357003694157 3408438884766883876385309)
                      ·
                        rfl

theorem cell23_6637911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_6637911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637911 prefixEnd_6637911 := by exact prefixLift 6637911
  have htrace : WordTrace (prefixWord ++ tailWord_6637911) baseStart_6637911 baseEnd_6637911 := by
    simpa [prefixWord, tailWord_6637911, baseEnd_6637911] using wordTrace_append hprefix tailTrace_6637911
  have hstable : (prefixWord ++ tailWord_6637911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637911).length < 2 ^ (prefixWord ++ tailWord_6637911).sum := by decide
  have hdescent : baseEnd_6637911 < baseStart_6637911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637928 : List Nat := [2, 1, 4, 2, 2, 3, 1, 1, 1, 3, 3]
def baseStart_6637928 : Nat := 118140960795 + 6637928 * 2 ^ 59
def prefixEnd_6637928 : Nat := 4983230072969 + 3 ^ 40 * 6637928 * 2
def baseEnd_6637928 : Nat := 3408447613938010309872731

theorem tailTrace_6637928 : CollatzResearch.WordTrace tailWord_6637928 prefixEnd_6637928 3408447613938010309872731 := by
  unfold tailWord_6637928
  simp only [CollatzResearch.WordTrace]
  refine ⟨121052561947963999345801219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161403415930618665794401625 121052561947963999345801219)
  ·
    refine ⟨181578842921945999018701829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121052561947963999345801219 181578842921945999018701829)
    ·
      refine ⟨34046033047864874816006593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181578842921945999018701829 34046033047864874816006593)
      ·
        refine ⟨25534524785898656112004945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34046033047864874816006593 25534524785898656112004945)
        ·
          refine ⟨19150893589423992084003709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25534524785898656112004945 19150893589423992084003709)
          ·
            refine ⟨7181585096033997031501391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19150893589423992084003709 7181585096033997031501391)
            ·
              refine ⟨10772377644050995547252087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7181585096033997031501391 10772377644050995547252087)
              ·
                refine ⟨16158566466076493320878131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10772377644050995547252087 16158566466076493320878131)
                ·
                  refine ⟨24237849699114739981317197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16158566466076493320878131 24237849699114739981317197)
                  ·
                    refine ⟨9089193637168027492993949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24237849699114739981317197 9089193637168027492993949)
                    ·
                      refine ⟨3408447613938010309872731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9089193637168027492993949 3408447613938010309872731)
                      ·
                        rfl

theorem cell23_6637928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_6637928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637928 prefixEnd_6637928 := by exact prefixLift 6637928
  have htrace : WordTrace (prefixWord ++ tailWord_6637928) baseStart_6637928 baseEnd_6637928 := by
    simpa [prefixWord, tailWord_6637928, baseEnd_6637928] using wordTrace_append hprefix tailTrace_6637928
  have hstable : (prefixWord ++ tailWord_6637928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637928).length < 2 ^ (prefixWord ++ tailWord_6637928).sum := by decide
  have hdescent : baseEnd_6637928 < baseStart_6637928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637938 : List Nat := [3, 2, 1, 2, 1, 3, 1, 4, 1, 3, 2]
def baseStart_6637938 : Nat := 118140960795 + 6637938 * 2 ^ 59
def prefixEnd_6637938 : Nat := 4983230072969 + 3 ^ 40 * 6637938 * 2
def baseEnd_6637938 : Nat := 3408452748744555270747685

theorem tailTrace_6637938 : CollatzResearch.WordTrace tailWord_6637938 prefixEnd_6637938 3408452748744555270747685 := by
  unfold tailWord_6637938
  simp only [CollatzResearch.WordTrace]
  refine ⟨60526372156472942599866617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161403659083927846932977645 60526372156472942599866617)
  ·
    refine ⟨45394779117354706949899963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60526372156472942599866617 45394779117354706949899963)
    ·
      refine ⟨68092168676032060424849945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45394779117354706949899963 68092168676032060424849945)
      ·
        refine ⟨51069126507024045318637459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68092168676032060424849945 51069126507024045318637459)
        ·
          refine ⟨76603689760536067977956189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51069126507024045318637459 76603689760536067977956189)
          ·
            refine ⟨28726383660201025491733571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76603689760536067977956189 28726383660201025491733571)
            ·
              refine ⟨43089575490301538237600357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28726383660201025491733571 43089575490301538237600357)
              ·
                refine ⟨8079295404431538419550067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43089575490301538237600357 8079295404431538419550067)
                ·
                  refine ⟨12118943106647307629325101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8079295404431538419550067 12118943106647307629325101)
                  ·
                    refine ⟨4544603664992740360996913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12118943106647307629325101 4544603664992740360996913)
                    ·
                      refine ⟨3408452748744555270747685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4544603664992740360996913 3408452748744555270747685)
                      ·
                        rfl

theorem cell23_6637938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_6637938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6637938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6637938 prefixEnd_6637938 := by exact prefixLift 6637938
  have htrace : WordTrace (prefixWord ++ tailWord_6637938) baseStart_6637938 baseEnd_6637938 := by
    simpa [prefixWord, tailWord_6637938, baseEnd_6637938] using wordTrace_append hprefix tailTrace_6637938
  have hstable : (prefixWord ++ tailWord_6637938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637938).length < 2 ^ (prefixWord ++ tailWord_6637938).sum := by decide
  have hdescent : baseEnd_6637938 < baseStart_6637938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638058 : List Nat := [3, 1, 3, 1, 3, 1, 3, 1, 2, 1, 4]
def baseStart_6638058 : Nat := 118140960795 + 6638058 * 2 ^ 59
def prefixEnd_6638058 : Nat := 4983230072969 + 3 ^ 40 * 6638058 * 2
def baseEnd_6638058 : Nat := 3408514366423094801247133

theorem tailTrace_6638058 : CollatzResearch.WordTrace tailWord_6638058 prefixEnd_6638058 3408514366423094801247133 := by
  unfold tailWord_6638058
  simp only [CollatzResearch.WordTrace]
  refine ⟨60527466346364257723458707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161406576923638020595889885 60527466346364257723458707)
  ·
    refine ⟨90791199519546386585188061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60527466346364257723458707 90791199519546386585188061)
    ·
      refine ⟨34046699819829894969445523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90791199519546386585188061 34046699819829894969445523)
      ·
        refine ⟨51070049729744842454168285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34046699819829894969445523 51070049729744842454168285)
        ·
          refine ⟨19151268648654315920313107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51070049729744842454168285 19151268648654315920313107)
          ·
            refine ⟨28726902972981473880469661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19151268648654315920313107 28726902972981473880469661)
            ·
              refine ⟨10772588614868052705176123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28726902972981473880469661 10772588614868052705176123)
              ·
                refine ⟨16158882922302079057764185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10772588614868052705176123 16158882922302079057764185)
                ·
                  refine ⟨12119162191726559293323139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16158882922302079057764185 12119162191726559293323139)
                  ·
                    refine ⟨18178743287589838939984709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12119162191726559293323139 18178743287589838939984709)
                    ·
                      refine ⟨3408514366423094801247133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18178743287589838939984709 3408514366423094801247133)
                      ·
                        rfl

theorem cell23_6638058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_6638058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638058 prefixEnd_6638058 := by exact prefixLift 6638058
  have htrace : WordTrace (prefixWord ++ tailWord_6638058) baseStart_6638058 baseEnd_6638058 := by
    simpa [prefixWord, tailWord_6638058, baseEnd_6638058] using wordTrace_append hprefix tailTrace_6638058
  have hstable : (prefixWord ++ tailWord_6638058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638058).length < 2 ^ (prefixWord ++ tailWord_6638058).sum := by decide
  have hdescent : baseEnd_6638058 < baseStart_6638058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638064 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 8]
def baseStart_6638064 : Nat := 118140960795 + 6638064 * 2 ^ 59
def prefixEnd_6638064 : Nat := 4983230072969 + 3 ^ 40 * 6638064 * 2
def baseEnd_6638064 : Nat := 378724160811891308641345

theorem tailTrace_6638064 : CollatzResearch.WordTrace tailWord_6638064 prefixEnd_6638064 378724160811891308641345 := by
  unfold tailWord_6638064
  simp only [CollatzResearch.WordTrace]
  refine ⟨121055042111717646959276623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161406722815623529279035497 121055042111717646959276623)
  ·
    refine ⟨181582563167576470438914935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121055042111717646959276623 181582563167576470438914935)
    ·
      refine ⟨272373844751364705658372403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181582563167576470438914935 272373844751364705658372403)
      ·
        refine ⟨408560767127047058487558605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272373844751364705658372403 408560767127047058487558605)
        ·
          refine ⟨153210287672642646932834477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 408560767127047058487558605 153210287672642646932834477)
          ·
            refine ⟨57453857877240992599812929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153210287672642646932834477 57453857877240992599812929)
            ·
              refine ⟨43090393407930744449859697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57453857877240992599812929 43090393407930744449859697)
              ·
                refine ⟨32317795055948058337394773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43090393407930744449859697 32317795055948058337394773)
                ·
                  refine ⟨378724160811891308641345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32317795055948058337394773 378724160811891308641345)
                  ·
                    rfl

theorem cell23_6638064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 8].length) (baseStart_6638064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638064 prefixEnd_6638064 := by exact prefixLift 6638064
  have htrace : WordTrace (prefixWord ++ tailWord_6638064) baseStart_6638064 baseEnd_6638064 := by
    simpa [prefixWord, tailWord_6638064, baseEnd_6638064] using wordTrace_append hprefix tailTrace_6638064
  have hstable : (prefixWord ++ tailWord_6638064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638064).length < 2 ^ (prefixWord ++ tailWord_6638064).sum := by decide
  have hdescent : baseEnd_6638064 < baseStart_6638064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638081 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 8]
def baseStart_6638081 : Nat := 118140960795 + 6638081 * 2 ^ 59
def prefixEnd_6638081 : Nat := 4983230072969 + 3 ^ 40 * 6638081 * 2
def baseEnd_6638081 : Nat := 378725130719794245695503

theorem tailTrace_6638081 : CollatzResearch.WordTrace tailWord_6638081 prefixEnd_6638081 378725130719794245695503 := by
  unfold tailWord_6638081
  simp only [CollatzResearch.WordTrace]
  refine ⟨242110704264373705821922097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161407136176249137214614731 242110704264373705821922097)
  ·
    refine ⟨181583028198280279366441573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242110704264373705821922097 181583028198280279366441573)
    ·
      refine ⟨34046817787177552381207795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181583028198280279366441573 34046817787177552381207795)
      ·
        refine ⟨51070226680766328571811693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34046817787177552381207795 51070226680766328571811693)
        ·
          refine ⟨19151335005287373214429385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51070226680766328571811693 19151335005287373214429385)
          ·
            refine ⟨14363501253965529910822039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19151335005287373214429385 14363501253965529910822039)
            ·
              refine ⟨21545251880948294866233059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14363501253965529910822039 21545251880948294866233059)
              ·
                refine ⟨32317877821422442299349589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21545251880948294866233059 32317877821422442299349589)
                ·
                  refine ⟨378725130719794245695503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32317877821422442299349589 378725130719794245695503)
                  ·
                    rfl

theorem cell23_6638081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 8].length) (baseStart_6638081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638081 prefixEnd_6638081 := by exact prefixLift 6638081
  have htrace : WordTrace (prefixWord ++ tailWord_6638081) baseStart_6638081 baseEnd_6638081 := by
    simpa [prefixWord, tailWord_6638081, baseEnd_6638081] using wordTrace_append hprefix tailTrace_6638081
  have hstable : (prefixWord ++ tailWord_6638081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638081).length < 2 ^ (prefixWord ++ tailWord_6638081).sum := by decide
  have hdescent : baseEnd_6638081 < baseStart_6638081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638161 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 1, 1, 6]
def baseStart_6638161 : Nat := 118140960795 + 6638161 * 2 ^ 59
def prefixEnd_6638161 : Nat := 4983230072969 + 3 ^ 40 * 6638161 * 2
def baseEnd_6638161 : Nat := 3408567254930507898259159

theorem tailTrace_6638161 : CollatzResearch.WordTrace tailWord_6638161 prefixEnd_6638161 3408567254930507898259159 := by
  unfold tailWord_6638161
  simp only [CollatzResearch.WordTrace]
  refine ⟨242113622104083879484834337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161409081402722586323222891 242113622104083879484834337)
  ·
    refine ⟨181585216578062909613625753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242113622104083879484834337 181585216578062909613625753)
    ·
      refine ⟨136188912433547182210219315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181585216578062909613625753 136188912433547182210219315)
      ·
        refine ⟨204283368650320773315328973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136188912433547182210219315 204283368650320773315328973)
        ·
          refine ⟨76606263243870289993248365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204283368650320773315328973 76606263243870289993248365)
          ·
            refine ⟨28727348716451358747468137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76606263243870289993248365 28727348716451358747468137)
            ·
              refine ⟨21545511537338519060601103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28727348716451358747468137 21545511537338519060601103)
              ·
                refine ⟨32318267306007778590901655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21545511537338519060601103 32318267306007778590901655)
                ·
                  refine ⟨48477400959011667886352483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32318267306007778590901655 48477400959011667886352483)
                  ·
                    refine ⟨72716101438517501829528725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48477400959011667886352483 72716101438517501829528725)
                    ·
                      refine ⟨3408567254930507898259159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72716101438517501829528725 3408567254930507898259159)
                      ·
                        rfl

theorem cell23_6638161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_6638161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638161 prefixEnd_6638161 := by exact prefixLift 6638161
  have htrace : WordTrace (prefixWord ++ tailWord_6638161) baseStart_6638161 baseEnd_6638161 := by
    simpa [prefixWord, tailWord_6638161, baseEnd_6638161] using wordTrace_append hprefix tailTrace_6638161
  have hstable : (prefixWord ++ tailWord_6638161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638161).length < 2 ^ (prefixWord ++ tailWord_6638161).sum := by decide
  have hdescent : baseEnd_6638161 < baseStart_6638161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638165 : List Nat := [1, 3, 2, 2, 1, 1, 2, 4, 3, 2, 2]
def baseStart_6638165 : Nat := 118140960795 + 6638165 * 2 ^ 59
def prefixEnd_6638165 : Nat := 4983230072969 + 3 ^ 40 * 6638165 * 2
def baseEnd_6638165 : Nat := 3408569308853125882609141

theorem tailTrace_6638165 : CollatzResearch.WordTrace tailWord_6638165 prefixEnd_6638165 3408569308853125882609141 := by
  unfold tailWord_6638165
  simp only [CollatzResearch.WordTrace]
  refine ⟨242113767996069388167979949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161409178664046258778653299 242113767996069388167979949)
  ·
    refine ⟨90792662998526020562992481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242113767996069388167979949 90792662998526020562992481)
    ·
      refine ⟨68094497248894515422244361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90792662998526020562992481 68094497248894515422244361)
      ·
        refine ⟨51070872936670886566683271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68094497248894515422244361 51070872936670886566683271)
        ·
          refine ⟨76606309405006329850024907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51070872936670886566683271 76606309405006329850024907)
          ·
            refine ⟨114909464107509494775037361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76606309405006329850024907 114909464107509494775037361)
            ·
              refine ⟨86182098080632121081278021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114909464107509494775037361 86182098080632121081278021)
              ·
                refine ⟨16159143390118522702739629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86182098080632121081278021 16159143390118522702739629)
                ·
                  refine ⟨6059678771294446013527361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16159143390118522702739629 6059678771294446013527361)
                  ·
                    refine ⟨4544759078470834510145521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6059678771294446013527361 4544759078470834510145521)
                    ·
                      refine ⟨3408569308853125882609141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4544759078470834510145521 3408569308853125882609141)
                      ·
                        rfl

theorem cell23_6638165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_6638165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638165 prefixEnd_6638165 := by exact prefixLift 6638165
  have htrace : WordTrace (prefixWord ++ tailWord_6638165) baseStart_6638165 baseEnd_6638165 := by
    simpa [prefixWord, tailWord_6638165, baseEnd_6638165] using wordTrace_append hprefix tailTrace_6638165
  have hstable : (prefixWord ++ tailWord_6638165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638165).length < 2 ^ (prefixWord ++ tailWord_6638165).sum := by decide
  have hdescent : baseEnd_6638165 < baseStart_6638165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638199 : List Nat := [1, 1, 3, 1, 1, 3, 6, 2, 1, 2, 2]
def baseStart_6638199 : Nat := 118140960795 + 6638199 * 2 ^ 59
def prefixEnd_6638199 : Nat := 4983230072969 + 3 ^ 40 * 6638199 * 2
def baseEnd_6638199 : Nat := 3408586767195378749583985

theorem tailTrace_6638199 : CollatzResearch.WordTrace tailWord_6638199 prefixEnd_6638199 3408586767195378749583985 := by
  unfold tailWord_6638199
  simp only [CollatzResearch.WordTrace]
  refine ⟨242115008077946211974717651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161410005385297474649811767 242115008077946211974717651)
  ·
    refine ⟨363172512116919317962076477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242115008077946211974717651 363172512116919317962076477)
    ·
      refine ⟨136189692043844744235778679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363172512116919317962076477 136189692043844744235778679)
      ·
        refine ⟨204284538065767116353668019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136189692043844744235778679 204284538065767116353668019)
        ·
          refine ⟨306426807098650674530502029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204284538065767116353668019 306426807098650674530502029)
          ·
            refine ⟨114910052661994002948938261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306426807098650674530502029 114910052661994002948938261)
            ·
              refine ⟨5386408718530968888231481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114910052661994002948938261 5386408718530968888231481)
              ·
                refine ⟨4039806538898226666173611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5386408718530968888231481 4039806538898226666173611)
                ·
                  refine ⟨6059709808347339999260417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4039806538898226666173611 6059709808347339999260417)
                  ·
                    refine ⟨4544782356260504999445313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6059709808347339999260417 4544782356260504999445313)
                    ·
                      refine ⟨3408586767195378749583985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4544782356260504999445313 3408586767195378749583985)
                      ·
                        rfl

theorem cell23_6638199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 1, 2, 2].length) (baseStart_6638199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638199 prefixEnd_6638199 := by exact prefixLift 6638199
  have htrace : WordTrace (prefixWord ++ tailWord_6638199) baseStart_6638199 baseEnd_6638199 := by
    simpa [prefixWord, tailWord_6638199, baseEnd_6638199] using wordTrace_append hprefix tailTrace_6638199
  have hstable : (prefixWord ++ tailWord_6638199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638199).length < 2 ^ (prefixWord ++ tailWord_6638199).sum := by decide
  have hdescent : baseEnd_6638199 < baseStart_6638199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638201 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 2, 7]
def baseStart_6638201 : Nat := 118140960795 + 6638201 * 2 ^ 59
def prefixEnd_6638201 : Nat := 4983230072969 + 3 ^ 40 * 6638201 * 2
def baseEnd_6638201 : Nat := 1136195931385562580586325

theorem tailTrace_6638201 : CollatzResearch.WordTrace tailWord_6638201 prefixEnd_6638201 1136195931385562580586325 := by
  unfold tailWord_6638201
  simp only [CollatzResearch.WordTrace]
  refine ⟨242115081023938966316290457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161410054015959310877526971 242115081023938966316290457)
  ·
    refine ⟨181586310767954224737217843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242115081023938966316290457 181586310767954224737217843)
    ·
      refine ⟨272379466151931337105826765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181586310767954224737217843 272379466151931337105826765)
      ·
        refine ⟨102142299806974251414685037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272379466151931337105826765 102142299806974251414685037)
        ·
          refine ⟨38303362427615344280506889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102142299806974251414685037 38303362427615344280506889)
          ·
            refine ⟨28727521820711508210380167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38303362427615344280506889 28727521820711508210380167)
            ·
              refine ⟨43091282731067262315570251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28727521820711508210380167 43091282731067262315570251)
              ·
                refine ⟨64636924096600893473355377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43091282731067262315570251 64636924096600893473355377)
                ·
                  refine ⟨48477693072450670105016533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64636924096600893473355377 48477693072450670105016533)
                  ·
                    refine ⟨1136195931385562580586325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48477693072450670105016533 1136195931385562580586325)
                    ·
                      rfl

theorem cell23_6638201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 7].length) (baseStart_6638201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638201 prefixEnd_6638201 := by exact prefixLift 6638201
  have htrace : WordTrace (prefixWord ++ tailWord_6638201) baseStart_6638201 baseEnd_6638201 := by
    simpa [prefixWord, tailWord_6638201, baseEnd_6638201] using wordTrace_append hprefix tailTrace_6638201
  have hstable : (prefixWord ++ tailWord_6638201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638201).length < 2 ^ (prefixWord ++ tailWord_6638201).sum := by decide
  have hdescent : baseEnd_6638201 < baseStart_6638201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638205 : List Nat := [1, 4, 1, 1, 6, 1, 1, 8]
def baseStart_6638205 : Nat := 118140960795 + 6638205 * 2 ^ 59
def prefixEnd_6638205 : Nat := 4983230072969 + 3 ^ 40 * 6638205 * 2
def baseEnd_6638205 : Nat := 126244068447381693559591

theorem tailTrace_6638205 : CollatzResearch.WordTrace tailWord_6638205 prefixEnd_6638205 126244068447381693559591 := by
  unfold tailWord_6638205
  simp only [CollatzResearch.WordTrace]
  refine ⟨242115226915924474999436069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161410151277282983332957379 242115226915924474999436069)
  ·
    refine ⟨45396605046735839062394263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242115226915924474999436069 45396605046735839062394263)
    ·
      refine ⟨68094907570103758593591395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45396605046735839062394263 68094907570103758593591395)
      ·
        refine ⟨102142361355155637890387093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68094907570103758593591395 102142361355155637890387093)
        ·
          refine ⟨4787923188522920526111895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 102142361355155637890387093 4787923188522920526111895)
          ·
            refine ⟨7181884782784380789167843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4787923188522920526111895 7181884782784380789167843)
            ·
              refine ⟨10772827174176571183751765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7181884782784380789167843 10772827174176571183751765)
              ·
                refine ⟨126244068447381693559591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10772827174176571183751765 126244068447381693559591)
                ·
                  rfl

theorem cell23_6638205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 8].length) (baseStart_6638205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638205 prefixEnd_6638205 := by exact prefixLift 6638205
  have htrace : WordTrace (prefixWord ++ tailWord_6638205) baseStart_6638205 baseEnd_6638205 := by
    simpa [prefixWord, tailWord_6638205, baseEnd_6638205] using wordTrace_append hprefix tailTrace_6638205
  have hstable : (prefixWord ++ tailWord_6638205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638205).length < 2 ^ (prefixWord ++ tailWord_6638205).sum := by decide
  have hdescent : baseEnd_6638205 < baseStart_6638205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638215 : List Nat := [1, 1, 4, 2, 1, 2, 1, 5, 2, 1, 3]
def baseStart_6638215 : Nat := 118140960795 + 6638215 * 2 ^ 59
def prefixEnd_6638215 : Nat := 4983230072969 + 3 ^ 40 * 6638215 * 2
def baseEnd_6638215 : Nat := 3408594982885850686983911

theorem tailTrace_6638215 : CollatzResearch.WordTrace tailWord_6638215 prefixEnd_6638215 3408594982885850686983911 := by
  unfold tailWord_6638215
  simp only [CollatzResearch.WordTrace]
  refine ⟨242115591645888246707300099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161410394430592164471533399 242115591645888246707300099)
  ·
    refine ⟨363173387468832370060950149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242115591645888246707300099 363173387468832370060950149)
    ·
      refine ⟨68095010150406069386428153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 363173387468832370060950149 68095010150406069386428153)
      ·
        refine ⟨51071257612804552039821115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68095010150406069386428153 51071257612804552039821115)
        ·
          refine ⟨76606886419206828059731673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51071257612804552039821115 76606886419206828059731673)
          ·
            refine ⟨57455164814405121044798755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76606886419206828059731673 57455164814405121044798755)
            ·
              refine ⟨86182747221607681567198133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57455164814405121044798755 86182747221607681567198133)
              ·
                refine ⟨8079632552025720146924825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86182747221607681567198133 8079632552025720146924825)
                ·
                  refine ⟨6059724414019290110193619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8079632552025720146924825 6059724414019290110193619)
                  ·
                    refine ⟨9089586621028935165290429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6059724414019290110193619 9089586621028935165290429)
                    ·
                      refine ⟨3408594982885850686983911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9089586621028935165290429 3408594982885850686983911)
                      ·
                        rfl

theorem cell23_6638215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_6638215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638215 prefixEnd_6638215 := by exact prefixLift 6638215
  have htrace : WordTrace (prefixWord ++ tailWord_6638215) baseStart_6638215 baseEnd_6638215 := by
    simpa [prefixWord, tailWord_6638215, baseEnd_6638215] using wordTrace_append hprefix tailTrace_6638215
  have hstable : (prefixWord ++ tailWord_6638215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638215).length < 2 ^ (prefixWord ++ tailWord_6638215).sum := by decide
  have hdescent : baseEnd_6638215 < baseStart_6638215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638231 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 1, 8]
def baseStart_6638231 : Nat := 118140960795 + 6638231 * 2 ^ 59
def prefixEnd_6638231 : Nat := 4983230072969 + 3 ^ 40 * 6638231 * 2
def baseEnd_6638231 : Nat := 1136201066192107541461279

theorem tailTrace_6638231 : CollatzResearch.WordTrace tailWord_6638231 prefixEnd_6638231 1136201066192107541461279 := by
  unfold tailWord_6638231
  simp only [CollatzResearch.WordTrace]
  refine ⟨242116175213830281439882547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161410783475886854293255031 242116175213830281439882547)
  ·
    refine ⟨363174262820745422159823821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242116175213830281439882547 363174262820745422159823821)
    ·
      refine ⟨136190348557779533309933933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363174262820745422159823821 136190348557779533309933933)
      ·
        refine ⟨51071380709167324991225225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136190348557779533309933933 51071380709167324991225225)
        ·
          refine ⟨38303535531875493743418919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51071380709167324991225225 38303535531875493743418919)
          ·
            refine ⟨57455303297813240615128379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38303535531875493743418919 57455303297813240615128379)
            ·
              refine ⟨86182954946719860922692569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57455303297813240615128379 86182954946719860922692569)
              ·
                refine ⟨64637216210039895692019427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86182954946719860922692569 64637216210039895692019427)
                ·
                  refine ⟨96955824315059843538029141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64637216210039895692019427 96955824315059843538029141)
                  ·
                    refine ⟨1136201066192107541461279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96955824315059843538029141 1136201066192107541461279)
                    ·
                      rfl

theorem cell23_6638231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_6638231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638231 prefixEnd_6638231 := by exact prefixLift 6638231
  have htrace : WordTrace (prefixWord ++ tailWord_6638231) baseStart_6638231 baseEnd_6638231 := by
    simpa [prefixWord, tailWord_6638231, baseEnd_6638231] using wordTrace_append hprefix tailTrace_6638231
  have hstable : (prefixWord ++ tailWord_6638231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638231).length < 2 ^ (prefixWord ++ tailWord_6638231).sum := by decide
  have hdescent : baseEnd_6638231 < baseStart_6638231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638268 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 2, 2, 4]
def baseStart_6638268 : Nat := 118140960795 + 6638268 * 2 ^ 59
def prefixEnd_6638268 : Nat := 4983230072969 + 3 ^ 40 * 6638268 * 2
def baseEnd_6638268 : Nat := 3408622197360538979621167

theorem tailTrace_6638268 : CollatzResearch.WordTrace tailWord_6638268 prefixEnd_6638268 3408622197360538979621167 := by
  unfold tailWord_6638268
  simp only [CollatzResearch.WordTrace]
  refine ⟨121058762357348118379489729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161411683143130824505986305 121058762357348118379489729)
  ·
    refine ⟨90794071768011088784617297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121058762357348118379489729 90794071768011088784617297)
    ·
      refine ⟨68095553826008316588462973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90794071768011088784617297 68095553826008316588462973)
      ·
        refine ⟨25535832684753118720673615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68095553826008316588462973 25535832684753118720673615)
        ·
          refine ⟨38303749027129678081010423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25535832684753118720673615 38303749027129678081010423)
          ·
            refine ⟨57455623540694517121515635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38303749027129678081010423 57455623540694517121515635)
            ·
              refine ⟨86183435311041775682273453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57455623540694517121515635 86183435311041775682273453)
              ·
                refine ⟨32318788241640665880852545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86183435311041775682273453 32318788241640665880852545)
                ·
                  refine ⟨24239091181230499410639409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32318788241640665880852545 24239091181230499410639409)
                  ·
                    refine ⟨18179318385922874557979557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24239091181230499410639409 18179318385922874557979557)
                    ·
                      refine ⟨3408622197360538979621167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18179318385922874557979557 3408622197360538979621167)
                      ·
                        rfl

theorem cell23_6638268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_6638268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638268 prefixEnd_6638268 := by exact prefixLift 6638268
  have htrace : WordTrace (prefixWord ++ tailWord_6638268) baseStart_6638268 baseEnd_6638268 := by
    simpa [prefixWord, tailWord_6638268, baseEnd_6638268] using wordTrace_append hprefix tailTrace_6638268
  have hstable : (prefixWord ++ tailWord_6638268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638268).length < 2 ^ (prefixWord ++ tailWord_6638268).sum := by decide
  have hdescent : baseEnd_6638268 < baseStart_6638268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638272 : List Nat := [2, 1, 1, 2, 4, 4, 1, 1, 1, 4, 2]
def baseStart_6638272 : Nat := 118140960795 + 6638272 * 2 ^ 59
def prefixEnd_6638272 : Nat := 4983230072969 + 3 ^ 40 * 6638272 * 2
def baseEnd_6638272 : Nat := 3408624251283156963971149

theorem tailTrace_6638272 : CollatzResearch.WordTrace tailWord_6638272 prefixEnd_6638272 3408624251283156963971149 := by
  unfold tailWord_6638272
  simp only [CollatzResearch.WordTrace]
  refine ⟨121058835303340872721062535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161411780404454496961416713 121058835303340872721062535)
  ·
    refine ⟨181588252955011309081593803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121058835303340872721062535 181588252955011309081593803)
    ·
      refine ⟨272382379432516963622390705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181588252955011309081593803 272382379432516963622390705)
      ·
        refine ⟨204286784574387722716793029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272382379432516963622390705 204286784574387722716793029)
        ·
          refine ⟨38303772107697698009398693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204286784574387722716793029 38303772107697698009398693)
          ·
            refine ⟨7181957270193318376762255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38303772107697698009398693 7181957270193318376762255)
            ·
              refine ⟨10772935905289977565143383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7181957270193318376762255 10772935905289977565143383)
              ·
                refine ⟨16159403857934966347715075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10772935905289977565143383 16159403857934966347715075)
                ·
                  refine ⟨24239105786902449521572613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16159403857934966347715075 24239105786902449521572613)
                  ·
                    refine ⟨4544832335044209285294865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24239105786902449521572613 4544832335044209285294865)
                    ·
                      refine ⟨3408624251283156963971149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4544832335044209285294865 3408624251283156963971149)
                      ·
                        rfl

theorem cell23_6638272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 1, 4, 2].length) (baseStart_6638272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638272 prefixEnd_6638272 := by exact prefixLift 6638272
  have htrace : WordTrace (prefixWord ++ tailWord_6638272) baseStart_6638272 baseEnd_6638272 := by
    simpa [prefixWord, tailWord_6638272, baseEnd_6638272] using wordTrace_append hprefix tailTrace_6638272
  have hstable : (prefixWord ++ tailWord_6638272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638272).length < 2 ^ (prefixWord ++ tailWord_6638272).sum := by decide
  have hdescent : baseEnd_6638272 < baseStart_6638272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638295 : List Nat := [1, 1, 3, 2, 1, 4, 3, 3, 5]
def baseStart_6638295 : Nat := 118140960795 + 6638295 * 2 ^ 59
def prefixEnd_6638295 : Nat := 4983230072969 + 3 ^ 40 * 6638295 * 2
def baseEnd_6638295 : Nat := 378737340148690041553727

theorem tailTrace_6638295 : CollatzResearch.WordTrace tailWord_6638295 prefixEnd_6638295 378737340148690041553727 := by
  unfold tailWord_6638295
  simp only [CollatzResearch.WordTrace]
  refine ⟨242118509485598420370212339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161412339657065613580141559 242118509485598420370212339)
  ·
    refine ⟨363177764228397630555318509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242118509485598420370212339 363177764228397630555318509)
    ·
      refine ⟨136191661585649111458244441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363177764228397630555318509 136191661585649111458244441)
      ·
        refine ⟨102143746189236833593683331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136191661585649111458244441 102143746189236833593683331)
        ·
          refine ⟨153215619283855250390524997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102143746189236833593683331 153215619283855250390524997)
          ·
            refine ⟨28727928615722859448223437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153215619283855250390524997 28727928615722859448223437)
            ·
              refine ⟨10772973230896072293083789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28727928615722859448223437 10772973230896072293083789)
              ·
                refine ⟨4039864961586027109906421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10772973230896072293083789 4039864961586027109906421)
                ·
                  refine ⟨378737340148690041553727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4039864961586027109906421 378737340148690041553727)
                  ·
                    rfl

theorem cell23_6638295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 5].length) (baseStart_6638295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638295 prefixEnd_6638295 := by exact prefixLift 6638295
  have htrace : WordTrace (prefixWord ++ tailWord_6638295) baseStart_6638295 baseEnd_6638295 := by
    simpa [prefixWord, tailWord_6638295, baseEnd_6638295] using wordTrace_append hprefix tailTrace_6638295
  have hstable : (prefixWord ++ tailWord_6638295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638295).length < 2 ^ (prefixWord ++ tailWord_6638295).sum := by decide
  have hdescent : baseEnd_6638295 < baseStart_6638295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638308 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 4, 5]
def baseStart_6638308 : Nat := 118140960795 + 6638308 * 2 ^ 59
def prefixEnd_6638308 : Nat := 4983230072969 + 3 ^ 40 * 6638308 * 2
def baseEnd_6638308 : Nat := 1136214245528906274373661

theorem tailTrace_6638308 : CollatzResearch.WordTrace tailWord_6638308 prefixEnd_6638308 1136214245528906274373661 := by
  unfold tailWord_6638308
  simp only [CollatzResearch.WordTrace]
  refine ⟨121059491817275661795217789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161412655756367549060290385 121059491817275661795217789)
  ·
    refine ⟨45397309431478373173206671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121059491817275661795217789 45397309431478373173206671)
    ·
      refine ⟨68095964147217559759810007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45397309431478373173206671 68095964147217559759810007)
      ·
        refine ⟨102143946220826339639715011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68095964147217559759810007 102143946220826339639715011)
        ·
          refine ⟨153215919331239509459572517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102143946220826339639715011 153215919331239509459572517)
          ·
            refine ⟨28727984874607408023669847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153215919331239509459572517 28727984874607408023669847)
            ·
              refine ⟨43091977311911112035504771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28727984874607408023669847 43091977311911112035504771)
              ·
                refine ⟨64637965967866668053257157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43091977311911112035504771 64637965967866668053257157)
                ·
                  refine ⟨12119618618975000259985717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64637965967866668053257157 12119618618975000259985717)
                  ·
                    refine ⟨1136214245528906274373661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12119618618975000259985717 1136214245528906274373661)
                    ·
                      rfl

theorem cell23_6638308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_6638308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638308 prefixEnd_6638308 := by exact prefixLift 6638308
  have htrace : WordTrace (prefixWord ++ tailWord_6638308) baseStart_6638308 baseEnd_6638308 := by
    simpa [prefixWord, tailWord_6638308, baseEnd_6638308] using wordTrace_append hprefix tailTrace_6638308
  have hstable : (prefixWord ++ tailWord_6638308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638308).length < 2 ^ (prefixWord ++ tailWord_6638308).sum := by decide
  have hdescent : baseEnd_6638308 < baseStart_6638308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638312 : List Nat := [2, 1, 4, 1, 5, 1, 1, 1, 7]
def baseStart_6638312 : Nat := 118140960795 + 6638312 * 2 ^ 59
def prefixEnd_6638312 : Nat := 4983230072969 + 3 ^ 40 * 6638312 * 2
def baseEnd_6638312 : Nat := 378738310056592978607885

theorem tailTrace_6638312 : CollatzResearch.WordTrace tailWord_6638312 prefixEnd_6638312 378738310056592978607885 := by
  unfold tailWord_6638312
  simp only [CollatzResearch.WordTrace]
  refine ⟨121059564763268416136790595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161412753017691221515720793 121059564763268416136790595)
  ·
    refine ⟨181589347144902624205185893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121059564763268416136790595 181589347144902624205185893)
    ·
      refine ⟨34048002589669242038472355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181589347144902624205185893 34048002589669242038472355)
      ·
        refine ⟨51072003884503863057708533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34048002589669242038472355 51072003884503863057708533)
        ·
          refine ⟨4788000364172237161660175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51072003884503863057708533 4788000364172237161660175)
          ·
            refine ⟨7182000546258355742490263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4788000364172237161660175 7182000546258355742490263)
            ·
              refine ⟨10773000819387533613735395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7182000546258355742490263 10773000819387533613735395)
              ·
                refine ⟨16159501229081300420603093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10773000819387533613735395 16159501229081300420603093)
                ·
                  refine ⟨378738310056592978607885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16159501229081300420603093 378738310056592978607885)
                  ·
                    rfl

theorem cell23_6638312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 7].length) (baseStart_6638312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638312 prefixEnd_6638312 := by exact prefixLift 6638312
  have htrace : WordTrace (prefixWord ++ tailWord_6638312) baseStart_6638312 baseEnd_6638312 := by
    simpa [prefixWord, tailWord_6638312, baseEnd_6638312] using wordTrace_append hprefix tailTrace_6638312
  have hstable : (prefixWord ++ tailWord_6638312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638312).length < 2 ^ (prefixWord ++ tailWord_6638312).sum := by decide
  have hdescent : baseEnd_6638312 < baseStart_6638312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638318 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_6638318 : Nat := 118140960795 + 6638318 * 2 ^ 59
def prefixEnd_6638318 : Nat := 4983230072969 + 3 ^ 40 * 6638318 * 2
def baseEnd_6638318 : Nat := 3408647871393263783995937

theorem tailTrace_6638318 : CollatzResearch.WordTrace tailWord_6638318 prefixEnd_6638318 3408647871393263783995937 := by
  unfold tailWord_6638318
  simp only [CollatzResearch.WordTrace]
  refine ⟨30264918545564386912287451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161412898909676730198866405 30264918545564386912287451)
  ·
    refine ⟨45397377818346580368431177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30264918545564386912287451 45397377818346580368431177)
    ·
      refine ⟨34048033363759935276323383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45397377818346580368431177 34048033363759935276323383)
      ·
        refine ⟨51072050045639902914485075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34048033363759935276323383 51072050045639902914485075)
        ·
          refine ⟨76608075068459854371727613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51072050045639902914485075 76608075068459854371727613)
          ·
            refine ⟨28728028150672445389397855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76608075068459854371727613 28728028150672445389397855)
            ·
              refine ⟨43092042226008668084096783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28728028150672445389397855 43092042226008668084096783)
              ·
                refine ⟨64638063339013002126145175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43092042226008668084096783 64638063339013002126145175)
                ·
                  refine ⟨96957095008519503189217763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64638063339013002126145175 96957095008519503189217763)
                  ·
                    refine ⟨145435642512779254783826645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96957095008519503189217763 145435642512779254783826645)
                    ·
                      refine ⟨3408647871393263783995937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145435642512779254783826645 3408647871393263783995937)
                      ·
                        rfl

theorem cell23_6638318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_6638318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638318 prefixEnd_6638318 := by exact prefixLift 6638318
  have htrace : WordTrace (prefixWord ++ tailWord_6638318) baseStart_6638318 baseEnd_6638318 := by
    simpa [prefixWord, tailWord_6638318, baseEnd_6638318] using wordTrace_append hprefix tailTrace_6638318
  have hstable : (prefixWord ++ tailWord_6638318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638318).length < 2 ^ (prefixWord ++ tailWord_6638318).sum := by decide
  have hdescent : baseEnd_6638318 < baseStart_6638318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638328 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 4, 1, 4]
def baseStart_6638328 : Nat := 118140960795 + 6638328 * 2 ^ 59
def prefixEnd_6638328 : Nat := 4983230072969 + 3 ^ 40 * 6638328 * 2
def baseEnd_6638328 : Nat := 3408653006199808744870891

theorem tailTrace_6638328 : CollatzResearch.WordTrace tailWord_6638328 prefixEnd_6638328 3408653006199808744870891 := by
  unfold tailWord_6638328
  simp only [CollatzResearch.WordTrace]
  refine ⟨121059856547239433503081819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161413142062985911337442425 121059856547239433503081819)
  ·
    refine ⟨181589784820859150254622729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121059856547239433503081819 181589784820859150254622729)
    ·
      refine ⟨136192338615644362690967047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181589784820859150254622729 136192338615644362690967047)
      ·
        refine ⟨204288507923466544036450571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136192338615644362690967047 204288507923466544036450571)
        ·
          refine ⟨306432761885199816054675857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204288507923466544036450571 306432761885199816054675857)
          ·
            refine ⟨229824571413899862041006893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306432761885199816054675857 229824571413899862041006893)
            ·
              refine ⟨86184214280212448265377585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229824571413899862041006893 86184214280212448265377585)
              ·
                refine ⟨64638160710159336199033189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86184214280212448265377585 64638160710159336199033189)
                ·
                  refine ⟨12119655133154875537318723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64638160710159336199033189 12119655133154875537318723)
                  ·
                    refine ⟨18179482699732313305978085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12119655133154875537318723 18179482699732313305978085)
                    ·
                      refine ⟨3408653006199808744870891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18179482699732313305978085 3408653006199808744870891)
                      ·
                        rfl

theorem cell23_6638328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_6638328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638328 prefixEnd_6638328 := by exact prefixLift 6638328
  have htrace : WordTrace (prefixWord ++ tailWord_6638328) baseStart_6638328 baseEnd_6638328 := by
    simpa [prefixWord, tailWord_6638328, baseEnd_6638328] using wordTrace_append hprefix tailTrace_6638328
  have hstable : (prefixWord ++ tailWord_6638328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638328).length < 2 ^ (prefixWord ++ tailWord_6638328).sum := by decide
  have hdescent : baseEnd_6638328 < baseStart_6638328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638331 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 9]
def baseStart_6638331 : Nat := 118140960795 + 6638331 * 2 ^ 59
def prefixEnd_6638331 : Nat := 4983230072969 + 3 ^ 40 * 6638331 * 2
def baseEnd_6638331 : Nat := 3408654546641772233133377

theorem tailTrace_6638331 : CollatzResearch.WordTrace tailWord_6638331 prefixEnd_6638331 3408654546641772233133377 := by
  unfold tailWord_6638331
  simp only [CollatzResearch.WordTrace]
  refine ⟨242119822513467998518522847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161413215008978665679015231 242119822513467998518522847)
  ·
    refine ⟨363179733770201997777784271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242119822513467998518522847 363179733770201997777784271)
    ·
      refine ⟨544769600655302996666676407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363179733770201997777784271 544769600655302996666676407)
      ·
        refine ⟨817154400982954495000014611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544769600655302996666676407 817154400982954495000014611)
        ·
          refine ⟨1225731601474431742500021917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817154400982954495000014611 1225731601474431742500021917)
          ·
            refine ⟨459649350552911903437508219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1225731601474431742500021917 459649350552911903437508219)
            ·
              refine ⟨689474025829367855156262329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459649350552911903437508219 689474025829367855156262329)
              ·
                refine ⟨517105519372025891367196747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 689474025829367855156262329 517105519372025891367196747)
                ·
                  refine ⟨775658279058038837050795121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 517105519372025891367196747 775658279058038837050795121)
                  ·
                    refine ⟨581743709293529127788096341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 775658279058038837050795121 581743709293529127788096341)
                    ·
                      refine ⟨3408654546641772233133377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 581743709293529127788096341 3408654546641772233133377)
                      ·
                        rfl

theorem cell23_6638331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 9].length) (baseStart_6638331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638331 prefixEnd_6638331 := by exact prefixLift 6638331
  have htrace : WordTrace (prefixWord ++ tailWord_6638331) baseStart_6638331 baseEnd_6638331 := by
    simpa [prefixWord, tailWord_6638331, baseEnd_6638331] using wordTrace_append hprefix tailTrace_6638331
  have hstable : (prefixWord ++ tailWord_6638331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638331).length < 2 ^ (prefixWord ++ tailWord_6638331).sum := by decide
  have hdescent : baseEnd_6638331 < baseStart_6638331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638455 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 3]
def baseStart_6638455 : Nat := 118140960795 + 6638455 * 2 ^ 59
def prefixEnd_6638455 : Nat := 4983230072969 + 3 ^ 40 * 6638455 * 2
def baseEnd_6638455 : Nat := 3408718218242929747982807

theorem tailTrace_6638455 : CollatzResearch.WordTrace tailWord_6638455 prefixEnd_6638455 3408718218242929747982807 := by
  unfold tailWord_6638455
  simp only [CollatzResearch.WordTrace]
  refine ⟨242124345165018767696036819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161416230110012511797357879 242124345165018767696036819)
  ·
    refine ⟨363186517747528151544055229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242124345165018767696036819 363186517747528151544055229)
    ·
      refine ⟨136194944155323056829020711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363186517747528151544055229 136194944155323056829020711)
      ·
        refine ⟨204292416232984585243531067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136194944155323056829020711 204292416232984585243531067)
        ·
          refine ⟨306438624349476877865296601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204292416232984585243531067 306438624349476877865296601)
          ·
            refine ⟨229828968262107658398972451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306438624349476877865296601 229828968262107658398972451)
            ·
              refine ⟨344743452393161487598458677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229828968262107658398972451 344743452393161487598458677)
              ·
                refine ⟨32319698661858889462355501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 344743452393161487598458677 32319698661858889462355501)
                ·
                  refine ⟨12119886998197083548383313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32319698661858889462355501 12119886998197083548383313)
                  ·
                    refine ⟨9089915248647812661287485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12119886998197083548383313 9089915248647812661287485)
                    ·
                      refine ⟨3408718218242929747982807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9089915248647812661287485 3408718218242929747982807)
                      ·
                        rfl

theorem cell23_6638455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 3].length) (baseStart_6638455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638455 prefixEnd_6638455 := by exact prefixLift 6638455
  have htrace : WordTrace (prefixWord ++ tailWord_6638455) baseStart_6638455 baseEnd_6638455 := by
    simpa [prefixWord, tailWord_6638455, baseEnd_6638455] using wordTrace_append hprefix tailTrace_6638455
  have hstable : (prefixWord ++ tailWord_6638455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638455).length < 2 ^ (prefixWord ++ tailWord_6638455).sum := by decide
  have hdescent : baseEnd_6638455 < baseStart_6638455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638472 : List Nat := [2, 1, 3, 3, 2, 2, 2, 1, 1, 1, 5]
def baseStart_6638472 : Nat := 118140960795 + 6638472 * 2 ^ 59
def prefixEnd_6638472 : Nat := 4983230072969 + 3 ^ 40 * 6638472 * 2
def baseEnd_6638472 : Nat := 3408726947414056181470229

theorem tailTrace_6638472 : CollatzResearch.WordTrace tailWord_6638472 prefixEnd_6638472 3408726947414056181470229 := by
  unfold tailWord_6638472
  simp only [CollatzResearch.WordTrace]
  refine ⟨121062482602978589799702835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161416643470638119732937113 121062482602978589799702835)
  ·
    refine ⟨181593723904467884699554253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121062482602978589799702835 181593723904467884699554253)
    ·
      refine ⟨68097646464175456762332845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181593723904467884699554253 68097646464175456762332845)
      ·
        refine ⟨25536617424065796285874817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68097646464175456762332845 25536617424065796285874817)
        ·
          refine ⟨19152463068049347214406113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25536617424065796285874817 19152463068049347214406113)
          ·
            refine ⟨14364347301037010410804585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19152463068049347214406113 14364347301037010410804585)
            ·
              refine ⟨10773260475777757808103439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14364347301037010410804585 10773260475777757808103439)
              ·
                refine ⟨16159890713666636712155159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10773260475777757808103439 16159890713666636712155159)
                ·
                  refine ⟨24239836070499955068232739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16159890713666636712155159 24239836070499955068232739)
                  ·
                    refine ⟨36359754105749932602349109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24239836070499955068232739 36359754105749932602349109)
                    ·
                      refine ⟨3408726947414056181470229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36359754105749932602349109 3408726947414056181470229)
                      ·
                        rfl

theorem cell23_6638472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_6638472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638472 prefixEnd_6638472 := by exact prefixLift 6638472
  have htrace : WordTrace (prefixWord ++ tailWord_6638472) baseStart_6638472 baseEnd_6638472 := by
    simpa [prefixWord, tailWord_6638472, baseEnd_6638472] using wordTrace_append hprefix tailTrace_6638472
  have hstable : (prefixWord ++ tailWord_6638472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638472).length < 2 ^ (prefixWord ++ tailWord_6638472).sum := by decide
  have hdescent : baseEnd_6638472 < baseStart_6638472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638492 : List Nat := [2, 2, 3, 3, 2, 1, 2, 8]
def baseStart_6638492 : Nat := 118140960795 + 6638492 * 2 ^ 59
def prefixEnd_6638492 : Nat := 4983230072969 + 3 ^ 40 * 6638492 * 2
def baseEnd_6638492 : Nat := 126249526556560966785931

theorem tailTrace_6638492 : CollatzResearch.WordTrace tailWord_6638492 prefixEnd_6638492 126249526556560966785931 := by
  unfold tailWord_6638492
  simp only [CollatzResearch.WordTrace]
  refine ⟨121062847332942361507566865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161417129777256482010089153 121062847332942361507566865)
  ·
    refine ⟨90797135499706771130675149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121062847332942361507566865 90797135499706771130675149)
    ·
      refine ⟨34048925812390039174003181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90797135499706771130675149 34048925812390039174003181)
      ·
        refine ⟨12768347179646264690251193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34048925812390039174003181 12768347179646264690251193)
        ·
          refine ⟨9576260384734698517688395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12768347179646264690251193 9576260384734698517688395)
          ·
            refine ⟨14364390577102047776532593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9576260384734698517688395 14364390577102047776532593)
            ·
              refine ⟨10773292932826535832399445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14364390577102047776532593 10773292932826535832399445)
              ·
                refine ⟨126249526556560966785931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10773292932826535832399445 126249526556560966785931)
                ·
                  rfl

theorem cell23_6638492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 8].length) (baseStart_6638492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638492 prefixEnd_6638492 := by exact prefixLift 6638492
  have htrace : WordTrace (prefixWord ++ tailWord_6638492) baseStart_6638492 baseEnd_6638492 := by
    simpa [prefixWord, tailWord_6638492, baseEnd_6638492] using wordTrace_append hprefix tailTrace_6638492
  have hstable : (prefixWord ++ tailWord_6638492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638492).length < 2 ^ (prefixWord ++ tailWord_6638492).sum := by decide
  have hdescent : baseEnd_6638492 < baseStart_6638492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638536 : List Nat := [2, 1, 3, 1, 5, 1, 2, 2, 2, 1, 3]
def baseStart_6638536 : Nat := 118140960795 + 6638536 * 2 ^ 59
def prefixEnd_6638536 : Nat := 4983230072969 + 3 ^ 40 * 6638536 * 2
def baseEnd_6638536 : Nat := 3408759810175943931069935

theorem tailTrace_6638536 : CollatzResearch.WordTrace tailWord_6638536 prefixEnd_6638536 3408759810175943931069935 := by
  unfold tailWord_6638536
  simp only [CollatzResearch.WordTrace]
  refine ⟨121063649738862659264867731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161418199651816879019823641 121063649738862659264867731)
  ·
    refine ⟨181595474608293988897301597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121063649738862659264867731 181595474608293988897301597)
    ·
      refine ⟨68098302978110245836488099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181595474608293988897301597 68098302978110245836488099)
      ·
        refine ⟨102147454467165368754732149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68098302978110245836488099 102147454467165368754732149)
        ·
          refine ⟨9576323856296753320756139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102147454467165368754732149 9576323856296753320756139)
          ·
            refine ⟨14364485784445129981134209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9576323856296753320756139 14364485784445129981134209)
            ·
              refine ⟨10773364338333847485850657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14364485784445129981134209 10773364338333847485850657)
              ·
                refine ⟨8080023253750385614387993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10773364338333847485850657 8080023253750385614387993)
                ·
                  refine ⟨6060017440312789210790995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8080023253750385614387993 6060017440312789210790995)
                  ·
                    refine ⟨9090026160469183816186493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6060017440312789210790995 9090026160469183816186493)
                    ·
                      refine ⟨3408759810175943931069935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9090026160469183816186493 3408759810175943931069935)
                      ·
                        rfl

theorem cell23_6638536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_6638536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638536 prefixEnd_6638536 := by exact prefixLift 6638536
  have htrace : WordTrace (prefixWord ++ tailWord_6638536) baseStart_6638536 baseEnd_6638536 := by
    simpa [prefixWord, tailWord_6638536, baseEnd_6638536] using wordTrace_append hprefix tailTrace_6638536
  have hstable : (prefixWord ++ tailWord_6638536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638536).length < 2 ^ (prefixWord ++ tailWord_6638536).sum := by decide
  have hdescent : baseEnd_6638536 < baseStart_6638536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638545 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 1, 6, 3]
def baseStart_6638545 : Nat := 118140960795 + 6638545 * 2 ^ 59
def prefixEnd_6638545 : Nat := 4983230072969 + 3 ^ 40 * 6638545 * 2
def baseEnd_6638545 : Nat := 3408764431501834395857393

theorem tailTrace_6638545 : CollatzResearch.WordTrace tailWord_6638545 prefixEnd_6638545 3408764431501834395857393 := by
  unfold tailWord_6638545
  simp only [CollatzResearch.WordTrace]
  refine ⟨242127627734692713066813089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161418418489795142044542059 242127627734692713066813089)
  ·
    refine ⟨181595720801019534800109817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242127627734692713066813089 181595720801019534800109817)
    ·
      refine ⟨136196790600764651100082363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181595720801019534800109817 136196790600764651100082363)
      ·
        refine ⟨204295185901146976650123545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136196790600764651100082363 204295185901146976650123545)
        ·
          refine ⟨153221389425860232487592659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204295185901146976650123545 153221389425860232487592659)
          ·
            refine ⟨229832084138790348731388989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153221389425860232487592659 229832084138790348731388989)
            ·
              refine ⟨86187031552046380774270871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229832084138790348731388989 86187031552046380774270871)
              ·
                refine ⟨129280547328069571161406307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86187031552046380774270871 129280547328069571161406307)
                ·
                  refine ⟨193920820992104356742109461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129280547328069571161406307 193920820992104356742109461)
                  ·
                    refine ⟨9090038484004891722286381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 193920820992104356742109461 9090038484004891722286381)
                    ·
                      refine ⟨3408764431501834395857393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9090038484004891722286381 3408764431501834395857393)
                      ·
                        rfl

theorem cell23_6638545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 6, 3].length) (baseStart_6638545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638545 prefixEnd_6638545 := by exact prefixLift 6638545
  have htrace : WordTrace (prefixWord ++ tailWord_6638545) baseStart_6638545 baseEnd_6638545 := by
    simpa [prefixWord, tailWord_6638545, baseEnd_6638545] using wordTrace_append hprefix tailTrace_6638545
  have hstable : (prefixWord ++ tailWord_6638545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638545).length < 2 ^ (prefixWord ++ tailWord_6638545).sum := by decide
  have hdescent : baseEnd_6638545 < baseStart_6638545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638593 : List Nat := [1, 2, 4, 1, 2, 4, 1, 2, 2, 2, 2]
def baseStart_6638593 : Nat := 118140960795 + 6638593 * 2 ^ 59
def prefixEnd_6638593 : Nat := 4983230072969 + 3 ^ 40 * 6638593 * 2
def baseEnd_6638593 : Nat := 3408789078573250208057173

theorem tailTrace_6638593 : CollatzResearch.WordTrace tailWord_6638593 prefixEnd_6638593 3408789078573250208057173 := by
  unfold tailWord_6638593
  simp only [CollatzResearch.WordTrace]
  refine ⟨242129378438518817264560433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161419585625679211509706955 242129378438518817264560433)
  ·
    refine ⟨181597033828889112948420325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242129378438518817264560433 181597033828889112948420325)
    ·
      refine ⟨34049443842916708677828811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181597033828889112948420325 34049443842916708677828811)
      ·
        refine ⟨51074165764375063016743217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34049443842916708677828811 51074165764375063016743217)
        ·
          refine ⟨38305624323281297262557413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51074165764375063016743217 38305624323281297262557413)
          ·
            refine ⟨7182304560615243236729515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38305624323281297262557413 7182304560615243236729515)
            ·
              refine ⟨10773456840922864855094273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7182304560615243236729515 10773456840922864855094273)
              ·
                refine ⟨8080092630692148641320705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10773456840922864855094273 8080092630692148641320705)
                ·
                  refine ⟨6060069473019111480990529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8080092630692148641320705 6060069473019111480990529)
                  ·
                    refine ⟨4545052104764333610742897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6060069473019111480990529 4545052104764333610742897)
                    ·
                      refine ⟨3408789078573250208057173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4545052104764333610742897 3408789078573250208057173)
                      ·
                        rfl

theorem cell23_6638593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_6638593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638593 prefixEnd_6638593 := by exact prefixLift 6638593
  have htrace : WordTrace (prefixWord ++ tailWord_6638593) baseStart_6638593 baseEnd_6638593 := by
    simpa [prefixWord, tailWord_6638593, baseEnd_6638593] using wordTrace_append hprefix tailTrace_6638593
  have hstable : (prefixWord ++ tailWord_6638593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638593).length < 2 ^ (prefixWord ++ tailWord_6638593).sum := by decide
  have hdescent : baseEnd_6638593 < baseStart_6638593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638649 : List Nat := [1, 2, 1, 5, 2, 2, 1, 2, 2, 1, 4]
def baseStart_6638649 : Nat := 118140960795 + 6638649 * 2 ^ 59
def prefixEnd_6638649 : Nat := 4983230072969 + 3 ^ 40 * 6638649 * 2
def baseEnd_6638649 : Nat := 3408817833489901988956915

theorem tailTrace_6638649 : CollatzResearch.WordTrace tailWord_6638649 prefixEnd_6638649 3408817833489901988956915 := by
  unfold tailWord_6638649
  simp only [CollatzResearch.WordTrace]
  refine ⟨242131420926315938828599001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161420947284210625885732667 242131420926315938828599001)
  ·
    refine ⟨181598565694736954121449251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242131420926315938828599001 181598565694736954121449251)
    ·
      refine ⟨272397848542105431182173877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181598565694736954121449251 272397848542105431182173877)
      ·
        refine ⟨25537298300822384173328801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 272397848542105431182173877 25537298300822384173328801)
        ·
          refine ⟨19152973725616788129996601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25537298300822384173328801 19152973725616788129996601)
          ·
            refine ⟨14364730294212591097497451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19152973725616788129996601 14364730294212591097497451)
            ·
              refine ⟨21547095441318886646246177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14364730294212591097497451 21547095441318886646246177)
              ·
                refine ⟨16160321580989164984684633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21547095441318886646246177 16160321580989164984684633)
                ·
                  refine ⟨12120241185741873738513475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16160321580989164984684633 12120241185741873738513475)
                  ·
                    refine ⟨18180361778612810607770213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12120241185741873738513475 18180361778612810607770213)
                    ·
                      refine ⟨3408817833489901988956915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18180361778612810607770213 3408817833489901988956915)
                      ·
                        rfl

theorem cell23_6638649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_6638649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638649 prefixEnd_6638649 := by exact prefixLift 6638649
  have htrace : WordTrace (prefixWord ++ tailWord_6638649) baseStart_6638649 baseEnd_6638649 := by
    simpa [prefixWord, tailWord_6638649, baseEnd_6638649] using wordTrace_append hprefix tailTrace_6638649
  have hstable : (prefixWord ++ tailWord_6638649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638649).length < 2 ^ (prefixWord ++ tailWord_6638649).sum := by decide
  have hdescent : baseEnd_6638649 < baseStart_6638649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638675 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 6]
def baseStart_6638675 : Nat := 118140960795 + 6638675 * 2 ^ 59
def prefixEnd_6638675 : Nat := 4983230072969 + 3 ^ 40 * 6638675 * 2
def baseEnd_6638675 : Nat := 3408831183986918887231795

theorem tailTrace_6638675 : CollatzResearch.WordTrace tailWord_6638675 prefixEnd_6638675 3408831183986918887231795 := by
  unfold tailWord_6638675
  simp only [CollatzResearch.WordTrace]
  refine ⟨242132369224221745269045479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161421579482814496846030319 242132369224221745269045479)
  ·
    refine ⟨363198553836332617903568219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242132369224221745269045479 363198553836332617903568219)
    ·
      refine ⟨544797830754498926855352329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363198553836332617903568219 544797830754498926855352329)
      ·
        refine ⟨408598373065874195141514247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 544797830754498926855352329 408598373065874195141514247)
        ·
          refine ⟨612897559598811292712271371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408598373065874195141514247 612897559598811292712271371)
          ·
            refine ⟨919346339398216939068407057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612897559598811292712271371 919346339398216939068407057)
            ·
              refine ⟨689509754548662704301305293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 919346339398216939068407057 689509754548662704301305293)
              ·
                refine ⟨258566157955748514112989485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 689509754548662704301305293 258566157955748514112989485)
                ·
                  refine ⟨96962309233405692792371057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 258566157955748514112989485 96962309233405692792371057)
                  ·
                    refine ⟨72721731925054269594278293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96962309233405692792371057 72721731925054269594278293)
                    ·
                      refine ⟨3408831183986918887231795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72721731925054269594278293 3408831183986918887231795)
                      ·
                        rfl

theorem cell23_6638675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_6638675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638675 prefixEnd_6638675 := by exact prefixLift 6638675
  have htrace : WordTrace (prefixWord ++ tailWord_6638675) baseStart_6638675 baseEnd_6638675 := by
    simpa [prefixWord, tailWord_6638675, baseEnd_6638675] using wordTrace_append hprefix tailTrace_6638675
  have hstable : (prefixWord ++ tailWord_6638675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638675).length < 2 ^ (prefixWord ++ tailWord_6638675).sum := by decide
  have hdescent : baseEnd_6638675 < baseStart_6638675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638743 : List Nat := [1, 1, 3, 3, 3, 3, 1, 1, 2, 3, 2]
def baseStart_6638743 : Nat := 118140960795 + 6638743 * 2 ^ 59
def prefixEnd_6638743 : Nat := 4983230072969 + 3 ^ 40 * 6638743 * 2
def baseEnd_6638743 : Nat := 3408866100671424621181483

theorem tailTrace_6638743 : CollatzResearch.WordTrace tailWord_6638743 prefixEnd_6638743 3408866100671424621181483 := by
  unfold tailWord_6638743
  simp only [CollatzResearch.WordTrace]
  refine ⟨242134849387975392882520883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161423232925316928588347255 242134849387975392882520883)
  ·
    refine ⟨363202274081963089323781325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242134849387975392882520883 363202274081963089323781325)
    ·
      refine ⟨136200852780736158496417997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363202274081963089323781325 136200852780736158496417997)
      ·
        refine ⟨51075319792776059436156749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136200852780736158496417997 51075319792776059436156749)
        ·
          refine ⟨19153244922291022288558781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51075319792776059436156749 19153244922291022288558781)
          ·
            refine ⟨7182466845859133358209543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19153244922291022288558781 7182466845859133358209543)
            ·
              refine ⟨10773700268788700037314315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7182466845859133358209543 10773700268788700037314315)
              ·
                refine ⟨16160550403183050055971473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10773700268788700037314315 16160550403183050055971473)
                ·
                  refine ⟨12120412802387287541978605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16160550403183050055971473 12120412802387287541978605)
                  ·
                    refine ⟨4545154800895232828241977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12120412802387287541978605 4545154800895232828241977)
                    ·
                      refine ⟨3408866100671424621181483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4545154800895232828241977 3408866100671424621181483)
                      ·
                        rfl

theorem cell23_6638743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_6638743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638743 prefixEnd_6638743 := by exact prefixLift 6638743
  have htrace : WordTrace (prefixWord ++ tailWord_6638743) baseStart_6638743 baseEnd_6638743 := by
    simpa [prefixWord, tailWord_6638743, baseEnd_6638743] using wordTrace_append hprefix tailTrace_6638743
  have hstable : (prefixWord ++ tailWord_6638743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638743).length < 2 ^ (prefixWord ++ tailWord_6638743).sum := by decide
  have hdescent : baseEnd_6638743 < baseStart_6638743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638749 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 4, 4]
def baseStart_6638749 : Nat := 118140960795 + 6638749 * 2 ^ 59
def prefixEnd_6638749 : Nat := 4983230072969 + 3 ^ 40 * 6638749 * 2
def baseEnd_6638749 : Nat := 1136289727185117199235485

theorem tailTrace_6638749 : CollatzResearch.WordTrace tailWord_6638749 prefixEnd_6638749 1136289727185117199235485 := by
  unfold tailWord_6638749
  simp only [CollatzResearch.WordTrace]
  refine ⟨242135068225953655907239301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161423378817302437271492867 242135068225953655907239301)
  ·
    refine ⟨45400325292366310482607369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242135068225953655907239301 45400325292366310482607369)
    ·
      refine ⟨34050243969274732861955527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45400325292366310482607369 34050243969274732861955527)
      ·
        refine ⟨51075365953912099292933291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34050243969274732861955527 51075365953912099292933291)
        ·
          refine ⟨76613048930868148939399937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51075365953912099292933291 76613048930868148939399937)
          ·
            refine ⟨57459786698151111704549953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76613048930868148939399937 57459786698151111704549953)
            ·
              refine ⟨43094840023613333778412465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57459786698151111704549953 43094840023613333778412465)
              ·
                refine ⟨32321130017710000333809349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43094840023613333778412465 32321130017710000333809349)
                ·
                  refine ⟨6060211878320625062589253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32321130017710000333809349 6060211878320625062589253)
                  ·
                    refine ⟨1136289727185117199235485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6060211878320625062589253 1136289727185117199235485)
                    ·
                      rfl

theorem cell23_6638749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_6638749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638749 prefixEnd_6638749 := by exact prefixLift 6638749
  have htrace : WordTrace (prefixWord ++ tailWord_6638749) baseStart_6638749 baseEnd_6638749 := by
    simpa [prefixWord, tailWord_6638749, baseEnd_6638749] using wordTrace_append hprefix tailTrace_6638749
  have hstable : (prefixWord ++ tailWord_6638749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638749).length < 2 ^ (prefixWord ++ tailWord_6638749).sum := by decide
  have hdescent : baseEnd_6638749 < baseStart_6638749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638750 : List Nat := [4, 3, 1, 1, 2, 1, 1, 5, 1, 1, 3]
def baseStart_6638750 : Nat := 118140960795 + 6638750 * 2 ^ 59
def prefixEnd_6638750 : Nat := 4983230072969 + 3 ^ 40 * 6638750 * 2
def baseEnd_6638750 : Nat := 3408869695036006093793951

theorem tailTrace_6638750 : CollatzResearch.WordTrace tailWord_6638750 prefixEnd_6638750 3408869695036006093793951 := by
  unfold tailWord_6638750
  simp only [CollatzResearch.WordTrace]
  refine ⟨30266888087368754134753213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161423403132633355385350469 30266888087368754134753213)
  ·
    refine ⟨11350083032763282800532455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30266888087368754134753213 11350083032763282800532455)
    ·
      refine ⟨17025124549144924200798683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11350083032763282800532455 17025124549144924200798683)
      ·
        refine ⟨25537686823717386301198025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17025124549144924200798683 25537686823717386301198025)
        ·
          refine ⟨19153265117788039725898519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25537686823717386301198025 19153265117788039725898519)
          ·
            refine ⟨28729897676682059588847779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19153265117788039725898519 28729897676682059588847779)
            ·
              refine ⟨43094846515023089383271669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28729897676682059588847779 43094846515023089383271669)
              ·
                refine ⟨4040141860783414629681719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43094846515023089383271669 4040141860783414629681719)
                ·
                  refine ⟨6060212791175121944522579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4040141860783414629681719 6060212791175121944522579)
                  ·
                    refine ⟨9090319186762682916783869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6060212791175121944522579 9090319186762682916783869)
                    ·
                      refine ⟨3408869695036006093793951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9090319186762682916783869 3408869695036006093793951)
                      ·
                        rfl

theorem cell23_6638750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_6638750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638750 prefixEnd_6638750 := by exact prefixLift 6638750
  have htrace : WordTrace (prefixWord ++ tailWord_6638750) baseStart_6638750 baseEnd_6638750 := by
    simpa [prefixWord, tailWord_6638750, baseEnd_6638750] using wordTrace_append hprefix tailTrace_6638750
  have hstable : (prefixWord ++ tailWord_6638750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638750).length < 2 ^ (prefixWord ++ tailWord_6638750).sum := by decide
  have hdescent : baseEnd_6638750 < baseStart_6638750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638756 : List Nat := [2, 3, 1, 2, 3, 2, 1, 3, 1, 1, 4]
def baseStart_6638756 : Nat := 118140960795 + 6638756 * 2 ^ 59
def prefixEnd_6638756 : Nat := 4983230072969 + 3 ^ 40 * 6638756 * 2
def baseEnd_6638756 : Nat := 3408872775919933070318923

theorem tailTrace_6638756 : CollatzResearch.WordTrace tailWord_6638756 prefixEnd_6638756 3408872775919933070318923 := by
  unfold tailWord_6638756
  simp only [CollatzResearch.WordTrace]
  refine ⟨121067661768464148051372061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161423549024618864068496081 121067661768464148051372061)
  ·
    refine ⟨45400373163174055519264523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121067661768464148051372061 45400373163174055519264523)
    ·
      refine ⟨68100559744761083278896785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45400373163174055519264523 68100559744761083278896785)
      ·
        refine ⟨51075419808570812459172589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68100559744761083278896785 51075419808570812459172589)
        ·
          refine ⟨19153282428214054672189721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51075419808570812459172589 19153282428214054672189721)
          ·
            refine ⟨14364961821160541004142291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19153282428214054672189721 14364961821160541004142291)
            ·
              refine ⟨21547442731740811506213437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14364961821160541004142291 21547442731740811506213437)
              ·
                refine ⟨8080291024402804314830039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21547442731740811506213437 8080291024402804314830039)
                ·
                  refine ⟨12120436536604206472245059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8080291024402804314830039 12120436536604206472245059)
                  ·
                    refine ⟨18180654804906309708367589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12120436536604206472245059 18180654804906309708367589)
                    ·
                      refine ⟨3408872775919933070318923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18180654804906309708367589 3408872775919933070318923)
                      ·
                        rfl

theorem cell23_6638756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_6638756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638756 prefixEnd_6638756 := by exact prefixLift 6638756
  have htrace : WordTrace (prefixWord ++ tailWord_6638756) baseStart_6638756 baseEnd_6638756 := by
    simpa [prefixWord, tailWord_6638756, baseEnd_6638756] using wordTrace_append hprefix tailTrace_6638756
  have hstable : (prefixWord ++ tailWord_6638756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638756).length < 2 ^ (prefixWord ++ tailWord_6638756).sum := by decide
  have hdescent : baseEnd_6638756 < baseStart_6638756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638792 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 2, 7]
def baseStart_6638792 : Nat := 118140960795 + 6638792 * 2 ^ 59
def prefixEnd_6638792 : Nat := 4983230072969 + 3 ^ 40 * 6638792 * 2
def baseEnd_6638792 : Nat := 1136297087074498309822919

theorem tailTrace_6638792 : CollatzResearch.WordTrace tailWord_6638792 prefixEnd_6638792 1136297087074498309822919 := by
  unfold tailWord_6638792
  simp only [CollatzResearch.WordTrace]
  refine ⟨121068318282398937125527315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161424424376531916167369753 121068318282398937125527315)
  ·
    refine ⟨181602477423598405688290973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121068318282398937125527315 181602477423598405688290973)
    ·
      refine ⟨68100929033849402133109115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181602477423598405688290973 68100929033849402133109115)
      ·
        refine ⟨102151393550774103199663673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68100929033849402133109115 102151393550774103199663673)
        ·
          refine ⟨76613545163080577399747755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102151393550774103199663673 76613545163080577399747755)
          ·
            refine ⟨114920317744620866099621633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76613545163080577399747755 114920317744620866099621633)
            ·
              refine ⟨86190238308465649574716225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114920317744620866099621633 86190238308465649574716225)
              ·
                refine ⟨64642678731349237181037169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86190238308465649574716225 64642678731349237181037169)
                ·
                  refine ⟨48482009048511927885777877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64642678731349237181037169 48482009048511927885777877)
                  ·
                    refine ⟨1136297087074498309822919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48482009048511927885777877 1136297087074498309822919)
                    ·
                      rfl

theorem cell23_6638792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_6638792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638792 prefixEnd_6638792 := by exact prefixLift 6638792
  have htrace : WordTrace (prefixWord ++ tailWord_6638792) baseStart_6638792 baseEnd_6638792 := by
    simpa [prefixWord, tailWord_6638792, baseEnd_6638792] using wordTrace_append hprefix tailTrace_6638792
  have hstable : (prefixWord ++ tailWord_6638792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638792).length < 2 ^ (prefixWord ++ tailWord_6638792).sum := by decide
  have hdescent : baseEnd_6638792 < baseStart_6638792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638849 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_6638849 : Nat := 118140960795 + 6638849 * 2 ^ 59
def prefixEnd_6638849 : Nat := 4983230072969 + 3 ^ 40 * 6638849 * 2
def baseEnd_6638849 : Nat := 3408920529620801206455995

theorem tailTrace_6638849 : CollatzResearch.WordTrace tailWord_6638849 prefixEnd_6638849 3408920529620801206455995 := by
  unfold tailWord_6638849
  simp only [CollatzResearch.WordTrace]
  refine ⟨242138715525591372985879601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161425810350394248657253067 242138715525591372985879601)
  ·
    refine ⟨181604036644193529739409701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242138715525591372985879601 181604036644193529739409701)
    ·
      refine ⟨34050756870786286826139319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181604036644193529739409701 34050756870786286826139319)
      ·
        refine ⟨51076135306179430239208979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34050756870786286826139319 51076135306179430239208979)
        ·
          refine ⟨76614202959269145358813469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51076135306179430239208979 76614202959269145358813469)
          ·
            refine ⟨28730326109725929509555051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76614202959269145358813469 28730326109725929509555051)
            ·
              refine ⟨43095489164588894264332577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28730326109725929509555051 43095489164588894264332577)
              ·
                refine ⟨32321616873441670698249433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43095489164588894264332577 32321616873441670698249433)
                ·
                  refine ⟨24241212655081253023687075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32321616873441670698249433 24241212655081253023687075)
                  ·
                    refine ⟨36361818982621879535530613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24241212655081253023687075 36361818982621879535530613)
                    ·
                      refine ⟨3408920529620801206455995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36361818982621879535530613 3408920529620801206455995)
                      ·
                        rfl

theorem cell23_6638849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_6638849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638849 prefixEnd_6638849 := by exact prefixLift 6638849
  have htrace : WordTrace (prefixWord ++ tailWord_6638849) baseStart_6638849 baseEnd_6638849 := by
    simpa [prefixWord, tailWord_6638849, baseEnd_6638849] using wordTrace_append hprefix tailTrace_6638849
  have hstable : (prefixWord ++ tailWord_6638849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638849).length < 2 ^ (prefixWord ++ tailWord_6638849).sum := by decide
  have hdescent : baseEnd_6638849 < baseStart_6638849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638850 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 3, 3, 2]
def baseStart_6638850 : Nat := 118140960795 + 6638850 * 2 ^ 59
def prefixEnd_6638850 : Nat := 4983230072969 + 3 ^ 40 * 6638850 * 2
def baseEnd_6638850 : Nat := 3408921043101455702543491

theorem tailTrace_6638850 : CollatzResearch.WordTrace tailWord_6638850 prefixEnd_6638850 3408921043101455702543491 := by
  unfold tailWord_6638850
  simp only [CollatzResearch.WordTrace]
  refine ⟨60534687999646937539166501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161425834665725166771110669 60534687999646937539166501)
  ·
    refine ⟨11350253999933800788593719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60534687999646937539166501 11350253999933800788593719)
    ·
      refine ⟨17025380999900701182890579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11350253999933800788593719 17025380999900701182890579)
      ·
        refine ⟨25538071499851051774335869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17025380999900701182890579 25538071499851051774335869)
        ·
          refine ⟨9576776812444144415375951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25538071499851051774335869 9576776812444144415375951)
          ·
            refine ⟨14365165218666216623063927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9576776812444144415375951 14365165218666216623063927)
            ·
              refine ⟨21547747827999324934595891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14365165218666216623063927 21547747827999324934595891)
              ·
                refine ⟨32321621741998987401893837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21547747827999324934595891 32321621741998987401893837)
                ·
                  refine ⟨12120608153249620275710189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32321621741998987401893837 12120608153249620275710189)
                  ·
                    refine ⟨4545228057468607603391321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12120608153249620275710189 4545228057468607603391321)
                    ·
                      refine ⟨3408921043101455702543491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4545228057468607603391321 3408921043101455702543491)
                      ·
                        rfl

theorem cell23_6638850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_6638850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638850 prefixEnd_6638850 := by exact prefixLift 6638850
  have htrace : WordTrace (prefixWord ++ tailWord_6638850) baseStart_6638850 baseEnd_6638850 := by
    simpa [prefixWord, tailWord_6638850, baseEnd_6638850] using wordTrace_append hprefix tailTrace_6638850
  have hstable : (prefixWord ++ tailWord_6638850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638850).length < 2 ^ (prefixWord ++ tailWord_6638850).sum := by decide
  have hdescent : baseEnd_6638850 < baseStart_6638850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638893 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_6638893 : Nat := 118140960795 + 6638893 * 2 ^ 59
def prefixEnd_6638893 : Nat := 4983230072969 + 3 ^ 40 * 6638893 * 2
def baseEnd_6638893 : Nat := 3408943122769599034305793

theorem tailTrace_6638893 : CollatzResearch.WordTrace tailWord_6638893 prefixEnd_6638893 3408943122769599034305793 := by
  unfold tailWord_6638893
  simp only [CollatzResearch.WordTrace]
  refine ⟨242140320337431968500481333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161426880224954645666987555 242140320337431968500481333)
  ·
    refine ⟨22700655031634247046920125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242140320337431968500481333 22700655031634247046920125)
    ·
      refine ⟨8512745636862842642595047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22700655031634247046920125 8512745636862842642595047)
      ·
        refine ⟨12769118455294263963892571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8512745636862842642595047 12769118455294263963892571)
        ·
          refine ⟨19153677682941395945838857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12769118455294263963892571 19153677682941395945838857)
          ·
            refine ⟨14365258262206046959379143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19153677682941395945838857 14365258262206046959379143)
            ·
              refine ⟨21547887393309070439068715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14365258262206046959379143 21547887393309070439068715)
              ·
                refine ⟨32321831089963605658603073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21547887393309070439068715 32321831089963605658603073)
                ·
                  refine ⟨24241373317472704243952305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32321831089963605658603073 24241373317472704243952305)
                  ·
                    refine ⟨18181029988104528182964229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24241373317472704243952305 18181029988104528182964229)
                    ·
                      refine ⟨3408943122769599034305793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18181029988104528182964229 3408943122769599034305793)
                      ·
                        rfl

theorem cell23_6638893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_6638893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638893 prefixEnd_6638893 := by exact prefixLift 6638893
  have htrace : WordTrace (prefixWord ++ tailWord_6638893) baseStart_6638893 baseEnd_6638893 := by
    simpa [prefixWord, tailWord_6638893, baseEnd_6638893] using wordTrace_append hprefix tailTrace_6638893
  have hstable : (prefixWord ++ tailWord_6638893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638893).length < 2 ^ (prefixWord ++ tailWord_6638893).sum := by decide
  have hdescent : baseEnd_6638893 < baseStart_6638893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638906 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2]
def baseStart_6638906 : Nat := 118140960795 + 6638906 * 2 ^ 59
def prefixEnd_6638906 : Nat := 4983230072969 + 3 ^ 40 * 6638906 * 2
def baseEnd_6638906 : Nat := 3408949798018107483443233

theorem tailTrace_6638906 : CollatzResearch.WordTrace tailWord_6638906 prefixEnd_6638906 3408949798018107483443233 := by
  unfold tailWord_6638906
  simp only [CollatzResearch.WordTrace]
  refine ⟨60535198621596217930176143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161427196324256581147136381 60535198621596217930176143)
  ·
    refine ⟨90802797932394326895264215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60535198621596217930176143 90802797932394326895264215)
    ·
      refine ⟨136204196898591490342896323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90802797932394326895264215 136204196898591490342896323)
      ·
        refine ⟨204306295347887235514344485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136204196898591490342896323 204306295347887235514344485)
        ·
          refine ⟨38307430377728856658939591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204306295347887235514344485 38307430377728856658939591)
          ·
            refine ⟨57461145566593284988409387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38307430377728856658939591 57461145566593284988409387)
            ·
              refine ⟨86191718349889927482614081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57461145566593284988409387 86191718349889927482614081)
              ·
                refine ⟨64643788762417445611960561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86191718349889927482614081 64643788762417445611960561)
                ·
                  refine ⟨48482841571813084208970421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64643788762417445611960561 48482841571813084208970421)
                  ·
                    refine ⟨4545266397357476644590977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48482841571813084208970421 4545266397357476644590977)
                    ·
                      refine ⟨3408949798018107483443233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4545266397357476644590977 3408949798018107483443233)
                      ·
                        rfl

theorem cell23_6638906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2].length) (baseStart_6638906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638906 prefixEnd_6638906 := by exact prefixLift 6638906
  have htrace : WordTrace (prefixWord ++ tailWord_6638906) baseStart_6638906 baseEnd_6638906 := by
    simpa [prefixWord, tailWord_6638906, baseEnd_6638906] using wordTrace_append hprefix tailTrace_6638906
  have hstable : (prefixWord ++ tailWord_6638906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638906).length < 2 ^ (prefixWord ++ tailWord_6638906).sum := by decide
  have hdescent : baseEnd_6638906 < baseStart_6638906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638918 : List Nat := [6, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2]
def baseStart_6638918 : Nat := 118140960795 + 6638918 * 2 ^ 59
def prefixEnd_6638918 : Nat := 4983230072969 + 3 ^ 40 * 6638918 * 2
def baseEnd_6638918 : Nat := 3408955959785961436493179

theorem tailTrace_6638918 : CollatzResearch.WordTrace tailWord_6638918 prefixEnd_6638918 3408955959785961436493179 := by
  unfold tailWord_6638918
  simp only [CollatzResearch.WordTrace]
  refine ⟨7566913505073168680316919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 161427488108227598513427605 7566913505073168680316919)
  ·
    refine ⟨11350370257609753020475379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7566913505073168680316919 11350370257609753020475379)
    ·
      refine ⟨17025555386414629530713069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11350370257609753020475379 17025555386414629530713069)
      ·
        refine ⟨6384583269905486074017401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17025555386414629530713069 6384583269905486074017401)
        ·
          refine ⟨4788437452429114555513051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6384583269905486074017401 4788437452429114555513051)
          ·
            refine ⟨7182656178643671833269577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4788437452429114555513051 7182656178643671833269577)
            ·
              refine ⟨5386992133982753874952183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7182656178643671833269577 5386992133982753874952183)
              ·
                refine ⟨8080488200974130812428275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5386992133982753874952183 8080488200974130812428275)
                ·
                  refine ⟨12120732301461196218642413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8080488200974130812428275 12120732301461196218642413)
                  ·
                    refine ⟨4545274613047948581990905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12120732301461196218642413 4545274613047948581990905)
                    ·
                      refine ⟨3408955959785961436493179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4545274613047948581990905 3408955959785961436493179)
                      ·
                        rfl

theorem cell23_6638918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_6638918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638918 prefixEnd_6638918 := by exact prefixLift 6638918
  have htrace : WordTrace (prefixWord ++ tailWord_6638918) baseStart_6638918 baseEnd_6638918 := by
    simpa [prefixWord, tailWord_6638918, baseEnd_6638918] using wordTrace_append hprefix tailTrace_6638918
  have hstable : (prefixWord ++ tailWord_6638918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638918).length < 2 ^ (prefixWord ++ tailWord_6638918).sum := by decide
  have hdescent : baseEnd_6638918 < baseStart_6638918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638936 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 4, 4, 2]
def baseStart_6638936 : Nat := 118140960795 + 6638936 * 2 ^ 59
def prefixEnd_6638936 : Nat := 4983230072969 + 3 ^ 40 * 6638936 * 2
def baseEnd_6638936 : Nat := 3408965202437742366068095

theorem tailTrace_6638936 : CollatzResearch.WordTrace tailWord_6638936 prefixEnd_6638936 3408965202437742366068095 := by
  unfold tailWord_6638936
  simp only [CollatzResearch.WordTrace]
  refine ⟨121070944338138093422148331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161427925784184124562864441 121070944338138093422148331)
  ·
    refine ⟨181606416507207140133222497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121070944338138093422148331 181606416507207140133222497)
    ·
      refine ⟨136204812380405355099916873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181606416507207140133222497 136204812380405355099916873)
      ·
        refine ⟨102153609285304016324937655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136204812380405355099916873 102153609285304016324937655)
        ·
          refine ⟨153230413927956024487406483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102153609285304016324937655 153230413927956024487406483)
          ·
            refine ⟨229845620891934036731109725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153230413927956024487406483 229845620891934036731109725)
            ·
              refine ⟨86192107834475263774166147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229845620891934036731109725 86192107834475263774166147)
              ·
                refine ⟨129288161751712895661249221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86192107834475263774166147 129288161751712895661249221)
                ·
                  refine ⟨24241530328446167936484229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129288161751712895661249221 24241530328446167936484229)
                  ·
                    refine ⟨4545286936583656488090793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24241530328446167936484229 4545286936583656488090793)
                    ·
                      refine ⟨3408965202437742366068095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4545286936583656488090793 3408965202437742366068095)
                      ·
                        rfl

theorem cell23_6638936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 4, 4, 2].length) (baseStart_6638936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638936 prefixEnd_6638936 := by exact prefixLift 6638936
  have htrace : WordTrace (prefixWord ++ tailWord_6638936) baseStart_6638936 baseEnd_6638936 := by
    simpa [prefixWord, tailWord_6638936, baseEnd_6638936] using wordTrace_append hprefix tailTrace_6638936
  have hstable : (prefixWord ++ tailWord_6638936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638936).length < 2 ^ (prefixWord ++ tailWord_6638936).sum := by decide
  have hdescent : baseEnd_6638936 < baseStart_6638936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638949 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 2, 1, 6]
def baseStart_6638949 : Nat := 118140960795 + 6638949 * 2 ^ 59
def prefixEnd_6638949 : Nat := 4983230072969 + 3 ^ 40 * 6638949 * 2
def baseEnd_6638949 : Nat := 3408971877686250815205535

theorem tailTrace_6638949 : CollatzResearch.WordTrace tailWord_6638949 prefixEnd_6638949 3408971877686250815205535 := by
  unfold tailWord_6638949
  simp only [CollatzResearch.WordTrace]
  refine ⟨242142362825229090064519901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161428241883486060043013267 242142362825229090064519901)
  ·
    refine ⟨90803386059460908774194963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242142362825229090064519901 90803386059460908774194963)
    ·
      refine ⟨136205079089191363161292445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90803386059460908774194963 136205079089191363161292445)
      ·
        refine ⟨51076904658446761185484667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136205079089191363161292445 51076904658446761185484667)
        ·
          refine ⟨76615356987670141778227001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51076904658446761185484667 76615356987670141778227001)
          ·
            refine ⟨57461517740752606333670251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76615356987670141778227001 57461517740752606333670251)
            ·
              refine ⟨86192276611128909500505377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57461517740752606333670251 86192276611128909500505377)
              ·
                refine ⟨64644207458346682125379033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86192276611128909500505377 64644207458346682125379033)
                ·
                  refine ⟨48483155593760011594034275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64644207458346682125379033 48483155593760011594034275)
                  ·
                    refine ⟨72724733390640017391051413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48483155593760011594034275 72724733390640017391051413)
                    ·
                      refine ⟨3408971877686250815205535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72724733390640017391051413 3408971877686250815205535)
                      ·
                        rfl

theorem cell23_6638949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_6638949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638949 prefixEnd_6638949 := by exact prefixLift 6638949
  have htrace : WordTrace (prefixWord ++ tailWord_6638949) baseStart_6638949 baseEnd_6638949 := by
    simpa [prefixWord, tailWord_6638949, baseEnd_6638949] using wordTrace_append hprefix tailTrace_6638949
  have hstable : (prefixWord ++ tailWord_6638949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638949).length < 2 ^ (prefixWord ++ tailWord_6638949).sum := by decide
  have hdescent : baseEnd_6638949 < baseStart_6638949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638956 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 3]
def baseStart_6638956 : Nat := 118140960795 + 6638956 * 2 ^ 59
def prefixEnd_6638956 : Nat := 4983230072969 + 3 ^ 40 * 6638956 * 2
def baseEnd_6638956 : Nat := 3408975472050832287818003

theorem tailTrace_6638956 : CollatzResearch.WordTrace tailWord_6638956 prefixEnd_6638956 3408975472050832287818003 := by
  unfold tailWord_6638956
  simp only [CollatzResearch.WordTrace]
  refine ⟨121071309068101865130012361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161428412090802486840016481 121071309068101865130012361)
  ·
    refine ⟨90803481801076398847509271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121071309068101865130012361 90803481801076398847509271)
    ·
      refine ⟨136205222701614598271263907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90803481801076398847509271 136205222701614598271263907)
      ·
        refine ⟨204307834052421897406895861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136205222701614598271263907 204307834052421897406895861)
        ·
          refine ⟨19153859442414552881896487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 204307834052421897406895861 19153859442414552881896487)
          ·
            refine ⟨28730789163621829322844731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19153859442414552881896487 28730789163621829322844731)
            ·
              refine ⟨43096183745432743984267097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28730789163621829322844731 43096183745432743984267097)
              ·
                refine ⟨32322137809074557988200323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43096183745432743984267097 32322137809074557988200323)
                ·
                  refine ⟨48483206713611836982300485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32322137809074557988200323 48483206713611836982300485)
                  ·
                    refine ⟨9090601258802219434181341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48483206713611836982300485 9090601258802219434181341)
                    ·
                      refine ⟨3408975472050832287818003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9090601258802219434181341 3408975472050832287818003)
                      ·
                        rfl

theorem cell23_6638956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 3].length) (baseStart_6638956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638956 prefixEnd_6638956 := by exact prefixLift 6638956
  have htrace : WordTrace (prefixWord ++ tailWord_6638956) baseStart_6638956 baseEnd_6638956 := by
    simpa [prefixWord, tailWord_6638956, baseEnd_6638956] using wordTrace_append hprefix tailTrace_6638956
  have hstable : (prefixWord ++ tailWord_6638956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638956).length < 2 ^ (prefixWord ++ tailWord_6638956).sum := by decide
  have hdescent : baseEnd_6638956 < baseStart_6638956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638980 : List Nat := [2, 3, 2, 1, 1, 3, 3, 3, 1, 4]
def baseStart_6638980 : Nat := 118140960795 + 6638980 * 2 ^ 59
def prefixEnd_6638980 : Nat := 4983230072969 + 3 ^ 40 * 6638980 * 2
def baseEnd_6638980 : Nat := 1136329265195513397972631

theorem tailTrace_6638980 : CollatzResearch.WordTrace tailWord_6638980 prefixEnd_6638980 1136329265195513397972631 := by
  unfold tailWord_6638980
  simp only [CollatzResearch.WordTrace]
  refine ⟨121071746744058391179449197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161428995658744521572598929 121071746744058391179449197)
  ·
    refine ⟨45401905029021896692293449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121071746744058391179449197 45401905029021896692293449)
    ·
      refine ⟨34051428771766422519220087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45401905029021896692293449 34051428771766422519220087)
      ·
        refine ⟨51077143157649633778830131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34051428771766422519220087 51077143157649633778830131)
        ·
          refine ⟨76615714736474450668245197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51077143157649633778830131 76615714736474450668245197)
          ·
            refine ⟨28730893026177919000591949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76615714736474450668245197 28730893026177919000591949)
            ·
              refine ⟨10774084884816719625221981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28730893026177919000591949 10774084884816719625221981)
              ·
                refine ⟨4040281831806269859458243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10774084884816719625221981 4040281831806269859458243)
                ·
                  refine ⟨6060422747709404789187365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4040281831806269859458243 6060422747709404789187365)
                  ·
                    refine ⟨1136329265195513397972631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6060422747709404789187365 1136329265195513397972631)
                    ·
                      rfl

theorem cell23_6638980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_6638980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638980 prefixEnd_6638980 := by exact prefixLift 6638980
  have htrace : WordTrace (prefixWord ++ tailWord_6638980) baseStart_6638980 baseEnd_6638980 := by
    simpa [prefixWord, tailWord_6638980, baseEnd_6638980] using wordTrace_append hprefix tailTrace_6638980
  have hstable : (prefixWord ++ tailWord_6638980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638980).length < 2 ^ (prefixWord ++ tailWord_6638980).sum := by decide
  have hdescent : baseEnd_6638980 < baseStart_6638980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638990 : List Nat := [4, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3]
def baseStart_6638990 : Nat := 118140960795 + 6638990 * 2 ^ 59
def prefixEnd_6638990 : Nat := 4983230072969 + 3 ^ 40 * 6638990 * 2
def baseEnd_6638990 : Nat := 3408992930393085154792847

theorem tailTrace_6638990 : CollatzResearch.WordTrace tailWord_6638990 prefixEnd_6638990 3408992930393085154792847 := by
  unfold tailWord_6638990
  simp only [CollatzResearch.WordTrace]
  refine ⟨30267982277260069258345303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161429238812053702711174949 30267982277260069258345303)
  ·
    refine ⟨45401973415890103887517955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30267982277260069258345303 45401973415890103887517955)
    ·
      refine ⟨68102960123835155831276933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45401973415890103887517955 68102960123835155831276933)
      ·
        refine ⟨12769305023219091718364425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68102960123835155831276933 12769305023219091718364425)
        ·
          refine ⟨9576978767414318788773319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12769305023219091718364425 9576978767414318788773319)
          ·
            refine ⟨14365468151121478183159979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9576978767414318788773319 14365468151121478183159979)
            ·
              refine ⟨21548202226682217274739969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14365468151121478183159979 21548202226682217274739969)
              ·
                refine ⟨16161151670011662956054977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21548202226682217274739969 16161151670011662956054977)
                ·
                  refine ⟨12120863752508747217041233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16161151670011662956054977 12120863752508747217041233)
                  ·
                    refine ⟨9090647814381560412780925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12120863752508747217041233 9090647814381560412780925)
                    ·
                      refine ⟨3408992930393085154792847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9090647814381560412780925 3408992930393085154792847)
                      ·
                        rfl

theorem cell23_6638990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_6638990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638990 prefixEnd_6638990 := by exact prefixLift 6638990
  have htrace : WordTrace (prefixWord ++ tailWord_6638990) baseStart_6638990 baseEnd_6638990 := by
    simpa [prefixWord, tailWord_6638990, baseEnd_6638990] using wordTrace_append hprefix tailTrace_6638990
  have hstable : (prefixWord ++ tailWord_6638990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638990).length < 2 ^ (prefixWord ++ tailWord_6638990).sum := by decide
  have hdescent : baseEnd_6638990 < baseStart_6638990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638999 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 7]
def baseStart_6638999 : Nat := 118140960795 + 6638999 * 2 ^ 59
def prefixEnd_6638999 : Nat := 4983230072969 + 3 ^ 40 * 6638999 * 2
def baseEnd_6638999 : Nat := 3408997551718975619580305

theorem tailTrace_6638999 : CollatzResearch.WordTrace tailWord_6638999 prefixEnd_6638999 3408997551718975619580305 := by
  unfold tailWord_6638999
  simp only [CollatzResearch.WordTrace]
  refine ⟨242144186475047948603840051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161429457650031965735893367 242144186475047948603840051)
  ·
    refine ⟨363216279712571922905760077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242144186475047948603840051 363216279712571922905760077)
    ·
      refine ⟨136206104892214471089660029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363216279712571922905760077 136206104892214471089660029)
      ·
        refine ⟨51077289334580426658622511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136206104892214471089660029 51077289334580426658622511)
        ·
          refine ⟨76615934001870639987933767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51077289334580426658622511 76615934001870639987933767)
          ·
            refine ⟨114923901002805959981900651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76615934001870639987933767 114923901002805959981900651)
            ·
              refine ⟨172385851504208939972850977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114923901002805959981900651 172385851504208939972850977)
              ·
                refine ⟨129289388628156704979638233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172385851504208939972850977 129289388628156704979638233)
                ·
                  refine ⟨96967041471117528734728675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129289388628156704979638233 96967041471117528734728675)
                  ·
                    refine ⟨145450562206676293102093013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96967041471117528734728675 145450562206676293102093013)
                    ·
                      refine ⟨3408997551718975619580305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145450562206676293102093013 3408997551718975619580305)
                      ·
                        rfl

theorem cell23_6638999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_6638999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6638999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6638999 prefixEnd_6638999 := by exact prefixLift 6638999
  have htrace : WordTrace (prefixWord ++ tailWord_6638999) baseStart_6638999 baseEnd_6638999 := by
    simpa [prefixWord, tailWord_6638999, baseEnd_6638999] using wordTrace_append hprefix tailTrace_6638999
  have hstable : (prefixWord ++ tailWord_6638999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638999).length < 2 ^ (prefixWord ++ tailWord_6638999).sum := by decide
  have hdescent : baseEnd_6638999 < baseStart_6638999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639010 : List Nat := [3, 3, 1, 2, 1, 4, 2, 1, 6]
def baseStart_6639010 : Nat := 118140960795 + 6639010 * 2 ^ 59
def prefixEnd_6639010 : Nat := 4983230072969 + 3 ^ 40 * 6639010 * 2
def baseEnd_6639010 : Nat := 378778133334019452949195

theorem tailTrace_6639010 : CollatzResearch.WordTrace tailWord_6639010 prefixEnd_6639010 378778133334019452949195 := by
  unfold tailWord_6639010
  simp only [CollatzResearch.WordTrace]
  refine ⟨60536146919502024370622621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161429725118672064988326989 60536146919502024370622621)
  ·
    refine ⟨22701055094813259138983483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60536146919502024370622621 22701055094813259138983483)
    ·
      refine ⟨34051582642219888708475225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22701055094813259138983483 34051582642219888708475225)
      ·
        refine ⟨25538686981664916531356419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34051582642219888708475225 25538686981664916531356419)
        ·
          refine ⟨38308030472497374797034629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25538686981664916531356419 38308030472497374797034629)
          ·
            refine ⟨7182755713593257774443993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38308030472497374797034629 7182755713593257774443993)
            ·
              refine ⟨5387066785194943330832995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7182755713593257774443993 5387066785194943330832995)
              ·
                refine ⟨8080600177792414996249493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5387066785194943330832995 8080600177792414996249493)
                ·
                  refine ⟨378778133334019452949195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8080600177792414996249493 378778133334019452949195)
                  ·
                    rfl

theorem cell23_6639010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_6639010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639010 prefixEnd_6639010 := by exact prefixLift 6639010
  have htrace : WordTrace (prefixWord ++ tailWord_6639010) baseStart_6639010 baseEnd_6639010 := by
    simpa [prefixWord, tailWord_6639010, baseEnd_6639010] using wordTrace_append hprefix tailTrace_6639010
  have hstable : (prefixWord ++ tailWord_6639010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639010).length < 2 ^ (prefixWord ++ tailWord_6639010).sum := by decide
  have hdescent : baseEnd_6639010 < baseStart_6639010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639066 : List Nat := [3, 1, 1, 2, 3, 2, 3, 8]
def baseStart_6639066 : Nat := 118140960795 + 6639066 * 2 ^ 59
def prefixEnd_6639066 : Nat := 4983230072969 + 3 ^ 40 * 6639066 * 2
def baseEnd_6639066 : Nat := 126260442774919513238611

theorem tailTrace_6639066 : CollatzResearch.WordTrace tailWord_6639066 prefixEnd_6639066 126260442774919513238611 := by
  unfold tailWord_6639066
  simp only [CollatzResearch.WordTrace]
  refine ⟨60536657541451304761632263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161431086777203479364352701 60536657541451304761632263)
  ·
    refine ⟨90804986312176957142448395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60536657541451304761632263 90804986312176957142448395)
    ·
      refine ⟨136207479468265435713672593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90804986312176957142448395 136207479468265435713672593)
      ·
        refine ⟨102155609601199076785254445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136207479468265435713672593 102155609601199076785254445)
        ·
          refine ⟨38308353600449653794470417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102155609601199076785254445 38308353600449653794470417)
          ·
            refine ⟨28731265200337240345852813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38308353600449653794470417 28731265200337240345852813)
            ·
              refine ⟨10774224450126465129694805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28731265200337240345852813 10774224450126465129694805)
              ·
                refine ⟨126260442774919513238611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10774224450126465129694805 126260442774919513238611)
                ·
                  rfl

theorem cell23_6639066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 8].length) (baseStart_6639066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639066 prefixEnd_6639066 := by exact prefixLift 6639066
  have htrace : WordTrace (prefixWord ++ tailWord_6639066) baseStart_6639066 baseEnd_6639066 := by
    simpa [prefixWord, tailWord_6639066, baseEnd_6639066] using wordTrace_append hprefix tailTrace_6639066
  have hstable : (prefixWord ++ tailWord_6639066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639066).length < 2 ^ (prefixWord ++ tailWord_6639066).sum := by decide
  have hdescent : baseEnd_6639066 < baseStart_6639066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639073 : List Nat := [1, 2, 3, 1, 2, 4, 2, 1, 1, 2, 4]
def baseStart_6639073 : Nat := 118140960795 + 6639073 * 2 ^ 59
def prefixEnd_6639073 : Nat := 4983230072969 + 3 ^ 40 * 6639073 * 2
def baseEnd_6639073 : Nat := 3409035549287408330054965

theorem tailTrace_6639073 : CollatzResearch.WordTrace tailWord_6639073 prefixEnd_6639073 3409035549287408330054965 := by
  unfold tailWord_6639073
  simp only [CollatzResearch.WordTrace]
  refine ⟨242146885476779859242033873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161431256984519906161355915 242146885476779859242033873)
  ·
    refine ⟨181610164107584894431525405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242146885476779859242033873 181610164107584894431525405)
    ·
      refine ⟨68103811540344335411822027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181610164107584894431525405 68103811540344335411822027)
      ·
        refine ⟨102155717310516503117733041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68103811540344335411822027 102155717310516503117733041)
        ·
          refine ⟨76616787982887377338299781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102155717310516503117733041 76616787982887377338299781)
          ·
            refine ⟨14365647746791383250931209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76616787982887377338299781 14365647746791383250931209)
            ·
              refine ⟨10774235810093537438198407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14365647746791383250931209 10774235810093537438198407)
              ·
                refine ⟨16161353715140306157297611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10774235810093537438198407 16161353715140306157297611)
                ·
                  refine ⟨24242030572710459235946417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16161353715140306157297611 24242030572710459235946417)
                  ·
                    refine ⟨18181522929532844426959813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24242030572710459235946417 18181522929532844426959813)
                    ·
                      refine ⟨3409035549287408330054965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18181522929532844426959813 3409035549287408330054965)
                      ·
                        rfl

theorem cell23_6639073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_6639073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639073 prefixEnd_6639073 := by exact prefixLift 6639073
  have htrace : WordTrace (prefixWord ++ tailWord_6639073) baseStart_6639073 baseEnd_6639073 := by
    simpa [prefixWord, tailWord_6639073, baseEnd_6639073] using wordTrace_append hprefix tailTrace_6639073
  have hstable : (prefixWord ++ tailWord_6639073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639073).length < 2 ^ (prefixWord ++ tailWord_6639073).sum := by decide
  have hdescent : baseEnd_6639073 < baseStart_6639073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639077 : List Nat := [1, 3, 1, 5, 1, 2, 1, 2, 3, 2, 2]
def baseStart_6639077 : Nat := 118140960795 + 6639077 * 2 ^ 59
def prefixEnd_6639077 : Nat := 4983230072969 + 3 ^ 40 * 6639077 * 2
def baseEnd_6639077 : Nat := 3409037603210026314404947

theorem tailTrace_6639077 : CollatzResearch.WordTrace tailWord_6639077 prefixEnd_6639077 3409037603210026314404947 := by
  unfold tailWord_6639077
  simp only [CollatzResearch.WordTrace]
  refine ⟨242147031368765367925179485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161431354245843578616786323 242147031368765367925179485)
  ·
    refine ⟨90805136763287012971942307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242147031368765367925179485 90805136763287012971942307)
    ·
      refine ⟨136207705144930519457913461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90805136763287012971942307 136207705144930519457913461)
      ·
        refine ⟨12769472357337236199179387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136207705144930519457913461 12769472357337236199179387)
        ·
          refine ⟨19154208536005854298769081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12769472357337236199179387 19154208536005854298769081)
          ·
            refine ⟨14365656402004390724076811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19154208536005854298769081 14365656402004390724076811)
            ·
              refine ⟨21548484603006586086115217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14365656402004390724076811 21548484603006586086115217)
              ·
                refine ⟨16161363452254939564586413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21548484603006586086115217 16161363452254939564586413)
                ·
                  refine ⟨6060511294595602336719905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16161363452254939564586413 6060511294595602336719905)
                  ·
                    refine ⟨4545383470946701752539929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6060511294595602336719905 4545383470946701752539929)
                    ·
                      refine ⟨3409037603210026314404947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4545383470946701752539929 3409037603210026314404947)
                      ·
                        rfl

theorem cell23_6639077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_6639077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639077 prefixEnd_6639077 := by exact prefixLift 6639077
  have htrace : WordTrace (prefixWord ++ tailWord_6639077) baseStart_6639077 baseEnd_6639077 := by
    simpa [prefixWord, tailWord_6639077, baseEnd_6639077] using wordTrace_append hprefix tailTrace_6639077
  have hstable : (prefixWord ++ tailWord_6639077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639077).length < 2 ^ (prefixWord ++ tailWord_6639077).sum := by decide
  have hdescent : baseEnd_6639077 < baseStart_6639077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639094 : List Nat := [5, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2]
def baseStart_6639094 : Nat := 118140960795 + 6639094 * 2 ^ 59
def prefixEnd_6639094 : Nat := 4983230072969 + 3 ^ 40 * 6639094 * 2
def baseEnd_6639094 : Nat := 3409046332381152747892369

theorem tailTrace_6639094 : CollatzResearch.WordTrace tailWord_6639094 prefixEnd_6639094 3409046332381152747892369 := by
  unfold tailWord_6639094
  simp only [CollatzResearch.WordTrace]
  refine ⟨15134228213106486239284271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161431767606469186552365557 15134228213106486239284271)
  ·
    refine ⟨22701342319659729358926407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15134228213106486239284271 22701342319659729358926407)
    ·
      refine ⟨34052013479489594038389611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22701342319659729358926407 34052013479489594038389611)
      ·
        refine ⟨51078020219234391057584417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34052013479489594038389611 51078020219234391057584417)
        ·
          refine ⟨38308515164425793293188313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51078020219234391057584417 38308515164425793293188313)
          ·
            refine ⟨28731386373319344969891235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38308515164425793293188313 28731386373319344969891235)
            ·
              refine ⟨43097079559979017454836853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28731386373319344969891235 43097079559979017454836853)
              ·
                refine ⟨4040351208748032886390955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43097079559979017454836853 4040351208748032886390955)
                ·
                  refine ⟨6060526813122049329586433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4040351208748032886390955 6060526813122049329586433)
                  ·
                    refine ⟨4545395109841536997189825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6060526813122049329586433 4545395109841536997189825)
                    ·
                      refine ⟨3409046332381152747892369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4545395109841536997189825 3409046332381152747892369)
                      ·
                        rfl

theorem cell23_6639094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_6639094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639094 prefixEnd_6639094 := by exact prefixLift 6639094
  have htrace : WordTrace (prefixWord ++ tailWord_6639094) baseStart_6639094 baseEnd_6639094 := by
    simpa [prefixWord, tailWord_6639094, baseEnd_6639094] using wordTrace_append hprefix tailTrace_6639094
  have hstable : (prefixWord ++ tailWord_6639094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639094).length < 2 ^ (prefixWord ++ tailWord_6639094).sum := by decide
  have hdescent : baseEnd_6639094 < baseStart_6639094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639103 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 5, 3, 2]
def baseStart_6639103 : Nat := 118140960795 + 6639103 * 2 ^ 59
def prefixEnd_6639103 : Nat := 4983230072969 + 3 ^ 40 * 6639103 * 2
def baseEnd_6639103 : Nat := 3409050953707043212679827

theorem tailTrace_6639103 : CollatzResearch.WordTrace tailWord_6639103 prefixEnd_6639103 3409050953707043212679827 := by
  unfold tailWord_6639103
  simp only [CollatzResearch.WordTrace]
  refine ⟨242147979666671174365625963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161431986444447449577083975 242147979666671174365625963)
  ·
    refine ⟨363221969500006761548438945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242147979666671174365625963 363221969500006761548438945)
    ·
      refine ⟨272416477125005071161329209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363221969500006761548438945 272416477125005071161329209)
      ·
        refine ⟨204312357843753803370996907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272416477125005071161329209 204312357843753803370996907)
        ·
          refine ⟨306468536765630705056495361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204312357843753803370996907 306468536765630705056495361)
          ·
            refine ⟨229851402574223028792371521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306468536765630705056495361 229851402574223028792371521)
            ·
              refine ⟨172388551930667271594278641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229851402574223028792371521 172388551930667271594278641)
              ·
                refine ⟨129291413948000453695708981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172388551930667271594278641 129291413948000453695708981)
                ·
                  refine ⟨12121070057625042533972717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129291413948000453695708981 12121070057625042533972717)
                  ·
                    refine ⟨4545401271609390950239769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12121070057625042533972717 4545401271609390950239769)
                    ·
                      refine ⟨3409050953707043212679827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4545401271609390950239769 3409050953707043212679827)
                      ·
                        rfl

theorem cell23_6639103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 3, 2].length) (baseStart_6639103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639103 prefixEnd_6639103 := by exact prefixLift 6639103
  have htrace : WordTrace (prefixWord ++ tailWord_6639103) baseStart_6639103 baseEnd_6639103 := by
    simpa [prefixWord, tailWord_6639103, baseEnd_6639103] using wordTrace_append hprefix tailTrace_6639103
  have hstable : (prefixWord ++ tailWord_6639103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639103).length < 2 ^ (prefixWord ++ tailWord_6639103).sum := by decide
  have hdescent : baseEnd_6639103 < baseStart_6639103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639124 : List Nat := [2, 4, 3, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_6639124 : Nat := 118140960795 + 6639124 * 2 ^ 59
def prefixEnd_6639124 : Nat := 4983230072969 + 3 ^ 40 * 6639124 * 2
def baseEnd_6639124 : Nat := 3409061736800787630517231

theorem tailTrace_6639124 : CollatzResearch.WordTrace tailWord_6639124 prefixEnd_6639124 3409061736800787630517231 := by
  unfold tailWord_6639124
  simp only [CollatzResearch.WordTrace]
  refine ⟨121074372799797547476070213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161432497066396729968093617 121074372799797547476070213)
  ·
    refine ⟨22701444899962040151763165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121074372799797547476070213 22701444899962040151763165)
    ·
      refine ⟨8513041837485765056911187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22701444899962040151763165 8513041837485765056911187)
      ·
        refine ⟨12769562756228647585366781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8513041837485765056911187 12769562756228647585366781)
        ·
          refine ⟨4788586033585742844512543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12769562756228647585366781 4788586033585742844512543)
          ·
            refine ⟨7182879050378614266768815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4788586033585742844512543 7182879050378614266768815)
            ·
              refine ⟨10774318575567921400153223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7182879050378614266768815 10774318575567921400153223)
              ·
                refine ⟨16161477863351882100229835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10774318575567921400153223 16161477863351882100229835)
                ·
                  refine ⟨24242216795027823150344753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16161477863351882100229835 24242216795027823150344753)
                  ·
                    refine ⟨18181662596270867362758565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24242216795027823150344753 18181662596270867362758565)
                    ·
                      refine ⟨3409061736800787630517231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18181662596270867362758565 3409061736800787630517231)
                      ·
                        rfl

theorem cell23_6639124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_6639124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639124 prefixEnd_6639124 := by exact prefixLift 6639124
  have htrace : WordTrace (prefixWord ++ tailWord_6639124) baseStart_6639124 baseEnd_6639124 := by
    simpa [prefixWord, tailWord_6639124, baseEnd_6639124] using wordTrace_append hprefix tailTrace_6639124
  have hstable : (prefixWord ++ tailWord_6639124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639124).length < 2 ^ (prefixWord ++ tailWord_6639124).sum := by decide
  have hdescent : baseEnd_6639124 < baseStart_6639124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639137 : List Nat := [1, 2, 3, 2, 2, 3, 2, 2, 1, 3, 2]
def baseStart_6639137 : Nat := 118140960795 + 6639137 * 2 ^ 59
def prefixEnd_6639137 : Nat := 4983230072969 + 3 ^ 40 * 6639137 * 2
def baseEnd_6639137 : Nat := 3409068412049296079654671

theorem tailTrace_6639137 : CollatzResearch.WordTrace tailWord_6639137 prefixEnd_6639137 3409068412049296079654671 := by
  unfold tailWord_6639137
  simp only [CollatzResearch.WordTrace]
  refine ⟨242149219748547998172363665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161432813165698665448242443 242149219748547998172363665)
  ·
    refine ⟨181611914811410998629272749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242149219748547998172363665 181611914811410998629272749)
    ·
      refine ⟨68104468054279124485977281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181611914811410998629272749 68104468054279124485977281)
      ·
        refine ⟨51078351040709343364482961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68104468054279124485977281 51078351040709343364482961)
        ·
          refine ⟨38308763280532007523362221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51078351040709343364482961 38308763280532007523362221)
          ·
            refine ⟨14365786230199502821260833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38308763280532007523362221 14365786230199502821260833)
            ·
              refine ⟨10774339672649627115945625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14365786230199502821260833 10774339672649627115945625)
              ·
                refine ⟨8080754754487220336959219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10774339672649627115945625 8080754754487220336959219)
                ·
                  refine ⟨12121132131730830505438829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8080754754487220336959219 12121132131730830505438829)
                  ·
                    refine ⟨4545424549399061439539561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12121132131730830505438829 4545424549399061439539561)
                    ·
                      refine ⟨3409068412049296079654671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4545424549399061439539561 3409068412049296079654671)
                      ·
                        rfl

theorem cell23_6639137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_6639137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639137 prefixEnd_6639137 := by exact prefixLift 6639137
  have htrace : WordTrace (prefixWord ++ tailWord_6639137) baseStart_6639137 baseEnd_6639137 := by
    simpa [prefixWord, tailWord_6639137, baseEnd_6639137] using wordTrace_append hprefix tailTrace_6639137
  have hstable : (prefixWord ++ tailWord_6639137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639137).length < 2 ^ (prefixWord ++ tailWord_6639137).sum := by decide
  have hdescent : baseEnd_6639137 < baseStart_6639137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639203 : List Nat := [1, 1, 1, 5, 1, 3, 1, 3, 2, 5]
def baseStart_6639203 : Nat := 118140960795 + 6639203 * 2 ^ 59
def prefixEnd_6639203 : Nat := 4983230072969 + 3 ^ 40 * 6639203 * 2
def baseEnd_6639203 : Nat := 1136367433924164273809789

theorem tailTrace_6639203 : CollatzResearch.WordTrace tailWord_6639203 prefixEnd_6639203 1136367433924164273809789 := by
  unfold tailWord_6639203
  simp only [CollatzResearch.WordTrace]
  refine ⟨242151626966308891444266263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161434417977539260962844175 242151626966308891444266263)
  ·
    refine ⟨363227440449463337166399395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242151626966308891444266263 363227440449463337166399395)
    ·
      refine ⟨544841160674195005749599093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363227440449463337166399395 544841160674195005749599093)
      ·
        refine ⟨51078858813205781789024915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 544841160674195005749599093 51078858813205781789024915)
        ·
          refine ⟨76618288219808672683537373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51078858813205781789024915 76618288219808672683537373)
          ·
            refine ⟨28731858082428252256326515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76618288219808672683537373 28731858082428252256326515)
            ·
              refine ⟨43097787123642378384489773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28731858082428252256326515 43097787123642378384489773)
              ·
                refine ⟨16161670171365891894183665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43097787123642378384489773 16161670171365891894183665)
                ·
                  refine ⟨12121252628524418920637749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16161670171365891894183665 12121252628524418920637749)
                  ·
                    refine ⟨1136367433924164273809789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12121252628524418920637749 1136367433924164273809789)
                    ·
                      rfl

theorem cell23_6639203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 5].length) (baseStart_6639203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639203 prefixEnd_6639203 := by exact prefixLift 6639203
  have htrace : WordTrace (prefixWord ++ tailWord_6639203) baseStart_6639203 baseEnd_6639203 := by
    simpa [prefixWord, tailWord_6639203, baseEnd_6639203] using wordTrace_append hprefix tailTrace_6639203
  have hstable : (prefixWord ++ tailWord_6639203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639203).length < 2 ^ (prefixWord ++ tailWord_6639203).sum := by decide
  have hdescent : baseEnd_6639203 < baseStart_6639203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639243 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 3]
def baseStart_6639243 : Nat := 118140960795 + 6639243 * 2 ^ 59
def prefixEnd_6639243 : Nat := 4983230072969 + 3 ^ 40 * 6639243 * 2
def baseEnd_6639243 : Nat := 3409122840998672664929183

theorem tailTrace_6639243 : CollatzResearch.WordTrace tailWord_6639243 prefixEnd_6639243 3409122840998672664929183 := by
  unfold tailWord_6639243
  simp only [CollatzResearch.WordTrace]
  refine ⟨242153085886163978275722383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161435390590775985517148255 242153085886163978275722383)
  ·
    refine ⟨363229628829245967413583575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242153085886163978275722383 363229628829245967413583575)
    ·
      refine ⟨544844443243868951120375363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363229628829245967413583575 544844443243868951120375363)
      ·
        refine ⟨817266664865803426680563045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544844443243868951120375363 817266664865803426680563045)
        ·
          refine ⟨153237499662338142502605571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 817266664865803426680563045 153237499662338142502605571)
          ·
            refine ⟨229856249493507213753908357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153237499662338142502605571 229856249493507213753908357)
            ·
              refine ⟨43098046780032602578857817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229856249493507213753908357 43098046780032602578857817)
              ·
                refine ⟨32323535085024451934143363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43098046780032602578857817 32323535085024451934143363)
                ·
                  refine ⟨48485302627536677901215045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32323535085024451934143363 48485302627536677901215045)
                  ·
                    refine ⟨9090994242663127106477821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48485302627536677901215045 9090994242663127106477821)
                    ·
                      refine ⟨3409122840998672664929183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9090994242663127106477821 3409122840998672664929183)
                      ·
                        rfl

theorem cell23_6639243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 3].length) (baseStart_6639243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639243 prefixEnd_6639243 := by exact prefixLift 6639243
  have htrace : WordTrace (prefixWord ++ tailWord_6639243) baseStart_6639243 baseEnd_6639243 := by
    simpa [prefixWord, tailWord_6639243, baseEnd_6639243] using wordTrace_append hprefix tailTrace_6639243
  have hstable : (prefixWord ++ tailWord_6639243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639243).length < 2 ^ (prefixWord ++ tailWord_6639243).sum := by decide
  have hdescent : baseEnd_6639243 < baseStart_6639243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639267 : List Nat := [1, 1, 1, 4, 1, 1, 6, 3, 1, 4]
def baseStart_6639267 : Nat := 118140960795 + 6639267 * 2 ^ 59
def prefixEnd_6639267 : Nat := 4983230072969 + 3 ^ 40 * 6639267 * 2
def baseEnd_6639267 : Nat := 1136378388178126857009691

theorem tailTrace_6639267 : CollatzResearch.WordTrace tailWord_6639267 prefixEnd_6639267 1136378388178126857009691 := by
  unfold tailWord_6639267
  simp only [CollatzResearch.WordTrace]
  refine ⟨242153961238077030374596055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161435974158718020249730703 242153961238077030374596055)
  ·
    refine ⟨363230941857115545561894083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242153961238077030374596055 363230941857115545561894083)
    ·
      refine ⟨544846412785673318342841125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363230941857115545561894083 544846412785673318342841125)
      ·
        refine ⟨102158702397313747189282711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 544846412785673318342841125 102158702397313747189282711)
        ·
          refine ⟨153238053595970620783924067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102158702397313747189282711 153238053595970620783924067)
          ·
            refine ⟨229857080393955931175886101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153238053595970620783924067 229857080393955931175886101)
            ·
              refine ⟨10774550643466684273869661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 229857080393955931175886101 10774550643466684273869661)
              ·
                refine ⟨4040456491300006602701123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10774550643466684273869661 4040456491300006602701123)
                ·
                  refine ⟨6060684736950009904051685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4040456491300006602701123 6060684736950009904051685)
                  ·
                    refine ⟨1136378388178126857009691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6060684736950009904051685 1136378388178126857009691)
                    ·
                      rfl

theorem cell23_6639267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 1, 4].length) (baseStart_6639267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639267 prefixEnd_6639267 := by exact prefixLift 6639267
  have htrace : WordTrace (prefixWord ++ tailWord_6639267) baseStart_6639267 baseEnd_6639267 := by
    simpa [prefixWord, tailWord_6639267, baseEnd_6639267] using wordTrace_append hprefix tailTrace_6639267
  have hstable : (prefixWord ++ tailWord_6639267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639267).length < 2 ^ (prefixWord ++ tailWord_6639267).sum := by decide
  have hdescent : baseEnd_6639267 < baseStart_6639267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639340 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 4, 4]
def baseStart_6639340 : Nat := 118140960795 + 6639340 * 2 ^ 59
def prefixEnd_6639340 : Nat := 4983230072969 + 3 ^ 40 * 6639340 * 2
def baseEnd_6639340 : Nat := 1136390882874052928472079

theorem tailTrace_6639340 : CollatzResearch.WordTrace tailWord_6639340 prefixEnd_6639340 1136390882874052928472079 := by
  unfold tailWord_6639340
  simp only [CollatzResearch.WordTrace]
  refine ⟨121078311883406281921001737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161437749177875042561335649 121078311883406281921001737)
  ·
    refine ⟨90808733912554711440751303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121078311883406281921001737 90808733912554711440751303)
    ·
      refine ⟨136213100868832067161126955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90808733912554711440751303 136213100868832067161126955)
      ·
        refine ⟨204319651303248100741690433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136213100868832067161126955 204319651303248100741690433)
        ·
          refine ⟨153239738477436075556267825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204319651303248100741690433 153239738477436075556267825)
          ·
            refine ⟨114929803858077056667200869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153239738477436075556267825 114929803858077056667200869)
            ·
              refine ⟨21549338223389448125100163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114929803858077056667200869 21549338223389448125100163)
              ·
                refine ⟨32324007335084172187650245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21549338223389448125100163 32324007335084172187650245)
                ·
                  refine ⟨6060751375328282285184421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32324007335084172187650245 6060751375328282285184421)
                  ·
                    refine ⟨1136390882874052928472079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6060751375328282285184421 1136390882874052928472079)
                    ·
                      rfl

theorem cell23_6639340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 4].length) (baseStart_6639340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639340 prefixEnd_6639340 := by exact prefixLift 6639340
  have htrace : WordTrace (prefixWord ++ tailWord_6639340) baseStart_6639340 baseEnd_6639340 := by
    simpa [prefixWord, tailWord_6639340, baseEnd_6639340] using wordTrace_append hprefix tailTrace_6639340
  have hstable : (prefixWord ++ tailWord_6639340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639340).length < 2 ^ (prefixWord ++ tailWord_6639340).sum := by decide
  have hdescent : baseEnd_6639340 < baseStart_6639340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639343 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 6]
def baseStart_6639343 : Nat := 118140960795 + 6639343 * 2 ^ 59
def prefixEnd_6639343 : Nat := 4983230072969 + 3 ^ 40 * 6639343 * 2
def baseEnd_6639343 : Nat := 3409174189064122273678723

theorem tailTrace_6639343 : CollatzResearch.WordTrace tailWord_6639343 prefixEnd_6639343 3409174189064122273678723 := by
  unfold tailWord_6639343
  simp only [CollatzResearch.WordTrace]
  refine ⟨242156733185801695354362683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161437822123867796902908455 242156733185801695354362683)
  ·
    refine ⟨363235099778702543031544025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242156733185801695354362683 363235099778702543031544025)
    ·
      refine ⟨272426324834026907273658019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363235099778702543031544025 272426324834026907273658019)
      ·
        refine ⟨408639487251040360910487029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272426324834026907273658019 408639487251040360910487029)
        ·
          refine ⟨38309951929785033835358159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 408639487251040360910487029 38309951929785033835358159)
          ·
            refine ⟨57464927894677550753037239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38309951929785033835358159 57464927894677550753037239)
            ·
              refine ⟨86197391842016326129555859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57464927894677550753037239 86197391842016326129555859)
              ·
                refine ⟨129296087763024489194333789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86197391842016326129555859 129296087763024489194333789)
                ·
                  refine ⟨48486032911134183447875171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129296087763024489194333789 48486032911134183447875171)
                  ·
                    refine ⟨72729049366701275171812757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48486032911134183447875171 72729049366701275171812757)
                    ·
                      refine ⟨3409174189064122273678723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72729049366701275171812757 3409174189064122273678723)
                      ·
                        rfl

theorem cell23_6639343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_6639343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639343 prefixEnd_6639343 := by exact prefixLift 6639343
  have htrace : WordTrace (prefixWord ++ tailWord_6639343) baseStart_6639343 baseEnd_6639343 := by
    simpa [prefixWord, tailWord_6639343, baseEnd_6639343] using wordTrace_append hprefix tailTrace_6639343
  have hstable : (prefixWord ++ tailWord_6639343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639343).length < 2 ^ (prefixWord ++ tailWord_6639343).sum := by decide
  have hdescent : baseEnd_6639343 < baseStart_6639343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639364 : List Nat := [2, 3, 2, 2, 1, 4, 1, 2, 1, 1, 4]
def baseStart_6639364 : Nat := 118140960795 + 6639364 * 2 ^ 59
def prefixEnd_6639364 : Nat := 4983230072969 + 3 ^ 40 * 6639364 * 2
def baseEnd_6639364 : Nat := 3409184972157866691516127

theorem tailTrace_6639364 : CollatzResearch.WordTrace tailWord_6639364 prefixEnd_6639364 3409184972157866691516127 := by
  unfold tailWord_6639364
  simp only [CollatzResearch.WordTrace]
  refine ⟨121078749559362807970438573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161438332745817077293918097 121078749559362807970438573)
  ·
    refine ⟨45404531084761052988914465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121078749559362807970438573 45404531084761052988914465)
    ·
      refine ⟨34053398313570789741685849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45404531084761052988914465 34053398313570789741685849)
      ·
        refine ⟨25540048735178092306264387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34053398313570789741685849 25540048735178092306264387)
        ·
          refine ⟨38310073102767138459396581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25540048735178092306264387 38310073102767138459396581)
          ·
            refine ⟨7183138706768838461136859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38310073102767138459396581 7183138706768838461136859)
            ·
              refine ⟨10774708060153257691705289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7183138706768838461136859 10774708060153257691705289)
              ·
                refine ⟨8081031045114943268778967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10774708060153257691705289 8081031045114943268778967)
                ·
                  refine ⟨12121546567672414903168451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8081031045114943268778967 12121546567672414903168451)
                  ·
                    refine ⟨18182319851508622354752677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12121546567672414903168451 18182319851508622354752677)
                    ·
                      refine ⟨3409184972157866691516127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18182319851508622354752677 3409184972157866691516127)
                      ·
                        rfl

theorem cell23_6639364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_6639364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639364 prefixEnd_6639364 := by exact prefixLift 6639364
  have htrace : WordTrace (prefixWord ++ tailWord_6639364) baseStart_6639364 baseEnd_6639364 := by
    simpa [prefixWord, tailWord_6639364, baseEnd_6639364] using wordTrace_append hprefix tailTrace_6639364
  have hstable : (prefixWord ++ tailWord_6639364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639364).length < 2 ^ (prefixWord ++ tailWord_6639364).sum := by decide
  have hdescent : baseEnd_6639364 < baseStart_6639364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639400 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 2, 7]
def baseStart_6639400 : Nat := 118140960795 + 6639400 * 2 ^ 59
def prefixEnd_6639400 : Nat := 4983230072969 + 3 ^ 40 * 6639400 * 2
def baseEnd_6639400 : Nat := 1136401152487142850221987

theorem tailTrace_6639400 : CollatzResearch.WordTrace tailWord_6639400 prefixEnd_6639400 1136401152487142850221987 := by
  unfold tailWord_6639400
  simp only [CollatzResearch.WordTrace]
  refine ⟨121079406073297597044593827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161439208097730129392791769 121079406073297597044593827)
  ·
    refine ⟨181619109109946395566890741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121079406073297597044593827 181619109109946395566890741)
    ·
      refine ⟨17026791479057474584396007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181619109109946395566890741 17026791479057474584396007)
      ·
        refine ⟨25540187218586211876594011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17026791479057474584396007 25540187218586211876594011)
        ·
          refine ⟨38310280827879317814891017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25540187218586211876594011 38310280827879317814891017)
          ·
            refine ⟨28732710620909488361168263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38310280827879317814891017 28732710620909488361168263)
            ·
              refine ⟨43099065931364232541752395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28732710620909488361168263 43099065931364232541752395)
              ·
                refine ⟨64648598897046348812628593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43099065931364232541752395 64648598897046348812628593)
                ·
                  refine ⟨48486449172784761609471445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64648598897046348812628593 48486449172784761609471445)
                  ·
                    refine ⟨1136401152487142850221987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48486449172784761609471445 1136401152487142850221987)
                    ·
                      rfl

theorem cell23_6639400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_6639400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639400 prefixEnd_6639400 := by exact prefixLift 6639400
  have htrace : WordTrace (prefixWord ++ tailWord_6639400) baseStart_6639400 baseEnd_6639400 := by
    simpa [prefixWord, tailWord_6639400, baseEnd_6639400] using wordTrace_append hprefix tailTrace_6639400
  have hstable : (prefixWord ++ tailWord_6639400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639400).length < 2 ^ (prefixWord ++ tailWord_6639400).sum := by decide
  have hdescent : baseEnd_6639400 < baseStart_6639400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639414 : List Nat := [5, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_6639414 : Nat := 118140960795 + 6639414 * 2 ^ 59
def prefixEnd_6639414 : Nat := 4983230072969 + 3 ^ 40 * 6639414 * 2
def baseEnd_6639414 : Nat := 3409210646190591495890897

theorem tailTrace_6639414 : CollatzResearch.WordTrace tailWord_6639414 prefixEnd_6639414 3409210646190591495890897 := by
  unfold tailWord_6639414
  simp only [CollatzResearch.WordTrace]
  refine ⟨15134957673034029655012331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161439548512362982986798197 15134957673034029655012331)
  ·
    refine ⟨22702436509551044482518497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15134957673034029655012331 22702436509551044482518497)
    ·
      refine ⟨17026827382163283361888873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22702436509551044482518497 17026827382163283361888873)
      ·
        refine ⟨12770120536622462521416655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17026827382163283361888873 12770120536622462521416655)
        ·
          refine ⟨19155180804933693782124983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12770120536622462521416655 19155180804933693782124983)
          ·
            refine ⟨28732771207400540673187475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19155180804933693782124983 28732771207400540673187475)
            ·
              refine ⟨43099156811100811009781213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28732771207400540673187475 43099156811100811009781213)
              ·
                refine ⟨16162183804162804128667955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43099156811100811009781213 16162183804162804128667955)
                ·
                  refine ⟨24243275706244206193001933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16162183804162804128667955 24243275706244206193001933)
                  ·
                    refine ⟨9091228389841577322375725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24243275706244206193001933 9091228389841577322375725)
                    ·
                      refine ⟨3409210646190591495890897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9091228389841577322375725 3409210646190591495890897)
                      ·
                        rfl

theorem cell23_6639414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_6639414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639414 prefixEnd_6639414 := by exact prefixLift 6639414
  have htrace : WordTrace (prefixWord ++ tailWord_6639414) baseStart_6639414 baseEnd_6639414 := by
    simpa [prefixWord, tailWord_6639414, baseEnd_6639414] using wordTrace_append hprefix tailTrace_6639414
  have hstable : (prefixWord ++ tailWord_6639414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639414).length < 2 ^ (prefixWord ++ tailWord_6639414).sum := by decide
  have hdescent : baseEnd_6639414 < baseStart_6639414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639441 : List Nat := [1, 2, 2, 1, 5, 1, 4, 1, 1, 3, 2]
def baseStart_6639441 : Nat := 118140960795 + 6639441 * 2 ^ 59
def prefixEnd_6639441 : Nat := 4983230072969 + 3 ^ 40 * 6639441 * 2
def baseEnd_6639441 : Nat := 3409224510168262890253273

theorem tailTrace_6639441 : CollatzResearch.WordTrace tailWord_6639441 prefixEnd_6639441 3409224510168262890253273 := by
  unfold tailWord_6639441
  simp only [CollatzResearch.WordTrace]
  refine ⟨242160307539446658091430177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161440205026297772060953451 242160307539446658091430177)
  ·
    refine ⟨181620230654584993568572633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242160307539446658091430177 181620230654584993568572633)
    ·
      refine ⟨136215172990938745176429475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181620230654584993568572633 136215172990938745176429475)
      ·
        refine ⟨204322759486408117764644213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136215172990938745176429475 204322759486408117764644213)
        ·
          refine ⟨19155258701850761040435395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 204322759486408117764644213 19155258701850761040435395)
          ·
            refine ⟨28732888052776141560653093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19155258701850761040435395 28732888052776141560653093)
            ·
              refine ⟨5387416509895526542622455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28732888052776141560653093 5387416509895526542622455)
              ·
                refine ⟨8081124764843289813933683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5387416509895526542622455 8081124764843289813933683)
                ·
                  refine ⟨12121687147264934720900525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8081124764843289813933683 12121687147264934720900525)
                  ·
                    refine ⟨4545632680224350520337697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12121687147264934720900525 4545632680224350520337697)
                    ·
                      refine ⟨3409224510168262890253273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4545632680224350520337697 3409224510168262890253273)
                      ·
                        rfl

theorem cell23_6639441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 1, 3, 2].length) (baseStart_6639441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639441 prefixEnd_6639441 := by exact prefixLift 6639441
  have htrace : WordTrace (prefixWord ++ tailWord_6639441) baseStart_6639441 baseEnd_6639441 := by
    simpa [prefixWord, tailWord_6639441, baseEnd_6639441] using wordTrace_append hprefix tailTrace_6639441
  have hstable : (prefixWord ++ tailWord_6639441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639441).length < 2 ^ (prefixWord ++ tailWord_6639441).sum := by decide
  have hdescent : baseEnd_6639441 < baseStart_6639441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639450 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4]
def baseStart_6639450 : Nat := 118140960795 + 6639450 * 2 ^ 59
def prefixEnd_6639450 : Nat := 4983230072969 + 3 ^ 40 * 6639450 * 2
def baseEnd_6639450 : Nat := 3409229131494153355040731

theorem tailTrace_6639450 : CollatzResearch.WordTrace tailWord_6639450 prefixEnd_6639450 3409229131494153355040731 := by
  unfold tailWord_6639450
  simp only [CollatzResearch.WordTrace]
  refine ⟨60540158949103513157126951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161440423864276035085671869 60540158949103513157126951)
  ·
    refine ⟨90810238423655269735690427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60540158949103513157126951 90810238423655269735690427)
    ·
      refine ⟨136215357635482904603535641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90810238423655269735690427 136215357635482904603535641)
      ·
        refine ⟨102161518226612178452651731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136215357635482904603535641 102161518226612178452651731)
        ·
          refine ⟨153242277339918267678977597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102161518226612178452651731 153242277339918267678977597)
          ·
            refine ⟨57465854002469350379616599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153242277339918267678977597 57465854002469350379616599)
            ·
              refine ⟨86198781003704025569424899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57465854002469350379616599 86198781003704025569424899)
              ·
                refine ⟨129298171505556038354137349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86198781003704025569424899 129298171505556038354137349)
                ·
                  refine ⟨24243407157291757191400753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129298171505556038354137349 24243407157291757191400753)
                  ·
                    refine ⟨18182555367968817893550565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24243407157291757191400753 18182555367968817893550565)
                    ·
                      refine ⟨3409229131494153355040731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18182555367968817893550565 3409229131494153355040731)
                      ·
                        rfl

theorem cell23_6639450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_6639450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639450 prefixEnd_6639450 := by exact prefixLift 6639450
  have htrace : WordTrace (prefixWord ++ tailWord_6639450) baseStart_6639450 baseEnd_6639450 := by
    simpa [prefixWord, tailWord_6639450, baseEnd_6639450] using wordTrace_append hprefix tailTrace_6639450
  have hstable : (prefixWord ++ tailWord_6639450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639450).length < 2 ^ (prefixWord ++ tailWord_6639450).sum := by decide
  have hdescent : baseEnd_6639450 < baseStart_6639450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639500 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 1, 2, 5]
def baseStart_6639500 : Nat := 118140960795 + 6639500 * 2 ^ 59
def prefixEnd_6639500 : Nat := 4983230072969 + 3 ^ 40 * 6639500 * 2
def baseEnd_6639500 : Nat := 3409254805526878159415501

theorem tailTrace_6639500 : CollatzResearch.WordTrace tailWord_6639500 prefixEnd_6639500 3409254805526878159415501 := by
  unfold tailWord_6639500
  simp only [CollatzResearch.WordTrace]
  refine ⟨121081229723116455583913977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161441639630821940778551969 121081229723116455583913977)
  ·
    refine ⟨90810922292337341687935483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121081229723116455583913977 90810922292337341687935483)
    ·
      refine ⟨136216383438506012531903225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90810922292337341687935483 136216383438506012531903225)
      ·
        refine ⟨102162287578879509398927419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136216383438506012531903225 102162287578879509398927419)
        ·
          refine ⟨153243431368319264098391129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102162287578879509398927419 153243431368319264098391129)
          ·
            refine ⟨114932573526239448073793347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153243431368319264098391129 114932573526239448073793347)
            ·
              refine ⟨172398860289359172110690021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114932573526239448073793347 172398860289359172110690021)
              ·
                refine ⟨32324786304254844770754379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172398860289359172110690021 32324786304254844770754379)
                ·
                  refine ⟨48487179456382267156131569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32324786304254844770754379 48487179456382267156131569)
                  ·
                    refine ⟨36365384592286700367098677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48487179456382267156131569 36365384592286700367098677)
                    ·
                      refine ⟨3409254805526878159415501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36365384592286700367098677 3409254805526878159415501)
                      ·
                        rfl

theorem cell23_6639500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_6639500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639500 prefixEnd_6639500 := by exact prefixLift 6639500
  have htrace : WordTrace (prefixWord ++ tailWord_6639500) baseStart_6639500 baseEnd_6639500 := by
    simpa [prefixWord, tailWord_6639500, baseEnd_6639500] using wordTrace_append hprefix tailTrace_6639500
  have hstable : (prefixWord ++ tailWord_6639500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639500).length < 2 ^ (prefixWord ++ tailWord_6639500).sum := by decide
  have hdescent : baseEnd_6639500 < baseStart_6639500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639517 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_6639517 : Nat := 118140960795 + 6639517 * 2 ^ 59
def prefixEnd_6639517 : Nat := 4983230072969 + 3 ^ 40 * 6639517 * 2
def baseEnd_6639517 : Nat := 3409263534698004592902923

theorem tailTrace_6639517 : CollatzResearch.WordTrace tailWord_6639517 prefixEnd_6639517 3409263534698004592902923 := by
  unfold tailWord_6639517
  simp only [CollatzResearch.WordTrace]
  refine ⟨242163079487171323071196805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161442052991447548714131203 242163079487171323071196805)
  ·
    refine ⟨45405577403844623075849401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242163079487171323071196805 45405577403844623075849401)
    ·
      refine ⟨34054183052883467306887051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45405577403844623075849401 34054183052883467306887051)
      ·
        refine ⟨51081274579325200960330577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34054183052883467306887051 51081274579325200960330577)
        ·
          refine ⟨38310955934493900720247933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51081274579325200960330577 38310955934493900720247933)
          ·
            refine ⟨14366608475435212770092975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38310955934493900720247933 14366608475435212770092975)
            ·
              refine ⟨21549912713152819155139463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14366608475435212770092975 21549912713152819155139463)
              ·
                refine ⟨32324869069729228732709195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21549912713152819155139463 32324869069729228732709195)
                ·
                  refine ⟨48487303604593843099063793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32324869069729228732709195 48487303604593843099063793)
                  ·
                    refine ⟨36365477703445382324297845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48487303604593843099063793 36365477703445382324297845)
                    ·
                      refine ⟨3409263534698004592902923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36365477703445382324297845 3409263534698004592902923)
                      ·
                        rfl

theorem cell23_6639517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_6639517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639517 prefixEnd_6639517 := by exact prefixLift 6639517
  have htrace : WordTrace (prefixWord ++ tailWord_6639517) baseStart_6639517 baseEnd_6639517 := by
    simpa [prefixWord, tailWord_6639517, baseEnd_6639517] using wordTrace_append hprefix tailTrace_6639517
  have hstable : (prefixWord ++ tailWord_6639517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639517).length < 2 ^ (prefixWord ++ tailWord_6639517).sum := by decide
  have hdescent : baseEnd_6639517 < baseStart_6639517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639522 : List Nat := [3, 3, 1, 2, 4, 1, 2, 1, 2, 2, 2]
def baseStart_6639522 : Nat := 118140960795 + 6639522 * 2 ^ 59
def prefixEnd_6639522 : Nat := 4983230072969 + 3 ^ 40 * 6639522 * 2
def baseEnd_6639522 : Nat := 3409266102101277073340401

theorem tailTrace_6639522 : CollatzResearch.WordTrace tailWord_6639522 prefixEnd_6639522 3409266102101277073340401 := by
  unfold tailWord_6639522
  simp only [CollatzResearch.WordTrace]
  refine ⟨60540815463038302231282205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161442174568102139283419213 60540815463038302231282205)
  ·
    refine ⟨22702805798639363336730827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60540815463038302231282205 22702805798639363336730827)
    ·
      refine ⟨34054208697959045005096241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22702805798639363336730827 34054208697959045005096241)
      ·
        refine ⟨25540656523469283753822181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34054208697959045005096241 25540656523469283753822181)
        ·
          refine ⟨4788873098150490703841659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25540656523469283753822181 4788873098150490703841659)
          ·
            refine ⟨7183309647225736055762489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4788873098150490703841659 7183309647225736055762489)
            ·
              refine ⟨5387482235419302041821867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7183309647225736055762489 5387482235419302041821867)
              ·
                refine ⟨8081223353128953062732801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5387482235419302041821867 8081223353128953062732801)
                ·
                  refine ⟨6060917514846714797049601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8081223353128953062732801 6060917514846714797049601)
                  ·
                    refine ⟨4545688136135036097787201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6060917514846714797049601 4545688136135036097787201)
                    ·
                      refine ⟨3409266102101277073340401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4545688136135036097787201 3409266102101277073340401)
                      ·
                        rfl

theorem cell23_6639522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_6639522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639522 prefixEnd_6639522 := by exact prefixLift 6639522
  have htrace : WordTrace (prefixWord ++ tailWord_6639522) baseStart_6639522 baseEnd_6639522 := by
    simpa [prefixWord, tailWord_6639522, baseEnd_6639522] using wordTrace_append hprefix tailTrace_6639522
  have hstable : (prefixWord ++ tailWord_6639522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639522).length < 2 ^ (prefixWord ++ tailWord_6639522).sum := by decide
  have hdescent : baseEnd_6639522 < baseStart_6639522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639547 : List Nat := [1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 3]
def baseStart_6639547 : Nat := 118140960795 + 6639547 * 2 ^ 59
def prefixEnd_6639547 : Nat := 4983230072969 + 3 ^ 40 * 6639547 * 2
def baseEnd_6639547 : Nat := 3409278939117639475527785

theorem tailTrace_6639547 : CollatzResearch.WordTrace tailWord_6639547 prefixEnd_6639547 3409278939117639475527785 := by
  unfold tailWord_6639547
  simp only [CollatzResearch.WordTrace]
  refine ⟨242164173677062638194788895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161442782451375092129859263 242164173677062638194788895)
  ·
    refine ⟨363246260515593957292183343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242164173677062638194788895 363246260515593957292183343)
    ·
      refine ⟨544869390773390935938275015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363246260515593957292183343 544869390773390935938275015)
      ·
        refine ⟨817304086160086403907412523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544869390773390935938275015 817304086160086403907412523)
        ·
          refine ⟨1225956129240129605861118785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817304086160086403907412523 1225956129240129605861118785)
          ·
            refine ⟨919467096930097204395839089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1225956129240129605861118785 919467096930097204395839089)
            ·
              refine ⟨689600322697572903296879317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 919467096930097204395839089 689600322697572903296879317)
              ·
                refine ⟨16162507563224364921020609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 689600322697572903296879317 16162507563224364921020609)
                ·
                  refine ⟨12121880672418273690765457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16162507563224364921020609 12121880672418273690765457)
                  ·
                    refine ⟨9091410504313705268074093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12121880672418273690765457 9091410504313705268074093)
                    ·
                      refine ⟨3409278939117639475527785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9091410504313705268074093 3409278939117639475527785)
                      ·
                        rfl

theorem cell23_6639547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 3].length) (baseStart_6639547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639547 prefixEnd_6639547 := by exact prefixLift 6639547
  have htrace : WordTrace (prefixWord ++ tailWord_6639547) baseStart_6639547 baseEnd_6639547 := by
    simpa [prefixWord, tailWord_6639547, baseEnd_6639547] using wordTrace_append hprefix tailTrace_6639547
  have hstable : (prefixWord ++ tailWord_6639547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639547).length < 2 ^ (prefixWord ++ tailWord_6639547).sum := by decide
  have hdescent : baseEnd_6639547 < baseStart_6639547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639564 : List Nat := [2, 2, 1, 4, 1, 2, 2, 2, 2, 2, 3]
def baseStart_6639564 : Nat := 118140960795 + 6639564 * 2 ^ 59
def prefixEnd_6639564 : Nat := 4983230072969 + 3 ^ 40 * 6639564 * 2
def baseEnd_6639564 : Nat := 3409287668288765909015207

theorem tailTrace_6639564 : CollatzResearch.WordTrace tailWord_6639564 prefixEnd_6639564 3409287668288765909015207 := by
  unfold tailWord_6639564
  simp only [CollatzResearch.WordTrace]
  refine ⟨121082396859000525049078873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161443195812000700065438497 121082396859000525049078873)
  ·
    refine ⟨90811797644250393786809155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121082396859000525049078873 90811797644250393786809155)
    ·
      refine ⟨136217696466375590680213733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90811797644250393786809155 136217696466375590680213733)
      ·
        refine ⟨25540818087445423252540075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136217696466375590680213733 25540818087445423252540075)
        ·
          refine ⟨38311227131168134878810113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25540818087445423252540075 38311227131168134878810113)
          ·
            refine ⟨28733420348376101159107585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38311227131168134878810113 28733420348376101159107585)
            ·
              refine ⟨21550065261282075869330689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28733420348376101159107585 21550065261282075869330689)
              ·
                refine ⟨16162548945961556901998017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21550065261282075869330689 16162548945961556901998017)
                ·
                  refine ⟨12121911709471167676498513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16162548945961556901998017 12121911709471167676498513)
                  ·
                    refine ⟨9091433782103375757373885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12121911709471167676498513 9091433782103375757373885)
                    ·
                      refine ⟨3409287668288765909015207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9091433782103375757373885 3409287668288765909015207)
                      ·
                        rfl

theorem cell23_6639564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_6639564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639564 prefixEnd_6639564 := by exact prefixLift 6639564
  have htrace : WordTrace (prefixWord ++ tailWord_6639564) baseStart_6639564 baseEnd_6639564 := by
    simpa [prefixWord, tailWord_6639564, baseEnd_6639564] using wordTrace_append hprefix tailTrace_6639564
  have hstable : (prefixWord ++ tailWord_6639564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639564).length < 2 ^ (prefixWord ++ tailWord_6639564).sum := by decide
  have hdescent : baseEnd_6639564 < baseStart_6639564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639567 : List Nat := [1, 1, 2, 1, 1, 5, 4, 2, 6]
def baseStart_6639567 : Nat := 118140960795 + 6639567 * 2 ^ 59
def prefixEnd_6639567 : Nat := 4983230072969 + 3 ^ 40 * 6639567 * 2
def baseEnd_6639567 : Nat := 378809912081192155253077

theorem tailTrace_6639567 : CollatzResearch.WordTrace tailWord_6639567 prefixEnd_6639567 378809912081192155253077 := by
  unfold tailWord_6639567
  simp only [CollatzResearch.WordTrace]
  refine ⟨242164903136990181610516955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161443268757993454407011303 242164903136990181610516955)
  ·
    refine ⟨363247354705485272415775433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242164903136990181610516955 363247354705485272415775433)
    ·
      refine ⟨272435516029113954311831575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363247354705485272415775433 272435516029113954311831575)
      ·
        refine ⟨408653274043670931467747363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272435516029113954311831575 408653274043670931467747363)
        ·
          refine ⟨612979911065506397201621045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408653274043670931467747363 612979911065506397201621045)
          ·
            refine ⟨57466866662391224737651973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 612979911065506397201621045 57466866662391224737651973)
            ·
              refine ⟨10775037499198354638309745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57466866662391224737651973 10775037499198354638309745)
              ·
                refine ⟨8081278124398765978732309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10775037499198354638309745 8081278124398765978732309)
                ·
                  refine ⟨378809912081192155253077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8081278124398765978732309 378809912081192155253077)
                  ·
                    rfl

theorem cell23_6639567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 6].length) (baseStart_6639567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639567 prefixEnd_6639567 := by exact prefixLift 6639567
  have htrace : WordTrace (prefixWord ++ tailWord_6639567) baseStart_6639567 baseEnd_6639567 := by
    simpa [prefixWord, tailWord_6639567, baseEnd_6639567] using wordTrace_append hprefix tailTrace_6639567
  have hstable : (prefixWord ++ tailWord_6639567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639567).length < 2 ^ (prefixWord ++ tailWord_6639567).sum := by decide
  have hdescent : baseEnd_6639567 < baseStart_6639567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639611 : List Nat := [1, 1, 1, 1, 1, 3, 5, 5, 1, 1, 3]
def baseStart_6639611 : Nat := 118140960795 + 6639611 * 2 ^ 59
def prefixEnd_6639611 : Nat := 4983230072969 + 3 ^ 40 * 6639611 * 2
def baseEnd_6639611 : Nat := 3409311801879527225127491

theorem tailTrace_6639611 : CollatzResearch.WordTrace tailWord_6639611 prefixEnd_6639611 3409311801879527225127491 := by
  unfold tailWord_6639611
  simp only [CollatzResearch.WordTrace]
  refine ⟨242166507948830777125118687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161444338632553851416745791 242166507948830777125118687)
  ·
    refine ⟨363249761923246165687678031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242166507948830777125118687 363249761923246165687678031)
    ·
      refine ⟨544874642884869248531517047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363249761923246165687678031 544874642884869248531517047)
      ·
        refine ⟨817311964327303872797275571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544874642884869248531517047 817311964327303872797275571)
        ·
          refine ⟨1225967946490955809195913357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817311964327303872797275571 1225967946490955809195913357)
          ·
            refine ⟨459737979934108428448467509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1225967946490955809195913357 459737979934108428448467509)
            ·
              refine ⟨43100435618822665167043829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 459737979934108428448467509 43100435618822665167043829)
              ·
                refine ⟨4040665839264624859410359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43100435618822665167043829 4040665839264624859410359)
                ·
                  refine ⟨6060998758896937289115539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4040665839264624859410359 6060998758896937289115539)
                  ·
                    refine ⟨9091498138345405933673309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6060998758896937289115539 9091498138345405933673309)
                    ·
                      refine ⟨3409311801879527225127491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9091498138345405933673309 3409311801879527225127491)
                      ·
                        rfl

theorem cell23_6639611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 1, 1, 3].length) (baseStart_6639611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639611 prefixEnd_6639611 := by exact prefixLift 6639611
  have htrace : WordTrace (prefixWord ++ tailWord_6639611) baseStart_6639611 baseEnd_6639611 := by
    simpa [prefixWord, tailWord_6639611, baseEnd_6639611] using wordTrace_append hprefix tailTrace_6639611
  have hstable : (prefixWord ++ tailWord_6639611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639611).length < 2 ^ (prefixWord ++ tailWord_6639611).sum := by decide
  have hdescent : baseEnd_6639611 < baseStart_6639611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639622 : List Nat := [6, 2, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_6639622 : Nat := 118140960795 + 6639622 * 2 ^ 59
def prefixEnd_6639622 : Nat := 4983230072969 + 3 ^ 40 * 6639622 * 2
def baseEnd_6639622 : Nat := 1136439150055575560696647

theorem tailTrace_6639622 : CollatzResearch.WordTrace tailWord_6639622 prefixEnd_6639622 1136439150055575560696647 := by
  unfold tailWord_6639622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7567715910993466437617785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 161444606101193950669179413 7567715910993466437617785)
  ·
    refine ⟨5675786933245099828213339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7567715910993466437617785 5675786933245099828213339)
    ·
      refine ⟨8513680399867649742320009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5675786933245099828213339 8513680399867649742320009)
      ·
        refine ⟨6385260299900737306740007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8513680399867649742320009 6385260299900737306740007)
        ·
          refine ⟨9577890449851105960110011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6385260299900737306740007 9577890449851105960110011)
          ·
            refine ⟨14366835674776658940165017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9577890449851105960110011 14366835674776658940165017)
            ·
              refine ⟨10775126756082494205123763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14366835674776658940165017 10775126756082494205123763)
              ·
                refine ⟨16162690134123741307685645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10775126756082494205123763 16162690134123741307685645)
                ·
                  refine ⟨6061008800296402990382117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16162690134123741307685645 6061008800296402990382117)
                  ·
                    refine ⟨1136439150055575560696647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6061008800296402990382117 1136439150055575560696647)
                    ·
                      rfl

theorem cell23_6639622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_6639622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639622 prefixEnd_6639622 := by exact prefixLift 6639622
  have htrace : WordTrace (prefixWord ++ tailWord_6639622) baseStart_6639622 baseEnd_6639622 := by
    simpa [prefixWord, tailWord_6639622, baseEnd_6639622] using wordTrace_append hprefix tailTrace_6639622
  have hstable : (prefixWord ++ tailWord_6639622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639622).length < 2 ^ (prefixWord ++ tailWord_6639622).sum := by decide
  have hdescent : baseEnd_6639622 < baseStart_6639622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639644 : List Nat := [2, 2, 3, 1, 3, 1, 3, 1, 1, 6]
def baseStart_6639644 : Nat := 118140960795 + 6639644 * 2 ^ 59
def prefixEnd_6639644 : Nat := 4983230072969 + 3 ^ 40 * 6639644 * 2
def baseEnd_6639644 : Nat := 1136442915580375198671613

theorem tailTrace_6639644 : CollatzResearch.WordTrace tailWord_6639644 prefixEnd_6639644 1136442915580375198671613 := by
  unfold tailWord_6639644
  simp only [CollatzResearch.WordTrace]
  refine ⟨121083855778855611880534993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161445141038474149174046657 121083855778855611880534993)
  ·
    refine ⟨90812891834141708910401245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121083855778855611880534993 90812891834141708910401245)
    ·
      refine ⟨34054834437803140841400467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90812891834141708910401245 34054834437803140841400467)
      ·
        refine ⟨51082251656704711262100701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34054834437803140841400467 51082251656704711262100701)
        ·
          refine ⟨19155844371264266723287763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51082251656704711262100701 19155844371264266723287763)
          ·
            refine ⟨28733766556896400084931645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19155844371264266723287763 28733766556896400084931645)
            ·
              refine ⟨10775162458836150031849367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28733766556896400084931645 10775162458836150031849367)
              ·
                refine ⟨16162743688254225047774051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10775162458836150031849367 16162743688254225047774051)
                ·
                  refine ⟨24244115532381337571661077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16162743688254225047774051 24244115532381337571661077)
                  ·
                    refine ⟨1136442915580375198671613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24244115532381337571661077 1136442915580375198671613)
                    ·
                      rfl

theorem cell23_6639644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_6639644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639644 prefixEnd_6639644 := by exact prefixLift 6639644
  have htrace : WordTrace (prefixWord ++ tailWord_6639644) baseStart_6639644 baseEnd_6639644 := by
    simpa [prefixWord, tailWord_6639644, baseEnd_6639644] using wordTrace_append hprefix tailTrace_6639644
  have hstable : (prefixWord ++ tailWord_6639644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639644).length < 2 ^ (prefixWord ++ tailWord_6639644).sum := by decide
  have hdescent : baseEnd_6639644 < baseStart_6639644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639647 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 6]
def baseStart_6639647 : Nat := 118140960795 + 6639647 * 2 ^ 59
def prefixEnd_6639647 : Nat := 4983230072969 + 3 ^ 40 * 6639647 * 2
def baseEnd_6639647 : Nat := 3409330287183089084277325

theorem tailTrace_6639647 : CollatzResearch.WordTrace tailWord_6639647 prefixEnd_6639647 3409330287183089084277325 := by
  unfold tailWord_6639647
  simp only [CollatzResearch.WordTrace]
  refine ⟨242167820976700355273429195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161445213984466903515619463 242167820976700355273429195)
  ·
    refine ⟨363251731465050532910143793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242167820976700355273429195 363251731465050532910143793)
    ·
      refine ⟨272438798598787899682607845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363251731465050532910143793 272438798598787899682607845)
      ·
        refine ⟨51082274737272731190488971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272438798598787899682607845 51082274737272731190488971)
        ·
          refine ⟨76623412105909096785733457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51082274737272731190488971 76623412105909096785733457)
          ·
            refine ⟨57467559079431822589300093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76623412105909096785733457 57467559079431822589300093)
            ·
              refine ⟨21550334654786933470987535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57467559079431822589300093 21550334654786933470987535)
              ·
                refine ⟨32325501982180400206481303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21550334654786933470987535 32325501982180400206481303)
                ·
                  refine ⟨48488252973270600309721955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32325501982180400206481303 48488252973270600309721955)
                  ·
                    refine ⟨72732379459905900464582933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48488252973270600309721955 72732379459905900464582933)
                    ·
                      refine ⟨3409330287183089084277325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72732379459905900464582933 3409330287183089084277325)
                      ·
                        rfl

theorem cell23_6639647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_6639647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639647 prefixEnd_6639647 := by exact prefixLift 6639647
  have htrace : WordTrace (prefixWord ++ tailWord_6639647) baseStart_6639647 baseEnd_6639647 := by
    simpa [prefixWord, tailWord_6639647, baseEnd_6639647] using wordTrace_append hprefix tailTrace_6639647
  have hstable : (prefixWord ++ tailWord_6639647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639647).length < 2 ^ (prefixWord ++ tailWord_6639647).sum := by decide
  have hdescent : baseEnd_6639647 < baseStart_6639647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639651 : List Nat := [1, 1, 1, 4, 3, 1, 1, 4, 3, 2, 2]
def baseStart_6639651 : Nat := 118140960795 + 6639651 * 2 ^ 59
def prefixEnd_6639651 : Nat := 4983230072969 + 3 ^ 40 * 6639651 * 2
def baseEnd_6639651 : Nat := 3409332341105707068627307

theorem tailTrace_6639651 : CollatzResearch.WordTrace tailWord_6639651 prefixEnd_6639651 3409332341105707068627307 := by
  unfold tailWord_6639651
  simp only [CollatzResearch.WordTrace]
  refine ⟨242167966868685863956574807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161445311245790575971049871 242167966868685863956574807)
  ·
    refine ⟨363251950303028795934862211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242167966868685863956574807 363251950303028795934862211)
    ·
      refine ⟨544877925454543193902293317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363251950303028795934862211 544877925454543193902293317)
      ·
        refine ⟨102164611022726848856679997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 544877925454543193902293317 102164611022726848856679997)
        ·
          refine ⟨38311729133522568321254999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102164611022726848856679997 38311729133522568321254999)
          ·
            refine ⟨57467593700283852481882499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38311729133522568321254999 57467593700283852481882499)
            ·
              refine ⟨86201390550425778722823749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57467593700283852481882499 86201390550425778722823749)
              ·
                refine ⟨16162760728204833510529453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86201390550425778722823749 16162760728204833510529453)
                ·
                  refine ⟨6061035273076812566448545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16162760728204833510529453 6061035273076812566448545)
                  ·
                    refine ⟨4545776454807609424836409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6061035273076812566448545 4545776454807609424836409)
                    ·
                      refine ⟨3409332341105707068627307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4545776454807609424836409 3409332341105707068627307)
                      ·
                        rfl

theorem cell23_6639651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 2, 2].length) (baseStart_6639651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639651 prefixEnd_6639651 := by exact prefixLift 6639651
  have htrace : WordTrace (prefixWord ++ tailWord_6639651) baseStart_6639651 baseEnd_6639651 := by
    simpa [prefixWord, tailWord_6639651, baseEnd_6639651] using wordTrace_append hprefix tailTrace_6639651
  have hstable : (prefixWord ++ tailWord_6639651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639651).length < 2 ^ (prefixWord ++ tailWord_6639651).sum := by decide
  have hdescent : baseEnd_6639651 < baseStart_6639651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639687 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 2, 7]
def baseStart_6639687 : Nat := 118140960795 + 6639687 * 2 ^ 59
def prefixEnd_6639687 : Nat := 4983230072969 + 3 ^ 40 * 6639687 * 2
def baseEnd_6639687 : Nat := 1136450275469756309259047

theorem tailTrace_6639687 : CollatzResearch.WordTrace tailWord_6639687 prefixEnd_6639687 1136450275469756309259047 := by
  unfold tailWord_6639687
  simp only [CollatzResearch.WordTrace]
  refine ⟨242169279896555442104885315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161446186597703628069923543 242169279896555442104885315)
  ·
    refine ⟨363253919844833163157327973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242169279896555442104885315 363253919844833163157327973)
    ·
      refine ⟨68110109970906218091998995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 363253919844833163157327973 68110109970906218091998995)
      ·
        refine ⟨102165164956359327137998493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68110109970906218091998995 102165164956359327137998493)
        ·
          refine ⟨38311936858634747676749435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102165164956359327137998493 38311936858634747676749435)
          ·
            refine ⟨57467905287952121515124153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38311936858634747676749435 57467905287952121515124153)
            ·
              refine ⟨43100928965964091136343115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57467905287952121515124153 43100928965964091136343115)
              ·
                refine ⟨64651393448946136704514673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43100928965964091136343115 64651393448946136704514673)
                ·
                  refine ⟨48488545086709602528386005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64651393448946136704514673 48488545086709602528386005)
                  ·
                    refine ⟨1136450275469756309259047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48488545086709602528386005 1136450275469756309259047)
                    ·
                      rfl

theorem cell23_6639687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_6639687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639687 prefixEnd_6639687 := by exact prefixLift 6639687
  have htrace : WordTrace (prefixWord ++ tailWord_6639687) baseStart_6639687 baseEnd_6639687 := by
    simpa [prefixWord, tailWord_6639687, baseEnd_6639687] using wordTrace_append hprefix tailTrace_6639687
  have hstable : (prefixWord ++ tailWord_6639687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639687).length < 2 ^ (prefixWord ++ tailWord_6639687).sum := by decide
  have hdescent : baseEnd_6639687 < baseStart_6639687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639711 : List Nat := [1, 1, 2, 3, 1, 1, 2, 6, 1, 3, 2]
def baseStart_6639711 : Nat := 118140960795 + 6639711 * 2 ^ 59
def prefixEnd_6639711 : Nat := 4983230072969 + 3 ^ 40 * 6639711 * 2
def baseEnd_6639711 : Nat := 3409363149944976833877031

theorem tailTrace_6639711 : CollatzResearch.WordTrace tailWord_6639711 prefixEnd_6639711 3409363149944976833877031 := by
  unfold tailWord_6639711
  simp only [CollatzResearch.WordTrace]
  refine ⟨242170155248468494203758987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161446770165645662802505991 242170155248468494203758987)
  ·
    refine ⟨363255232872702741305638481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242170155248468494203758987 363255232872702741305638481)
    ·
      refine ⟨272441424654527055979228861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363255232872702741305638481 272441424654527055979228861)
      ·
        refine ⟨102165534245447645992210823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272441424654527055979228861 102165534245447645992210823)
        ·
          refine ⟨153248301368171468988316235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102165534245447645992210823 153248301368171468988316235)
          ·
            refine ⟨229872452052257203482474353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153248301368171468988316235 229872452052257203482474353)
            ·
              refine ⟨172404339039192902611855765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229872452052257203482474353 172404339039192902611855765)
              ·
                refine ⟨8081453392462167309930739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 172404339039192902611855765 8081453392462167309930739)
                ·
                  refine ⟨12122180088693250964896109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8081453392462167309930739 12122180088693250964896109)
                  ·
                    refine ⟨4545817533259969111836041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12122180088693250964896109 4545817533259969111836041)
                    ·
                      refine ⟨3409363149944976833877031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4545817533259969111836041 3409363149944976833877031)
                      ·
                        rfl

theorem cell23_6639711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 3, 2].length) (baseStart_6639711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639711 prefixEnd_6639711 := by exact prefixLift 6639711
  have htrace : WordTrace (prefixWord ++ tailWord_6639711) baseStart_6639711 baseEnd_6639711 := by
    simpa [prefixWord, tailWord_6639711, baseEnd_6639711] using wordTrace_append hprefix tailTrace_6639711
  have hstable : (prefixWord ++ tailWord_6639711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639711).length < 2 ^ (prefixWord ++ tailWord_6639711).sum := by decide
  have hdescent : baseEnd_6639711 < baseStart_6639711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639754 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 1, 4, 4]
def baseStart_6639754 : Nat := 118140960795 + 6639754 * 2 ^ 59
def prefixEnd_6639754 : Nat := 4983230072969 + 3 ^ 40 * 6639754 * 2
def baseEnd_6639754 : Nat := 3409385229613120165639333

theorem tailTrace_6639754 : CollatzResearch.WordTrace tailWord_6639754 prefixEnd_6639754 3409385229613120165639333 := by
  unfold tailWord_6639754
  simp only [CollatzResearch.WordTrace]
  refine ⟨60542930896828178136893579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161447815724875141698382877 60542930896828178136893579)
  ·
    refine ⟨90814396345242267205340369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60542930896828178136893579 90814396345242267205340369)
    ·
      refine ⟨68110797258931700404005277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90814396345242267205340369 68110797258931700404005277)
      ·
        refine ⟨25541548972099387651501979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68110797258931700404005277 25541548972099387651501979)
        ·
          refine ⟨38312323458149081477252969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25541548972099387651501979 38312323458149081477252969)
          ·
            refine ⟨28734242593611811107939727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38312323458149081477252969 28734242593611811107939727)
            ·
              refine ⟨43101363890417716661909591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28734242593611811107939727 43101363890417716661909591)
              ·
                refine ⟨64652045835626574992864387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43101363890417716661909591 64652045835626574992864387)
                ·
                  refine ⟨96978068753439862489296581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64652045835626574992864387 96978068753439862489296581)
                  ·
                    refine ⟨18183387891269974216743109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96978068753439862489296581 18183387891269974216743109)
                    ·
                      refine ⟨3409385229613120165639333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18183387891269974216743109 3409385229613120165639333)
                      ·
                        rfl

theorem cell23_6639754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_6639754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639754 prefixEnd_6639754 := by exact prefixLift 6639754
  have htrace : WordTrace (prefixWord ++ tailWord_6639754) baseStart_6639754 baseEnd_6639754 := by
    simpa [prefixWord, tailWord_6639754, baseEnd_6639754] using wordTrace_append hprefix tailTrace_6639754
  have hstable : (prefixWord ++ tailWord_6639754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639754).length < 2 ^ (prefixWord ++ tailWord_6639754).sum := by decide
  have hdescent : baseEnd_6639754 < baseStart_6639754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639781 : List Nat := [1, 3, 1, 2, 1, 3, 4, 3, 5]
def baseStart_6639781 : Nat := 118140960795 + 6639781 * 2 ^ 59
def prefixEnd_6639781 : Nat := 4983230072969 + 3 ^ 40 * 6639781 * 2
def baseEnd_6639781 : Nat := 378822121510087951111301

theorem tailTrace_6639781 : CollatzResearch.WordTrace tailWord_6639781 prefixEnd_6639781 378822121510087951111301 := by
  unfold tailWord_6639781
  simp only [CollatzResearch.WordTrace]
  refine ⟨242172708358214896158807197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161448472238809930772538131 242172708358214896158807197)
  ·
    refine ⟨90814765634330586059552699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242172708358214896158807197 90814765634330586059552699)
    ·
      refine ⟨136222148451495879089329049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90814765634330586059552699 136222148451495879089329049)
      ·
        refine ⟨102166611338621909316996787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136222148451495879089329049 102166611338621909316996787)
        ·
          refine ⟨153249917007932863975495181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102166611338621909316996787 153249917007932863975495181)
          ·
            refine ⟨57468718877974823990810693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153249917007932863975495181 57468718877974823990810693)
            ·
              refine ⟨10775384789620279498277005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57468718877974823990810693 10775384789620279498277005)
              ·
                refine ⟨4040769296107604811853877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10775384789620279498277005 4040769296107604811853877)
                ·
                  refine ⟨378822121510087951111301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4040769296107604811853877 378822121510087951111301)
                  ·
                    rfl

theorem cell23_6639781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 5].length) (baseStart_6639781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639781 prefixEnd_6639781 := by exact prefixLift 6639781
  have htrace : WordTrace (prefixWord ++ tailWord_6639781) baseStart_6639781 baseEnd_6639781 := by
    simpa [prefixWord, tailWord_6639781, baseEnd_6639781] using wordTrace_append hprefix tailTrace_6639781
  have hstable : (prefixWord ++ tailWord_6639781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639781).length < 2 ^ (prefixWord ++ tailWord_6639781).sum := by decide
  have hdescent : baseEnd_6639781 < baseStart_6639781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639794 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 4, 5]
def baseStart_6639794 : Nat := 118140960795 + 6639794 * 2 ^ 59
def prefixEnd_6639794 : Nat := 4983230072969 + 3 ^ 40 * 6639794 * 2
def baseEnd_6639794 : Nat := 1136468589613100003046383

theorem tailTrace_6639794 : CollatzResearch.WordTrace tailWord_6639794 prefixEnd_6639794 1136468589613100003046383 := by
  unfold tailWord_6639794
  simp only [CollatzResearch.WordTrace]
  refine ⟨60543295626791949844757609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161448788338111866252686957 60543295626791949844757609)
  ·
    refine ⟨45407471720093962383568207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60543295626791949844757609 45407471720093962383568207)
    ·
      refine ⟨68111207580140943575352311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45407471720093962383568207 68111207580140943575352311)
      ·
        refine ⟨102166811370211415363028467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68111207580140943575352311 102166811370211415363028467)
        ·
          refine ⟨153250217055317123044542701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102166811370211415363028467 153250217055317123044542701)
          ·
            refine ⟨57468831395743921141703513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153250217055317123044542701 57468831395743921141703513)
            ·
              refine ⟨43101623546807940856277635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57468831395743921141703513 43101623546807940856277635)
              ·
                refine ⟨64652435320211911284416453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43101623546807940856277635 64652435320211911284416453)
                ·
                  refine ⟨12122331622539733365828085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64652435320211911284416453 12122331622539733365828085)
                  ·
                    refine ⟨1136468589613100003046383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12122331622539733365828085 1136468589613100003046383)
                    ·
                      rfl

theorem cell23_6639794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_6639794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639794 prefixEnd_6639794 := by exact prefixLift 6639794
  have htrace : WordTrace (prefixWord ++ tailWord_6639794) baseStart_6639794 baseEnd_6639794 := by
    simpa [prefixWord, tailWord_6639794, baseEnd_6639794] using wordTrace_append hprefix tailTrace_6639794
  have hstable : (prefixWord ++ tailWord_6639794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639794).length < 2 ^ (prefixWord ++ tailWord_6639794).sum := by decide
  have hdescent : baseEnd_6639794 < baseStart_6639794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639809 : List Nat := [1, 2, 6, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_6639809 : Nat := 118140960795 + 6639809 * 2 ^ 59
def prefixEnd_6639809 : Nat := 4983230072969 + 3 ^ 40 * 6639809 * 2
def baseEnd_6639809 : Nat := 3409413471049117450451581

theorem tailTrace_6639809 : CollatzResearch.WordTrace tailWord_6639809 prefixEnd_6639809 3409413471049117450451581 := by
  unfold tailWord_6639809
  simp only [CollatzResearch.WordTrace]
  refine ⟨242173729602113456940826481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161449153068075637960550987 242173729602113456940826481)
  ·
    refine ⟨181630297201585092705619861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242173729602113456940826481 181630297201585092705619861)
    ·
      refine ⟨8513920181324301220575931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 181630297201585092705619861 8513920181324301220575931)
      ·
        refine ⟨12770880271986451830863897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8513920181324301220575931 12770880271986451830863897)
        ·
          refine ⟨9578160203989838873147923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12770880271986451830863897 9578160203989838873147923)
          ·
            refine ⟨14367240305984758309721885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9578160203989838873147923 14367240305984758309721885)
            ·
              refine ⟨5387715114744284366145707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14367240305984758309721885 5387715114744284366145707)
              ·
                refine ⟨8081572672116426549218561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5387715114744284366145707 8081572672116426549218561)
                ·
                  refine ⟨6061179504087319911913921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8081572672116426549218561 6061179504087319911913921)
                  ·
                    refine ⟨4545884628065489933935441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6061179504087319911913921 4545884628065489933935441)
                    ·
                      refine ⟨3409413471049117450451581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4545884628065489933935441 3409413471049117450451581)
                      ·
                        rfl

theorem cell23_6639809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_6639809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639809 prefixEnd_6639809 := by exact prefixLift 6639809
  have htrace : WordTrace (prefixWord ++ tailWord_6639809) baseStart_6639809 baseEnd_6639809 := by
    simpa [prefixWord, tailWord_6639809, baseEnd_6639809] using wordTrace_append hprefix tailTrace_6639809
  have hstable : (prefixWord ++ tailWord_6639809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639809).length < 2 ^ (prefixWord ++ tailWord_6639809).sum := by decide
  have hdescent : baseEnd_6639809 < baseStart_6639809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639851 : List Nat := [1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 3]
def baseStart_6639851 : Nat := 118140960795 + 6639851 * 2 ^ 59
def prefixEnd_6639851 : Nat := 4983230072969 + 3 ^ 40 * 6639851 * 2
def baseEnd_6639851 : Nat := 3409435037236606286126387

theorem tailTrace_6639851 : CollatzResearch.WordTrace tailWord_6639851 prefixEnd_6639851 3409435037236606286126387 := by
  unfold tailWord_6639851
  simp only [CollatzResearch.WordTrace]
  refine ⟨242175261467961298113855407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161450174311974198742570271 242175261467961298113855407)
  ·
    refine ⟨363262892201941947170783111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242175261467961298113855407 363262892201941947170783111)
    ·
      refine ⟨544894338302912920756174667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363262892201941947170783111 544894338302912920756174667)
      ·
        refine ⟨817341507454369381134262001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544894338302912920756174667 817341507454369381134262001)
        ·
          refine ⟨613006130590777035850696501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 817341507454369381134262001 613006130590777035850696501)
          ·
            refine ⟨57469324742885347111002797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 613006130590777035850696501 57469324742885347111002797)
            ·
              refine ⟨21550996778582005166626049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57469324742885347111002797 21550996778582005166626049)
              ·
                refine ⟨16163247583936503874969537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21550996778582005166626049 16163247583936503874969537)
                ·
                  refine ⟨12122435687952377906227153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16163247583936503874969537 12122435687952377906227153)
                  ·
                    refine ⟨9091826765964283429670365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12122435687952377906227153 9091826765964283429670365)
                    ·
                      refine ⟨3409435037236606286126387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9091826765964283429670365 3409435037236606286126387)
                      ·
                        rfl

theorem cell23_6639851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 3].length) (baseStart_6639851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639851 prefixEnd_6639851 := by exact prefixLift 6639851
  have htrace : WordTrace (prefixWord ++ tailWord_6639851) baseStart_6639851 baseEnd_6639851 := by
    simpa [prefixWord, tailWord_6639851, baseEnd_6639851] using wordTrace_append hprefix tailTrace_6639851
  have hstable : (prefixWord ++ tailWord_6639851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639851).length < 2 ^ (prefixWord ++ tailWord_6639851).sum := by decide
  have hdescent : baseEnd_6639851 < baseStart_6639851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639858 : List Nat := [3, 2, 1, 3, 2, 1, 3, 1, 3, 4]
def baseStart_6639858 : Nat := 118140960795 + 6639858 * 2 ^ 59
def prefixEnd_6639858 : Nat := 4983230072969 + 3 ^ 40 * 6639858 * 2
def baseEnd_6639858 : Nat := 1136479543867062586246285

theorem tailTrace_6639858 : CollatzResearch.WordTrace tailWord_6639858 prefixEnd_6639858 1136479543867062586246285 := by
  unfold tailWord_6639858
  simp only [CollatzResearch.WordTrace]
  refine ⟨60543879194733984577340057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161450344519290625539573485 60543879194733984577340057)
  ·
    refine ⟨45407909396050488433005043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60543879194733984577340057 45407909396050488433005043)
    ·
      refine ⟨68111864094075732649507565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45407909396050488433005043 68111864094075732649507565)
      ·
        refine ⟨25541949035278399743565337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68111864094075732649507565 25541949035278399743565337)
        ·
          refine ⟨19156461776458799807674003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25541949035278399743565337 19156461776458799807674003)
          ·
            refine ⟨28734692664688199711511005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19156461776458799807674003 28734692664688199711511005)
            ·
              refine ⟨10775509749258074891816627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28734692664688199711511005 10775509749258074891816627)
              ·
                refine ⟨16163264623887112337724941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10775509749258074891816627 16163264623887112337724941)
                ·
                  refine ⟨6061224233957667126646853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16163264623887112337724941 6061224233957667126646853)
                  ·
                    refine ⟨1136479543867062586246285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6061224233957667126646853 1136479543867062586246285)
                    ·
                      rfl

theorem cell23_6639858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_6639858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639858 prefixEnd_6639858 := by exact prefixLift 6639858
  have htrace : WordTrace (prefixWord ++ tailWord_6639858) baseStart_6639858 baseEnd_6639858 := by
    simpa [prefixWord, tailWord_6639858, baseEnd_6639858] using wordTrace_append hprefix tailTrace_6639858
  have hstable : (prefixWord ++ tailWord_6639858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639858).length < 2 ^ (prefixWord ++ tailWord_6639858).sum := by decide
  have hdescent : baseEnd_6639858 < baseStart_6639858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639891 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 1, 5, 2]
def baseStart_6639891 : Nat := 118140960795 + 6639891 * 2 ^ 59
def prefixEnd_6639891 : Nat := 4983230072969 + 3 ^ 40 * 6639891 * 2
def baseEnd_6639891 : Nat := 3409455576462786129626203

theorem tailTrace_6639891 : CollatzResearch.WordTrace tailWord_6639891 prefixEnd_6639891 3409455576462786129626203 := by
  unfold tailWord_6639891
  simp only [CollatzResearch.WordTrace]
  refine ⟨242176720387816384945311527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161451146925210923296874351 242176720387816384945311527)
  ·
    refine ⟨363265080581724577417967291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242176720387816384945311527 363265080581724577417967291)
    ·
      refine ⟨544897620872586866126950937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363265080581724577417967291 544897620872586866126950937)
      ·
        refine ⟨408673215654440149595213203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 544897620872586866126950937 408673215654440149595213203)
        ·
          refine ⟨613009823481660224392819805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408673215654440149595213203 613009823481660224392819805)
          ·
            refine ⟨229878683805622584147307427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 613009823481660224392819805 229878683805622584147307427)
            ·
              refine ⟨344818025708433876220961141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229878683805622584147307427 344818025708433876220961141)
              ·
                refine ⟨32326689910165675895715107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 344818025708433876220961141 32326689910165675895715107)
                ·
                  refine ⟨48490034865248513843572661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32326689910165675895715107 48490034865248513843572661)
                  ·
                    refine ⟨4545940768617048172834937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48490034865248513843572661 4545940768617048172834937)
                    ·
                      refine ⟨3409455576462786129626203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4545940768617048172834937 3409455576462786129626203)
                      ·
                        rfl

theorem cell23_6639891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 5, 2].length) (baseStart_6639891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639891 prefixEnd_6639891 := by exact prefixLift 6639891
  have htrace : WordTrace (prefixWord ++ tailWord_6639891) baseStart_6639891 baseEnd_6639891 := by
    simpa [prefixWord, tailWord_6639891, baseEnd_6639891] using wordTrace_append hprefix tailTrace_6639891
  have hstable : (prefixWord ++ tailWord_6639891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639891).length < 2 ^ (prefixWord ++ tailWord_6639891).sum := by decide
  have hdescent : baseEnd_6639891 < baseStart_6639891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639909 : List Nat := [1, 3, 1, 2, 6, 1, 2, 2, 1, 4]
def baseStart_6639909 : Nat := 118140960795 + 6639909 * 2 ^ 59
def prefixEnd_6639909 : Nat := 4983230072969 + 3 ^ 40 * 6639909 * 2
def baseEnd_6639909 : Nat := 1136488273038189019733707

theorem tailTrace_6639909 : CollatzResearch.WordTrace tailWord_6639909 prefixEnd_6639909 1136488273038189019733707 := by
  unfold tailWord_6639909
  simp only [CollatzResearch.WordTrace]
  refine ⟨242177376901751174019466781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161451584601167449346311187 242177376901751174019466781)
  ·
    refine ⟨90816516338156690257300043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242177376901751174019466781 90816516338156690257300043)
    ·
      refine ⟨136224774507235035385950065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90816516338156690257300043 136224774507235035385950065)
      ·
        refine ⟨102168580880426276539462549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136224774507235035385950065 102168580880426276539462549)
        ·
          refine ⟨4789152228769981712787307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 102168580880426276539462549 4789152228769981712787307)
          ·
            refine ⟨7183728343154972569180961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4789152228769981712787307 7183728343154972569180961)
            ·
              refine ⟨5387796257366229426885721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7183728343154972569180961 5387796257366229426885721)
              ·
                refine ⟨4040847193024672070164291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5387796257366229426885721 4040847193024672070164291)
                ·
                  refine ⟨6061270789537008105246437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4040847193024672070164291 6061270789537008105246437)
                  ·
                    refine ⟨1136488273038189019733707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6061270789537008105246437 1136488273038189019733707)
                    ·
                      rfl

theorem cell23_6639909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 1, 4].length) (baseStart_6639909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639909 prefixEnd_6639909 := by exact prefixLift 6639909
  have htrace : WordTrace (prefixWord ++ tailWord_6639909) baseStart_6639909 baseEnd_6639909 := by
    simpa [prefixWord, tailWord_6639909, baseEnd_6639909] using wordTrace_append hprefix tailTrace_6639909
  have hstable : (prefixWord ++ tailWord_6639909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639909).length < 2 ^ (prefixWord ++ tailWord_6639909).sum := by decide
  have hdescent : baseEnd_6639909 < baseStart_6639909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6639944 : List Nat := [2, 1, 3, 1, 1, 2, 2, 11]
def baseStart_6639944 : Nat := 118140960795 + 6639944 * 2 ^ 59
def prefixEnd_6639944 : Nat := 4983230072969 + 3 ^ 40 * 6639944 * 2
def baseEnd_6639944 : Nat := 126277140405091645269017

theorem tailTrace_6639944 : CollatzResearch.WordTrace tailWord_6639944 prefixEnd_6639944 126277140405091645269017 := by
  unfold tailWord_6639944
  simp only [CollatzResearch.WordTrace]
  refine ⟨121089326728312187498495443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161452435637749583331327257 121089326728312187498495443)
  ·
    refine ⟨181633990092468281247743165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121089326728312187498495443 181633990092468281247743165)
    ·
      refine ⟨68112746284675605467903687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181633990092468281247743165 68112746284675605467903687)
      ·
        refine ⟨102169119427013408201855531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68112746284675605467903687 102169119427013408201855531)
        ·
          refine ⟨153253679140520112302783297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102169119427013408201855531 153253679140520112302783297)
          ·
            refine ⟨114940259355390084227087473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153253679140520112302783297 114940259355390084227087473)
            ·
              refine ⟨86205194516542563170315605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114940259355390084227087473 86205194516542563170315605)
              ·
                refine ⟨126277140405091645269017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 86205194516542563170315605 126277140405091645269017)
                ·
                  rfl

theorem cell23_6639944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 11].length) (baseStart_6639944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639944 prefixEnd_6639944 := by exact prefixLift 6639944
  have htrace : WordTrace (prefixWord ++ tailWord_6639944) baseStart_6639944 baseEnd_6639944 := by
    simpa [prefixWord, tailWord_6639944, baseEnd_6639944] using wordTrace_append hprefix tailTrace_6639944
  have hstable : (prefixWord ++ tailWord_6639944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639944).length < 2 ^ (prefixWord ++ tailWord_6639944).sum := by decide
  have hdescent : baseEnd_6639944 < baseStart_6639944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
