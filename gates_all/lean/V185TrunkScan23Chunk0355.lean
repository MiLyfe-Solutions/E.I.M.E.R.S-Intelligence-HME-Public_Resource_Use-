import V185TrunkScan23Chunk0354

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2100108 : List Nat := [2, 2, 1, 2, 1, 2, 2, 4, 3, 4]
def baseStart_2100108 : Nat := 118140960795 + 2100108 * 2 ^ 59
def prefixEnd_2100108 : Nat := 4983230072969 + 3 ^ 40 * 2100108 * 2
def baseEnd_2100108 : Nat := 359454943450858183830595

theorem tailTrace_2100108 : CollatzResearch.WordTrace tailWord_2100108 prefixEnd_2100108 359454943450858183830595 := by
  unfold tailWord_2100108
  simp only [CollatzResearch.WordTrace]
  refine ⟨38298615737837430368170489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51064820983783240490893985 38298615737837430368170489)
  ·
    refine ⟨28723961803378072776127867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38298615737837430368170489 28723961803378072776127867)
    ·
      refine ⟨43085942705067109164191801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28723961803378072776127867 43085942705067109164191801)
      ·
        refine ⟨32314457028800331873143851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43085942705067109164191801 32314457028800331873143851)
        ·
          refine ⟨48471685543200497809715777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32314457028800331873143851 48471685543200497809715777)
          ·
            refine ⟨36353764157400373357286833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48471685543200497809715777 36353764157400373357286833)
            ·
              refine ⟨27265323118050280017965125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36353764157400373357286833 27265323118050280017965125)
              ·
                refine ⟨5112248084634427503368461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27265323118050280017965125 5112248084634427503368461)
                ·
                  refine ⟨1917093031737910313763173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5112248084634427503368461 1917093031737910313763173)
                  ·
                    refine ⟨359454943450858183830595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1917093031737910313763173 359454943450858183830595)
                    ·
                      rfl

theorem cell23_2100108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 3, 4].length) (baseStart_2100108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100108 prefixEnd_2100108 := by exact prefixLift 2100108
  have htrace : WordTrace (prefixWord ++ tailWord_2100108) baseStart_2100108 baseEnd_2100108 := by
    simpa [prefixWord, tailWord_2100108, baseEnd_2100108] using wordTrace_append hprefix tailTrace_2100108
  have hstable : (prefixWord ++ tailWord_2100108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100108).length < 2 ^ (prefixWord ++ tailWord_2100108).sum := by decide
  have hdescent : baseEnd_2100108 < baseStart_2100108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100166 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_2100166 : Nat := 118140960795 + 2100166 * 2 ^ 59
def prefixEnd_2100166 : Nat := 4983230072969 + 3 ^ 40 * 2100166 * 2
def baseEnd_2100166 : Nat := 1078394612230535324566519

theorem tailTrace_2100166 : CollatzResearch.WordTrace tailWord_2100166 prefixEnd_2100166 1078394612230535324566519 := by
  unfold tailWord_2100166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2393729590920773020061011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51066231272976491094634901 2393729590920773020061011)
  ·
    refine ⟨3590594386381159530091517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2393729590920773020061011 3590594386381159530091517)
    ·
      refine ⟨1346472894892934823784319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3590594386381159530091517 1346472894892934823784319)
      ·
        refine ⟨2019709342339402235676479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1346472894892934823784319 2019709342339402235676479)
        ·
          refine ⟨3029564013509103353514719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2019709342339402235676479 3029564013509103353514719)
          ·
            refine ⟨4544346020263655030272079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3029564013509103353514719 4544346020263655030272079)
            ·
              refine ⟨6816519030395482545408119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4544346020263655030272079 6816519030395482545408119)
              ·
                refine ⟨10224778545593223818112179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6816519030395482545408119 10224778545593223818112179)
                ·
                  refine ⟨15337167818389835727168269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10224778545593223818112179 15337167818389835727168269)
                  ·
                    refine ⟨5751437931896188397688101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15337167818389835727168269 5751437931896188397688101)
                    ·
                      refine ⟨1078394612230535324566519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5751437931896188397688101 1078394612230535324566519)
                      ·
                        rfl

theorem cell23_2100166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_2100166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100166 prefixEnd_2100166 := by exact prefixLift 2100166
  have htrace : WordTrace (prefixWord ++ tailWord_2100166) baseStart_2100166 baseEnd_2100166 := by
    simpa [prefixWord, tailWord_2100166, baseEnd_2100166] using wordTrace_append hprefix tailTrace_2100166
  have hstable : (prefixWord ++ tailWord_2100166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100166).length < 2 ^ (prefixWord ++ tailWord_2100166).sum := by decide
  have hdescent : baseEnd_2100166 < baseStart_2100166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100175 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 1, 5, 2]
def baseStart_2100175 : Nat := 118140960795 + 2100175 * 2 ^ 59
def prefixEnd_2100175 : Nat := 4983230072969 + 3 ^ 40 * 2100175 * 2
def baseEnd_2100175 : Nat := 1078399233556425789353977

theorem tailTrace_2100175 : CollatzResearch.WordTrace tailWord_2100175 prefixEnd_2100175 1078399233556425789353977 := by
  unfold tailWord_2100175
  simp only [CollatzResearch.WordTrace]
  refine ⟨76599675166432131179029979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51066450110954754119353319 76599675166432131179029979)
  ·
    refine ⟨114899512749648196768544969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76599675166432131179029979 114899512749648196768544969)
    ·
      refine ⟨86174634562236147576408727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114899512749648196768544969 86174634562236147576408727)
      ·
        refine ⟨129261951843354221364613091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86174634562236147576408727 129261951843354221364613091)
        ·
          refine ⟨193892927765031332046919637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129261951843354221364613091 193892927765031332046919637)
          ·
            refine ⟨4544365494492921844849679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 193892927765031332046919637 4544365494492921844849679)
            ·
              refine ⟨6816548241739382767274519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4544365494492921844849679 6816548241739382767274519)
              ·
                refine ⟨10224822362609074150911779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6816548241739382767274519 10224822362609074150911779)
                ·
                  refine ⟨15337233543913611226367669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10224822362609074150911779 15337233543913611226367669)
                  ·
                    refine ⟨1437865644741901052471969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15337233543913611226367669 1437865644741901052471969)
                    ·
                      refine ⟨1078399233556425789353977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1437865644741901052471969 1078399233556425789353977)
                      ·
                        rfl

theorem cell23_2100175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 5, 2].length) (baseStart_2100175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100175 prefixEnd_2100175 := by exact prefixLift 2100175
  have htrace : WordTrace (prefixWord ++ tailWord_2100175) baseStart_2100175 baseEnd_2100175 := by
    simpa [prefixWord, tailWord_2100175, baseEnd_2100175] using wordTrace_append hprefix tailTrace_2100175
  have hstable : (prefixWord ++ tailWord_2100175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100175).length < 2 ^ (prefixWord ++ tailWord_2100175).sum := by decide
  have hdescent : baseEnd_2100175 < baseStart_2100175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100185 : List Nat := [1, 2, 1, 2, 5, 2, 1, 3, 1, 5]
def baseStart_2100185 : Nat := 118140960795 + 2100185 * 2 ^ 59
def prefixEnd_2100185 : Nat := 4983230072969 + 3 ^ 40 * 2100185 * 2
def baseEnd_2100185 : Nat := 359468122787656916742977

theorem tailTrace_2100185 : CollatzResearch.WordTrace tailWord_2100185 prefixEnd_2100185 359468122787656916742977 := by
  unfold tailWord_2100185
  simp only [CollatzResearch.WordTrace]
  refine ⟨76600039896395902886894009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51066693264263935257929339 76600039896395902886894009)
  ·
    refine ⟨57450029922296927165170507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76600039896395902886894009 57450029922296927165170507)
    ·
      refine ⟨86175044883445390747755761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57450029922296927165170507 86175044883445390747755761)
      ·
        refine ⟨64631283662584043060816821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86175044883445390747755761 64631283662584043060816821)
        ·
          refine ⟨6059182843367254036951577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64631283662584043060816821 6059182843367254036951577)
          ·
            refine ⟨4544387132525440527713683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6059182843367254036951577 4544387132525440527713683)
            ·
              refine ⟨6816580698788160791570525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4544387132525440527713683 6816580698788160791570525)
              ·
                refine ⟨2556217762045560296838947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6816580698788160791570525 2556217762045560296838947)
                ·
                  refine ⟨3834326643068340445258421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2556217762045560296838947 3834326643068340445258421)
                  ·
                    refine ⟨359468122787656916742977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3834326643068340445258421 359468122787656916742977)
                    ·
                      rfl

theorem cell23_2100185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 5].length) (baseStart_2100185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100185 prefixEnd_2100185 := by exact prefixLift 2100185
  have htrace : WordTrace (prefixWord ++ tailWord_2100185) baseStart_2100185 baseEnd_2100185 := by
    simpa [prefixWord, tailWord_2100185, baseEnd_2100185] using wordTrace_append hprefix tailTrace_2100185
  have hstable : (prefixWord ++ tailWord_2100185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100185).length < 2 ^ (prefixWord ++ tailWord_2100185).sum := by decide
  have hdescent : baseEnd_2100185 < baseStart_2100185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100199 : List Nat := [1, 1, 5, 2, 2, 1, 2, 4, 1, 1, 3]
def baseStart_2100199 : Nat := 118140960795 + 2100199 * 2 ^ 59
def prefixEnd_2100199 : Nat := 4983230072969 + 3 ^ 40 * 2100199 * 2
def baseEnd_2100199 : Nat := 1078411557092133695453867

theorem tailTrace_2100199 : CollatzResearch.WordTrace tailWord_2100199 prefixEnd_2100199 1078411557092133695453867 := by
  unfold tailWord_2100199
  simp only [CollatzResearch.WordTrace]
  refine ⟨76600550518345183277903651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51067033678896788851935767 76600550518345183277903651)
  ·
    refine ⟨114900825777517774916855477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76600550518345183277903651 114900825777517774916855477)
    ·
      refine ⟨10771952416642291398455201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114900825777517774916855477 10771952416642291398455201)
      ·
        refine ⟨8078964312481718548841401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10771952416642291398455201 8078964312481718548841401)
        ·
          refine ⟨6059223234361288911631051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8078964312481718548841401 6059223234361288911631051)
          ·
            refine ⟨9088834851541933367446577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6059223234361288911631051 9088834851541933367446577)
            ·
              refine ⟨6816626138656450025584933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9088834851541933367446577 6816626138656450025584933)
              ·
                refine ⟨1278117400998084379797175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6816626138656450025584933 1278117400998084379797175)
                ·
                  refine ⟨1917176101497126569695763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1278117400998084379797175 1917176101497126569695763)
                  ·
                    refine ⟨2875764152245689854543645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1917176101497126569695763 2875764152245689854543645)
                    ·
                      refine ⟨1078411557092133695453867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2875764152245689854543645 1078411557092133695453867)
                      ·
                        rfl

theorem cell23_2100199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_2100199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100199 prefixEnd_2100199 := by exact prefixLift 2100199
  have htrace : WordTrace (prefixWord ++ tailWord_2100199) baseStart_2100199 baseEnd_2100199 := by
    simpa [prefixWord, tailWord_2100199, baseEnd_2100199] using wordTrace_append hprefix tailTrace_2100199
  have hstable : (prefixWord ++ tailWord_2100199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100199).length < 2 ^ (prefixWord ++ tailWord_2100199).sum := by decide
  have hdescent : baseEnd_2100199 < baseStart_2100199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100266 : List Nat := [3, 1, 4, 1, 3, 2, 2, 1, 2, 4]
def baseStart_2100266 : Nat := 118140960795 + 2100266 * 2 ^ 59
def prefixEnd_2100266 : Nat := 4983230072969 + 3 ^ 40 * 2100266 * 2
def baseEnd_2100266 : Nat := 359481986765328311105353

theorem tailTrace_2100266 : CollatzResearch.WordTrace tailWord_2100266 prefixEnd_2100266 359481986765328311105353 := by
  unfold tailWord_2100266
  simp only [CollatzResearch.WordTrace]
  refine ⟨19150748552275613430148163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51068662806068302480395101 19150748552275613430148163)
  ·
    refine ⟨28726122828413420145222245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19150748552275613430148163 28726122828413420145222245)
    ·
      refine ⟨5386148030327516277229171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28726122828413420145222245 5386148030327516277229171)
      ·
        refine ⟨8079222045491274415843757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5386148030327516277229171 8079222045491274415843757)
        ·
          refine ⟨3029708267059227905941409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8079222045491274415843757 3029708267059227905941409)
          ·
            refine ⟨2272281200294420929456057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3029708267059227905941409 2272281200294420929456057)
            ·
              refine ⟨1704210900220815697092043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2272281200294420929456057 1704210900220815697092043)
              ·
                refine ⟨2556316350331223545638065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1704210900220815697092043 2556316350331223545638065)
                ·
                  refine ⟨1917237262748417659228549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2556316350331223545638065 1917237262748417659228549)
                  ·
                    refine ⟨359481986765328311105353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1917237262748417659228549 359481986765328311105353)
                    ·
                      rfl

theorem cell23_2100266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_2100266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100266 prefixEnd_2100266 := by exact prefixLift 2100266
  have htrace : WordTrace (prefixWord ++ tailWord_2100266) baseStart_2100266 baseEnd_2100266 := by
    simpa [prefixWord, tailWord_2100266, baseEnd_2100266] using wordTrace_append hprefix tailTrace_2100266
  have hstable : (prefixWord ++ tailWord_2100266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100266).length < 2 ^ (prefixWord ++ tailWord_2100266).sum := by decide
  have hdescent : baseEnd_2100266 < baseStart_2100266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100272 : List Nat := [2, 1, 1, 1, 2, 4, 3, 3, 2, 1, 3]
def baseStart_2100272 : Nat := 118140960795 + 2100272 * 2 ^ 59
def prefixEnd_2100272 : Nat := 4983230072969 + 3 ^ 40 * 2100272 * 2
def baseEnd_2100272 : Nat := 1078449041179911909841031

theorem tailTrace_2100272 : CollatzResearch.WordTrace tailWord_2100272 prefixEnd_2100272 1078449041179911909841031 := by
  unfold tailWord_2100272
  simp only [CollatzResearch.WordTrace]
  refine ⟨38301606523540358372655535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51068808698053811163540713 38301606523540358372655535)
  ·
    refine ⟨57452409785310537558983303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38301606523540358372655535 57452409785310537558983303)
    ·
      refine ⟨86178614677965806338474955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57452409785310537558983303 86178614677965806338474955)
      ·
        refine ⟨129267922016948709507712433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86178614677965806338474955 129267922016948709507712433)
        ·
          refine ⟨96950941512711532130784325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129267922016948709507712433 96950941512711532130784325)
          ·
            refine ⟨18178301533633412274522061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96950941512711532130784325 18178301533633412274522061)
            ·
              refine ⟨6816863075112529602945773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18178301533633412274522061 6816863075112529602945773)
              ·
                refine ⟨2556323653167198601104665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6816863075112529602945773 2556323653167198601104665)
                ·
                  refine ⟨1917242739875398950828499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2556323653167198601104665 1917242739875398950828499)
                  ·
                    refine ⟨2875864109813098426242749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1917242739875398950828499 2875864109813098426242749)
                    ·
                      refine ⟨1078449041179911909841031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2875864109813098426242749 1078449041179911909841031)
                      ·
                        rfl

theorem cell23_2100272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 2, 1, 3].length) (baseStart_2100272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100272 prefixEnd_2100272 := by exact prefixLift 2100272
  have htrace : WordTrace (prefixWord ++ tailWord_2100272) baseStart_2100272 baseEnd_2100272 := by
    simpa [prefixWord, tailWord_2100272, baseEnd_2100272] using wordTrace_append hprefix tailTrace_2100272
  have hstable : (prefixWord ++ tailWord_2100272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100272).length < 2 ^ (prefixWord ++ tailWord_2100272).sum := by decide
  have hdescent : baseEnd_2100272 < baseStart_2100272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100276 : List Nat := [2, 5, 1, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_2100276 : Nat := 118140960795 + 2100276 * 2 ^ 59
def prefixEnd_2100276 : Nat := 4983230072969 + 3 ^ 40 * 2100276 * 2
def baseEnd_2100276 : Nat := 1078451095102529894191013

theorem tailTrace_2100276 : CollatzResearch.WordTrace tailWord_2100276 prefixEnd_2100276 1078451095102529894191013 := by
  unfold tailWord_2100276
  simp only [CollatzResearch.WordTrace]
  refine ⟨38301679469533112714228341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51068905959377483618971121 38301679469533112714228341)
  ·
    refine ⟨3590782450268729316958907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38301679469533112714228341 3590782450268729316958907)
    ·
      refine ⟨5386173675403093975438361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3590782450268729316958907 5386173675403093975438361)
      ·
        refine ⟨4039630256552320481578771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5386173675403093975438361 4039630256552320481578771)
        ·
          refine ⟨6059445384828480722368157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4039630256552320481578771 6059445384828480722368157)
          ·
            refine ⟨2272292019310680270888059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6059445384828480722368157 2272292019310680270888059)
            ·
              refine ⟨3408438028966020406332089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2272292019310680270888059 3408438028966020406332089)
              ·
                refine ⟨2556328521724515304749067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3408438028966020406332089 2556328521724515304749067)
                ·
                  refine ⟨3834492782586772957123601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2556328521724515304749067 3834492782586772957123601)
                  ·
                    refine ⟨2875869586940079717842701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3834492782586772957123601 2875869586940079717842701)
                    ·
                      refine ⟨1078451095102529894191013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2875869586940079717842701 1078451095102529894191013)
                      ·
                        rfl

theorem cell23_2100276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_2100276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100276 prefixEnd_2100276 := by exact prefixLift 2100276
  have htrace : WordTrace (prefixWord ++ tailWord_2100276) baseStart_2100276 baseEnd_2100276 := by
    simpa [prefixWord, tailWord_2100276, baseEnd_2100276] using wordTrace_append hprefix tailTrace_2100276
  have hstable : (prefixWord ++ tailWord_2100276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100276).length < 2 ^ (prefixWord ++ tailWord_2100276).sum := by decide
  have hdescent : baseEnd_2100276 < baseStart_2100276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100322 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 2, 6]
def baseStart_2100322 : Nat := 118140960795 + 2100322 * 2 ^ 59
def prefixEnd_2100322 : Nat := 4983230072969 + 3 ^ 40 * 2100322 * 2
def baseEnd_2100322 : Nat := 359491571737545571405267

theorem tailTrace_2100322 : CollatzResearch.WordTrace tailWord_2100322 prefixEnd_2100322 359491571737545571405267 := by
  unfold tailWord_2100322
  simp only [CollatzResearch.WordTrace]
  refine ⟨19151259174224893821157805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51070024464599716856420813 19151259174224893821157805)
  ·
    refine ⟨7181722190334335182934177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19151259174224893821157805 7181722190334335182934177)
    ·
      refine ⟨5386291642750751387200633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7181722190334335182934177 5386291642750751387200633)
      ·
        refine ⟨4039718732063063540400475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5386291642750751387200633 4039718732063063540400475)
        ·
          refine ⟨6059578098094595310600713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4039718732063063540400475 6059578098094595310600713)
          ·
            refine ⟨4544683573570946482950535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6059578098094595310600713 4544683573570946482950535)
            ·
              refine ⟨6817025360356419724425803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4544683573570946482950535 6817025360356419724425803)
              ·
                refine ⟨10225538040534629586638705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6817025360356419724425803 10225538040534629586638705)
                ·
                  refine ⟨7669153530400972189979029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10225538040534629586638705 7669153530400972189979029)
                  ·
                    refine ⟨359491571737545571405267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7669153530400972189979029 359491571737545571405267)
                    ·
                      rfl

theorem cell23_2100322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_2100322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100322 prefixEnd_2100322 := by exact prefixLift 2100322
  have htrace : WordTrace (prefixWord ++ tailWord_2100322) baseStart_2100322 baseEnd_2100322 := by
    simpa [prefixWord, tailWord_2100322, baseEnd_2100322] using wordTrace_append hprefix tailTrace_2100322
  have hstable : (prefixWord ++ tailWord_2100322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100322).length < 2 ^ (prefixWord ++ tailWord_2100322).sum := by decide
  have hdescent : baseEnd_2100322 < baseStart_2100322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100325 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 2, 2, 4]
def baseStart_2100325 : Nat := 118140960795 + 2100325 * 2 ^ 59
def prefixEnd_2100325 : Nat := 4983230072969 + 3 ^ 40 * 2100325 * 2
def baseEnd_2100325 : Nat := 1078476255654600202478287

theorem tailTrace_2100325 : CollatzResearch.WordTrace tailWord_2100325 prefixEnd_2100325 1078476255654600202478287 := by
  unfold tailWord_2100325
  simp only [CollatzResearch.WordTrace]
  refine ⟨76605146115888706796990429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51070097410592471197993619 76605146115888706796990429)
  ·
    refine ⟨28726929793458265048871411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76605146115888706796990429 28726929793458265048871411)
    ·
      refine ⟨43090394690187397573307117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28726929793458265048871411 43090394690187397573307117)
      ·
        refine ⟨16158898008820274089990169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43090394690187397573307117 16158898008820274089990169)
        ·
          refine ⟨12119173506615205567492627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16158898008820274089990169 12119173506615205567492627)
          ·
            refine ⟨18178760259922808351238941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12119173506615205567492627 18178760259922808351238941)
            ·
              refine ⟨6817035097471053131714603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18178760259922808351238941 6817035097471053131714603)
              ·
                refine ⟨10225552646206579697571905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6817035097471053131714603 10225552646206579697571905)
                ·
                  refine ⟨7669164484654934773178929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10225552646206579697571905 7669164484654934773178929)
                  ·
                    refine ⟨5751873363491201079884197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7669164484654934773178929 5751873363491201079884197)
                    ·
                      refine ⟨1078476255654600202478287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5751873363491201079884197 1078476255654600202478287)
                      ·
                        rfl

theorem cell23_2100325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_2100325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100325 prefixEnd_2100325 := by exact prefixLift 2100325
  have htrace : WordTrace (prefixWord ++ tailWord_2100325) baseStart_2100325 baseEnd_2100325 := by
    simpa [prefixWord, tailWord_2100325, baseEnd_2100325] using wordTrace_append hprefix tailTrace_2100325
  have hstable : (prefixWord ++ tailWord_2100325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100325).length < 2 ^ (prefixWord ++ tailWord_2100325).sum := by decide
  have hdescent : baseEnd_2100325 < baseStart_2100325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100329 : List Nat := [1, 2, 1, 1, 1, 6, 2, 3, 2, 2, 2]
def baseStart_2100329 : Nat := 118140960795 + 2100329 * 2 ^ 59
def prefixEnd_2100329 : Nat := 4983230072969 + 3 ^ 40 * 2100329 * 2
def baseEnd_2100329 : Nat := 1078478309577218186828269

theorem tailTrace_2100329 : CollatzResearch.WordTrace tailWord_2100329 prefixEnd_2100329 1078478309577218186828269 := by
  unfold tailWord_2100329
  simp only [CollatzResearch.WordTrace]
  refine ⟨76605292007874215480136041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51070194671916143653424027 76605292007874215480136041)
  ·
    refine ⟨57453969005905661610102031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76605292007874215480136041 57453969005905661610102031)
    ·
      refine ⟨86180953508858492415153047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57453969005905661610102031 86180953508858492415153047)
      ·
        refine ⟨129271430263287738622729571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86180953508858492415153047 129271430263287738622729571)
        ·
          refine ⟨193907145394931607934094357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129271430263287738622729571 193907145394931607934094357)
          ·
            refine ⟨9089397440387419121910673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 193907145394931607934094357 9089397440387419121910673)
            ·
              refine ⟨6817048080290564341433005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9089397440387419121910673 6817048080290564341433005)
              ·
                refine ⟨2556393030108961628037377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6817048080290564341433005 2556393030108961628037377)
                ·
                  refine ⟨1917294772581721221028033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2556393030108961628037377 1917294772581721221028033)
                  ·
                    refine ⟨1437971079436290915771025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1917294772581721221028033 1437971079436290915771025)
                    ·
                      refine ⟨1078478309577218186828269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1437971079436290915771025 1078478309577218186828269)
                      ·
                        rfl

theorem cell23_2100329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 2, 2].length) (baseStart_2100329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100329 prefixEnd_2100329 := by exact prefixLift 2100329
  have htrace : WordTrace (prefixWord ++ tailWord_2100329) baseStart_2100329 baseEnd_2100329 := by
    simpa [prefixWord, tailWord_2100329, baseEnd_2100329] using wordTrace_append hprefix tailTrace_2100329
  have hstable : (prefixWord ++ tailWord_2100329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100329).length < 2 ^ (prefixWord ++ tailWord_2100329).sum := by decide
  have hdescent : baseEnd_2100329 < baseStart_2100329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100350 : List Nat := [4, 2, 4, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_2100350 : Nat := 118140960795 + 2100350 * 2 ^ 59
def prefixEnd_2100350 : Nat := 4983230072969 + 3 ^ 40 * 2100350 * 2
def baseEnd_2100350 : Nat := 1078489092670962604665673

theorem tailTrace_2100350 : CollatzResearch.WordTrace tailWord_2100350 prefixEnd_2100350 1078489092670962604665673 := by
  unfold tailWord_2100350
  simp only [CollatzResearch.WordTrace]
  refine ⟨9575757242599767008331313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51070705293865424044433669 9575757242599767008331313)
  ·
    refine ⟨7181817931949825256248485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9575757242599767008331313 7181817931949825256248485)
    ·
      refine ⟨1346590862240592235546591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7181817931949825256248485 1346590862240592235546591)
      ·
        refine ⟨2019886293360888353319887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1346590862240592235546591 2019886293360888353319887)
        ·
          refine ⟨3029829440041332529979831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2019886293360888353319887 3029829440041332529979831)
          ·
            refine ⟨4544744160061998794969747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3029829440041332529979831 4544744160061998794969747)
            ·
              refine ⟨6817116240092998192454621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4544744160061998794969747 6817116240092998192454621)
              ·
                refine ⟨2556418590034874322170483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6817116240092998192454621 2556418590034874322170483)
                ·
                  refine ⟨3834627885052311483255725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2556418590034874322170483 3834627885052311483255725)
                  ·
                    refine ⟨1437985456894616806220897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3834627885052311483255725 1437985456894616806220897)
                    ·
                      refine ⟨1078489092670962604665673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1437985456894616806220897 1078489092670962604665673)
                      ·
                        rfl

theorem cell23_2100350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_2100350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100350 prefixEnd_2100350 := by exact prefixLift 2100350
  have htrace : WordTrace (prefixWord ++ tailWord_2100350) baseStart_2100350 baseEnd_2100350 := by
    simpa [prefixWord, tailWord_2100350, baseEnd_2100350] using wordTrace_append hprefix tailTrace_2100350
  have hstable : (prefixWord ++ tailWord_2100350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100350).length < 2 ^ (prefixWord ++ tailWord_2100350).sum := by decide
  have hdescent : baseEnd_2100350 < baseStart_2100350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100382 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_2100382 : Nat := 118140960795 + 2100382 * 2 ^ 59
def prefixEnd_2100382 : Nat := 4983230072969 + 3 ^ 40 * 2100382 * 2
def baseEnd_2100382 : Nat := 359501841350635493155175

theorem tailTrace_2100382 : CollatzResearch.WordTrace tailWord_2100382 prefixEnd_2100382 359501841350635493155175 := by
  unfold tailWord_2100382
  simp only [CollatzResearch.WordTrace]
  refine ⟨9575903134585275691476925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51071483384454803687876933 9575903134585275691476925)
  ·
    refine ⟨3590963675469478384303847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9575903134585275691476925 3590963675469478384303847)
    ·
      refine ⟨5386445513204217576455771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3590963675469478384303847 5386445513204217576455771)
      ·
        refine ⟨8079668269806326364683657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5386445513204217576455771 8079668269806326364683657)
        ·
          refine ⟨6059751202354744773512743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8079668269806326364683657 6059751202354744773512743)
          ·
            refine ⟨9089626803532117160269115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6059751202354744773512743 9089626803532117160269115)
            ·
              refine ⟨13634440205298175740403673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9089626803532117160269115 13634440205298175740403673)
              ·
                refine ⟨10225830153973631805302755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13634440205298175740403673 10225830153973631805302755)
                ·
                  refine ⟨15338745230960447707954133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10225830153973631805302755 15338745230960447707954133)
                  ·
                    refine ⟨359501841350635493155175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15338745230960447707954133 359501841350635493155175)
                    ·
                      rfl

theorem cell23_2100382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_2100382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100382 prefixEnd_2100382 := by exact prefixLift 2100382
  have htrace : WordTrace (prefixWord ++ tailWord_2100382) baseStart_2100382 baseEnd_2100382 := by
    simpa [prefixWord, tailWord_2100382, baseEnd_2100382] using wordTrace_append hprefix tailTrace_2100382
  have hstable : (prefixWord ++ tailWord_2100382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100382).length < 2 ^ (prefixWord ++ tailWord_2100382).sum := by decide
  have hdescent : baseEnd_2100382 < baseStart_2100382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100385 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 3, 3, 4]
def baseStart_2100385 : Nat := 118140960795 + 2100385 * 2 ^ 59
def prefixEnd_2100385 : Nat := 4983230072969 + 3 ^ 40 * 2100385 * 2
def baseEnd_2100385 : Nat := 1078507064493869967728011

theorem tailTrace_2100385 : CollatzResearch.WordTrace tailWord_2100385 prefixEnd_2100385 1078507064493869967728011 := by
  unfold tailWord_2100385
  simp only [CollatzResearch.WordTrace]
  refine ⟨76607334495671337044174609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51071556330447558029449739 76607334495671337044174609)
  ·
    refine ⟨57455500871753502783130957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76607334495671337044174609 57455500871753502783130957)
    ·
      refine ⟨21545812826907563543674109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57455500871753502783130957 21545812826907563543674109)
      ·
        refine ⟨8079679810090336328877791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21545812826907563543674109 8079679810090336328877791)
        ·
          refine ⟨12119519715135504493316687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8079679810090336328877791 12119519715135504493316687)
          ·
            refine ⟨18179279572703256739975031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12119519715135504493316687 18179279572703256739975031)
            ·
              refine ⟨27268919359054885109962547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18179279572703256739975031 27268919359054885109962547)
              ·
                refine ⟨40903379038582327664943821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27268919359054885109962547 40903379038582327664943821)
                ·
                  refine ⟨15338767139468372874353933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40903379038582327664943821 15338767139468372874353933)
                  ·
                    refine ⟨5752037677300639827882725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15338767139468372874353933 5752037677300639827882725)
                    ·
                      refine ⟨1078507064493869967728011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5752037677300639827882725 1078507064493869967728011)
                      ·
                        rfl

theorem cell23_2100385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_2100385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100385 prefixEnd_2100385 := by exact prefixLift 2100385
  have htrace : WordTrace (prefixWord ++ tailWord_2100385) baseStart_2100385 baseEnd_2100385 := by
    simpa [prefixWord, tailWord_2100385, baseEnd_2100385] using wordTrace_append hprefix tailTrace_2100385
  have hstable : (prefixWord ++ tailWord_2100385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100385).length < 2 ^ (prefixWord ++ tailWord_2100385).sum := by decide
  have hdescent : baseEnd_2100385 < baseStart_2100385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100479 : List Nat := [1, 1, 2, 2, 1, 5, 2, 2, 2, 3, 2]
def baseStart_2100479 : Nat := 118140960795 + 2100479 * 2 ^ 59
def prefixEnd_2100479 : Nat := 4983230072969 + 3 ^ 40 * 2100479 * 2
def baseEnd_2100479 : Nat := 1078555331675392599952579

theorem tailTrace_2100479 : CollatzResearch.WordTrace tailWord_2100479 prefixEnd_2100479 1078555331675392599952579 := by
  unfold tailWord_2100479
  simp only [CollatzResearch.WordTrace]
  refine ⟨76610762957330791098096491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51073841971553860732064327 76610762957330791098096491)
  ·
    refine ⟨114916144435996186647144737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76610762957330791098096491 114916144435996186647144737)
    ·
      refine ⟨86187108326997139985358553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114916144435996186647144737 86187108326997139985358553)
      ·
        refine ⟨64640331245247854989018915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86187108326997139985358553 64640331245247854989018915)
        ·
          refine ⟨96960496867871782483528373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64640331245247854989018915 96960496867871782483528373)
          ·
            refine ⟨9090046581362979607830785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96960496867871782483528373 9090046581362979607830785)
            ·
              refine ⟨6817534936022234705873089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9090046581362979607830785 6817534936022234705873089)
              ·
                refine ⟨5113151202016676029404817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6817534936022234705873089 5113151202016676029404817)
                ·
                  refine ⟨3834863401512507022053613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5113151202016676029404817 3834863401512507022053613)
                  ·
                    refine ⟨1438073775567190133270105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3834863401512507022053613 1438073775567190133270105)
                    ·
                      refine ⟨1078555331675392599952579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1438073775567190133270105 1078555331675392599952579)
                      ·
                        rfl

theorem cell23_2100479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 3, 2].length) (baseStart_2100479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100479 prefixEnd_2100479 := by exact prefixLift 2100479
  have htrace : WordTrace (prefixWord ++ tailWord_2100479) baseStart_2100479 baseEnd_2100479 := by
    simpa [prefixWord, tailWord_2100479, baseEnd_2100479] using wordTrace_append hprefix tailTrace_2100479
  have hstable : (prefixWord ++ tailWord_2100479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100479).length < 2 ^ (prefixWord ++ tailWord_2100479).sum := by decide
  have hdescent : baseEnd_2100479 < baseStart_2100479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100485 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 3, 6]
def baseStart_2100485 : Nat := 118140960795 + 2100485 * 2 ^ 59
def prefixEnd_2100485 : Nat := 4983230072969 + 3 ^ 40 * 2100485 * 2
def baseEnd_2100485 : Nat := 359519470853106525492517

theorem tailTrace_2100485 : CollatzResearch.WordTrace tailWord_2100485 prefixEnd_2100485 359519470853106525492517 := by
  unfold tailWord_2100485
  simp only [CollatzResearch.WordTrace]
  refine ⟨76610981795309054122814909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51073987863539369415209939 76610981795309054122814909)
  ·
    refine ⟨28729118173240895296055591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76610981795309054122814909 28729118173240895296055591)
    ·
      refine ⟨43093677259861342944083387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28729118173240895296055591 43093677259861342944083387)
      ·
        refine ⟨64640515889792014416125081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43093677259861342944083387 64640515889792014416125081)
        ·
          refine ⟨48480386917344010812093811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64640515889792014416125081 48480386917344010812093811)
          ·
            refine ⟨72720580376016016218140717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48480386917344010812093811 72720580376016016218140717)
            ·
              refine ⟨27270217641006006081802769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72720580376016016218140717 27270217641006006081802769)
              ·
                refine ⟨20452663230754504561352077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27270217641006006081802769 20452663230754504561352077)
                ·
                  refine ⟨7669748711532939210507029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20452663230754504561352077 7669748711532939210507029)
                  ·
                    refine ⟨359519470853106525492517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7669748711532939210507029 359519470853106525492517)
                    ·
                      rfl

theorem cell23_2100485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_2100485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100485 prefixEnd_2100485 := by exact prefixLift 2100485
  have htrace : WordTrace (prefixWord ++ tailWord_2100485) baseStart_2100485 baseEnd_2100485 := by
    simpa [prefixWord, tailWord_2100485, baseEnd_2100485] using wordTrace_append hprefix tailTrace_2100485
  have hstable : (prefixWord ++ tailWord_2100485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100485).length < 2 ^ (prefixWord ++ tailWord_2100485).sum := by decide
  have hdescent : baseEnd_2100485 < baseStart_2100485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100492 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 3, 1, 4]
def baseStart_2100492 : Nat := 118140960795 + 2100492 * 2 ^ 59
def prefixEnd_2100492 : Nat := 4983230072969 + 3 ^ 40 * 2100492 * 2
def baseEnd_2100492 : Nat := 1078562006923901049090019

theorem tailTrace_2100492 : CollatzResearch.WordTrace tailWord_2100492 prefixEnd_2100492 1078562006923901049090019 := by
  unfold tailWord_2100492
  simp only [CollatzResearch.WordTrace]
  refine ⟨38305618553141847159159865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51074158070855796212213153 38305618553141847159159865)
  ·
    refine ⟨28729213914856385369369899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38305618553141847159159865 28729213914856385369369899)
    ·
      refine ⟨43093820872284578054054849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28729213914856385369369899 43093820872284578054054849)
      ·
        refine ⟨32320365654213433540541137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43093820872284578054054849 32320365654213433540541137)
        ·
          refine ⟨24240274240660075155405853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32320365654213433540541137 24240274240660075155405853)
          ·
            refine ⟨9090102840247528183277195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24240274240660075155405853 9090102840247528183277195)
            ·
              refine ⟨13635154260371292274915793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9090102840247528183277195 13635154260371292274915793)
              ·
                refine ⟨10226365695278469206186845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13635154260371292274915793 10226365695278469206186845)
                ·
                  refine ⟨3834887135729425952320067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10226365695278469206186845 3834887135729425952320067)
                  ·
                    refine ⟨5752330703594138928480101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3834887135729425952320067 5752330703594138928480101)
                    ·
                      refine ⟨1078562006923901049090019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5752330703594138928480101 1078562006923901049090019)
                      ·
                        rfl

theorem cell23_2100492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_2100492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100492 prefixEnd_2100492 := by exact prefixLift 2100492
  have htrace : WordTrace (prefixWord ++ tailWord_2100492) baseStart_2100492 baseEnd_2100492 := by
    simpa [prefixWord, tailWord_2100492, baseEnd_2100492] using wordTrace_append hprefix tailTrace_2100492
  have hstable : (prefixWord ++ tailWord_2100492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100492).length < 2 ^ (prefixWord ++ tailWord_2100492).sum := by decide
  have hdescent : baseEnd_2100492 < baseStart_2100492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100509 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_2100509 : Nat := 118140960795 + 2100509 * 2 ^ 59
def prefixEnd_2100509 : Nat := 4983230072969 + 3 ^ 40 * 2100509 * 2
def baseEnd_2100509 : Nat := 1078570736095027482577441

theorem tailTrace_2100509 : CollatzResearch.WordTrace tailWord_2100509 prefixEnd_2100509 1078570736095027482577441 := by
  unfold tailWord_2100509
  simp only [CollatzResearch.WordTrace]
  refine ⟨76611857147222106221688581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51074571431481404147792387 76611857147222106221688581)
  ·
    refine ⟨14364723215104144916566609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76611857147222106221688581 14364723215104144916566609)
    ·
      refine ⟨10773542411328108687424957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14364723215104144916566609 10773542411328108687424957)
      ·
        refine ⟨4040078404248040757784359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10773542411328108687424957 4040078404248040757784359)
        ·
          refine ⟨6060117606372061136676539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4040078404248040757784359 6060117606372061136676539)
          ·
            refine ⟨9090176409558091705014809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6060117606372061136676539 9090176409558091705014809)
            ·
              refine ⟨6817632307168568778761107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9090176409558091705014809 6817632307168568778761107)
              ·
                refine ⟨10226448460752853168141661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6817632307168568778761107 10226448460752853168141661)
                ·
                  refine ⟨3834918172782319938053123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10226448460752853168141661 3834918172782319938053123)
                  ·
                    refine ⟨5752377259173479907079685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3834918172782319938053123 5752377259173479907079685)
                    ·
                      refine ⟨1078570736095027482577441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5752377259173479907079685 1078570736095027482577441)
                      ·
                        rfl

theorem cell23_2100509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_2100509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100509 prefixEnd_2100509 := by exact prefixLift 2100509
  have htrace : WordTrace (prefixWord ++ tailWord_2100509) baseStart_2100509 baseEnd_2100509 := by
    simpa [prefixWord, tailWord_2100509, baseEnd_2100509] using wordTrace_append hprefix tailTrace_2100509
  have hstable : (prefixWord ++ tailWord_2100509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100509).length < 2 ^ (prefixWord ++ tailWord_2100509).sum := by decide
  have hdescent : baseEnd_2100509 < baseStart_2100509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100532 : List Nat := [2, 5, 1, 1, 1, 1, 12]
def baseStart_2100532 : Nat := 118140960795 + 2100532 * 2 ^ 59
def prefixEnd_2100532 : Nat := 4983230072969 + 3 ^ 40 * 2100532 * 2
def baseEnd_2100532 : Nat := 13315833903087418427035

theorem tailTrace_2100532 : CollatzResearch.WordTrace tailWord_2100532 prefixEnd_2100532 13315833903087418427035 := by
  unfold tailWord_2100532
  simp only [CollatzResearch.WordTrace]
  refine ⟨38306348013069390574887925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51075130684092520766517233 38306348013069390574887925)
  ·
    refine ⟨3591220126225255366395743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38306348013069390574887925 3591220126225255366395743)
    ·
      refine ⟨5386830189337883049593615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3591220126225255366395743 5386830189337883049593615)
      ·
        refine ⟨8080245284006824574390423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5386830189337883049593615 8080245284006824574390423)
        ·
          refine ⟨12120367926010236861585635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8080245284006824574390423 12120367926010236861585635)
          ·
            refine ⟨18180551889015355292378453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12120367926010236861585635 18180551889015355292378453)
            ·
              refine ⟨13315833903087418427035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 18180551889015355292378453 13315833903087418427035)
              ·
                rfl

theorem cell23_2100532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 12].length) (baseStart_2100532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100532 prefixEnd_2100532 := by exact prefixLift 2100532
  have htrace : WordTrace (prefixWord ++ tailWord_2100532) baseStart_2100532 baseEnd_2100532 := by
    simpa [prefixWord, tailWord_2100532, baseEnd_2100532] using wordTrace_append hprefix tailTrace_2100532
  have hstable : (prefixWord ++ tailWord_2100532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100532).length < 2 ^ (prefixWord ++ tailWord_2100532).sum := by decide
  have hdescent : baseEnd_2100532 < baseStart_2100532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100535 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 6]
def baseStart_2100535 : Nat := 118140960795 + 2100535 * 2 ^ 59
def prefixEnd_2100535 : Nat := 4983230072969 + 3 ^ 40 * 2100535 * 2
def baseEnd_2100535 : Nat := 1078584086592044380852321

theorem tailTrace_2100535 : CollatzResearch.WordTrace tailWord_2100535 prefixEnd_2100535 1078584086592044380852321 := by
  unfold tailWord_2100535
  simp only [CollatzResearch.WordTrace]
  refine ⟨76612805445127912662135059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51075203630085275108090039 76612805445127912662135059)
  ·
    refine ⟨114919208167691868993202589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76612805445127912662135059 114919208167691868993202589)
    ·
      refine ⟨43094703062884450872450971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114919208167691868993202589 43094703062884450872450971)
      ·
        refine ⟨64642054594326676308676457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43094703062884450872450971 64642054594326676308676457)
        ·
          refine ⟨48481540945745007231507343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64642054594326676308676457 48481540945745007231507343)
          ·
            refine ⟨72722311418617510847261015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48481540945745007231507343 72722311418617510847261015)
            ·
              refine ⟨109083467127926266270891523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72722311418617510847261015 109083467127926266270891523)
              ·
                refine ⟨163625200691889399406337285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109083467127926266270891523 163625200691889399406337285)
                ·
                  refine ⟨30679725129729262388688241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163625200691889399406337285 30679725129729262388688241)
                  ·
                    refine ⟨23009793847296946791516181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30679725129729262388688241 23009793847296946791516181)
                    ·
                      refine ⟨1078584086592044380852321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23009793847296946791516181 1078584086592044380852321)
                      ·
                        rfl

theorem cell23_2100535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_2100535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100535 prefixEnd_2100535 := by exact prefixLift 2100535
  have htrace : WordTrace (prefixWord ++ tailWord_2100535) baseStart_2100535 baseEnd_2100535 := by
    simpa [prefixWord, tailWord_2100535, baseEnd_2100535] using wordTrace_append hprefix tailTrace_2100535
  have hstable : (prefixWord ++ tailWord_2100535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100535).length < 2 ^ (prefixWord ++ tailWord_2100535).sum := by decide
  have hdescent : baseEnd_2100535 < baseStart_2100535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100543 : List Nat := [1, 1, 2, 2, 4, 2, 2, 4, 1, 2, 2]
def baseStart_2100543 : Nat := 118140960795 + 2100543 * 2 ^ 59
def prefixEnd_2100543 : Nat := 4983230072969 + 3 ^ 40 * 2100543 * 2
def baseEnd_2100543 : Nat := 1078588194437280349552285

theorem tailTrace_2100543 : CollatzResearch.WordTrace tailWord_2100543 prefixEnd_2100543 1078588194437280349552285 := by
  unfold tailWord_2100543
  simp only [CollatzResearch.WordTrace]
  refine ⟨76613097229098930028426283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51075398152732620018950855 76613097229098930028426283)
  ·
    refine ⟨114919645843648395042639425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76613097229098930028426283 114919645843648395042639425)
    ·
      refine ⟨86189734382736296281979569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114919645843648395042639425 86189734382736296281979569)
      ·
        refine ⟨64642300787052222211484677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86189734382736296281979569 64642300787052222211484677)
        ·
          refine ⟨12120431397572291664653377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64642300787052222211484677 12120431397572291664653377)
          ·
            refine ⟨9090323548179218748490033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12120431397572291664653377 9090323548179218748490033)
            ·
              refine ⟨6817742661134414061367525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9090323548179218748490033 6817742661134414061367525)
              ·
                refine ⟨1278326748962702636506411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6817742661134414061367525 1278326748962702636506411)
                ·
                  refine ⟨1917490123444053954759617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1278326748962702636506411 1917490123444053954759617)
                  ·
                    refine ⟨1438117592583040466069713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1917490123444053954759617 1438117592583040466069713)
                    ·
                      refine ⟨1078588194437280349552285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1438117592583040466069713 1078588194437280349552285)
                      ·
                        rfl

theorem cell23_2100543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 1, 2, 2].length) (baseStart_2100543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100543 prefixEnd_2100543 := by exact prefixLift 2100543
  have htrace : WordTrace (prefixWord ++ tailWord_2100543) baseStart_2100543 baseEnd_2100543 := by
    simpa [prefixWord, tailWord_2100543, baseEnd_2100543] using wordTrace_append hprefix tailTrace_2100543
  have hstable : (prefixWord ++ tailWord_2100543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100543).length < 2 ^ (prefixWord ++ tailWord_2100543).sum := by decide
  have hdescent : baseEnd_2100543 < baseStart_2100543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100569 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 3, 3, 2]
def baseStart_2100569 : Nat := 118140960795 + 2100569 * 2 ^ 59
def prefixEnd_2100569 : Nat := 4983230072969 + 3 ^ 40 * 2100569 * 2
def baseEnd_2100569 : Nat := 1078601544934297247827165

theorem tailTrace_2100569 : CollatzResearch.WordTrace tailWord_2100569 prefixEnd_2100569 1078601544934297247827165 := by
  unfold tailWord_2100569
  simp only [CollatzResearch.WordTrace]
  refine ⟨76614045527004736468872761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51076030351336490979248507 76614045527004736468872761)
  ·
    refine ⟨57460534145253552351654571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76614045527004736468872761 57460534145253552351654571)
    ·
      refine ⟨86190801217880328527481857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57460534145253552351654571 86190801217880328527481857)
      ·
        refine ⟨64643100913410246395611393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86190801217880328527481857 64643100913410246395611393)
        ·
          refine ⟨48482325685057684796708545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64643100913410246395611393 48482325685057684796708545)
          ·
            refine ⟨36361744263793263597531409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48482325685057684796708545 36361744263793263597531409)
            ·
              refine ⟨27271308197844947698148557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36361744263793263597531409 27271308197844947698148557)
              ·
                refine ⟨10226740574191855386805709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27271308197844947698148557 10226740574191855386805709)
                ·
                  refine ⟨3835027715321945770052141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10226740574191855386805709 3835027715321945770052141)
                  ·
                    refine ⟨1438135393245729663769553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3835027715321945770052141 1438135393245729663769553)
                    ·
                      refine ⟨1078601544934297247827165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1438135393245729663769553 1078601544934297247827165)
                      ·
                        rfl

theorem cell23_2100569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 3, 2].length) (baseStart_2100569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100569 prefixEnd_2100569 := by exact prefixLift 2100569
  have htrace : WordTrace (prefixWord ++ tailWord_2100569) baseStart_2100569 baseEnd_2100569 := by
    simpa [prefixWord, tailWord_2100569, baseEnd_2100569] using wordTrace_append hprefix tailTrace_2100569
  have hstable : (prefixWord ++ tailWord_2100569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100569).length < 2 ^ (prefixWord ++ tailWord_2100569).sum := by decide
  have hdescent : baseEnd_2100569 < baseStart_2100569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100602 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3]
def baseStart_2100602 : Nat := 118140960795 + 2100602 * 2 ^ 59
def prefixEnd_2100602 : Nat := 4983230072969 + 3 ^ 40 * 2100602 * 2
def baseEnd_2100602 : Nat := 1078618489795895618714513

theorem tailTrace_2100602 : CollatzResearch.WordTrace tailWord_2100602 prefixEnd_2100602 1078618489795895618714513 := by
  unfold tailWord_2100602
  simp only [CollatzResearch.WordTrace]
  refine ⟨19153812283971295776206015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51076832757256788736549373 19153812283971295776206015)
  ·
    refine ⟨28730718425956943664309023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19153812283971295776206015 28730718425956943664309023)
    ·
      refine ⟨43096077638935415496463535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28730718425956943664309023 43096077638935415496463535)
      ·
        refine ⟨64644116458403123244695303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43096077638935415496463535 64644116458403123244695303)
        ·
          refine ⟨96966174687604684867042955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64644116458403123244695303 96966174687604684867042955)
          ·
            refine ⟨145449262031407027300564433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96966174687604684867042955 145449262031407027300564433)
            ·
              refine ⟨109086946523555270475423325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145449262031407027300564433 109086946523555270475423325)
              ·
                refine ⟨40907604946333226428283747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109086946523555270475423325 40907604946333226428283747)
                ·
                  refine ⟨61361407419499839642425621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40907604946333226428283747 61361407419499839642425621)
                  ·
                    refine ⟨2876315972789054983238701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61361407419499839642425621 2876315972789054983238701)
                    ·
                      refine ⟨1078618489795895618714513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2876315972789054983238701 1078618489795895618714513)
                      ·
                        rfl

theorem cell23_2100602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3].length) (baseStart_2100602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100602 prefixEnd_2100602 := by exact prefixLift 2100602
  have htrace : WordTrace (prefixWord ++ tailWord_2100602) baseStart_2100602 baseEnd_2100602 := by
    simpa [prefixWord, tailWord_2100602, baseEnd_2100602] using wordTrace_append hprefix tailTrace_2100602
  have hstable : (prefixWord ++ tailWord_2100602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100602).length < 2 ^ (prefixWord ++ tailWord_2100602).sum := by decide
  have hdescent : baseEnd_2100602 < baseStart_2100602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100610 : List Nat := [3, 4, 2, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_2100610 : Nat := 118140960795 + 2100610 * 2 ^ 59
def prefixEnd_2100610 : Nat := 4983230072969 + 3 ^ 40 * 2100610 * 2
def baseEnd_2100610 : Nat := 1078622597641131587414477

theorem tailTrace_2100610 : CollatzResearch.WordTrace tailWord_2100610 prefixEnd_2100610 1078622597641131587414477 := by
  unfold tailWord_2100610
  simp only [CollatzResearch.WordTrace]
  refine ⟨19153885229964050117778821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51077027279904133647410189 19153885229964050117778821)
  ·
    refine ⟨3591353480618259397083529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19153885229964050117778821 3591353480618259397083529)
    ·
      refine ⟨2693515110463694547812647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3591353480618259397083529 2693515110463694547812647)
      ·
        refine ⟨4040272665695541821718971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2693515110463694547812647 4040272665695541821718971)
        ·
          refine ⟨6060408998543312732578457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4040272665695541821718971 6060408998543312732578457)
          ·
            refine ⟨4545306748907484549433843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6060408998543312732578457 4545306748907484549433843)
            ·
              refine ⟨6817960123361226824150765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4545306748907484549433843 6817960123361226824150765)
              ·
                refine ⟨2556735046260460059056537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6817960123361226824150765 2556735046260460059056537)
                ·
                  refine ⟨1917551284695345044292403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2556735046260460059056537 1917551284695345044292403)
                  ·
                    refine ⟨2876326927043017566438605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1917551284695345044292403 2876326927043017566438605)
                    ·
                      refine ⟨1078622597641131587414477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2876326927043017566438605 1078622597641131587414477)
                      ·
                        rfl

theorem cell23_2100610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_2100610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100610 prefixEnd_2100610 := by exact prefixLift 2100610
  have htrace : WordTrace (prefixWord ++ tailWord_2100610) baseStart_2100610 baseEnd_2100610 := by
    simpa [prefixWord, tailWord_2100610, baseEnd_2100610] using wordTrace_append hprefix tailTrace_2100610
  have hstable : (prefixWord ++ tailWord_2100610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100610).length < 2 ^ (prefixWord ++ tailWord_2100610).sum := by decide
  have hdescent : baseEnd_2100610 < baseStart_2100610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100726 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3]
def baseStart_2100726 : Nat := 118140960795 + 2100726 * 2 ^ 59
def prefixEnd_2100726 : Nat := 4983230072969 + 3 ^ 40 * 2100726 * 2
def baseEnd_2100726 : Nat := 1078682161397053133563943

theorem tailTrace_2100726 : CollatzResearch.WordTrace tailWord_2100726 prefixEnd_2100726 1078682161397053133563943 := by
  unfold tailWord_2100726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4788735736714747017646127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51079847858290634854892021 4788735736714747017646127)
  ·
    refine ⟨7183103605072120526469191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4788735736714747017646127 7183103605072120526469191)
    ·
      refine ⟨10774655407608180789703787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7183103605072120526469191 10774655407608180789703787)
      ·
        refine ⟨16161983111412271184555681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10774655407608180789703787 16161983111412271184555681)
        ·
          refine ⟨12121487333559203388416761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16161983111412271184555681 12121487333559203388416761)
          ·
            refine ⟨9091115500169402541312571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12121487333559203388416761 9091115500169402541312571)
            ·
              refine ⟨13636673250254103811968857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9091115500169402541312571 13636673250254103811968857)
              ·
                refine ⟨10227504937690577858976643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13636673250254103811968857 10227504937690577858976643)
                ·
                  refine ⟨15341257406535866788464965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10227504937690577858976643 15341257406535866788464965)
                  ·
                    refine ⟨2876485763725475022837181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15341257406535866788464965 2876485763725475022837181)
                    ·
                      refine ⟨1078682161397053133563943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2876485763725475022837181 1078682161397053133563943)
                      ·
                        rfl

theorem cell23_2100726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_2100726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100726 prefixEnd_2100726 := by exact prefixLift 2100726
  have htrace : WordTrace (prefixWord ++ tailWord_2100726) baseStart_2100726 baseEnd_2100726 := by
    simpa [prefixWord, tailWord_2100726, baseEnd_2100726] using wordTrace_append hprefix tailTrace_2100726
  have hstable : (prefixWord ++ tailWord_2100726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100726).length < 2 ^ (prefixWord ++ tailWord_2100726).sum := by decide
  have hdescent : baseEnd_2100726 < baseStart_2100726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100793 : List Nat := [1, 2, 1, 5, 1, 4, 1, 2, 1, 5]
def baseStart_2100793 : Nat := 118140960795 + 2100793 * 2 ^ 59
def prefixEnd_2100793 : Nat := 4983230072969 + 3 ^ 40 * 2100793 * 2
def baseEnd_2100793 : Nat := 359572188200301457142045

theorem tailTrace_2100793 : CollatzResearch.WordTrace tailWord_2100793 prefixEnd_2100793 359572188200301457142045 := by
  unfold tailWord_2100793
  simp only [CollatzResearch.WordTrace]
  refine ⟨76622215478193222725027033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51081476985462148483351355 76622215478193222725027033)
  ·
    refine ⟨57466661608644917043770275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76622215478193222725027033 57466661608644917043770275)
    ·
      refine ⟨86199992412967375565655413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57466661608644917043770275 86199992412967375565655413)
      ·
        refine ⟨8081249288715691459280195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86199992412967375565655413 8081249288715691459280195)
        ·
          refine ⟨12121873933073537188920293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8081249288715691459280195 12121873933073537188920293)
          ·
            refine ⟨2272851362451288222922555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12121873933073537188920293 2272851362451288222922555)
            ·
              refine ⟨3409277043676932334383833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2272851362451288222922555 3409277043676932334383833)
              ·
                refine ⟨2556957782757699250787875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3409277043676932334383833 2556957782757699250787875)
                ·
                  refine ⟨3835436674136548876181813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2556957782757699250787875 3835436674136548876181813)
                  ·
                    refine ⟨359572188200301457142045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3835436674136548876181813 359572188200301457142045)
                    ·
                      rfl

theorem cell23_2100793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 5].length) (baseStart_2100793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100793 prefixEnd_2100793 := by exact prefixLift 2100793
  have htrace : WordTrace (prefixWord ++ tailWord_2100793) baseStart_2100793 baseEnd_2100793 := by
    simpa [prefixWord, tailWord_2100793, baseEnd_2100793] using wordTrace_append hprefix tailTrace_2100793
  have hstable : (prefixWord ++ tailWord_2100793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100793).length < 2 ^ (prefixWord ++ tailWord_2100793).sum := by decide
  have hdescent : baseEnd_2100793 < baseStart_2100793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100823 : List Nat := [1, 1, 3, 2, 2, 4, 2, 2, 2, 4]
def baseStart_2100823 : Nat := 118140960795 + 2100823 * 2 ^ 59
def prefixEnd_2100823 : Nat := 4983230072969 + 3 ^ 40 * 2100823 * 2
def baseEnd_2100823 : Nat := 359577323006846418016999

theorem tailTrace_2100823 : CollatzResearch.WordTrace tailWord_2100823 prefixEnd_2100823 359577323006846418016999 := by
  unfold tailWord_2100823
  simp only [CollatzResearch.WordTrace]
  refine ⟨76623309668084537848619123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51082206445389691899079415 76623309668084537848619123)
  ·
    refine ⟨114934964502126806772928685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76623309668084537848619123 114934964502126806772928685)
    ·
      refine ⟨43100611688297552539848257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114934964502126806772928685 43100611688297552539848257)
      ·
        refine ⟨32325458766223164404886193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43100611688297552539848257 32325458766223164404886193)
        ·
          refine ⟨24244094074667373303664645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32325458766223164404886193 24244094074667373303664645)
          ·
            refine ⟨4545767639000132494437121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24244094074667373303664645 4545767639000132494437121)
            ·
              refine ⟨3409325729250099370827841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4545767639000132494437121 3409325729250099370827841)
              ·
                refine ⟨2556994296937574528120881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3409325729250099370827841 2556994296937574528120881)
                ·
                  refine ⟨1917745722703180896090661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2556994296937574528120881 1917745722703180896090661)
                  ·
                    refine ⟨359577323006846418016999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1917745722703180896090661 359577323006846418016999)
                    ·
                      rfl

theorem cell23_2100823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 4].length) (baseStart_2100823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100823 prefixEnd_2100823 := by exact prefixLift 2100823
  have htrace : WordTrace (prefixWord ++ tailWord_2100823) baseStart_2100823 baseEnd_2100823 := by
    simpa [prefixWord, tailWord_2100823, baseEnd_2100823] using wordTrace_append hprefix tailTrace_2100823
  have hstable : (prefixWord ++ tailWord_2100823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100823).length < 2 ^ (prefixWord ++ tailWord_2100823).sum := by decide
  have hdescent : baseEnd_2100823 < baseStart_2100823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100836 : List Nat := [2, 3, 1, 1, 2, 5, 1, 8]
def baseStart_2100836 : Nat := 118140960795 + 2100836 * 2 ^ 59
def prefixEnd_2100836 : Nat := 4983230072969 + 3 ^ 40 * 2100836 * 2
def baseEnd_2100836 : Nat := 39953283121075840858831

theorem tailTrace_2100836 : CollatzResearch.WordTrace tailWord_2100836 prefixEnd_2100836 39953283121075840858831 := by
  unfold tailWord_2100836
  simp only [CollatzResearch.WordTrace]
  refine ⟨38311891908518720534421181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51082522544691627379228241 38311891908518720534421181)
  ·
    refine ⟨14366959465694520200407943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38311891908518720534421181 14366959465694520200407943)
    ·
      refine ⟨21550439198541780300611915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14366959465694520200407943 21550439198541780300611915)
      ·
        refine ⟨32325658797812670450917873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21550439198541780300611915 32325658797812670450917873)
        ·
          refine ⟨24244244098359502838188405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32325658797812670450917873 24244244098359502838188405)
          ·
            refine ⟨2272897884221203391080163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24244244098359502838188405 2272897884221203391080163)
            ·
              refine ⟨3409346826331805086620245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2272897884221203391080163 3409346826331805086620245)
              ·
                refine ⟨39953283121075840858831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3409346826331805086620245 39953283121075840858831)
                ·
                  rfl

theorem cell23_2100836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 8].length) (baseStart_2100836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100836 prefixEnd_2100836 := by exact prefixLift 2100836
  have htrace : WordTrace (prefixWord ++ tailWord_2100836) baseStart_2100836 baseEnd_2100836 := by
    simpa [prefixWord, tailWord_2100836, baseEnd_2100836] using wordTrace_append hprefix tailTrace_2100836
  have hstable : (prefixWord ++ tailWord_2100836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100836).length < 2 ^ (prefixWord ++ tailWord_2100836).sum := by decide
  have hdescent : baseEnd_2100836 < baseStart_2100836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100839 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_2100839 : Nat := 118140960795 + 2100839 * 2 ^ 59
def prefixEnd_2100839 : Nat := 4983230072969 + 3 ^ 40 * 2100839 * 2
def baseEnd_2100839 : Nat := 1078740184711011191450923

theorem tailTrace_2100839 : CollatzResearch.WordTrace tailWord_2100839 prefixEnd_2100839 1078740184711011191450923 := by
  unfold tailWord_2100839
  simp only [CollatzResearch.WordTrace]
  refine ⟨76623893236026572581201571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51082595490684381720801047 76623893236026572581201571)
  ·
    refine ⟨114935839854039858871802357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76623893236026572581201571 114935839854039858871802357)
    ·
      refine ⟨10775234986316236769231471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114935839854039858871802357 10775234986316236769231471)
      ·
        refine ⟨16162852479474355153847207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10775234986316236769231471 16162852479474355153847207)
        ·
          refine ⟨24244278719211532730770811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16162852479474355153847207 24244278719211532730770811)
          ·
            refine ⟨36366418078817299096156217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24244278719211532730770811 36366418078817299096156217)
            ·
              refine ⟨27274813559112974322117163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36366418078817299096156217 27274813559112974322117163)
              ·
                refine ⟨40912220338669461483175745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27274813559112974322117163 40912220338669461483175745)
                ·
                  refine ⟨30684165254002096112381809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40912220338669461483175745 30684165254002096112381809)
                  ·
                    refine ⟨23013123940501572084286357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30684165254002096112381809 23013123940501572084286357)
                    ·
                      refine ⟨1078740184711011191450923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23013123940501572084286357 1078740184711011191450923)
                      ·
                        rfl

theorem cell23_2100839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_2100839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100839 prefixEnd_2100839 := by exact prefixLift 2100839
  have htrace : WordTrace (prefixWord ++ tailWord_2100839) baseStart_2100839 baseEnd_2100839 := by
    simpa [prefixWord, tailWord_2100839, baseEnd_2100839] using wordTrace_append hprefix tailTrace_2100839
  have hstable : (prefixWord ++ tailWord_2100839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100839).length < 2 ^ (prefixWord ++ tailWord_2100839).sum := by decide
  have hdescent : baseEnd_2100839 < baseStart_2100839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100853 : List Nat := [1, 3, 4, 2, 1, 2, 3, 7]
def baseStart_2100853 : Nat := 118140960795 + 2100853 * 2 ^ 59
def prefixEnd_2100853 : Nat := 4983230072969 + 3 ^ 40 * 2100853 * 2
def baseEnd_2100853 : Nat := 39953606423710153210217

theorem tailTrace_2100853 : CollatzResearch.WordTrace tailWord_2100853 prefixEnd_2100853 39953606423710153210217 := by
  unfold tailWord_2100853
  simp only [CollatzResearch.WordTrace]
  refine ⟨76624403857975852972211213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51082935905317235314807475 76624403857975852972211213)
  ·
    refine ⟨28734151446740944864579205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76624403857975852972211213 28734151446740944864579205)
    ·
      refine ⟨5387653396263927162108601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28734151446740944864579205 5387653396263927162108601)
      ·
        refine ⟨4040740047197945371581451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5387653396263927162108601 4040740047197945371581451)
        ·
          refine ⟨6061110070796918057372177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4040740047197945371581451 6061110070796918057372177)
          ·
            refine ⟨4545832553097688543029133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6061110070796918057372177 4545832553097688543029133)
            ·
              refine ⟨1704687207411633203635925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4545832553097688543029133 1704687207411633203635925)
              ·
                refine ⟨39953606423710153210217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1704687207411633203635925 39953606423710153210217)
                ·
                  rfl

theorem cell23_2100853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 7].length) (baseStart_2100853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100853 prefixEnd_2100853 := by exact prefixLift 2100853
  have htrace : WordTrace (prefixWord ++ tailWord_2100853) baseStart_2100853 baseEnd_2100853 := by
    simpa [prefixWord, tailWord_2100853, baseEnd_2100853] using wordTrace_append hprefix tailTrace_2100853
  have hstable : (prefixWord ++ tailWord_2100853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100853).length < 2 ^ (prefixWord ++ tailWord_2100853).sum := by decide
  have hdescent : baseEnd_2100853 < baseStart_2100853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100859 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 5]
def baseStart_2100859 : Nat := 118140960795 + 2100859 * 2 ^ 59
def prefixEnd_2100859 : Nat := 4983230072969 + 3 ^ 40 * 2100859 * 2
def baseEnd_2100859 : Nat := 1078750454324101113200831

theorem tailTrace_2100859 : CollatzResearch.WordTrace tailWord_2100859 prefixEnd_2100859 1078750454324101113200831 := by
  unfold tailWord_2100859
  simp only [CollatzResearch.WordTrace]
  refine ⟨76624622695954115996929631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51083081797302743997953087 76624622695954115996929631)
  ·
    refine ⟨114936934043931173995394447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76624622695954115996929631 114936934043931173995394447)
    ·
      refine ⟨172405401065896760993091671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114936934043931173995394447 172405401065896760993091671)
      ·
        refine ⟨258608101598845141489637507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172405401065896760993091671 258608101598845141489637507)
        ·
          refine ⟨387912152398267712234456261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258608101598845141489637507 387912152398267712234456261)
          ·
            refine ⟨72733528574675196043960549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 387912152398267712234456261 72733528574675196043960549)
            ·
              refine ⟨13637536607751599258242603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72733528574675196043960549 13637536607751599258242603)
              ·
                refine ⟨20456304911627398887363905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13637536607751599258242603 20456304911627398887363905)
                ·
                  refine ⟨15342228683720549165522929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20456304911627398887363905 15342228683720549165522929)
                  ·
                    refine ⟨11506671512790411874142197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15342228683720549165522929 11506671512790411874142197)
                    ·
                      refine ⟨1078750454324101113200831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11506671512790411874142197 1078750454324101113200831)
                      ·
                        rfl

theorem cell23_2100859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 5].length) (baseStart_2100859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100859 prefixEnd_2100859 := by exact prefixLift 2100859
  have htrace : WordTrace (prefixWord ++ tailWord_2100859) baseStart_2100859 baseEnd_2100859 := by
    simpa [prefixWord, tailWord_2100859, baseEnd_2100859] using wordTrace_append hprefix tailTrace_2100859
  have hstable : (prefixWord ++ tailWord_2100859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100859).length < 2 ^ (prefixWord ++ tailWord_2100859).sum := by decide
  have hdescent : baseEnd_2100859 < baseStart_2100859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100889 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 3, 3, 5]
def baseStart_2100889 : Nat := 118140960795 + 2100889 * 2 ^ 59
def prefixEnd_2100889 : Nat := 4983230072969 + 3 ^ 40 * 2100889 * 2
def baseEnd_2100889 : Nat := 1078765858743735995825693

theorem tailTrace_2100889 : CollatzResearch.WordTrace tailWord_2100889 prefixEnd_2100889 1078765858743735995825693 := by
  unfold tailWord_2100889
  simp only [CollatzResearch.WordTrace]
  refine ⟨76625716885845431120521721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51083811257230287413681147 76625716885845431120521721)
  ·
    refine ⟨57469287664384073340391291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76625716885845431120521721 57469287664384073340391291)
    ·
      refine ⟨86203931496576110010586937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57469287664384073340391291 86203931496576110010586937)
      ·
        refine ⟨64652948622432082507940203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86203931496576110010586937 64652948622432082507940203)
        ·
          refine ⟨96979422933648123761910305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64652948622432082507940203 96979422933648123761910305)
          ·
            refine ⟨72734567200236092821432729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96979422933648123761910305 72734567200236092821432729)
            ·
              refine ⟨54550925400177069616074547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72734567200236092821432729 54550925400177069616074547)
              ·
                refine ⟨81826388100265604424111821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54550925400177069616074547 81826388100265604424111821)
                ·
                  refine ⟨30684895537599601659041933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81826388100265604424111821 30684895537599601659041933)
                  ·
                    refine ⟨11506835826599850622140725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30684895537599601659041933 11506835826599850622140725)
                    ·
                      refine ⟨1078765858743735995825693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11506835826599850622140725 1078765858743735995825693)
                      ·
                        rfl

theorem cell23_2100889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_2100889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100889 prefixEnd_2100889 := by exact prefixLift 2100889
  have htrace : WordTrace (prefixWord ++ tailWord_2100889) baseStart_2100889 baseEnd_2100889 := by
    simpa [prefixWord, tailWord_2100889, baseEnd_2100889] using wordTrace_append hprefix tailTrace_2100889
  have hstable : (prefixWord ++ tailWord_2100889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100889).length < 2 ^ (prefixWord ++ tailWord_2100889).sum := by decide
  have hdescent : baseEnd_2100889 < baseStart_2100889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100896 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 2, 6]
def baseStart_2100896 : Nat := 118140960795 + 2100896 * 2 ^ 59
def prefixEnd_2100896 : Nat := 4983230072969 + 3 ^ 40 * 2100896 * 2
def baseEnd_2100896 : Nat := 359589817702772489479387

theorem tailTrace_2100896 : CollatzResearch.WordTrace tailWord_2100896 prefixEnd_2100896 359589817702772489479387 := by
  unfold tailWord_2100896
  simp only [CollatzResearch.WordTrace]
  refine ⟨38312986098410035658013271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51083981464546714210684361 38312986098410035658013271)
  ·
    refine ⟨57469479147615053487019907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38312986098410035658013271 57469479147615053487019907)
    ·
      refine ⟨86204218721422580230529861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57469479147615053487019907 86204218721422580230529861)
      ·
        refine ⟨16163291010266733793224349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86204218721422580230529861 16163291010266733793224349)
        ·
          refine ⟨6061234128850025172459131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16163291010266733793224349 6061234128850025172459131)
          ·
            refine ⟨9091851193275037758688697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6061234128850025172459131 9091851193275037758688697)
            ·
              refine ⟨6818888394956278319016523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9091851193275037758688697 6818888394956278319016523)
              ·
                refine ⟨10228332592434417478524785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6818888394956278319016523 10228332592434417478524785)
                ·
                  refine ⟨7671249444325813108893589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10228332592434417478524785 7671249444325813108893589)
                  ·
                    refine ⟨359589817702772489479387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7671249444325813108893589 359589817702772489479387)
                    ·
                      rfl

theorem cell23_2100896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 2, 6].length) (baseStart_2100896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100896 prefixEnd_2100896 := by exact prefixLift 2100896
  have htrace : WordTrace (prefixWord ++ tailWord_2100896) baseStart_2100896 baseEnd_2100896 := by
    simpa [prefixWord, tailWord_2100896, baseEnd_2100896] using wordTrace_append hprefix tailTrace_2100896
  have hstable : (prefixWord ++ tailWord_2100896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100896).length < 2 ^ (prefixWord ++ tailWord_2100896).sum := by decide
  have hdescent : baseEnd_2100896 < baseStart_2100896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100897 : List Nat := [1, 2, 3, 3, 2, 2, 3, 1, 2, 1, 3]
def baseStart_2100897 : Nat := 118140960795 + 2100897 * 2 ^ 59
def prefixEnd_2100897 : Nat := 4983230072969 + 3 ^ 40 * 2100897 * 2
def baseEnd_2100897 : Nat := 1078769966588971964525657

theorem tailTrace_2100897 : CollatzResearch.WordTrace tailWord_2100897 prefixEnd_2100897 1078769966588971964525657 := by
  unfold tailWord_2100897
  simp only [CollatzResearch.WordTrace]
  refine ⟨76626008669816448486812945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51084005779877632324541963 76626008669816448486812945)
  ·
    refine ⟨57469506502362336365109709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76626008669816448486812945 57469506502362336365109709)
    ·
      refine ⟨21551064938385876136916141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57469506502362336365109709 21551064938385876136916141)
      ·
        refine ⟨8081649351894703551343553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21551064938385876136916141 8081649351894703551343553)
        ·
          refine ⟨6061237013921027663507665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8081649351894703551343553 6061237013921027663507665)
          ·
            refine ⟨4545927760440770747630749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6061237013921027663507665 4545927760440770747630749)
            ·
              refine ⟨1704722910165289030361531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4545927760440770747630749 1704722910165289030361531)
              ·
                refine ⟨2557084365247933545542297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1704722910165289030361531 2557084365247933545542297)
                ·
                  refine ⟨1917813273935950159156723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2557084365247933545542297 1917813273935950159156723)
                  ·
                    refine ⟨2876719910903925238735085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1917813273935950159156723 2876719910903925238735085)
                    ·
                      refine ⟨1078769966588971964525657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2876719910903925238735085 1078769966588971964525657)
                      ·
                        rfl

theorem cell23_2100897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_2100897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100897 prefixEnd_2100897 := by exact prefixLift 2100897
  have htrace : WordTrace (prefixWord ++ tailWord_2100897) baseStart_2100897 baseEnd_2100897 := by
    simpa [prefixWord, tailWord_2100897, baseEnd_2100897] using wordTrace_append hprefix tailTrace_2100897
  have hstable : (prefixWord ++ tailWord_2100897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100897).length < 2 ^ (prefixWord ++ tailWord_2100897).sum := by decide
  have hdescent : baseEnd_2100897 < baseStart_2100897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100904 : List Nat := [2, 1, 7, 1, 2, 1, 2, 7]
def baseStart_2100904 : Nat := 118140960795 + 2100904 * 2 ^ 59
def prefixEnd_2100904 : Nat := 4983230072969 + 3 ^ 40 * 2100904 * 2
def baseEnd_2100904 : Nat := 39954576331613090264375

theorem tailTrace_2100904 : CollatzResearch.WordTrace tailWord_2100904 prefixEnd_2100904 39954576331613090264375 := by
  unfold tailWord_2100904
  simp only [CollatzResearch.WordTrace]
  refine ⟨38313131990395544341158883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51084175987194059121545177 38313131990395544341158883)
  ·
    refine ⟨57469697985593316511738325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38313131990395544341158883 57469697985593316511738325)
    ·
      refine ⟨1346946046537343355743867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 57469697985593316511738325 1346946046537343355743867)
      ·
        refine ⟨2020419069806015033615801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1346946046537343355743867 2020419069806015033615801)
        ·
          refine ⟨1515314302354511275211851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2020419069806015033615801 1515314302354511275211851)
          ·
            refine ⟨2272971453531766912817777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1515314302354511275211851 2272971453531766912817777)
            ·
              refine ⟨1704728590148825184613333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2272971453531766912817777 1704728590148825184613333)
              ·
                refine ⟨39954576331613090264375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1704728590148825184613333 39954576331613090264375)
                ·
                  rfl

theorem cell23_2100904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 7].length) (baseStart_2100904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100904 prefixEnd_2100904 := by exact prefixLift 2100904
  have htrace : WordTrace (prefixWord ++ tailWord_2100904) baseStart_2100904 baseEnd_2100904 := by
    simpa [prefixWord, tailWord_2100904, baseEnd_2100904] using wordTrace_append hprefix tailTrace_2100904
  have hstable : (prefixWord ++ tailWord_2100904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100904).length < 2 ^ (prefixWord ++ tailWord_2100904).sum := by decide
  have hdescent : baseEnd_2100904 < baseStart_2100904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100954 : List Nat := [3, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2]
def baseStart_2100954 : Nat := 118140960795 + 2100954 * 2 ^ 59
def prefixEnd_2100954 : Nat := 4983230072969 + 3 ^ 40 * 2100954 * 2
def baseEnd_2100954 : Nat := 1078799234986278241512895

theorem tailTrace_2100954 : CollatzResearch.WordTrace tailWord_2100954 prefixEnd_2100954 1078799234986278241512895 := by
  unfold tailWord_2100954
  simp only [CollatzResearch.WordTrace]
  refine ⟨19157021907652486805409479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51085391753739964814425277 19157021907652486805409479)
  ·
    refine ⟨28735532861478730208114219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19157021907652486805409479 28735532861478730208114219)
    ·
      refine ⟨43103299292218095312171329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28735532861478730208114219 43103299292218095312171329)
      ·
        refine ⟨32327474469163571484128497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43103299292218095312171329 32327474469163571484128497)
        ·
          refine ⟨24245605851872678613096373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32327474469163571484128497 24245605851872678613096373)
          ·
            refine ⟨2273025548613063619977785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24245605851872678613096373 2273025548613063619977785)
            ·
              refine ⟨1704769161459797714983339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2273025548613063619977785 1704769161459797714983339)
              ·
                refine ⟨2557153742189696572475009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1704769161459797714983339 2557153742189696572475009)
                ·
                  refine ⟨1917865306642272429356257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2557153742189696572475009 1917865306642272429356257)
                  ·
                    refine ⟨1438398979981704322017193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1917865306642272429356257 1438398979981704322017193)
                    ·
                      refine ⟨1078799234986278241512895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1438398979981704322017193 1078799234986278241512895)
                      ·
                        rfl

theorem cell23_2100954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2].length) (baseStart_2100954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100954 prefixEnd_2100954 := by exact prefixLift 2100954
  have htrace : WordTrace (prefixWord ++ tailWord_2100954) baseStart_2100954 baseEnd_2100954 := by
    simpa [prefixWord, tailWord_2100954, baseEnd_2100954] using wordTrace_append hprefix tailTrace_2100954
  have hstable : (prefixWord ++ tailWord_2100954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100954).length < 2 ^ (prefixWord ++ tailWord_2100954).sum := by decide
  have hdescent : baseEnd_2100954 < baseStart_2100954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100973 : List Nat := [1, 5, 1, 2, 1, 2, 1, 3, 2, 5]
def baseStart_2100973 : Nat := 118140960795 + 2100973 * 2 ^ 59
def prefixEnd_2100973 : Nat := 4983230072969 + 3 ^ 40 * 2100973 * 2
def baseEnd_2100973 : Nat := 359602997039571222391769

theorem tailTrace_2100973 : CollatzResearch.WordTrace tailWord_2100973 prefixEnd_2100973 359602997039571222391769 := by
  unfold tailWord_2100973
  simp only [CollatzResearch.WordTrace]
  refine ⟨76628780617541113466579573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51085853745027408977719715 76628780617541113466579573)
  ·
    refine ⟨7183948182894479387491835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76628780617541113466579573 7183948182894479387491835)
    ·
      refine ⟨10775922274341719081237753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7183948182894479387491835 10775922274341719081237753)
      ·
        refine ⟨8081941705756289310928315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10775922274341719081237753 8081941705756289310928315)
        ·
          refine ⟨12122912558634433966392473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8081941705756289310928315 12122912558634433966392473)
          ·
            refine ⟨9092184418975825474794355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12122912558634433966392473 9092184418975825474794355)
            ·
              refine ⟨13638276628463738212191533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9092184418975825474794355 13638276628463738212191533)
              ·
                refine ⟨5114353735673901829571825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13638276628463738212191533 5114353735673901829571825)
                ·
                  refine ⟨3835765301755426372178869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5114353735673901829571825 3835765301755426372178869)
                  ·
                    refine ⟨359602997039571222391769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3835765301755426372178869 359602997039571222391769)
                    ·
                      rfl

theorem cell23_2100973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_2100973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100973 prefixEnd_2100973 := by exact prefixLift 2100973
  have htrace : WordTrace (prefixWord ++ tailWord_2100973) baseStart_2100973 baseEnd_2100973 := by
    simpa [prefixWord, tailWord_2100973, baseEnd_2100973] using wordTrace_append hprefix tailTrace_2100973
  have hstable : (prefixWord ++ tailWord_2100973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100973).length < 2 ^ (prefixWord ++ tailWord_2100973).sum := by decide
  have hdescent : baseEnd_2100973 < baseStart_2100973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100993 : List Nat := [1, 2, 4, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_2100993 : Nat := 118140960795 + 2100993 * 2 ^ 59
def prefixEnd_2100993 : Nat := 4983230072969 + 3 ^ 40 * 2100993 * 2
def baseEnd_2100993 : Nat := 1078819260731803588925215

theorem tailTrace_2100993 : CollatzResearch.WordTrace tailWord_2100993 prefixEnd_2100993 1078819260731803588925215 := by
  unfold tailWord_2100993
  simp only [CollatzResearch.WordTrace]
  refine ⟨76629510077468656882307633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51086340051645771254871755 76629510077468656882307633)
  ·
    refine ⟨57472132558101492661730725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76629510077468656882307633 57472132558101492661730725)
    ·
      refine ⟨10776024854644029874074511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57472132558101492661730725 10776024854644029874074511)
      ·
        refine ⟨16164037281966044811111767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10776024854644029874074511 16164037281966044811111767)
        ·
          refine ⟨24246055922949067216667651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16164037281966044811111767 24246055922949067216667651)
          ·
            refine ⟨36369083884423600825001477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24246055922949067216667651 36369083884423600825001477)
            ·
              refine ⟨6819203228329425154687777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36369083884423600825001477 6819203228329425154687777)
              ·
                refine ⟨5114402421247068866015833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6819203228329425154687777 5114402421247068866015833)
                ·
                  refine ⟨3835801815935301649511875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5114402421247068866015833 3835801815935301649511875)
                  ·
                    refine ⟨5753702723902952474267813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3835801815935301649511875 5753702723902952474267813)
                    ·
                      refine ⟨1078819260731803588925215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5753702723902952474267813 1078819260731803588925215)
                      ·
                        rfl

theorem cell23_2100993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_2100993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2100993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2100993 prefixEnd_2100993 := by exact prefixLift 2100993
  have htrace : WordTrace (prefixWord ++ tailWord_2100993) baseStart_2100993 baseEnd_2100993 := by
    simpa [prefixWord, tailWord_2100993, baseEnd_2100993] using wordTrace_append hprefix tailTrace_2100993
  have hstable : (prefixWord ++ tailWord_2100993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100993).length < 2 ^ (prefixWord ++ tailWord_2100993).sum := by decide
  have hdescent : baseEnd_2100993 < baseStart_2100993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101050 : List Nat := [3, 1, 1, 1, 5, 3, 1, 2, 6]
def baseStart_2101050 : Nat := 118140960795 + 2101050 * 2 ^ 59
def prefixEnd_2101050 : Nat := 4983230072969 + 3 ^ 40 * 2101050 * 2
def baseEnd_2101050 : Nat := 119872058792123318434717

theorem tailTrace_2101050 : CollatzResearch.WordTrace tailWord_2101050 prefixEnd_2101050 119872058792123318434717 := by
  unfold tailWord_2101050
  simp only [CollatzResearch.WordTrace]
  refine ⟨19157897259565538904283151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51087726025508103744755069 19157897259565538904283151)
  ·
    refine ⟨28736845889348308356424727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19157897259565538904283151 28736845889348308356424727)
    ·
      refine ⟨43105268834022462534637091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28736845889348308356424727 43105268834022462534637091)
      ·
        refine ⟨64657903251033693801955637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43105268834022462534637091 64657903251033693801955637)
        ·
          refine ⟨6061678429784408793933341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64657903251033693801955637 6061678429784408793933341)
          ·
            refine ⟨2273129411169153297725003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6061678429784408793933341 2273129411169153297725003)
            ·
              refine ⟨3409694116753729946587505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2273129411169153297725003 3409694116753729946587505)
              ·
                refine ⟨2557270587565297459940629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3409694116753729946587505 2557270587565297459940629)
                ·
                  refine ⟨119872058792123318434717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2557270587565297459940629 119872058792123318434717)
                  ·
                    rfl

theorem cell23_2101050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 6].length) (baseStart_2101050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101050 prefixEnd_2101050 := by exact prefixLift 2101050
  have htrace : WordTrace (prefixWord ++ tailWord_2101050) baseStart_2101050 baseEnd_2101050 := by
    simpa [prefixWord, tailWord_2101050, baseEnd_2101050] using wordTrace_append hprefix tailTrace_2101050
  have hstable : (prefixWord ++ tailWord_2101050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101050).length < 2 ^ (prefixWord ++ tailWord_2101050).sum := by decide
  have hdescent : baseEnd_2101050 < baseStart_2101050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101053 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 1, 2, 6]
def baseStart_2101053 : Nat := 118140960795 + 2101053 * 2 ^ 59
def prefixEnd_2101053 : Nat := 4983230072969 + 3 ^ 40 * 2101053 * 2
def baseEnd_2101053 : Nat := 1078850069571073354174939

theorem tailTrace_2101053 : CollatzResearch.WordTrace tailWord_2101053 prefixEnd_2101053 1078850069571073354174939 := by
  unfold tailWord_2101053
  simp only [CollatzResearch.WordTrace]
  refine ⟨76631698457251287129491813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51087798971500858086327875 76631698457251287129491813)
  ·
    refine ⟨14368443460734616336779715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76631698457251287129491813 14368443460734616336779715)
    ·
      refine ⟨21552665191101924505169573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14368443460734616336779715 21552665191101924505169573)
      ·
        refine ⟨4041124723331610844719295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21552665191101924505169573 4041124723331610844719295)
        ·
          refine ⟨6061687084997416267078943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4041124723331610844719295 6061687084997416267078943)
          ·
            refine ⟨9092530627496124400618415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6061687084997416267078943 9092530627496124400618415)
            ·
              refine ⟨13638795941244186600927623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9092530627496124400618415 13638795941244186600927623)
              ·
                refine ⟨20458193911866279901391435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13638795941244186600927623 20458193911866279901391435)
                ·
                  refine ⟨30687290867799419852087153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20458193911866279901391435 30687290867799419852087153)
                  ·
                    refine ⟨23015468150849564889065365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30687290867799419852087153 23015468150849564889065365)
                    ·
                      refine ⟨1078850069571073354174939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23015468150849564889065365 1078850069571073354174939)
                      ·
                        rfl

theorem cell23_2101053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_2101053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101053 prefixEnd_2101053 := by exact prefixLift 2101053
  have htrace : WordTrace (prefixWord ++ tailWord_2101053) baseStart_2101053 baseEnd_2101053 := by
    simpa [prefixWord, tailWord_2101053, baseEnd_2101053] using wordTrace_append hprefix tailTrace_2101053
  have hstable : (prefixWord ++ tailWord_2101053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101053).length < 2 ^ (prefixWord ++ tailWord_2101053).sum := by decide
  have hdescent : baseEnd_2101053 < baseStart_2101053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101100 : List Nat := [2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 4]
def baseStart_2101100 : Nat := 118140960795 + 2101100 * 2 ^ 59
def prefixEnd_2101100 : Nat := 4983230072969 + 3 ^ 40 * 2101100 * 2
def baseEnd_2101100 : Nat := 1078874203161834670287223

theorem tailTrace_2101100 : CollatzResearch.WordTrace tailWord_2101100 prefixEnd_2101100 1078874203161834670287223 := by
  unfold tailWord_2101100
  simp only [CollatzResearch.WordTrace]
  refine ⟨38316706344040507078226377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51088941792054009437635169 38316706344040507078226377)
  ·
    refine ⟨28737529758030380308669783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38316706344040507078226377 28737529758030380308669783)
    ·
      refine ⟨43106294637045570463004675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28737529758030380308669783 43106294637045570463004675)
      ·
        refine ⟨64659441955568355694507013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43106294637045570463004675 64659441955568355694507013)
        ·
          refine ⟨12123645366669066692720065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64659441955568355694507013 12123645366669066692720065)
          ·
            refine ⟨9092734025001800019540049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12123645366669066692720065 9092734025001800019540049)
            ·
              refine ⟨6819550518751350014655037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9092734025001800019540049 6819550518751350014655037)
              ·
                refine ⟨2557331444531756255495639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6819550518751350014655037 2557331444531756255495639)
                ·
                  refine ⟨3835997166797634383243459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2557331444531756255495639 3835997166797634383243459)
                  ·
                    refine ⟨5753995750196451574865189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3835997166797634383243459 5753995750196451574865189)
                    ·
                      refine ⟨1078874203161834670287223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5753995750196451574865189 1078874203161834670287223)
                      ·
                        rfl

theorem cell23_2101100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 4].length) (baseStart_2101100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101100 prefixEnd_2101100 := by exact prefixLift 2101100
  have htrace : WordTrace (prefixWord ++ tailWord_2101100) baseStart_2101100 baseEnd_2101100 := by
    simpa [prefixWord, tailWord_2101100, baseEnd_2101100] using wordTrace_append hprefix tailTrace_2101100
  have hstable : (prefixWord ++ tailWord_2101100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101100).length < 2 ^ (prefixWord ++ tailWord_2101100).sum := by decide
  have hdescent : baseEnd_2101100 < baseStart_2101100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101103 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 3]
def baseStart_2101103 : Nat := 118140960795 + 2101103 * 2 ^ 59
def prefixEnd_2101103 : Nat := 4983230072969 + 3 ^ 40 * 2101103 * 2
def baseEnd_2101103 : Nat := 1078875743603798158549709

theorem tailTrace_2101103 : CollatzResearch.WordTrace tailWord_2101103 prefixEnd_2101103 1078875743603798158549709 := by
  unfold tailWord_2101103
  simp only [CollatzResearch.WordTrace]
  refine ⟨76633522107070145668811963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51089014738046763779207975 76633522107070145668811963)
  ·
    refine ⟨114950283160605218503217945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76633522107070145668811963 114950283160605218503217945)
    ·
      refine ⟨86212712370453913877413459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114950283160605218503217945 86212712370453913877413459)
      ·
        refine ⟨129319068555680870816120189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86212712370453913877413459 129319068555680870816120189)
        ·
          refine ⟨48494650708380326556045071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129319068555680870816120189 48494650708380326556045071)
          ·
            refine ⟨72741976062570489834067607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48494650708380326556045071 72741976062570489834067607)
            ·
              refine ⟨109112964093855734751101411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72741976062570489834067607 109112964093855734751101411)
              ·
                refine ⟨163669446140783602126652117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109112964093855734751101411 163669446140783602126652117)
                ·
                  refine ⟨3836002643924615674843409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 163669446140783602126652117 3836002643924615674843409)
                  ·
                    refine ⟨2877001982943461756132557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3836002643924615674843409 2877001982943461756132557)
                    ·
                      refine ⟨1078875743603798158549709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2877001982943461756132557 1078875743603798158549709)
                      ·
                        rfl

theorem cell23_2101103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 3].length) (baseStart_2101103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101103 prefixEnd_2101103 := by exact prefixLift 2101103
  have htrace : WordTrace (prefixWord ++ tailWord_2101103) baseStart_2101103 baseEnd_2101103 := by
    simpa [prefixWord, tailWord_2101103, baseEnd_2101103] using wordTrace_append hprefix tailTrace_2101103
  have hstable : (prefixWord ++ tailWord_2101103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101103).length < 2 ^ (prefixWord ++ tailWord_2101103).sum := by decide
  have hdescent : baseEnd_2101103 < baseStart_2101103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101123 : List Nat := [1, 1, 1, 3, 4, 3, 2, 8]
def baseStart_2101123 : Nat := 118140960795 + 2101123 * 2 ^ 59
def prefixEnd_2101123 : Nat := 4983230072969 + 3 ^ 40 * 2101123 * 2
def baseEnd_2101123 : Nat := 39958741230255114085171

theorem tailTrace_2101123 : CollatzResearch.WordTrace tailWord_2101123 prefixEnd_2101123 39958741230255114085171 := by
  unfold tailWord_2101123
  simp only [CollatzResearch.WordTrace]
  refine ⟨76634251566997689084540023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51089501044665126056360015 76634251566997689084540023)
  ·
    refine ⟨114951377350496533626810035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76634251566997689084540023 114951377350496533626810035)
    ·
      refine ⟨172427066025744800440215053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114951377350496533626810035 172427066025744800440215053)
      ·
        refine ⟨64660149759654300165080645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172427066025744800440215053 64660149759654300165080645)
        ·
          refine ⟨12123778079935181280952621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64660149759654300165080645 12123778079935181280952621)
          ·
            refine ⟨4546416779975692980357233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12123778079935181280952621 4546416779975692980357233)
            ·
              refine ⟨3409812584981769735267925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4546416779975692980357233 3409812584981769735267925)
              ·
                refine ⟨39958741230255114085171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3409812584981769735267925 39958741230255114085171)
                ·
                  rfl

theorem cell23_2101123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 8].length) (baseStart_2101123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101123 prefixEnd_2101123 := by exact prefixLift 2101123
  have htrace : WordTrace (prefixWord ++ tailWord_2101123) baseStart_2101123 baseEnd_2101123 := by
    simpa [prefixWord, tailWord_2101123, baseEnd_2101123] using wordTrace_append hprefix tailTrace_2101123
  have hstable : (prefixWord ++ tailWord_2101123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101123).length < 2 ^ (prefixWord ++ tailWord_2101123).sum := by decide
  have hdescent : baseEnd_2101123 < baseStart_2101123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101127 : List Nat := [1, 1, 4, 2, 4, 1, 1, 3, 2, 4]
def baseStart_2101127 : Nat := 118140960795 + 2101127 * 2 ^ 59
def prefixEnd_2101127 : Nat := 4983230072969 + 3 ^ 40 * 2101127 * 2
def baseEnd_2101127 : Nat := 359629355713168688216533

theorem tailTrace_2101127 : CollatzResearch.WordTrace tailWord_2101127 prefixEnd_2101127 359629355713168688216533 := by
  unfold tailWord_2101127
  simp only [CollatzResearch.WordTrace]
  refine ⟨76634397458983197767685635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51089598305988798511790423 76634397458983197767685635)
  ·
    refine ⟨114951596188474796651528453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76634397458983197767685635 114951596188474796651528453)
    ·
      refine ⟨21553424285339024372161585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114951596188474796651528453 21553424285339024372161585)
      ·
        refine ⟨16165068214004268279121189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21553424285339024372161585 16165068214004268279121189)
        ·
          refine ⟨3030950290125800302335223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16165068214004268279121189 3030950290125800302335223)
          ·
            refine ⟨4546425435188700453502835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3030950290125800302335223 4546425435188700453502835)
            ·
              refine ⟨6819638152783050680254253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4546425435188700453502835 6819638152783050680254253)
              ·
                refine ⟨2557364307293644005095345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6819638152783050680254253 2557364307293644005095345)
                ·
                  refine ⟨1918023230470233003821509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2557364307293644005095345 1918023230470233003821509)
                  ·
                    refine ⟨359629355713168688216533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1918023230470233003821509 359629355713168688216533)
                    ·
                      rfl

theorem cell23_2101127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_2101127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101127 prefixEnd_2101127 := by exact prefixLift 2101127
  have htrace : WordTrace (prefixWord ++ tailWord_2101127) baseStart_2101127 baseEnd_2101127 := by
    simpa [prefixWord, tailWord_2101127, baseEnd_2101127] using wordTrace_append hprefix tailTrace_2101127
  have hstable : (prefixWord ++ tailWord_2101127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101127).length < 2 ^ (prefixWord ++ tailWord_2101127).sum := by decide
  have hdescent : baseEnd_2101127 < baseStart_2101127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101154 : List Nat := [3, 3, 1, 2, 4, 1, 1, 1, 1, 1, 5]
def baseStart_2101154 : Nat := 118140960795 + 2101154 * 2 ^ 59
def prefixEnd_2101154 : Nat := 4983230072969 + 3 ^ 40 * 2101154 * 2
def baseEnd_2101154 : Nat := 1078901931117177459011975

theorem tailTrace_2101154 : CollatzResearch.WordTrace tailWord_2101154 prefixEnd_2101154 1078901931117177459011975 := by
  unfold tailWord_2101154
  simp only [CollatzResearch.WordTrace]
  refine ⟨19158845557471345344729629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51090254819923587585945677 19158845557471345344729629)
  ·
    refine ⟨7184567084051754504273611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19158845557471345344729629 7184567084051754504273611)
    ·
      refine ⟨10776850626077631756410417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7184567084051754504273611 10776850626077631756410417)
      ·
        refine ⟨8082637969558223817307813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10776850626077631756410417 8082637969558223817307813)
        ·
          refine ⟨1515494619292166965745215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8082637969558223817307813 1515494619292166965745215)
          ·
            refine ⟨2273241928938250448617823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1515494619292166965745215 2273241928938250448617823)
            ·
              refine ⟨3409862893407375672926735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2273241928938250448617823 3409862893407375672926735)
              ·
                refine ⟨5114794340111063509390103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3409862893407375672926735 5114794340111063509390103)
                ·
                  refine ⟨7672191510166595264085155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5114794340111063509390103 7672191510166595264085155)
                  ·
                    refine ⟨11508287265249892896127733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7672191510166595264085155 11508287265249892896127733)
                    ·
                      refine ⟨1078901931117177459011975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11508287265249892896127733 1078901931117177459011975)
                      ·
                        rfl

theorem cell23_2101154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_2101154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101154 prefixEnd_2101154 := by exact prefixLift 2101154
  have htrace : WordTrace (prefixWord ++ tailWord_2101154) baseStart_2101154 baseEnd_2101154 := by
    simpa [prefixWord, tailWord_2101154, baseEnd_2101154] using wordTrace_append hprefix tailTrace_2101154
  have hstable : (prefixWord ++ tailWord_2101154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101154).length < 2 ^ (prefixWord ++ tailWord_2101154).sum := by decide
  have hdescent : baseEnd_2101154 < baseStart_2101154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101167 : List Nat := [1, 1, 2, 1, 2, 2, 6, 2, 2, 1, 3]
def baseStart_2101167 : Nat := 118140960795 + 2101167 * 2 ^ 59
def prefixEnd_2101167 : Nat := 4983230072969 + 3 ^ 40 * 2101167 * 2
def baseEnd_2101167 : Nat := 1078908606365685908149415

theorem tailTrace_2101167 : CollatzResearch.WordTrace tailWord_2101167 prefixEnd_2101167 1078908606365685908149415 := by
  unfold tailWord_2101167
  simp only [CollatzResearch.WordTrace]
  refine ⟨76635856378838284599141755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51090570919225523066094503 76635856378838284599141755)
  ·
    refine ⟨114953784568257426898712633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76635856378838284599141755 114953784568257426898712633)
    ·
      refine ⟨86215338426193070174034475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114953784568257426898712633 86215338426193070174034475)
      ·
        refine ⟨129323007639289605261051713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86215338426193070174034475 129323007639289605261051713)
        ·
          refine ⟨96992255729467203945788785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129323007639289605261051713 96992255729467203945788785)
          ·
            refine ⟨72744191797100402959341589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96992255729467203945788785 72744191797100402959341589)
            ·
              refine ⟨3409883990489081388719137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72744191797100402959341589 3409883990489081388719137)
              ·
                refine ⟨2557412992866811041539353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3409883990489081388719137 2557412992866811041539353)
                ·
                  refine ⟨1918059744650108281154515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2557412992866811041539353 1918059744650108281154515)
                  ·
                    refine ⟨2877089616975162421731773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1918059744650108281154515 2877089616975162421731773)
                    ·
                      refine ⟨1078908606365685908149415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2877089616975162421731773 1078908606365685908149415)
                      ·
                        rfl

theorem cell23_2101167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 1, 3].length) (baseStart_2101167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101167 prefixEnd_2101167 := by exact prefixLift 2101167
  have htrace : WordTrace (prefixWord ++ tailWord_2101167) baseStart_2101167 baseEnd_2101167 := by
    simpa [prefixWord, tailWord_2101167, baseEnd_2101167] using wordTrace_append hprefix tailTrace_2101167
  have hstable : (prefixWord ++ tailWord_2101167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101167).length < 2 ^ (prefixWord ++ tailWord_2101167).sum := by decide
  have hdescent : baseEnd_2101167 < baseStart_2101167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101183 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 2, 6]
def baseStart_2101183 : Nat := 118140960795 + 2101183 * 2 ^ 59
def prefixEnd_2101183 : Nat := 4983230072969 + 3 ^ 40 * 2101183 * 2
def baseEnd_2101183 : Nat := 359638940685385948516447

theorem tailTrace_2101183 : CollatzResearch.WordTrace tailWord_2101183 prefixEnd_2101183 359638940685385948516447 := by
  unfold tailWord_2101183
  simp only [CollatzResearch.WordTrace]
  refine ⟨76636439946780319331724203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51090959964520212887816135 76636439946780319331724203)
  ·
    refine ⟨114954659920170478997586305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76636439946780319331724203 114954659920170478997586305)
    ·
      refine ⟨86215994940127859248189729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114954659920170478997586305 86215994940127859248189729)
      ·
        refine ⟨64661996205095894436142297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86215994940127859248189729 64661996205095894436142297)
        ·
          refine ⟨48496497153821920827106723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64661996205095894436142297 48496497153821920827106723)
          ·
            refine ⟨72744745730732881240660085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48496497153821920827106723 72744745730732881240660085)
            ·
              refine ⟨6819819912256207616311883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72744745730732881240660085 6819819912256207616311883)
              ·
                refine ⟨10229729868384311424467825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6819819912256207616311883 10229729868384311424467825)
                ·
                  refine ⟨7672297401288233568350869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10229729868384311424467825 7672297401288233568350869)
                  ·
                    refine ⟨359638940685385948516447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7672297401288233568350869 359638940685385948516447)
                    ·
                      rfl

theorem cell23_2101183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 6].length) (baseStart_2101183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101183 prefixEnd_2101183 := by exact prefixLift 2101183
  have htrace : WordTrace (prefixWord ++ tailWord_2101183) baseStart_2101183 baseEnd_2101183 := by
    simpa [prefixWord, tailWord_2101183, baseEnd_2101183] using wordTrace_append hprefix tailTrace_2101183
  have hstable : (prefixWord ++ tailWord_2101183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101183).length < 2 ^ (prefixWord ++ tailWord_2101183).sum := by decide
  have hdescent : baseEnd_2101183 < baseStart_2101183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101207 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 4, 2, 2]
def baseStart_2101207 : Nat := 118140960795 + 2101207 * 2 ^ 59
def prefixEnd_2101207 : Nat := 4983230072969 + 3 ^ 40 * 2101207 * 2
def baseEnd_2101207 : Nat := 1078929145591865751649231

theorem tailTrace_2101207 : CollatzResearch.WordTrace tailWord_2101207 prefixEnd_2101207 1078929145591865751649231 := by
  unfold tailWord_2101207
  simp only [CollatzResearch.WordTrace]
  refine ⟨76637315298693371430597875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51091543532462247620398583 76637315298693371430597875)
  ·
    refine ⟨114955972948040057145896813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76637315298693371430597875 114955972948040057145896813)
    ·
      refine ⟨43108489855515021429711305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114955972948040057145896813 43108489855515021429711305)
      ·
        refine ⟨32331367391636266072283479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43108489855515021429711305 32331367391636266072283479)
        ·
          refine ⟨48497051087454399108425219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32331367391636266072283479 48497051087454399108425219)
          ·
            refine ⟨72745576631181598662637829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48497051087454399108425219 72745576631181598662637829)
            ·
              refine ⟨13639795618346549749244593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72745576631181598662637829 13639795618346549749244593)
              ·
                refine ⟨10229846713759912311933445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13639795618346549749244593 10229846713759912311933445)
                ·
                  refine ⟨1918096258829983558487521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10229846713759912311933445 1918096258829983558487521)
                  ·
                    refine ⟨1438572194122487668865641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1918096258829983558487521 1438572194122487668865641)
                    ·
                      refine ⟨1078929145591865751649231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1438572194122487668865641 1078929145591865751649231)
                      ·
                        rfl

theorem cell23_2101207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 2, 2].length) (baseStart_2101207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101207 prefixEnd_2101207 := by exact prefixLift 2101207
  have htrace : WordTrace (prefixWord ++ tailWord_2101207) baseStart_2101207 baseEnd_2101207 := by
    simpa [prefixWord, tailWord_2101207, baseEnd_2101207] using wordTrace_append hprefix tailTrace_2101207
  have hstable : (prefixWord ++ tailWord_2101207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101207).length < 2 ^ (prefixWord ++ tailWord_2101207).sum := by decide
  have hdescent : baseEnd_2101207 < baseStart_2101207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101218 : List Nat := [3, 3, 3, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_2101218 : Nat := 118140960795 + 2101218 * 2 ^ 59
def prefixEnd_2101218 : Nat := 4983230072969 + 3 ^ 40 * 2101218 * 2
def baseEnd_2101218 : Nat := 1078934793879065208611681

theorem tailTrace_2101218 : CollatzResearch.WordTrace tailWord_2101218 prefixEnd_2101218 1078934793879065208611681 := by
  unfold tailWord_2101218
  simp only [CollatzResearch.WordTrace]
  refine ⟨19159429125413380077312077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51091811001102346872832205 19159429125413380077312077)
  ·
    refine ⟨7184785922030017528992029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19159429125413380077312077 7184785922030017528992029)
    ·
      refine ⟨2694294720761256573372011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7184785922030017528992029 2694294720761256573372011)
      ·
        refine ⟨4041442081141884860058017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2694294720761256573372011 4041442081141884860058017)
        ·
          refine ⟨3031081560856413645043513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4041442081141884860058017 3031081560856413645043513)
          ·
            refine ⟨2273311170642310233782635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3031081560856413645043513 2273311170642310233782635)
            ·
              refine ⟨3409966755963465350673953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2273311170642310233782635 3409966755963465350673953)
              ·
                refine ⟨2557475066972599013005465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3409966755963465350673953 2557475066972599013005465)
                ·
                  refine ⟨1918106300229449259754099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2557475066972599013005465 1918106300229449259754099)
                  ·
                    refine ⟨2877159450344173889631149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1918106300229449259754099 2877159450344173889631149)
                    ·
                      refine ⟨1078934793879065208611681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2877159450344173889631149 1078934793879065208611681)
                      ·
                        rfl

theorem cell23_2101218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_2101218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101218 prefixEnd_2101218 := by exact prefixLift 2101218
  have htrace : WordTrace (prefixWord ++ tailWord_2101218) baseStart_2101218 baseEnd_2101218 := by
    simpa [prefixWord, tailWord_2101218, baseEnd_2101218] using wordTrace_append hprefix tailTrace_2101218
  have hstable : (prefixWord ++ tailWord_2101218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101218).length < 2 ^ (prefixWord ++ tailWord_2101218).sum := by decide
  have hdescent : baseEnd_2101218 < baseStart_2101218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101230 : List Nat := [4, 1, 2, 1, 3, 1, 1, 3, 7]
def baseStart_2101230 : Nat := 118140960795 + 2101230 * 2 ^ 59
def prefixEnd_2101230 : Nat := 4983230072969 + 3 ^ 40 * 2101230 * 2
def baseEnd_2101230 : Nat := 119882328405213240184625

theorem tailTrace_2101230 : CollatzResearch.WordTrace tailWord_2101230 prefixEnd_2101230 119882328405213240184625 := by
  unfold tailWord_2101230
  simp only [CollatzResearch.WordTrace]
  refine ⟨9579769272201255794835643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51092102785073364239123429 9579769272201255794835643)
  ·
    refine ⟨14369653908301883692253465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9579769272201255794835643 14369653908301883692253465)
    ·
      refine ⟨10777240431226412769190099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14369653908301883692253465 10777240431226412769190099)
      ·
        refine ⟨16165860646839619153785149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10777240431226412769190099 16165860646839619153785149)
        ·
          refine ⟨6062197742564857182669431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16165860646839619153785149 6062197742564857182669431)
          ·
            refine ⟨9093296613847285774004147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6062197742564857182669431 9093296613847285774004147)
            ·
              refine ⟨13639944920770928661006221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9093296613847285774004147 13639944920770928661006221)
              ·
                refine ⟨5114979345289098247877333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13639944920770928661006221 5114979345289098247877333)
                ·
                  refine ⟨119882328405213240184625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5114979345289098247877333 119882328405213240184625)
                  ·
                    rfl

theorem cell23_2101230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_2101230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101230 prefixEnd_2101230 := by exact prefixLift 2101230
  have htrace : WordTrace (prefixWord ++ tailWord_2101230) baseStart_2101230 baseEnd_2101230 := by
    simpa [prefixWord, tailWord_2101230, baseEnd_2101230] using wordTrace_append hprefix tailTrace_2101230
  have hstable : (prefixWord ++ tailWord_2101230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101230).length < 2 ^ (prefixWord ++ tailWord_2101230).sum := by decide
  have hdescent : baseEnd_2101230 < baseStart_2101230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101240 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 2, 3, 3]
def baseStart_2101240 : Nat := 118140960795 + 2101240 * 2 ^ 59
def prefixEnd_2101240 : Nat := 4983230072969 + 3 ^ 40 * 2101240 * 2
def baseEnd_2101240 : Nat := 1078946090453464122536579

theorem tailTrace_2101240 : CollatzResearch.WordTrace tailWord_2101240 prefixEnd_2101240 1078946090453464122536579 := by
  unfold tailWord_2101240
  simp only [CollatzResearch.WordTrace]
  refine ⟨38319259453786909033274587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51092345938382545377699449 38319259453786909033274587)
  ·
    refine ⟨57478889180680363549911881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38319259453786909033274587 57478889180680363549911881)
    ·
      refine ⟨43109166885510272662433911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57478889180680363549911881 43109166885510272662433911)
      ·
        refine ⟨64663750328265408993650867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43109166885510272662433911 64663750328265408993650867)
        ·
          refine ⟨96995625492398113490476301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64663750328265408993650867 96995625492398113490476301)
          ·
            refine ⟨36373359559649292558928613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96995625492398113490476301 36373359559649292558928613)
            ·
              refine ⟨6820004917434242354799115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36373359559649292558928613 6820004917434242354799115)
              ·
                refine ⟨10230007376151363532198673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6820004917434242354799115 10230007376151363532198673)
                ·
                  refine ⟨7672505532113522649149005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10230007376151363532198673 7672505532113522649149005)
                  ·
                    refine ⟨2877189574542570993430877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7672505532113522649149005 2877189574542570993430877)
                    ·
                      refine ⟨1078946090453464122536579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2877189574542570993430877 1078946090453464122536579)
                      ·
                        rfl

theorem cell23_2101240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 2, 3, 3].length) (baseStart_2101240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101240 prefixEnd_2101240 := by exact prefixLift 2101240
  have htrace : WordTrace (prefixWord ++ tailWord_2101240) baseStart_2101240 baseEnd_2101240 := by
    simpa [prefixWord, tailWord_2101240, baseEnd_2101240] using wordTrace_append hprefix tailTrace_2101240
  have hstable : (prefixWord ++ tailWord_2101240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101240).length < 2 ^ (prefixWord ++ tailWord_2101240).sum := by decide
  have hdescent : baseEnd_2101240 < baseStart_2101240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101241 : List Nat := [1, 2, 1, 3, 1, 5, 3, 1, 2, 2, 2]
def baseStart_2101241 : Nat := 118140960795 + 2101241 * 2 ^ 59
def prefixEnd_2101241 : Nat := 4983230072969 + 3 ^ 40 * 2101241 * 2
def baseEnd_2101241 : Nat := 1078946603934118618624075

theorem tailTrace_2101241 : CollatzResearch.WordTrace tailWord_2101241 prefixEnd_2101241 1078946603934118618624075 := by
  unfold tailWord_2101241
  simp only [CollatzResearch.WordTrace]
  refine ⟨76638555380570195237335577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51092370253713463491557051 76638555380570195237335577)
  ·
    refine ⟨57478916535427646428001683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76638555380570195237335577 57478916535427646428001683)
    ·
      refine ⟨86218374803141469642002525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57478916535427646428001683 86218374803141469642002525)
      ·
        refine ⟨32331890551178051115750947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86218374803141469642002525 32331890551178051115750947)
        ·
          refine ⟨48497835826767076673626421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32331890551178051115750947 48497835826767076673626421)
          ·
            refine ⟨4546672108759413438152477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48497835826767076673626421 4546672108759413438152477)
            ·
              refine ⟨1705002040784780039307179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4546672108759413438152477 1705002040784780039307179)
              ·
                refine ⟨2557503061177170058960769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1705002040784780039307179 2557503061177170058960769)
                ·
                  refine ⟨1918127295882877544220577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2557503061177170058960769 1918127295882877544220577)
                  ·
                    refine ⟨1438595471912158158165433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1918127295882877544220577 1438595471912158158165433)
                    ·
                      refine ⟨1078946603934118618624075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1438595471912158158165433 1078946603934118618624075)
                      ·
                        rfl

theorem cell23_2101241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 2, 2, 2].length) (baseStart_2101241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101241 prefixEnd_2101241 := by exact prefixLift 2101241
  have htrace : WordTrace (prefixWord ++ tailWord_2101241) baseStart_2101241 baseEnd_2101241 := by
    simpa [prefixWord, tailWord_2101241, baseEnd_2101241] using wordTrace_append hprefix tailTrace_2101241
  have hstable : (prefixWord ++ tailWord_2101241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101241).length < 2 ^ (prefixWord ++ tailWord_2101241).sum := by decide
  have hdescent : baseEnd_2101241 < baseStart_2101241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101243 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 1, 7]
def baseStart_2101243 : Nat := 118140960795 + 2101243 * 2 ^ 59
def prefixEnd_2101243 : Nat := 4983230072969 + 3 ^ 40 * 2101243 * 2
def baseEnd_2101243 : Nat := 359649210298475870266355

theorem tailTrace_2101243 : CollatzResearch.WordTrace tailWord_2101243 prefixEnd_2101243 359649210298475870266355 := by
  unfold tailWord_2101243
  simp only [CollatzResearch.WordTrace]
  refine ⟨76638628326562949578908383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51092418884375299719272255 76638628326562949578908383)
  ·
    refine ⟨114957942489844424368362575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76638628326562949578908383 114957942489844424368362575)
    ·
      refine ⟨172436913734766636552543863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114957942489844424368362575 172436913734766636552543863)
      ·
        refine ⟨258655370602149954828815795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172436913734766636552543863 258655370602149954828815795)
        ·
          refine ⟨387983055903224932243223693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258655370602149954828815795 387983055903224932243223693)
          ·
            refine ⟨145493645963709349591208885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 387983055903224932243223693 145493645963709349591208885)
            ·
              refine ⟨13640029309097751524175833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 145493645963709349591208885 13640029309097751524175833)
              ·
                refine ⟨10230021981823313643131875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13640029309097751524175833 10230021981823313643131875)
                ·
                  refine ⟨15345032972734970464697813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10230021981823313643131875 15345032972734970464697813)
                  ·
                    refine ⟨359649210298475870266355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15345032972734970464697813 359649210298475870266355)
                    ·
                      rfl

theorem cell23_2101243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 7].length) (baseStart_2101243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101243 prefixEnd_2101243 := by exact prefixLift 2101243
  have htrace : WordTrace (prefixWord ++ tailWord_2101243) baseStart_2101243 baseEnd_2101243 := by
    simpa [prefixWord, tailWord_2101243, baseEnd_2101243] using wordTrace_append hprefix tailTrace_2101243
  have hstable : (prefixWord ++ tailWord_2101243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101243).length < 2 ^ (prefixWord ++ tailWord_2101243).sum := by decide
  have hdescent : baseEnd_2101243 < baseStart_2101243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101260 : List Nat := [2, 2, 1, 2, 3, 1, 2, 3, 2, 5]
def baseStart_2101260 : Nat := 118140960795 + 2101260 * 2 ^ 59
def prefixEnd_2101260 : Nat := 4983230072969 + 3 ^ 40 * 2101260 * 2
def baseEnd_2101260 : Nat := 359652120022184681428829

theorem tailTrace_2101260 : CollatzResearch.WordTrace tailWord_2101260 prefixEnd_2101260 359652120022184681428829 := by
  unfold tailWord_2101260
  simp only [CollatzResearch.WordTrace]
  refine ⟨38319624183750680741138617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51092832245000907654851489 38319624183750680741138617)
  ·
    refine ⟨28739718137813010555853963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38319624183750680741138617 28739718137813010555853963)
    ·
      refine ⟨43109577206719515833780945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28739718137813010555853963 43109577206719515833780945)
      ·
        refine ⟨32332182905039636875335709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43109577206719515833780945 32332182905039636875335709)
        ·
          refine ⟨12124568589389863828250891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32332182905039636875335709 12124568589389863828250891)
          ·
            refine ⟨18186852884084795742376337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12124568589389863828250891 18186852884084795742376337)
            ·
              refine ⟨13640139663063596806782253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18186852884084795742376337 13640139663063596806782253)
              ·
                refine ⟨5115052373648848802543345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13640139663063596806782253 5115052373648848802543345)
                ·
                  refine ⟨3836289280236636601907509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5115052373648848802543345 3836289280236636601907509)
                  ·
                    refine ⟨359652120022184681428829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3836289280236636601907509 359652120022184681428829)
                    ·
                      rfl

theorem cell23_2101260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_2101260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101260 prefixEnd_2101260 := by exact prefixLift 2101260
  have htrace : WordTrace (prefixWord ++ tailWord_2101260) baseStart_2101260 baseEnd_2101260 := by
    simpa [prefixWord, tailWord_2101260, baseEnd_2101260] using wordTrace_append hprefix tailTrace_2101260
  have hstable : (prefixWord ++ tailWord_2101260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101260).length < 2 ^ (prefixWord ++ tailWord_2101260).sum := by decide
  have hdescent : baseEnd_2101260 < baseStart_2101260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101261 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_2101261 : Nat := 118140960795 + 2101261 * 2 ^ 59
def prefixEnd_2101261 : Nat := 4983230072969 + 3 ^ 40 * 2101261 * 2
def baseEnd_2101261 : Nat := 1078956873547208540373983

theorem tailTrace_2101261 : CollatzResearch.WordTrace tailWord_2101261 prefixEnd_2101261 1078956873547208540373983 := by
  unfold tailWord_2101261
  simp only [CollatzResearch.WordTrace]
  refine ⟨76639284840497738653063637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51092856560331825768709091 76639284840497738653063637)
  ·
    refine ⟨1796233238449165749681179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 76639284840497738653063637 1796233238449165749681179)
    ·
      refine ⟨2694349857673748624521769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1796233238449165749681179 2694349857673748624521769)
      ·
        refine ⟨2020762393255311468391327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2694349857673748624521769 2020762393255311468391327)
        ·
          refine ⟨3031143589882967202586991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2020762393255311468391327 3031143589882967202586991)
          ·
            refine ⟨4546715384824450803880487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3031143589882967202586991 4546715384824450803880487)
            ·
              refine ⟨6820073077236676205820731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4546715384824450803880487 6820073077236676205820731)
              ·
                refine ⟨10230109615855014308731097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6820073077236676205820731 10230109615855014308731097)
                ·
                  refine ⟨7672582211891260731548323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10230109615855014308731097 7672582211891260731548323)
                  ·
                    refine ⟨11508873317836891097322485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7672582211891260731548323 11508873317836891097322485)
                    ·
                      refine ⟨1078956873547208540373983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11508873317836891097322485 1078956873547208540373983)
                      ·
                        rfl

theorem cell23_2101261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_2101261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101261 prefixEnd_2101261 := by exact prefixLift 2101261
  have htrace : WordTrace (prefixWord ++ tailWord_2101261) baseStart_2101261 baseEnd_2101261 := by
    simpa [prefixWord, tailWord_2101261, baseEnd_2101261] using wordTrace_append hprefix tailTrace_2101261
  have hstable : (prefixWord ++ tailWord_2101261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101261).length < 2 ^ (prefixWord ++ tailWord_2101261).sum := by decide
  have hdescent : baseEnd_2101261 < baseStart_2101261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101277 : List Nat := [1, 4, 2, 2, 2, 2, 1, 2, 2, 5]
def baseStart_2101277 : Nat := 118140960795 + 2101277 * 2 ^ 59
def prefixEnd_2101277 : Nat := 4983230072969 + 3 ^ 40 * 2101277 * 2
def baseEnd_2101277 : Nat := 359655029745893492591303

theorem tailTrace_2101277 : CollatzResearch.WordTrace tailWord_2101277 prefixEnd_2101277 359655029745893492591303 := by
  unfold tailWord_2101277
  simp only [CollatzResearch.WordTrace]
  refine ⟨76639868408439773385646085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51093245605626515590430723 76639868408439773385646085)
  ·
    refine ⟨14369975326582457509808641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76639868408439773385646085 14369975326582457509808641)
    ·
      refine ⟨10777481494936843132356481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14369975326582457509808641 10777481494936843132356481)
      ·
        refine ⟨8083111121202632349267361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10777481494936843132356481 8083111121202632349267361)
        ·
          refine ⟨6062333340901974261950521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8083111121202632349267361 6062333340901974261950521)
          ·
            refine ⟨4546750005676480696462891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6062333340901974261950521 4546750005676480696462891)
            ·
              refine ⟨6820125008514721044694337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4546750005676480696462891 6820125008514721044694337)
              ·
                refine ⟨5115093756386040783520753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6820125008514721044694337 5115093756386040783520753)
                ·
                  refine ⟨3836320317289530587640565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5115093756386040783520753 3836320317289530587640565)
                  ·
                    refine ⟨359655029745893492591303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3836320317289530587640565 359655029745893492591303)
                    ·
                      rfl

theorem cell23_2101277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_2101277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101277 prefixEnd_2101277 := by exact prefixLift 2101277
  have htrace : WordTrace (prefixWord ++ tailWord_2101277) baseStart_2101277 baseEnd_2101277 := by
    simpa [prefixWord, tailWord_2101277, baseEnd_2101277] using wordTrace_append hprefix tailTrace_2101277
  have hstable : (prefixWord ++ tailWord_2101277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101277).length < 2 ^ (prefixWord ++ tailWord_2101277).sum := by decide
  have hdescent : baseEnd_2101277 < baseStart_2101277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101381 : List Nat := [1, 3, 1, 1, 5, 1, 1, 5, 1, 1, 3]
def baseStart_2101381 : Nat := 118140960795 + 2101381 * 2 ^ 59
def prefixEnd_2101381 : Nat := 4983230072969 + 3 ^ 40 * 2101381 * 2
def baseEnd_2101381 : Nat := 1079018491225748070873431

theorem tailTrace_2101381 : CollatzResearch.WordTrace tailWord_2101381 prefixEnd_2101381 1079018491225748070873431 := by
  unfold tailWord_2101381
  simp only [CollatzResearch.WordTrace]
  refine ⟨76643661600062999147431997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51095774400041999431621331 76643661600062999147431997)
  ·
    refine ⟨28741373100023624680286999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76643661600062999147431997 28741373100023624680286999)
    ·
      refine ⟨43112059650035437020430499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28741373100023624680286999 43112059650035437020430499)
      ·
        refine ⟨64668089475053155530645749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43112059650035437020430499 64668089475053155530645749)
        ·
          refine ⟨6062633388286233330998039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64668089475053155530645749 6062633388286233330998039)
          ·
            refine ⟨9093950082429349996497059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6062633388286233330998039 9093950082429349996497059)
            ·
              refine ⟨13640925123644024994745589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9093950082429349996497059 13640925123644024994745589)
              ·
                refine ⟨1278836730341627343257399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13640925123644024994745589 1278836730341627343257399)
                ·
                  refine ⟨1918255095512441014886099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1278836730341627343257399 1918255095512441014886099)
                  ·
                    refine ⟨2877382643268661522329149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1918255095512441014886099 2877382643268661522329149)
                    ·
                      refine ⟨1079018491225748070873431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2877382643268661522329149 1079018491225748070873431)
                      ·
                        rfl

theorem cell23_2101381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 1, 1, 3].length) (baseStart_2101381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101381 prefixEnd_2101381 := by exact prefixLift 2101381
  have htrace : WordTrace (prefixWord ++ tailWord_2101381) baseStart_2101381 baseEnd_2101381 := by
    simpa [prefixWord, tailWord_2101381, baseEnd_2101381] using wordTrace_append hprefix tailTrace_2101381
  have hstable : (prefixWord ++ tailWord_2101381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101381).length < 2 ^ (prefixWord ++ tailWord_2101381).sum := by decide
  have hdescent : baseEnd_2101381 < baseStart_2101381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101384 : List Nat := [2, 1, 3, 4, 1, 2, 1, 3, 1, 5]
def baseStart_2101384 : Nat := 118140960795 + 2101384 * 2 ^ 59
def prefixEnd_2101384 : Nat := 4983230072969 + 3 ^ 40 * 2101384 * 2
def baseEnd_2101384 : Nat := 359673343889237186378639

theorem tailTrace_2101384 : CollatzResearch.WordTrace tailWord_2101384 prefixEnd_2101384 359673343889237186378639 := by
  unfold tailWord_2101384
  simp only [CollatzResearch.WordTrace]
  refine ⟨38321885509526065329895603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51095847346034753773194137 38321885509526065329895603)
  ·
    refine ⟨57482828264289097994843405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38321885509526065329895603 57482828264289097994843405)
    ·
      refine ⟨21556060599108411748066277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57482828264289097994843405 21556060599108411748066277)
      ·
        refine ⟨4041761362332827202762427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21556060599108411748066277 4041761362332827202762427)
        ·
          refine ⟨6062642043499240804143641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4041761362332827202762427 6062642043499240804143641)
          ·
            refine ⟨4546981532624430603107731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6062642043499240804143641 4546981532624430603107731)
            ·
              refine ⟨6820472298936645904661597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4546981532624430603107731 6820472298936645904661597)
              ·
                refine ⟨2557677112101242214248099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6820472298936645904661597 2557677112101242214248099)
                ·
                  refine ⟨3836515668151863321372149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2557677112101242214248099 3836515668151863321372149)
                  ·
                    refine ⟨359673343889237186378639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3836515668151863321372149 359673343889237186378639)
                    ·
                      rfl

theorem cell23_2101384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_2101384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101384 prefixEnd_2101384 := by exact prefixLift 2101384
  have htrace : WordTrace (prefixWord ++ tailWord_2101384) baseStart_2101384 baseEnd_2101384 := by
    simpa [prefixWord, tailWord_2101384, baseEnd_2101384] using wordTrace_append hprefix tailTrace_2101384
  have hstable : (prefixWord ++ tailWord_2101384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101384).length < 2 ^ (prefixWord ++ tailWord_2101384).sum := by decide
  have hdescent : baseEnd_2101384 < baseStart_2101384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101397 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 4, 4]
def baseStart_2101397 : Nat := 118140960795 + 2101397 * 2 ^ 59
def prefixEnd_2101397 : Nat := 4983230072969 + 3 ^ 40 * 2101397 * 2
def baseEnd_2101397 : Nat := 359675568972073336091119

theorem tailTrace_2101397 : CollatzResearch.WordTrace tailWord_2101397 prefixEnd_2101397 359675568972073336091119 := by
  unfold tailWord_2101397
  simp only [CollatzResearch.WordTrace]
  refine ⟨76644245168005033880014445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51096163445336689253342963 76644245168005033880014445)
  ·
    refine ⟨28741591938001887705005417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76644245168005033880014445 28741591938001887705005417)
    ·
      refine ⟨21556193953501415778754063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28741591938001887705005417 21556193953501415778754063)
      ·
        refine ⟨32334290930252123668131095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21556193953501415778754063 32334290930252123668131095)
        ·
          refine ⟨48501436395378185502196643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32334290930252123668131095 48501436395378185502196643)
          ·
            refine ⟨72752154593067278253294965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48501436395378185502196643 72752154593067278253294965)
            ·
              refine ⟨6820514493100057336246403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72752154593067278253294965 6820514493100057336246403)
              ·
                refine ⟨10230771739650086004369605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6820514493100057336246403 10230771739650086004369605)
                ·
                  refine ⟨1918269701184391125819301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10230771739650086004369605 1918269701184391125819301)
                  ·
                    refine ⟨359675568972073336091119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1918269701184391125819301 359675568972073336091119)
                    ·
                      rfl

theorem cell23_2101397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_2101397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101397 prefixEnd_2101397 := by exact prefixLift 2101397
  have htrace : WordTrace (prefixWord ++ tailWord_2101397) baseStart_2101397 baseEnd_2101397 := by
    simpa [prefixWord, tailWord_2101397, baseEnd_2101397] using wordTrace_append hprefix tailTrace_2101397
  have hstable : (prefixWord ++ tailWord_2101397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101397).length < 2 ^ (prefixWord ++ tailWord_2101397).sum := by decide
  have hdescent : baseEnd_2101397 < baseStart_2101397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101407 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 5]
def baseStart_2101407 : Nat := 118140960795 + 2101407 * 2 ^ 59
def prefixEnd_2101407 : Nat := 4983230072969 + 3 ^ 40 * 2101407 * 2
def baseEnd_2101407 : Nat := 1079031841722764969148311

theorem tailTrace_2101407 : CollatzResearch.WordTrace tailWord_2101407 prefixEnd_2101407 1079031841722764969148311 := by
  unfold tailWord_2101407
  simp only [CollatzResearch.WordTrace]
  refine ⟨76644609897968805587878475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51096406598645870391918983 76644609897968805587878475)
  ·
    refine ⟨114966914846953208381817713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76644609897968805587878475 114966914846953208381817713)
    ·
      refine ⟨86225186135214906286363285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114966914846953208381817713 86225186135214906286363285)
      ·
        refine ⟨4041805600088198732173279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 86225186135214906286363285 4041805600088198732173279)
        ·
          refine ⟨6062708400132298098259919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4041805600088198732173279 6062708400132298098259919)
          ·
            refine ⟨9094062600198447147389879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6062708400132298098259919 9094062600198447147389879)
            ·
              refine ⟨13641093900297670721084819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9094062600198447147389879 13641093900297670721084819)
              ·
                refine ⟨20461640850446506081627229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13641093900297670721084819 20461640850446506081627229)
                ·
                  refine ⟨7673115318917439780610211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20461640850446506081627229 7673115318917439780610211)
                  ·
                    refine ⟨11509672978376159670915317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7673115318917439780610211 11509672978376159670915317)
                    ·
                      refine ⟨1079031841722764969148311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11509672978376159670915317 1079031841722764969148311)
                      ·
                        rfl

theorem cell23_2101407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_2101407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101407 prefixEnd_2101407 := by exact prefixLift 2101407
  have htrace : WordTrace (prefixWord ++ tailWord_2101407) baseStart_2101407 baseEnd_2101407 := by
    simpa [prefixWord, tailWord_2101407, baseEnd_2101407] using wordTrace_append hprefix tailTrace_2101407
  have hstable : (prefixWord ++ tailWord_2101407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101407).length < 2 ^ (prefixWord ++ tailWord_2101407).sum := by decide
  have hdescent : baseEnd_2101407 < baseStart_2101407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101421 : List Nat := [1, 5, 2, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_2101421 : Nat := 118140960795 + 2101421 * 2 ^ 59
def prefixEnd_2101421 : Nat := 4983230072969 + 3 ^ 40 * 2101421 * 2
def baseEnd_2101421 : Nat := 1079039030451927914373247

theorem tailTrace_2101421 : CollatzResearch.WordTrace tailWord_2101421 prefixEnd_2101421 1079039030451927914373247 := by
  unfold tailWord_2101421
  simp only [CollatzResearch.WordTrace]
  refine ⟨76645120519918085978888117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51096747013278723985925411 76645120519918085978888117)
  ·
    refine ⟨7185480048742320560520761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76645120519918085978888117 7185480048742320560520761)
    ·
      refine ⟨5389110036556740420390571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7185480048742320560520761 5389110036556740420390571)
      ·
        refine ⟨8083665054835110630585857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5389110036556740420390571 8083665054835110630585857)
        ·
          refine ⟨6062748791126332972939393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8083665054835110630585857 6062748791126332972939393)
          ·
            refine ⟨4547061593344749729704545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6062748791126332972939393 4547061593344749729704545)
            ·
              refine ⟨3410296195008562297278409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4547061593344749729704545 3410296195008562297278409)
              ·
                refine ⟨2557722146256421722958807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3410296195008562297278409 2557722146256421722958807)
                ·
                  refine ⟨3836583219384632584438211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2557722146256421722958807 3836583219384632584438211)
                  ·
                    refine ⟨5754874829076948876657317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3836583219384632584438211 5754874829076948876657317)
                    ·
                      refine ⟨1079039030451927914373247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5754874829076948876657317 1079039030451927914373247)
                      ·
                        rfl

theorem cell23_2101421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_2101421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101421 prefixEnd_2101421 := by exact prefixLift 2101421
  have htrace : WordTrace (prefixWord ++ tailWord_2101421) baseStart_2101421 baseEnd_2101421 := by
    simpa [prefixWord, tailWord_2101421, baseEnd_2101421] using wordTrace_append hprefix tailTrace_2101421
  have hstable : (prefixWord ++ tailWord_2101421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101421).length < 2 ^ (prefixWord ++ tailWord_2101421).sum := by decide
  have hdescent : baseEnd_2101421 < baseStart_2101421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101437 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 3, 3, 3]
def baseStart_2101437 : Nat := 118140960795 + 2101437 * 2 ^ 59
def prefixEnd_2101437 : Nat := 4983230072969 + 3 ^ 40 * 2101437 * 2
def baseEnd_2101437 : Nat := 1079047246142399851773173

theorem tailTrace_2101437 : CollatzResearch.WordTrace tailWord_2101437 prefixEnd_2101437 1079047246142399851773173 := by
  unfold tailWord_2101437
  simp only [CollatzResearch.WordTrace]
  refine ⟨76645704087860120711470565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51097136058573413807647043 76645704087860120711470565)
  ·
    refine ⟨14371069516473772633400731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76645704087860120711470565 14371069516473772633400731)
    ·
      refine ⟨21556604274710658950101097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14371069516473772633400731 21556604274710658950101097)
      ·
        refine ⟨16167453206032994212575823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21556604274710658950101097 16167453206032994212575823)
        ·
          refine ⟨24251179809049491318863735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16167453206032994212575823 24251179809049491318863735)
          ·
            refine ⟨36376769713574236978295603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24251179809049491318863735 36376769713574236978295603)
            ·
              refine ⟨54565154570361355467443405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36376769713574236978295603 54565154570361355467443405)
              ·
                refine ⟨20461932963885508300291277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54565154570361355467443405 20461932963885508300291277)
                ·
                  refine ⟨7673224861457065612609229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20461932963885508300291277 7673224861457065612609229)
                  ·
                    refine ⟨2877459323046399604728461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7673224861457065612609229 2877459323046399604728461)
                    ·
                      refine ⟨1079047246142399851773173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2877459323046399604728461 1079047246142399851773173)
                      ·
                        rfl

theorem cell23_2101437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_2101437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101437 prefixEnd_2101437 := by exact prefixLift 2101437
  have htrace : WordTrace (prefixWord ++ tailWord_2101437) baseStart_2101437 baseEnd_2101437 := by
    simpa [prefixWord, tailWord_2101437, baseEnd_2101437] using wordTrace_append hprefix tailTrace_2101437
  have hstable : (prefixWord ++ tailWord_2101437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101437).length < 2 ^ (prefixWord ++ tailWord_2101437).sum := by decide
  have hdescent : baseEnd_2101437 < baseStart_2101437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101441 : List Nat := [1, 2, 6, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_2101441 : Nat := 118140960795 + 2101441 * 2 ^ 59
def prefixEnd_2101441 : Nat := 4983230072969 + 3 ^ 40 * 2101441 * 2
def baseEnd_2101441 : Nat := 1079049300065017836123155

theorem tailTrace_2101441 : CollatzResearch.WordTrace tailWord_2101441 prefixEnd_2101441 1079049300065017836123155 := by
  unfold tailWord_2101441
  simp only [CollatzResearch.WordTrace]
  refine ⟨76645849979845629394616177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51097233319897086263077451 76645849979845629394616177)
  ·
    refine ⟨57484387484884222045962133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76645849979845629394616177 57484387484884222045962133)
    ·
      refine ⟨2694580663353947908404475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57484387484884222045962133 2694580663353947908404475)
      ·
        refine ⟨4041870995030921862606713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2694580663353947908404475 4041870995030921862606713)
        ·
          refine ⟨3031403246273191396955035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4041870995030921862606713 3031403246273191396955035)
          ·
            refine ⟨4547104869409787095432553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3031403246273191396955035 4547104869409787095432553)
            ·
              refine ⟨3410328652057340321574415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4547104869409787095432553 3410328652057340321574415)
              ·
                refine ⟨5115492978086010482361623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3410328652057340321574415 5115492978086010482361623)
                ·
                  refine ⟨7673239467129015723542435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5115492978086010482361623 7673239467129015723542435)
                  ·
                    refine ⟨11509859200693523585313653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7673239467129015723542435 11509859200693523585313653)
                    ·
                      refine ⟨1079049300065017836123155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11509859200693523585313653 1079049300065017836123155)
                      ·
                        rfl

theorem cell23_2101441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_2101441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101441 prefixEnd_2101441 := by exact prefixLift 2101441
  have htrace : WordTrace (prefixWord ++ tailWord_2101441) baseStart_2101441 baseEnd_2101441 := by
    simpa [prefixWord, tailWord_2101441, baseEnd_2101441] using wordTrace_append hprefix tailTrace_2101441
  have hstable : (prefixWord ++ tailWord_2101441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101441).length < 2 ^ (prefixWord ++ tailWord_2101441).sum := by decide
  have hdescent : baseEnd_2101441 < baseStart_2101441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101475 : List Nat := [1, 1, 1, 8, 2, 1, 1, 2, 1, 2, 3]
def baseStart_2101475 : Nat := 118140960795 + 2101475 * 2 ^ 59
def prefixEnd_2101475 : Nat := 4983230072969 + 3 ^ 40 * 2101475 * 2
def baseEnd_2101475 : Nat := 1079066758407270703097999

theorem tailTrace_2101475 : CollatzResearch.WordTrace tailWord_2101475 prefixEnd_2101475 1079066758407270703097999 := by
  unfold tailWord_2101475
  simp only [CollatzResearch.WordTrace]
  refine ⟨76647090061722453201353879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51098060041148302134235919 76647090061722453201353879)
  ·
    refine ⟨114970635092583679802030819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76647090061722453201353879 114970635092583679802030819)
    ·
      refine ⟨172455952638875519703046229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114970635092583679802030819 172455952638875519703046229)
      ·
        refine ⟨2020968194986822496520073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 172455952638875519703046229 2020968194986822496520073)
        ·
          refine ⟨1515726146240116872390055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2020968194986822496520073 1515726146240116872390055)
          ·
            refine ⟨2273589219360175308585083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1515726146240116872390055 2273589219360175308585083)
            ·
              refine ⟨3410383829040262962877625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2273589219360175308585083 3410383829040262962877625)
              ·
                refine ⟨2557787871780197222158219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3410383829040262962877625 2557787871780197222158219)
                ·
                  refine ⟨3836681807670295833237329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2557787871780197222158219 3836681807670295833237329)
                  ·
                    refine ⟨2877511355752721874927997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3836681807670295833237329 2877511355752721874927997)
                    ·
                      refine ⟨1079066758407270703097999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2877511355752721874927997 1079066758407270703097999)
                      ·
                        rfl

theorem cell23_2101475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_2101475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101475 prefixEnd_2101475 := by exact prefixLift 2101475
  have htrace : WordTrace (prefixWord ++ tailWord_2101475) baseStart_2101475 baseEnd_2101475 := by
    simpa [prefixWord, tailWord_2101475, baseEnd_2101475] using wordTrace_append hprefix tailTrace_2101475
  have hstable : (prefixWord ++ tailWord_2101475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101475).length < 2 ^ (prefixWord ++ tailWord_2101475).sum := by decide
  have hdescent : baseEnd_2101475 < baseStart_2101475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101498 : List Nat := [3, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2]
def baseStart_2101498 : Nat := 118140960795 + 2101498 * 2 ^ 59
def prefixEnd_2101498 : Nat := 4983230072969 + 3 ^ 40 * 2101498 * 2
def baseEnd_2101498 : Nat := 1079078568462324113110393

theorem tailTrace_2101498 : CollatzResearch.WordTrace tailWord_2101498 prefixEnd_2101498 1079078568462324113110393 := by
  unfold tailWord_2101498
  simp only [CollatzResearch.WordTrace]
  refine ⟨19161982235159782032360287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51098619293759418752960765 19161982235159782032360287)
  ·
    refine ⟨28742973352739673048540431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19161982235159782032360287 28742973352739673048540431)
    ·
      refine ⟨43114460029109509572810647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28742973352739673048540431 43114460029109509572810647)
      ·
        refine ⟨64671690043664264359215971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43114460029109509572810647 64671690043664264359215971)
        ·
          refine ⟨97007535065496396538823957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64671690043664264359215971 97007535065496396538823957)
          ·
            refine ⟨4547228206195143587757373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 97007535065496396538823957 4547228206195143587757373)
            ·
              refine ⟨1705210577323178845409015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4547228206195143587757373 1705210577323178845409015)
              ·
                refine ⟨2557815865984768268113523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1705210577323178845409015 2557815865984768268113523)
                ·
                  refine ⟨3836723798977152402170285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2557815865984768268113523 3836723798977152402170285)
                  ·
                    refine ⟨1438771424616432150813857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3836723798977152402170285 1438771424616432150813857)
                    ·
                      refine ⟨1079078568462324113110393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1438771424616432150813857 1079078568462324113110393)
                      ·
                        rfl

theorem cell23_2101498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2].length) (baseStart_2101498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101498 prefixEnd_2101498 := by exact prefixLift 2101498
  have htrace : WordTrace (prefixWord ++ tailWord_2101498) baseStart_2101498 baseEnd_2101498 := by
    simpa [prefixWord, tailWord_2101498, baseEnd_2101498] using wordTrace_append hprefix tailTrace_2101498
  have hstable : (prefixWord ++ tailWord_2101498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101498).length < 2 ^ (prefixWord ++ tailWord_2101498).sum := by decide
  have hdescent : baseEnd_2101498 < baseStart_2101498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101507 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 4]
def baseStart_2101507 : Nat := 118140960795 + 2101507 * 2 ^ 59
def prefixEnd_2101507 : Nat := 4983230072969 + 3 ^ 40 * 2101507 * 2
def baseEnd_2101507 : Nat := 1079083189788214577897851

theorem tailTrace_2101507 : CollatzResearch.WordTrace tailWord_2101507 prefixEnd_2101507 1079083189788214577897851 := by
  unfold tailWord_2101507
  simp only [CollatzResearch.WordTrace]
  refine ⟨76648257197606522666518775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51098838131737681777679183 76648257197606522666518775)
  ·
    refine ⟨114972385796409783999778163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76648257197606522666518775 114972385796409783999778163)
    ·
      refine ⟨172458578694614675999667245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114972385796409783999778163 172458578694614675999667245)
      ·
        refine ⟨64671967010480503499875217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172458578694614675999667245 64671967010480503499875217)
        ·
          refine ⟨48503975257860377624906413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64671967010480503499875217 48503975257860377624906413)
          ·
            refine ⟨18188990721697641609339905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48503975257860377624906413 18188990721697641609339905)
            ·
              refine ⟨13641743041273231207004929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18188990721697641609339905 13641743041273231207004929)
              ·
                refine ⟨10231307280954923405253697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13641743041273231207004929 10231307280954923405253697)
                ·
                  refine ⟨7673480460716192553940273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10231307280954923405253697 7673480460716192553940273)
                  ·
                    refine ⟨5755110345537144415455205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7673480460716192553940273 5755110345537144415455205)
                    ·
                      refine ⟨1079083189788214577897851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5755110345537144415455205 1079083189788214577897851)
                      ·
                        rfl

theorem cell23_2101507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_2101507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101507 prefixEnd_2101507 := by exact prefixLift 2101507
  have htrace : WordTrace (prefixWord ++ tailWord_2101507) baseStart_2101507 baseEnd_2101507 := by
    simpa [prefixWord, tailWord_2101507, baseEnd_2101507] using wordTrace_append hprefix tailTrace_2101507
  have hstable : (prefixWord ++ tailWord_2101507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101507).length < 2 ^ (prefixWord ++ tailWord_2101507).sum := by decide
  have hdescent : baseEnd_2101507 < baseStart_2101507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101549 : List Nat := [1, 5, 3, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_2101549 : Nat := 118140960795 + 2101549 * 2 ^ 59
def prefixEnd_2101549 : Nat := 4983230072969 + 3 ^ 40 * 2101549 * 2
def baseEnd_2101549 : Nat := 1079104755975703413572659

theorem tailTrace_2101549 : CollatzResearch.WordTrace tailWord_2101549 prefixEnd_2101549 1079104755975703413572659 := by
  unfold tailWord_2101549
  simp only [CollatzResearch.WordTrace]
  refine ⟨76649789063454363839547701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51099859375636242559698467 76649789063454363839547701)
  ·
    refine ⟨7185917724698846609957597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76649789063454363839547701 7185917724698846609957597)
    ·
      refine ⟨2694719146762067478734099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7185917724698846609957597 2694719146762067478734099)
      ·
        refine ⟨4042078720143101218101149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2694719146762067478734099 4042078720143101218101149)
        ·
          refine ⟨1515779520053662956787931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4042078720143101218101149 1515779520053662956787931)
          ·
            refine ⟨2273669280080494435181897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1515779520053662956787931 2273669280080494435181897)
            ·
              refine ⟨1705251960060370826386423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2273669280080494435181897 1705251960060370826386423)
              ·
                refine ⟨2557877940090556239579635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1705251960060370826386423 2557877940090556239579635)
                ·
                  refine ⟨3836816910135834359369453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2557877940090556239579635 3836816910135834359369453)
                  ·
                    refine ⟨1438806341300937884763545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3836816910135834359369453 1438806341300937884763545)
                    ·
                      refine ⟨1079104755975703413572659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1438806341300937884763545 1079104755975703413572659)
                      ·
                        rfl

theorem cell23_2101549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_2101549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101549 prefixEnd_2101549 := by exact prefixLift 2101549
  have htrace : WordTrace (prefixWord ++ tailWord_2101549) baseStart_2101549 baseEnd_2101549 := by
    simpa [prefixWord, tailWord_2101549, baseEnd_2101549] using wordTrace_append hprefix tailTrace_2101549
  have hstable : (prefixWord ++ tailWord_2101549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101549).length < 2 ^ (prefixWord ++ tailWord_2101549).sum := by decide
  have hdescent : baseEnd_2101549 < baseStart_2101549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101604 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 1, 4, 3]
def baseStart_2101604 : Nat := 118140960795 + 2101604 * 2 ^ 59
def prefixEnd_2101604 : Nat := 4983230072969 + 3 ^ 40 * 2101604 * 2
def baseEnd_2101604 : Nat := 1079132997411700698384905

theorem tailTrace_2101604 : CollatzResearch.WordTrace tailWord_2101604 prefixEnd_2101604 1079132997411700698384905 := by
  unfold tailWord_2101604
  simp only [CollatzResearch.WordTrace]
  refine ⟨38325897539127554116399933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51101196718836738821866577 38325897539127554116399933)
  ·
    refine ⟨14372211577172832793649975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38325897539127554116399933 14372211577172832793649975)
    ·
      refine ⟨21558317365759249190474963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14372211577172832793649975 21558317365759249190474963)
      ·
        refine ⟨32337476048638873785712445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21558317365759249190474963 32337476048638873785712445)
        ·
          refine ⟨12126553518239577669642167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32337476048638873785712445 12126553518239577669642167)
          ·
            refine ⟨18189830277359366504463251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12126553518239577669642167 18189830277359366504463251)
            ·
              refine ⟨27284745416039049756694877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18189830277359366504463251 27284745416039049756694877)
              ·
                refine ⟨10231779531014643658760579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27284745416039049756694877 10231779531014643658760579)
                ·
                  refine ⟨15347669296521965488140869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10231779531014643658760579 15347669296521965488140869)
                  ·
                    refine ⟨2877687993097868529026413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15347669296521965488140869 2877687993097868529026413)
                    ·
                      refine ⟨1079132997411700698384905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2877687993097868529026413 1079132997411700698384905)
                      ·
                        rfl

theorem cell23_2101604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_2101604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101604 prefixEnd_2101604 := by exact prefixLift 2101604
  have htrace : WordTrace (prefixWord ++ tailWord_2101604) baseStart_2101604 baseEnd_2101604 := by
    simpa [prefixWord, tailWord_2101604, baseEnd_2101604] using wordTrace_append hprefix tailTrace_2101604
  have hstable : (prefixWord ++ tailWord_2101604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101604).length < 2 ^ (prefixWord ++ tailWord_2101604).sum := by decide
  have hdescent : baseEnd_2101604 < baseStart_2101604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101621 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_2101621 : Nat := 118140960795 + 2101621 * 2 ^ 59
def prefixEnd_2101621 : Nat := 4983230072969 + 3 ^ 40 * 2101621 * 2
def baseEnd_2101621 : Nat := 1079141726582827131872327

theorem tailTrace_2101621 : CollatzResearch.WordTrace tailWord_2101621 prefixEnd_2101621 1079141726582827131872327 := by
  unfold tailWord_2101621
  simp only [CollatzResearch.WordTrace]
  refine ⟨76652415119193520136168717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51101610079462346757445811 76652415119193520136168717)
  ·
    refine ⟨28744655669697570051063269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76652415119193520136168717 28744655669697570051063269)
    ·
      refine ⟨5389622938068294384574363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28744655669697570051063269 5389622938068294384574363)
      ·
        refine ⟨8084434407102441576861545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5389622938068294384574363 8084434407102441576861545)
        ·
          refine ⟨6063325805326831182646159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8084434407102441576861545 6063325805326831182646159)
          ·
            refine ⟨9094988707990246773969239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6063325805326831182646159 9094988707990246773969239)
            ·
              refine ⟨13642483061985370160953859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9094988707990246773969239 13642483061985370160953859)
              ·
                refine ⟨20463724592978055241430789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13642483061985370160953859 20463724592978055241430789)
                ·
                  refine ⟨3836948361183385357768273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20463724592978055241430789 3836948361183385357768273)
                  ·
                    refine ⟨2877711270887539018326205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3836948361183385357768273 2877711270887539018326205)
                    ·
                      refine ⟨1079141726582827131872327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2877711270887539018326205 1079141726582827131872327)
                      ·
                        rfl

theorem cell23_2101621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_2101621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101621 prefixEnd_2101621 := by exact prefixLift 2101621
  have htrace : WordTrace (prefixWord ++ tailWord_2101621) baseStart_2101621 baseEnd_2101621 := by
    simpa [prefixWord, tailWord_2101621, baseEnd_2101621] using wordTrace_append hprefix tailTrace_2101621
  have hstable : (prefixWord ++ tailWord_2101621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101621).length < 2 ^ (prefixWord ++ tailWord_2101621).sum := by decide
  have hdescent : baseEnd_2101621 < baseStart_2101621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101637 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 2, 9]
def baseStart_2101637 : Nat := 118140960795 + 2101637 * 2 ^ 59
def prefixEnd_2101637 : Nat := 4983230072969 + 3 ^ 40 * 2101637 * 2
def baseEnd_2101637 : Nat := 359716647424433023090751

theorem tailTrace_2101637 : CollatzResearch.WordTrace tailWord_2101637 prefixEnd_2101637 359716647424433023090751 := by
  unfold tailWord_2101637
  simp only [CollatzResearch.WordTrace]
  refine ⟨76652998687135554868751165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51101999124757036579167443 76652998687135554868751165)
  ·
    refine ⟨28744874507675833075781687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76652998687135554868751165 28744874507675833075781687)
    ·
      refine ⟨43117311761513749613672531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28744874507675833075781687 43117311761513749613672531)
      ·
        refine ⟨64675967642270624420508797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43117311761513749613672531 64675967642270624420508797)
        ·
          refine ⟨24253487865851484157690799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64675967642270624420508797 24253487865851484157690799)
          ·
            refine ⟨36380231798777226236536199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24253487865851484157690799 36380231798777226236536199)
            ·
              refine ⟨54570347698165839354804299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36380231798777226236536199 54570347698165839354804299)
              ·
                refine ⟨81855521547248759032206449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54570347698165839354804299 81855521547248759032206449)
                ·
                  refine ⟨61391641160436569274154837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81855521547248759032206449 61391641160436569274154837)
                  ·
                    refine ⟨359716647424433023090751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 61391641160436569274154837 359716647424433023090751)
                    ·
                      rfl

theorem cell23_2101637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_2101637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101637 prefixEnd_2101637 := by exact prefixLift 2101637
  have htrace : WordTrace (prefixWord ++ tailWord_2101637) baseStart_2101637 baseEnd_2101637 := by
    simpa [prefixWord, tailWord_2101637, baseEnd_2101637] using wordTrace_append hprefix tailTrace_2101637
  have hstable : (prefixWord ++ tailWord_2101637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101637).length < 2 ^ (prefixWord ++ tailWord_2101637).sum := by decide
  have hdescent : baseEnd_2101637 < baseStart_2101637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101641 : List Nat := [1, 2, 1, 1, 6, 1, 4, 1, 6]
def baseStart_2101641 : Nat := 118140960795 + 2101641 * 2 ^ 59
def prefixEnd_2101641 : Nat := 4983230072969 + 3 ^ 40 * 2101641 * 2
def baseEnd_2101641 : Nat := 119905777355101894846915

theorem tailTrace_2101641 : CollatzResearch.WordTrace tailWord_2101641 prefixEnd_2101641 119905777355101894846915 := by
  unfold tailWord_2101641
  simp only [CollatzResearch.WordTrace]
  refine ⟨76653144579121063551896777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51102096386080709034597851 76653144579121063551896777)
  ·
    refine ⟨57489858434340797663922583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76653144579121063551896777 57489858434340797663922583)
    ·
      refine ⟨86234787651511196495883875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57489858434340797663922583 86234787651511196495883875)
      ·
        refine ⟨129352181477266794743825813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86234787651511196495883875 129352181477266794743825813)
        ·
          refine ⟨6063383506746881003616835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 129352181477266794743825813 6063383506746881003616835)
          ·
            refine ⟨9095075260120321505425253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6063383506746881003616835 9095075260120321505425253)
            ·
              refine ⟨1705326611272560282267235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9095075260120321505425253 1705326611272560282267235)
              ·
                refine ⟨2557989916908840423400853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1705326611272560282267235 2557989916908840423400853)
                ·
                  refine ⟨119905777355101894846915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2557989916908840423400853 119905777355101894846915)
                  ·
                    rfl

theorem cell23_2101641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 6].length) (baseStart_2101641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101641 prefixEnd_2101641 := by exact prefixLift 2101641
  have htrace : WordTrace (prefixWord ++ tailWord_2101641) baseStart_2101641 baseEnd_2101641 := by
    simpa [prefixWord, tailWord_2101641, baseEnd_2101641] using wordTrace_append hprefix tailTrace_2101641
  have hstable : (prefixWord ++ tailWord_2101641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101641).length < 2 ^ (prefixWord ++ tailWord_2101641).sum := by decide
  have hdescent : baseEnd_2101641 < baseStart_2101641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101711 : List Nat := [1, 1, 2, 1, 1, 4, 1, 6, 1, 2, 3]
def baseStart_2101711 : Nat := 118140960795 + 2101711 * 2 ^ 59
def prefixEnd_2101711 : Nat := 4983230072969 + 3 ^ 40 * 2101711 * 2
def baseEnd_2101711 : Nat := 1079187939841731779746913

theorem tailTrace_2101711 : CollatzResearch.WordTrace tailWord_2101711 prefixEnd_2101711 1079187939841731779746913 := by
  unfold tailWord_2101711
  simp only [CollatzResearch.WordTrace]
  refine ⟨76655697688867465506944987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51103798459244977004629991 76655697688867465506944987)
  ·
    refine ⟨114983546533301198260417481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76655697688867465506944987 114983546533301198260417481)
    ·
      refine ⟨86237659899975898695313111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114983546533301198260417481 86237659899975898695313111)
      ·
        refine ⟨129356489849963848042969667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86237659899975898695313111 129356489849963848042969667)
        ·
          refine ⟨194034734774945772064454501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129356489849963848042969667 194034734774945772064454501)
          ·
            refine ⟨36381512770302332262085219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 194034734774945772064454501 36381512770302332262085219)
            ·
              refine ⟨54572269155453498393127829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36381512770302332262085219 54572269155453498393127829)
              ·
                refine ⟨2558075116661882737177867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54572269155453498393127829 2558075116661882737177867)
                ·
                  refine ⟨3837112674992824105766801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2558075116661882737177867 3837112674992824105766801)
                  ·
                    refine ⟨2877834506244618079325101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3837112674992824105766801 2877834506244618079325101)
                    ·
                      refine ⟨1079187939841731779746913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2877834506244618079325101 1079187939841731779746913)
                      ·
                        rfl

theorem cell23_2101711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 2, 3].length) (baseStart_2101711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101711 prefixEnd_2101711 := by exact prefixLift 2101711
  have htrace : WordTrace (prefixWord ++ tailWord_2101711) baseStart_2101711 baseEnd_2101711 := by
    simpa [prefixWord, tailWord_2101711, baseEnd_2101711] using wordTrace_append hprefix tailTrace_2101711
  have hstable : (prefixWord ++ tailWord_2101711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101711).length < 2 ^ (prefixWord ++ tailWord_2101711).sum := by decide
  have hdescent : baseEnd_2101711 < baseStart_2101711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101718 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_2101718 : Nat := 118140960795 + 2101718 * 2 ^ 59
def prefixEnd_2101718 : Nat := 4983230072969 + 3 ^ 40 * 2101718 * 2
def baseEnd_2101718 : Nat := 359730511402104417453127

theorem tailTrace_2101718 : CollatzResearch.WordTrace tailWord_2101718 prefixEnd_2101718 359730511402104417453127 := by
  unfold tailWord_2101718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4790997062490131606403113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51103968666561403801633205 4790997062490131606403113)
  ·
    refine ⟨3593247796867598704802335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4790997062490131606403113 3593247796867598704802335)
    ·
      refine ⟨5389871695301398057203503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3593247796867598704802335 5389871695301398057203503)
      ·
        refine ⟨8084807542952097085805255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5389871695301398057203503 8084807542952097085805255)
        ·
          refine ⟨12127211314428145628707883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8084807542952097085805255 12127211314428145628707883)
          ·
            refine ⟨18190816971642218443061825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12127211314428145628707883 18190816971642218443061825)
            ·
              refine ⟨13643112728731663832296369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18190816971642218443061825 13643112728731663832296369)
              ·
                refine ⟨10232334546548747874222277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13643112728731663832296369 10232334546548747874222277)
                ·
                  refine ⟨1918562727477890226416677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10232334546548747874222277 1918562727477890226416677)
                  ·
                    refine ⟨359730511402104417453127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1918562727477890226416677 359730511402104417453127)
                    ·
                      rfl

theorem cell23_2101718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_2101718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101718 prefixEnd_2101718 := by exact prefixLift 2101718
  have htrace : WordTrace (prefixWord ++ tailWord_2101718) baseStart_2101718 baseEnd_2101718 := by
    simpa [prefixWord, tailWord_2101718, baseEnd_2101718] using wordTrace_append hprefix tailTrace_2101718
  have hstable : (prefixWord ++ tailWord_2101718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101718).length < 2 ^ (prefixWord ++ tailWord_2101718).sum := by decide
  have hdescent : baseEnd_2101718 < baseStart_2101718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101742 : List Nat := [4, 1, 2, 1, 2, 2, 2, 4, 1, 2, 2]
def baseStart_2101742 : Nat := 118140960795 + 2101742 * 2 ^ 59
def prefixEnd_2101742 : Nat := 4983230072969 + 3 ^ 40 * 2101742 * 2
def baseEnd_2101742 : Nat := 1079203857742021158459271

theorem tailTrace_2101742 : CollatzResearch.WordTrace tailWord_2101742 prefixEnd_2101742 1079203857742021158459271 := by
  unfold tailWord_2101742
  simp only [CollatzResearch.WordTrace]
  refine ⟨9582103543969394725165435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51104552234503438534215653 9582103543969394725165435)
  ·
    refine ⟨14373155315954092087748153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9582103543969394725165435 14373155315954092087748153)
    ·
      refine ⟨10779866486965569065811115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14373155315954092087748153 10779866486965569065811115)
      ·
        refine ⟨16169799730448353598716673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10779866486965569065811115 16169799730448353598716673)
        ·
          refine ⟨12127349797836265199037505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16169799730448353598716673 12127349797836265199037505)
          ·
            refine ⟨9095512348377198899278129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12127349797836265199037505 9095512348377198899278129)
            ·
              refine ⟨6821634261282899174458597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9095512348377198899278129 6821634261282899174458597)
              ·
                refine ⟨1279056423990543595210987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6821634261282899174458597 1279056423990543595210987)
                ·
                  refine ⟨1918584635985815392816481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1279056423990543595210987 1918584635985815392816481)
                  ·
                    refine ⟨1438938476989361544612361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1918584635985815392816481 1438938476989361544612361)
                    ·
                      refine ⟨1079203857742021158459271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1438938476989361544612361 1079203857742021158459271)
                      ·
                        rfl

theorem cell23_2101742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_2101742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101742 prefixEnd_2101742 := by exact prefixLift 2101742
  have htrace : WordTrace (prefixWord ++ tailWord_2101742) baseStart_2101742 baseEnd_2101742 := by
    simpa [prefixWord, tailWord_2101742, baseEnd_2101742] using wordTrace_append hprefix tailTrace_2101742
  have hstable : (prefixWord ++ tailWord_2101742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101742).length < 2 ^ (prefixWord ++ tailWord_2101742).sum := by decide
  have hdescent : baseEnd_2101742 < baseStart_2101742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101762 : List Nat := [3, 4, 1, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_2101762 : Nat := 118140960795 + 2101762 * 2 ^ 59
def prefixEnd_2101762 : Nat := 4983230072969 + 3 ^ 40 * 2101762 * 2
def baseEnd_2101762 : Nat := 1079214127355111080209179

theorem tailTrace_2101762 : CollatzResearch.WordTrace tailWord_2101762 prefixEnd_2101762 1079214127355111080209179 := by
  unfold tailWord_2101762
  simp only [CollatzResearch.WordTrace]
  refine ⟨19164389452920675304262885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51105038541121800811367693 19164389452920675304262885)
  ·
    refine ⟨3593323022422626619549291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19164389452920675304262885 3593323022422626619549291)
    ·
      refine ⟨5389984533633939929323937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3593323022422626619549291 5389984533633939929323937)
      ·
        refine ⟨4042488400225454946992953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5389984533633939929323937 4042488400225454946992953)
        ·
          refine ⟨3031866300169091210244715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4042488400225454946992953 3031866300169091210244715)
          ·
            refine ⟨4547799450253636815367073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3031866300169091210244715 4547799450253636815367073)
            ·
              refine ⟨3410849587690227611525305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4547799450253636815367073 3410849587690227611525305)
              ·
                refine ⟨2558137190767670708643979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3410849587690227611525305 2558137190767670708643979)
                ·
                  refine ⟨3837205786151506062965969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2558137190767670708643979 3837205786151506062965969)
                  ·
                    refine ⟨2877904339613629547224477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3837205786151506062965969 2877904339613629547224477)
                    ·
                      refine ⟨1079214127355111080209179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2877904339613629547224477 1079214127355111080209179)
                      ·
                        rfl

theorem cell23_2101762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_2101762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101762 prefixEnd_2101762 := by exact prefixLift 2101762
  have htrace : WordTrace (prefixWord ++ tailWord_2101762) baseStart_2101762 baseEnd_2101762 := by
    simpa [prefixWord, tailWord_2101762, baseEnd_2101762] using wordTrace_append hprefix tailTrace_2101762
  have hstable : (prefixWord ++ tailWord_2101762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101762).length < 2 ^ (prefixWord ++ tailWord_2101762).sum := by decide
  have hdescent : baseEnd_2101762 < baseStart_2101762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101815 : List Nat := [1, 1, 3, 1, 2, 3, 3, 3, 2, 2, 2]
def baseStart_2101815 : Nat := 118140960795 + 2101815 * 2 ^ 59
def prefixEnd_2101815 : Nat := 4983230072969 + 3 ^ 40 * 2101815 * 2
def baseEnd_2101815 : Nat := 1079241341829799372846435

theorem tailTrace_2101815 : CollatzResearch.WordTrace tailWord_2101815 prefixEnd_2101815 1079241341829799372846435 := by
  unfold tailWord_2101815
  simp only [CollatzResearch.WordTrace]
  refine ⟨76659490880490691268730899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51106327253660460845820599 76659490880490691268730899)
  ·
    refine ⟨114989236320736036903096349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76659490880490691268730899 114989236320736036903096349)
    ·
      refine ⟨43120963620276013838661131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114989236320736036903096349 43120963620276013838661131)
      ·
        refine ⟨64681445430414020757991697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43120963620276013838661131 64681445430414020757991697)
        ·
          refine ⟨48511084072810515568493773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64681445430414020757991697 48511084072810515568493773)
          ·
            refine ⟨18191656527303943338185165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48511084072810515568493773 18191656527303943338185165)
            ·
              refine ⟨6821871197738978751819437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18191656527303943338185165 6821871197738978751819437)
              ·
                refine ⟨2558201699152117031932289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6821871197738978751819437 2558201699152117031932289)
                ·
                  refine ⟨1918651274364087773949217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2558201699152117031932289 1918651274364087773949217)
                  ·
                    refine ⟨1438988455773065830461913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1918651274364087773949217 1438988455773065830461913)
                    ·
                      refine ⟨1079241341829799372846435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1438988455773065830461913 1079241341829799372846435)
                      ·
                        rfl

theorem cell23_2101815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 2, 2].length) (baseStart_2101815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101815 prefixEnd_2101815 := by exact prefixLift 2101815
  have htrace : WordTrace (prefixWord ++ tailWord_2101815) baseStart_2101815 baseEnd_2101815 := by
    simpa [prefixWord, tailWord_2101815, baseEnd_2101815] using wordTrace_append hprefix tailTrace_2101815
  have hstable : (prefixWord ++ tailWord_2101815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101815).length < 2 ^ (prefixWord ++ tailWord_2101815).sum := by decide
  have hdescent : baseEnd_2101815 < baseStart_2101815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101871 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 4]
def baseStart_2101871 : Nat := 118140960795 + 2101871 * 2 ^ 59
def prefixEnd_2101871 : Nat := 4983230072969 + 3 ^ 40 * 2101871 * 2
def baseEnd_2101871 : Nat := 1079270096746451153746177

theorem tailTrace_2101871 : CollatzResearch.WordTrace tailWord_2101871 prefixEnd_2101871 1079270096746451153746177 := by
  unfold tailWord_2101871
  simp only [CollatzResearch.WordTrace]
  refine ⟨76661533368287812832769467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51107688912191875221846311 76661533368287812832769467)
  ·
    refine ⟨114992300052431719249154201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76661533368287812832769467 114992300052431719249154201)
    ·
      refine ⟨86244225039323789436865651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114992300052431719249154201 86244225039323789436865651)
      ·
        refine ⟨129366337558985684155298477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86244225039323789436865651 129366337558985684155298477)
        ·
          refine ⟨48512376584619631558236929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129366337558985684155298477 48512376584619631558236929)
          ·
            refine ⟨36384282438464723668677697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48512376584619631558236929 36384282438464723668677697)
            ·
              refine ⟨27288211828848542751508273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36384282438464723668677697 27288211828848542751508273)
              ·
                refine ⟨20466158871636407063631205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27288211828848542751508273 20466158871636407063631205)
                ·
                  refine ⟨3837404788431826324430851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20466158871636407063631205 3837404788431826324430851)
                  ·
                    refine ⟨5756107182647739486646277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3837404788431826324430851 5756107182647739486646277)
                    ·
                      refine ⟨1079270096746451153746177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5756107182647739486646277 1079270096746451153746177)
                      ·
                        rfl

theorem cell23_2101871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 4].length) (baseStart_2101871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101871 prefixEnd_2101871 := by exact prefixLift 2101871
  have htrace : WordTrace (prefixWord ++ tailWord_2101871) baseStart_2101871 baseEnd_2101871 := by
    simpa [prefixWord, tailWord_2101871, baseEnd_2101871] using wordTrace_append hprefix tailTrace_2101871
  have hstable : (prefixWord ++ tailWord_2101871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101871).length < 2 ^ (prefixWord ++ tailWord_2101871).sum := by decide
  have hdescent : baseEnd_2101871 < baseStart_2101871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101885 : List Nat := [1, 4, 1, 1, 5, 2, 1, 1, 2, 5]
def baseStart_2101885 : Nat := 118140960795 + 2101885 * 2 ^ 59
def prefixEnd_2101885 : Nat := 4983230072969 + 3 ^ 40 * 2101885 * 2
def baseEnd_2101885 : Nat := 359759095158538032990371

theorem tailTrace_2101885 : CollatzResearch.WordTrace tailWord_2101885 prefixEnd_2101885 359759095158538032990371 := by
  unfold tailWord_2101885
  simp only [CollatzResearch.WordTrace]
  refine ⟨76662043990237093223779109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51108029326824728815852739 76662043990237093223779109)
  ·
    refine ⟨14374133248169454979458583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76662043990237093223779109 14374133248169454979458583)
    ·
      refine ⟨21561199872254182469187875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14374133248169454979458583 21561199872254182469187875)
      ·
        refine ⟨32341799808381273703781813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21561199872254182469187875 32341799808381273703781813)
        ·
          refine ⟨3032043732035744409729545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32341799808381273703781813 3032043732035744409729545)
          ·
            refine ⟨2274032799026808307297159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3032043732035744409729545 2274032799026808307297159)
            ·
              refine ⟨3411049198540212460945739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2274032799026808307297159 3411049198540212460945739)
              ·
                refine ⟨5116573797810318691418609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3411049198540212460945739 5116573797810318691418609)
                ·
                  refine ⟨3837430348357739018563957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5116573797810318691418609 3837430348357739018563957)
                  ·
                    refine ⟨359759095158538032990371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3837430348357739018563957 359759095158538032990371)
                    ·
                      rfl

theorem cell23_2101885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_2101885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101885 prefixEnd_2101885 := by exact prefixLift 2101885
  have htrace : WordTrace (prefixWord ++ tailWord_2101885) baseStart_2101885 baseEnd_2101885 := by
    simpa [prefixWord, tailWord_2101885, baseEnd_2101885] using wordTrace_append hprefix tailTrace_2101885
  have hstable : (prefixWord ++ tailWord_2101885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101885).length < 2 ^ (prefixWord ++ tailWord_2101885).sum := by decide
  have hdescent : baseEnd_2101885 < baseStart_2101885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101888 : List Nat := [2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 4]
def baseStart_2101888 : Nat := 118140960795 + 2101888 * 2 ^ 59
def prefixEnd_2101888 : Nat := 4983230072969 + 3 ^ 40 * 2101888 * 2
def baseEnd_2101888 : Nat := 1079278825917577587233599

theorem tailTrace_2101888 : CollatzResearch.WordTrace tailWord_2101888 prefixEnd_2101888 1079278825917577587233599 := by
  unfold tailWord_2101888
  simp only [CollatzResearch.WordTrace]
  refine ⟨38331076704613112368069159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51108102272817483157425545 38331076704613112368069159)
  ·
    refine ⟨57496615056919668552103739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38331076704613112368069159 57496615056919668552103739)
    ·
      refine ⟨86244922585379502828155609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57496615056919668552103739 86244922585379502828155609)
      ·
        refine ⟨64683691939034627121116707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86244922585379502828155609 64683691939034627121116707)
        ·
          refine ⟨97025537908551940681675061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64683691939034627121116707 97025537908551940681675061)
          ·
            refine ⟨9096144178926744438907037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97025537908551940681675061 9096144178926744438907037)
            ·
              refine ⟨3411054067097529164590139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9096144178926744438907037 3411054067097529164590139)
              ·
                refine ⟨5116581100646293746885209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3411054067097529164590139 5116581100646293746885209)
                ·
                  refine ⟨3837435825484720310163907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5116581100646293746885209 3837435825484720310163907)
                  ·
                    refine ⟨5756153738227080465245861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3837435825484720310163907 5756153738227080465245861)
                    ·
                      refine ⟨1079278825917577587233599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5756153738227080465245861 1079278825917577587233599)
                      ·
                        rfl

theorem cell23_2101888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 4].length) (baseStart_2101888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101888 prefixEnd_2101888 := by exact prefixLift 2101888
  have htrace : WordTrace (prefixWord ++ tailWord_2101888) baseStart_2101888 baseEnd_2101888 := by
    simpa [prefixWord, tailWord_2101888, baseEnd_2101888] using wordTrace_append hprefix tailTrace_2101888
  have hstable : (prefixWord ++ tailWord_2101888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101888).length < 2 ^ (prefixWord ++ tailWord_2101888).sum := by decide
  have hdescent : baseEnd_2101888 < baseStart_2101888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101911 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 8]
def baseStart_2101911 : Nat := 118140960795 + 2101911 * 2 ^ 59
def prefixEnd_2101911 : Nat := 4983230072969 + 3 ^ 40 * 2101911 * 2
def baseEnd_2101911 : Nat := 119921181774736777471777

theorem tailTrace_2101911 : CollatzResearch.WordTrace tailWord_2101911 prefixEnd_2101911 119921181774736777471777 := by
  unfold tailWord_2101911
  simp only [CollatzResearch.WordTrace]
  refine ⟨76662992288142899664225587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51108661525428599776150391 76662992288142899664225587)
  ·
    refine ⟨114994488432214349496338381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76662992288142899664225587 114994488432214349496338381)
    ·
      refine ⟨43122933162080381061126893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114994488432214349496338381 43122933162080381061126893)
      ·
        refine ⟨16171099935780142897922585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43122933162080381061126893 16171099935780142897922585)
        ·
          refine ⟨12128324951835107173441939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16171099935780142897922585 12128324951835107173441939)
          ·
            refine ⟨18192487427752660760162909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12128324951835107173441939 18192487427752660760162909)
            ·
              refine ⟨6822182785407247785061091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18192487427752660760162909 6822182785407247785061091)
              ·
                refine ⟨10233274178110871677591637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6822182785407247785061091 10233274178110871677591637)
                ·
                  refine ⟨119921181774736777471777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10233274178110871677591637 119921181774736777471777)
                  ·
                    rfl

theorem cell23_2101911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 8].length) (baseStart_2101911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101911 prefixEnd_2101911 := by exact prefixLift 2101911
  have htrace : WordTrace (prefixWord ++ tailWord_2101911) baseStart_2101911 baseEnd_2101911 := by
    simpa [prefixWord, tailWord_2101911, baseEnd_2101911] using wordTrace_append hprefix tailTrace_2101911
  have hstable : (prefixWord ++ tailWord_2101911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101911).length < 2 ^ (prefixWord ++ tailWord_2101911).sum := by decide
  have hdescent : baseEnd_2101911 < baseStart_2101911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101918 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_2101918 : Nat := 118140960795 + 2101918 * 2 ^ 59
def prefixEnd_2101918 : Nat := 4983230072969 + 3 ^ 40 * 2101918 * 2
def baseEnd_2101918 : Nat := 1079294230337212469858461

theorem tailTrace_2101918 : CollatzResearch.WordTrace tailWord_2101918 prefixEnd_2101918 1079294230337212469858461 := by
  unfold tailWord_2101918
  simp only [CollatzResearch.WordTrace]
  refine ⟨9582905949889692482466301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51108831732745026573153605 9582905949889692482466301)
  ·
    refine ⟨3593589731208634680924863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9582905949889692482466301 3593589731208634680924863)
    ·
      refine ⟨5390384596812952021387295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3593589731208634680924863 5390384596812952021387295)
      ·
        refine ⟨8085576895219428032080943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5390384596812952021387295 8085576895219428032080943)
        ·
          refine ⟨12128365342829142048121415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8085576895219428032080943 12128365342829142048121415)
          ·
            refine ⟨18192548014243713072182123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12128365342829142048121415 18192548014243713072182123)
            ·
              refine ⟨27288822021365569608273185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18192548014243713072182123 27288822021365569608273185)
              ·
                refine ⟨20466616516024177206204889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27288822021365569608273185 20466616516024177206204889)
                ·
                  refine ⟨15349962387018132904653667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20466616516024177206204889 15349962387018132904653667)
                  ·
                    refine ⟨23024943580527199356980501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15349962387018132904653667 23024943580527199356980501)
                    ·
                      refine ⟨1079294230337212469858461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23024943580527199356980501 1079294230337212469858461)
                      ·
                        rfl

theorem cell23_2101918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_2101918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101918 prefixEnd_2101918 := by exact prefixLift 2101918
  have htrace : WordTrace (prefixWord ++ tailWord_2101918) baseStart_2101918 baseEnd_2101918 := by
    simpa [prefixWord, tailWord_2101918, baseEnd_2101918] using wordTrace_append hprefix tailTrace_2101918
  have hstable : (prefixWord ++ tailWord_2101918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101918).length < 2 ^ (prefixWord ++ tailWord_2101918).sum := by decide
  have hdescent : baseEnd_2101918 < baseStart_2101918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101978 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4]
def baseStart_2101978 : Nat := 118140960795 + 2101978 * 2 ^ 59
def prefixEnd_2101978 : Nat := 4983230072969 + 3 ^ 40 * 2101978 * 2
def baseEnd_2101978 : Nat := 1079325039176482235108185

theorem tailTrace_2101978 : CollatzResearch.WordTrace tailWord_2101978 prefixEnd_2101978 1079325039176482235108185 := by
  unfold tailWord_2101978
  simp only [CollatzResearch.WordTrace]
  refine ⟨19166358994725042526728647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51110290652600113404609725 19166358994725042526728647)
  ·
    refine ⟨28749538492087563790092971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19166358994725042526728647 28749538492087563790092971)
    ·
      refine ⟨43124307738131345685139457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28749538492087563790092971 43124307738131345685139457)
      ·
        refine ⟨32343230803598509263854593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43124307738131345685139457 32343230803598509263854593)
        ·
          refine ⟨24257423102698881947890945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32343230803598509263854593 24257423102698881947890945)
          ·
            refine ⟨18193067327024161460918209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24257423102698881947890945 18193067327024161460918209)
            ·
              refine ⟨13644800495268121095688657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18193067327024161460918209 13644800495268121095688657)
              ·
                refine ⟨10233600371451090821766493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13644800495268121095688657 10233600371451090821766493)
                ·
                  refine ⟨3837600139294159058162435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10233600371451090821766493 3837600139294159058162435)
                  ·
                    refine ⟨5756400208941238587243653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3837600139294159058162435 5756400208941238587243653)
                    ·
                      refine ⟨1079325039176482235108185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5756400208941238587243653 1079325039176482235108185)
                      ·
                        rfl

theorem cell23_2101978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_2101978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101978 prefixEnd_2101978 := by exact prefixLift 2101978
  have htrace : WordTrace (prefixWord ++ tailWord_2101978) baseStart_2101978 baseEnd_2101978 := by
    simpa [prefixWord, tailWord_2101978, baseEnd_2101978] using wordTrace_append hprefix tailTrace_2101978
  have hstable : (prefixWord ++ tailWord_2101978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101978).length < 2 ^ (prefixWord ++ tailWord_2101978).sum := by decide
  have hdescent : baseEnd_2101978 < baseStart_2101978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101992 : List Nat := [2, 1, 4, 1, 4, 2, 1, 2, 1, 5]
def baseStart_2101992 : Nat := 118140960795 + 2101992 * 2 ^ 59
def prefixEnd_2101992 : Nat := 4983230072969 + 3 ^ 40 * 2101992 * 2
def baseEnd_2101992 : Nat := 359777409301881726777707

theorem tailTrace_2101992 : CollatzResearch.WordTrace tailWord_2101992 prefixEnd_2101992 359777409301881726777707 := by
  unfold tailWord_2101992
  simp only [CollatzResearch.WordTrace]
  refine ⟨38332973300424725248962115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51110631067232966998616153 38332973300424725248962115)
  ·
    refine ⟨57499459950637087873443173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38332973300424725248962115 57499459950637087873443173)
    ·
      refine ⟨10781148740744453976270595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57499459950637087873443173 10781148740744453976270595)
      ·
        refine ⟨16171723111116680964405893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10781148740744453976270595 16171723111116680964405893)
        ·
          refine ⟨3032198083334377680826105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16171723111116680964405893 3032198083334377680826105)
          ·
            refine ⟨2274148562500783260619579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3032198083334377680826105 2274148562500783260619579)
            ·
              refine ⟨3411222843751174890929369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2274148562500783260619579 3411222843751174890929369)
              ·
                refine ⟨2558417132813381168197027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3411222843751174890929369 2558417132813381168197027)
                ·
                  refine ⟨3837625699220071752295541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2558417132813381168197027 3837625699220071752295541)
                  ·
                    refine ⟨359777409301881726777707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3837625699220071752295541 359777409301881726777707)
                    ·
                      rfl

theorem cell23_2101992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_2101992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101992 prefixEnd_2101992 := by exact prefixLift 2101992
  have htrace : WordTrace (prefixWord ++ tailWord_2101992) baseStart_2101992 baseEnd_2101992 := by
    simpa [prefixWord, tailWord_2101992, baseEnd_2101992] using wordTrace_append hprefix tailTrace_2101992
  have hstable : (prefixWord ++ tailWord_2101992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101992).length < 2 ^ (prefixWord ++ tailWord_2101992).sum := by decide
  have hdescent : baseEnd_2101992 < baseStart_2101992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101995 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 5, 2, 2]
def baseStart_2101995 : Nat := 118140960795 + 2101995 * 2 ^ 59
def prefixEnd_2101995 : Nat := 4983230072969 + 3 ^ 40 * 2101995 * 2
def baseEnd_2101995 : Nat := 1079333768347608668595607

theorem tailTrace_2101995 : CollatzResearch.WordTrace tailWord_2101995 prefixEnd_2101995 1079333768347608668595607 := by
  unfold tailWord_2101995
  simp only [CollatzResearch.WordTrace]
  refine ⟨76666056019838582010283439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51110704013225721340188959 76666056019838582010283439)
  ·
    refine ⟨114999084029757873015425159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76666056019838582010283439 114999084029757873015425159)
    ·
      refine ⟨172498626044636809523137739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114999084029757873015425159 172498626044636809523137739)
      ·
        refine ⟨258747939066955214284706609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172498626044636809523137739 258747939066955214284706609)
        ·
          refine ⟨194060954300216410713529957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258747939066955214284706609 194060954300216410713529957)
          ·
            refine ⟨36386428931290577008786867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 194060954300216410713529957 36386428931290577008786867)
            ·
              refine ⟨54579643396935865513180301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36386428931290577008786867 54579643396935865513180301)
              ·
                refine ⟨20467366273850949567442613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54579643396935865513180301 20467366273850949567442613)
                ·
                  refine ⟨1918815588173526521947745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20467366273850949567442613 1918815588173526521947745)
                  ·
                    refine ⟨1439111691130144891460809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1918815588173526521947745 1439111691130144891460809)
                    ·
                      refine ⟨1079333768347608668595607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1439111691130144891460809 1079333768347608668595607)
                      ·
                        rfl

theorem cell23_2101995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 2, 2].length) (baseStart_2101995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2101995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2101995 prefixEnd_2101995 := by exact prefixLift 2101995
  have htrace : WordTrace (prefixWord ++ tailWord_2101995) baseStart_2101995 baseEnd_2101995 := by
    simpa [prefixWord, tailWord_2101995, baseEnd_2101995] using wordTrace_append hprefix tailTrace_2101995
  have hstable : (prefixWord ++ tailWord_2101995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101995).length < 2 ^ (prefixWord ++ tailWord_2101995).sum := by decide
  have hdescent : baseEnd_2101995 < baseStart_2101995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102001 : List Nat := [1, 2, 2, 2, 2, 2, 1, 11]
def baseStart_2102001 : Nat := 118140960795 + 2102001 * 2 ^ 59
def prefixEnd_2102001 : Nat := 4983230072969 + 3 ^ 40 * 2102001 * 2
def baseEnd_2102001 : Nat := 39975438860427246115577

theorem tailTrace_2102001 : CollatzResearch.WordTrace tailWord_2102001 prefixEnd_2102001 39975438860427246115577 := by
  unfold tailWord_2102001
  simp only [CollatzResearch.WordTrace]
  refine ⟨76666274857816845035001857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51110849905211230023334571 76666274857816845035001857)
  ·
    refine ⟨57499706143362633776251393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76666274857816845035001857 57499706143362633776251393)
    ·
      refine ⟨43124779607521975332188545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57499706143362633776251393 43124779607521975332188545)
      ·
        refine ⟨32343584705641481499141409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43124779607521975332188545 32343584705641481499141409)
        ·
          refine ⟨24257688529231111124356057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32343584705641481499141409 24257688529231111124356057)
          ·
            refine ⟨18193266396923333343267043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24257688529231111124356057 18193266396923333343267043)
            ·
              refine ⟨27289899595385000014900565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18193266396923333343267043 27289899595385000014900565)
              ·
                refine ⟨39975438860427246115577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 27289899595385000014900565 39975438860427246115577)
                ·
                  rfl

theorem cell23_2102001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 11].length) (baseStart_2102001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102001 prefixEnd_2102001 := by exact prefixLift 2102001
  have htrace : WordTrace (prefixWord ++ tailWord_2102001) baseStart_2102001 baseEnd_2102001 := by
    simpa [prefixWord, tailWord_2102001, baseEnd_2102001] using wordTrace_append hprefix tailTrace_2102001
  have hstable : (prefixWord ++ tailWord_2102001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102001).length < 2 ^ (prefixWord ++ tailWord_2102001).sum := by decide
  have hdescent : baseEnd_2102001 < baseStart_2102001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102008 : List Nat := [2, 1, 2, 1, 1, 2, 5, 2, 1, 2, 4]
def baseStart_2102008 : Nat := 118140960795 + 2102008 * 2 ^ 59
def prefixEnd_2102008 : Nat := 4983230072969 + 3 ^ 40 * 2102008 * 2
def baseEnd_2102008 : Nat := 1079340443596117117733047

theorem tailTrace_2102008 : CollatzResearch.WordTrace tailWord_2102008 prefixEnd_2102008 1079340443596117117733047 := by
  unfold tailWord_2102008
  simp only [CollatzResearch.WordTrace]
  refine ⟨38333265084395742615253339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51111020112527656820337785 38333265084395742615253339)
  ·
    refine ⟨57499897626593613922880009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38333265084395742615253339 57499897626593613922880009)
    ·
      refine ⟨43124923219945210442160007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57499897626593613922880009 43124923219945210442160007)
      ·
        refine ⟨64687384829917815663240011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43124923219945210442160007 64687384829917815663240011)
        ·
          refine ⟨97031077244876723494860017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64687384829917815663240011 97031077244876723494860017)
          ·
            refine ⟨72773307933657542621145013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97031077244876723494860017 72773307933657542621145013)
            ·
              refine ⟨6822497618780394620732345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72773307933657542621145013 6822497618780394620732345)
              ·
                refine ⟨5116873214085295965549259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6822497618780394620732345 5116873214085295965549259)
                ·
                  refine ⟨7675309821127943948323889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5116873214085295965549259 7675309821127943948323889)
                  ·
                    refine ⟨5756482365845957961242917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7675309821127943948323889 5756482365845957961242917)
                    ·
                      refine ⟨1079340443596117117733047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5756482365845957961242917 1079340443596117117733047)
                      ·
                        rfl

theorem cell23_2102008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_2102008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102008 prefixEnd_2102008 := by exact prefixLift 2102008
  have htrace : WordTrace (prefixWord ++ tailWord_2102008) baseStart_2102008 baseEnd_2102008 := by
    simpa [prefixWord, tailWord_2102008, baseEnd_2102008] using wordTrace_append hprefix tailTrace_2102008
  have hstable : (prefixWord ++ tailWord_2102008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102008).length < 2 ^ (prefixWord ++ tailWord_2102008).sum := by decide
  have hdescent : baseEnd_2102008 < baseStart_2102008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102012 : List Nat := [2, 2, 2, 1, 3, 3, 3, 1, 1, 1, 4]
def baseStart_2102012 : Nat := 118140960795 + 2102012 * 2 ^ 59
def prefixEnd_2102012 : Nat := 4983230072969 + 3 ^ 40 * 2102012 * 2
def baseEnd_2102012 : Nat := 1079342497518735102083029

theorem tailTrace_2102012 : CollatzResearch.WordTrace tailWord_2102012 prefixEnd_2102012 1079342497518735102083029 := by
  unfold tailWord_2102012
  simp only [CollatzResearch.WordTrace]
  refine ⟨38333338030388496956826145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51111117373851329275768193 38333338030388496956826145)
  ·
    refine ⟨28750003522791372717619609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38333338030388496956826145 28750003522791372717619609)
    ·
      refine ⟨21562502642093529538214707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28750003522791372717619609 21562502642093529538214707)
      ·
        refine ⟨32343753963140294307322061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21562502642093529538214707 32343753963140294307322061)
        ·
          refine ⟨12128907736177610365245773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32343753963140294307322061 12128907736177610365245773)
          ·
            refine ⟨4548340401066603886967165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12128907736177610365245773 4548340401066603886967165)
            ·
              refine ⟨1705627650399976457612687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4548340401066603886967165 1705627650399976457612687)
              ·
                refine ⟨2558441475599964686419031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1705627650399976457612687 2558441475599964686419031)
                ·
                  refine ⟨3837662213399947029628547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2558441475599964686419031 3837662213399947029628547)
                  ·
                    refine ⟨5756493320099920544442821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3837662213399947029628547 5756493320099920544442821)
                    ·
                      refine ⟨1079342497518735102083029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5756493320099920544442821 1079342497518735102083029)
                      ·
                        rfl

theorem cell23_2102012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 1, 1, 4].length) (baseStart_2102012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102012 prefixEnd_2102012 := by exact prefixLift 2102012
  have htrace : WordTrace (prefixWord ++ tailWord_2102012) baseStart_2102012 baseEnd_2102012 := by
    simpa [prefixWord, tailWord_2102012, baseEnd_2102012] using wordTrace_append hprefix tailTrace_2102012
  have hstable : (prefixWord ++ tailWord_2102012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102012).length < 2 ^ (prefixWord ++ tailWord_2102012).sum := by decide
  have hdescent : baseEnd_2102012 < baseStart_2102012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102018 : List Nat := [3, 4, 1, 1, 1, 13]
def baseStart_2102018 : Nat := 118140960795 + 2102018 * 2 ^ 59
def prefixEnd_2102018 : Nat := 4983230072969 + 3 ^ 40 * 2102018 * 2
def baseEnd_2102018 : Nat := 4441751351451284274107

theorem tailTrace_2102018 : CollatzResearch.WordTrace tailWord_2102018 prefixEnd_2102018 4441751351451284274107 := by
  unfold tailWord_2102018
  simp only [CollatzResearch.WordTrace]
  refine ⟨19166723724688814234592677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51111263265836837958913805 19166723724688814234592677)
  ·
    refine ⟨3593760698379152668986127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19166723724688814234592677 3593760698379152668986127)
    ·
      refine ⟨5390641047568729003479191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3593760698379152668986127 5390641047568729003479191)
      ·
        refine ⟨8085961571353093505218787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5390641047568729003479191 8085961571353093505218787)
        ·
          refine ⟨12128942357029640257828181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8085961571353093505218787 12128942357029640257828181)
          ·
            refine ⟨4441751351451284274107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 12128942357029640257828181 4441751351451284274107)
            ·
              rfl

theorem cell23_2102018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 13].length) (baseStart_2102018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102018 prefixEnd_2102018 := by exact prefixLift 2102018
  have htrace : WordTrace (prefixWord ++ tailWord_2102018) baseStart_2102018 baseEnd_2102018 := by
    simpa [prefixWord, tailWord_2102018, baseEnd_2102018] using wordTrace_append hprefix tailTrace_2102018
  have hstable : (prefixWord ++ tailWord_2102018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102018).length < 2 ^ (prefixWord ++ tailWord_2102018).sum := by decide
  have hdescent : baseEnd_2102018 < baseStart_2102018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102028 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 5, 3, 3]
def baseStart_2102028 : Nat := 118140960795 + 2102028 * 2 ^ 59
def prefixEnd_2102028 : Nat := 4983230072969 + 3 ^ 40 * 2102028 * 2
def baseEnd_2102028 : Nat := 1079350713209207039482955

theorem tailTrace_2102028 : CollatzResearch.WordTrace tailWord_2102028 prefixEnd_2102028 1079350713209207039482955 := by
  unfold tailWord_2102028
  simp only [CollatzResearch.WordTrace]
  refine ⟨38333629814359514323117369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51111506419146019097489825 38333629814359514323117369)
  ·
    refine ⟨28750222360769635742338027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38333629814359514323117369 28750222360769635742338027)
    ·
      refine ⟨43125333541154453613507041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28750222360769635742338027 43125333541154453613507041)
      ·
        refine ⟨32344000155865840210130281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43125333541154453613507041 32344000155865840210130281)
        ·
          refine ⟨24258000116899380157597711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32344000155865840210130281 24258000116899380157597711)
          ·
            refine ⟨36387000175349070236396567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24258000116899380157597711 36387000175349070236396567)
            ·
              refine ⟨54580500263023605354594851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36387000175349070236396567 54580500263023605354594851)
              ·
                refine ⟨81870750394535408031892277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54580500263023605354594851 81870750394535408031892277)
                ·
                  refine ⟨7675382849487694502989901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81870750394535408031892277 7675382849487694502989901)
                  ·
                    refine ⟨2878268568557885438621213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7675382849487694502989901 2878268568557885438621213)
                    ·
                      refine ⟨1079350713209207039482955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2878268568557885438621213 1079350713209207039482955)
                      ·
                        rfl

theorem cell23_2102028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_2102028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102028 prefixEnd_2102028 := by exact prefixLift 2102028
  have htrace : WordTrace (prefixWord ++ tailWord_2102028) baseStart_2102028 baseEnd_2102028 := by
    simpa [prefixWord, tailWord_2102028, baseEnd_2102028] using wordTrace_append hprefix tailTrace_2102028
  have hstable : (prefixWord ++ tailWord_2102028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102028).length < 2 ^ (prefixWord ++ tailWord_2102028).sum := by decide
  have hdescent : baseEnd_2102028 < baseStart_2102028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102031 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 1, 9]
def baseStart_2102031 : Nat := 118140960795 + 2102031 * 2 ^ 59
def prefixEnd_2102031 : Nat := 4983230072969 + 3 ^ 40 * 2102031 * 2
def baseEnd_2102031 : Nat := 359784084550390175915147

theorem tailTrace_2102031 : CollatzResearch.WordTrace tailWord_2102031 prefixEnd_2102031 359784084550390175915147 := by
  unfold tailWord_2102031
  simp only [CollatzResearch.WordTrace]
  refine ⟨76667369047708160158593947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51111579365138773439062631 76667369047708160158593947)
  ·
    refine ⟨115001053571562240237890921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76667369047708160158593947 115001053571562240237890921)
    ·
      refine ⟨86250790178671680178418191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115001053571562240237890921 86250790178671680178418191)
      ·
        refine ⟨129376185268007520267627287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86250790178671680178418191 129376185268007520267627287)
        ·
          refine ⟨194064277902011280401440931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129376185268007520267627287 194064277902011280401440931)
          ·
            refine ⟨291096416853016920602161397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194064277902011280401440931 291096416853016920602161397)
            ·
              refine ⟨27290289079970336306452631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 291096416853016920602161397 27290289079970336306452631)
              ·
                refine ⟨40935433619955504459678947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27290289079970336306452631 40935433619955504459678947)
                ·
                  refine ⟨61403150429933256689518421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40935433619955504459678947 61403150429933256689518421)
                  ·
                    refine ⟨359784084550390175915147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 61403150429933256689518421 359784084550390175915147)
                    ·
                      rfl

theorem cell23_2102031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 9].length) (baseStart_2102031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102031 prefixEnd_2102031 := by exact prefixLift 2102031
  have htrace : WordTrace (prefixWord ++ tailWord_2102031) baseStart_2102031 baseEnd_2102031 := by
    simpa [prefixWord, tailWord_2102031, baseEnd_2102031] using wordTrace_append hprefix tailTrace_2102031
  have hstable : (prefixWord ++ tailWord_2102031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102031).length < 2 ^ (prefixWord ++ tailWord_2102031).sum := by decide
  have hdescent : baseEnd_2102031 < baseStart_2102031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102062 : List Nat := [4, 1, 3, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_2102062 : Nat := 118140960795 + 2102062 * 2 ^ 59
def prefixEnd_2102062 : Nat := 4983230072969 + 3 ^ 40 * 2102062 * 2
def baseEnd_2102062 : Nat := 1079368171551459906457799

theorem tailTrace_2102062 : CollatzResearch.WordTrace tailWord_2102062 prefixEnd_2102062 1079368171551459906457799 := by
  unfold tailWord_2102062
  simp only [CollatzResearch.WordTrace]
  refine ⟨9583562463824481556621555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51112333140397234968648293 9583562463824481556621555)
  ·
    refine ⟨14375343695736722334932333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9583562463824481556621555 14375343695736722334932333)
    ·
      refine ⟨5390753885901270875599625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14375343695736722334932333 5390753885901270875599625)
      ·
        refine ⟨4043065414425953156699719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5390753885901270875599625 4043065414425953156699719)
        ·
          refine ⟨6064598121638929735049579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4043065414425953156699719 6064598121638929735049579)
          ·
            refine ⟨9096897182458394602574369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6064598121638929735049579 9096897182458394602574369)
            ·
              refine ⟨6822672886843795951930777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9096897182458394602574369 6822672886843795951930777)
              ·
                refine ⟨5117004665132846963948083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6822672886843795951930777 5117004665132846963948083)
                ·
                  refine ⟨7675506997699270445922125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5117004665132846963948083 7675506997699270445922125)
                  ·
                    refine ⟨2878315124137226417220797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7675506997699270445922125 2878315124137226417220797)
                    ·
                      refine ⟨1079368171551459906457799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2878315124137226417220797 1079368171551459906457799)
                      ·
                        rfl

theorem cell23_2102062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_2102062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102062 prefixEnd_2102062 := by exact prefixLift 2102062
  have htrace : WordTrace (prefixWord ++ tailWord_2102062) baseStart_2102062 baseEnd_2102062 := by
    simpa [prefixWord, tailWord_2102062, baseEnd_2102062] using wordTrace_append hprefix tailTrace_2102062
  have hstable : (prefixWord ++ tailWord_2102062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102062).length < 2 ^ (prefixWord ++ tailWord_2102062).sum := by decide
  have hdescent : baseEnd_2102062 < baseStart_2102062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102072 : List Nat := [2, 1, 2, 1, 3, 2, 3, 3, 1, 3, 2]
def baseStart_2102072 : Nat := 118140960795 + 2102072 * 2 ^ 59
def prefixEnd_2102072 : Nat := 4983230072969 + 3 ^ 40 * 2102072 * 2
def baseEnd_2102072 : Nat := 1079373306358004867332753

theorem tailTrace_2102072 : CollatzResearch.WordTrace tailWord_2102072 prefixEnd_2102072 1079373306358004867332753 := by
  unfold tailWord_2102072
  simp only [CollatzResearch.WordTrace]
  refine ⟨38334432220279812080418235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51112576293706416107224313 38334432220279812080418235)
  ·
    refine ⟨57501648330419718120627353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38334432220279812080418235 57501648330419718120627353)
    ·
      refine ⟨43126236247814788590470515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57501648330419718120627353 43126236247814788590470515)
      ·
        refine ⟨64689354371722182885705773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43126236247814788590470515 64689354371722182885705773)
        ·
          refine ⟨24258507889395818582139665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64689354371722182885705773 24258507889395818582139665)
          ·
            refine ⟨18193880917046863936604749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24258507889395818582139665 18193880917046863936604749)
            ·
              refine ⟨6822705343892573976226781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18193880917046863936604749 6822705343892573976226781)
              ·
                refine ⟨2558514503959715241085043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6822705343892573976226781 2558514503959715241085043)
                ·
                  refine ⟨3837771755939572861627565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2558514503959715241085043 3837771755939572861627565)
                  ·
                    refine ⟨1439164408477339823110337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3837771755939572861627565 1439164408477339823110337)
                    ·
                      refine ⟨1079373306358004867332753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1439164408477339823110337 1079373306358004867332753)
                      ·
                        rfl

theorem cell23_2102072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 1, 3, 2].length) (baseStart_2102072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102072 prefixEnd_2102072 := by exact prefixLift 2102072
  have htrace : WordTrace (prefixWord ++ tailWord_2102072) baseStart_2102072 baseEnd_2102072 := by
    simpa [prefixWord, tailWord_2102072, baseEnd_2102072] using wordTrace_append hprefix tailTrace_2102072
  have hstable : (prefixWord ++ tailWord_2102072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102072).length < 2 ^ (prefixWord ++ tailWord_2102072).sum := by decide
  have hdescent : baseEnd_2102072 < baseStart_2102072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102079 : List Nat := [1, 1, 2, 2, 5, 3, 1, 2, 2, 1, 3]
def baseStart_2102079 : Nat := 118140960795 + 2102079 * 2 ^ 59
def prefixEnd_2102079 : Nat := 4983230072969 + 3 ^ 40 * 2102079 * 2
def baseEnd_2102079 : Nat := 1079376900722586339945221

theorem tailTrace_2102079 : CollatzResearch.WordTrace tailWord_2102079 prefixEnd_2102079 1079376900722586339945221 := by
  unfold tailWord_2102079
  simp only [CollatzResearch.WordTrace]
  refine ⟨76669119751534264356341291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51112746501022842904227527 76669119751534264356341291)
  ·
    refine ⟨115003679627301396534511937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76669119751534264356341291 115003679627301396534511937)
    ·
      refine ⟨86252759720476047400883953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115003679627301396534511937 86252759720476047400883953)
      ·
        refine ⟨64689569790357035550662965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86252759720476047400883953 64689569790357035550662965)
        ·
          refine ⟨6064647167845972082874653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64689569790357035550662965 6064647167845972082874653)
          ·
            refine ⟨2274242687942239531077995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6064647167845972082874653 2274242687942239531077995)
            ·
              refine ⟨3411364031913359296616993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2274242687942239531077995 3411364031913359296616993)
              ·
                refine ⟨2558523023935019472462745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3411364031913359296616993 2558523023935019472462745)
                ·
                  refine ⟨1918892267951264604347059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2558523023935019472462745 1918892267951264604347059)
                  ·
                    refine ⟨2878338401926896906520589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1918892267951264604347059 2878338401926896906520589)
                    ·
                      refine ⟨1079376900722586339945221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2878338401926896906520589 1079376900722586339945221)
                      ·
                        rfl

theorem cell23_2102079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 1, 3].length) (baseStart_2102079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102079 prefixEnd_2102079 := by exact prefixLift 2102079
  have htrace : WordTrace (prefixWord ++ tailWord_2102079) baseStart_2102079 baseEnd_2102079 := by
    simpa [prefixWord, tailWord_2102079, baseEnd_2102079] using wordTrace_append hprefix tailTrace_2102079
  have hstable : (prefixWord ++ tailWord_2102079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102079).length < 2 ^ (prefixWord ++ tailWord_2102079).sum := by decide
  have hdescent : baseEnd_2102079 < baseStart_2102079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102188 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 6]
def baseStart_2102188 : Nat := 118140960795 + 2102188 * 2 ^ 59
def prefixEnd_2102188 : Nat := 4983230072969 + 3 ^ 40 * 2102188 * 2
def baseEnd_2102188 : Nat := 1079432870113926413482219

theorem tailTrace_2102188 : CollatzResearch.WordTrace tailWord_2102188 prefixEnd_2102188 1079432870113926413482219 := by
  unfold tailWord_2102188
  simp only [CollatzResearch.WordTrace]
  refine ⟨38336547654069687986029609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51115396872092917314706145 38336547654069687986029609)
  ·
    refine ⟨28752410740552265989522207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38336547654069687986029609 28752410740552265989522207)
    ·
      refine ⟨43128616110828398984283311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28752410740552265989522207 43128616110828398984283311)
      ·
        refine ⟨64692924166242598476424967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43128616110828398984283311 64692924166242598476424967)
        ·
          refine ⟨97039386249363897714637451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64692924166242598476424967 97039386249363897714637451)
          ·
            refine ⟨145559079374045846571956177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97039386249363897714637451 145559079374045846571956177)
            ·
              refine ⟨109169309530534384928967133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145559079374045846571956177 109169309530534384928967133)
              ·
                refine ⟨40938491073950394348362675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109169309530534384928967133 40938491073950394348362675)
                ·
                  refine ⟨61407736610925591522544013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40938491073950394348362675 61407736610925591522544013)
                  ·
                    refine ⟨23027901229097096820954005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61407736610925591522544013 23027901229097096820954005)
                    ·
                      refine ⟨1079432870113926413482219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23027901229097096820954005 1079432870113926413482219)
                      ·
                        rfl

theorem cell23_2102188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_2102188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102188 prefixEnd_2102188 := by exact prefixLift 2102188
  have htrace : WordTrace (prefixWord ++ tailWord_2102188) baseStart_2102188 baseEnd_2102188 := by
    simpa [prefixWord, tailWord_2102188, baseEnd_2102188] using wordTrace_append hprefix tailTrace_2102188
  have hstable : (prefixWord ++ tailWord_2102188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102188).length < 2 ^ (prefixWord ++ tailWord_2102188).sum := by decide
  have hdescent : baseEnd_2102188 < baseStart_2102188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102195 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 3]
def baseStart_2102195 : Nat := 118140960795 + 2102195 * 2 ^ 59
def prefixEnd_2102195 : Nat := 4983230072969 + 3 ^ 40 * 2102195 * 2
def baseEnd_2102195 : Nat := 1079436464478507886094687

theorem tailTrace_2102195 : CollatzResearch.WordTrace tailWord_2102195 prefixEnd_2102195 1079436464478507886094687 := by
  unfold tailWord_2102195
  simp only [CollatzResearch.WordTrace]
  refine ⟨76673350619114016167564039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51115567079409344111709359 76673350619114016167564039)
  ·
    refine ⟨115010025928671024251346059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76673350619114016167564039 115010025928671024251346059)
    ·
      refine ⟨172515038893006536377019089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115010025928671024251346059 172515038893006536377019089)
      ·
        refine ⟨129386279169754902282764317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172515038893006536377019089 129386279169754902282764317)
        ·
          refine ⟨48519854688658088356036619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129386279169754902282764317 48519854688658088356036619)
          ·
            refine ⟨72779782032987132534054929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48519854688658088356036619 72779782032987132534054929)
            ·
              refine ⟨54584836524740349400541197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72779782032987132534054929 54584836524740349400541197)
              ·
                refine ⟨20469313696777631025202949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54584836524740349400541197 20469313696777631025202949)
                ·
                  refine ⟨3837996318145805817225553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20469313696777631025202949 3837996318145805817225553)
                  ·
                    refine ⟨2878497238609354362919165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3837996318145805817225553 2878497238609354362919165)
                    ·
                      refine ⟨1079436464478507886094687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2878497238609354362919165 1079436464478507886094687)
                      ·
                        rfl

theorem cell23_2102195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 3].length) (baseStart_2102195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102195 prefixEnd_2102195 := by exact prefixLift 2102195
  have htrace : WordTrace (prefixWord ++ tailWord_2102195) baseStart_2102195 baseEnd_2102195 := by
    simpa [prefixWord, tailWord_2102195, baseEnd_2102195] using wordTrace_append hprefix tailTrace_2102195
  have hstable : (prefixWord ++ tailWord_2102195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102195).length < 2 ^ (prefixWord ++ tailWord_2102195).sum := by decide
  have hdescent : baseEnd_2102195 < baseStart_2102195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102215 : List Nat := [1, 1, 4, 1, 1, 2, 4, 3, 6]
def baseStart_2102215 : Nat := 118140960795 + 2102215 * 2 ^ 59
def prefixEnd_2102215 : Nat := 4983230072969 + 3 ^ 40 * 2102215 * 2
def baseEnd_2102215 : Nat := 119938526010177534204955

theorem tailTrace_2102215 : CollatzResearch.WordTrace tailWord_2102215 prefixEnd_2102215 119938526010177534204955 := by
  unfold tailWord_2102215
  simp only [CollatzResearch.WordTrace]
  refine ⟨76674080079041559583292099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51116053386027706388861399 76674080079041559583292099)
  ·
    refine ⟨115011120118562339374938149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76674080079041559583292099 115011120118562339374938149)
    ·
      refine ⟨21564585022230438632800903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115011120118562339374938149 21564585022230438632800903)
      ·
        refine ⟨32346877533345657949201355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21564585022230438632800903 32346877533345657949201355)
        ·
          refine ⟨48520316300018486923802033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32346877533345657949201355 48520316300018486923802033)
          ·
            refine ⟨36390237225013865192851525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48520316300018486923802033 36390237225013865192851525)
            ·
              refine ⟨6823169479690099723659661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36390237225013865192851525 6823169479690099723659661)
              ·
                refine ⟨2558688554883787396372373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6823169479690099723659661 2558688554883787396372373)
                ·
                  refine ⟨119938526010177534204955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2558688554883787396372373 119938526010177534204955)
                  ·
                    rfl

theorem cell23_2102215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 6].length) (baseStart_2102215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102215 prefixEnd_2102215 := by exact prefixLift 2102215
  have htrace : WordTrace (prefixWord ++ tailWord_2102215) baseStart_2102215 baseEnd_2102215 := by
    simpa [prefixWord, tailWord_2102215, baseEnd_2102215] using wordTrace_append hprefix tailTrace_2102215
  have hstable : (prefixWord ++ tailWord_2102215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102215).length < 2 ^ (prefixWord ++ tailWord_2102215).sum := by decide
  have hdescent : baseEnd_2102215 < baseStart_2102215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102293 : List Nat := [1, 3, 2, 1, 4, 3, 1, 3, 1, 1, 3]
def baseStart_2102293 : Nat := 118140960795 + 2102293 * 2 ^ 59
def prefixEnd_2102293 : Nat := 4983230072969 + 3 ^ 40 * 2102293 * 2
def baseEnd_2102293 : Nat := 1079486785582648502669237

theorem tailTrace_2102293 : CollatzResearch.WordTrace tailWord_2102293 prefixEnd_2102293 1079486785582648502669237 := by
  unfold tailWord_2102293
  simp only [CollatzResearch.WordTrace]
  refine ⟨76676924972758978904631533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51117949981839319269754355 76676924972758978904631533)
  ·
    refine ⟨28753846864784617089236825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76676924972758978904631533 28753846864784617089236825)
    ·
      refine ⟨21565385148588462816927619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28753846864784617089236825 21565385148588462816927619)
      ·
        refine ⟨32348077722882694225391429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21565385148588462816927619 32348077722882694225391429)
        ·
          refine ⟨6065264573040505167260893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32348077722882694225391429 6065264573040505167260893)
          ·
            refine ⟨2274474214890189437722835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6065264573040505167260893 2274474214890189437722835)
            ·
              refine ⟨3411711322335284156584253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2274474214890189437722835 3411711322335284156584253)
              ·
                refine ⟨1279391745875731558719095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3411711322335284156584253 1279391745875731558719095)
                ·
                  refine ⟨1919087618813597338078643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1279391745875731558719095 1919087618813597338078643)
                  ·
                    refine ⟨2878631428220396007117965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1919087618813597338078643 2878631428220396007117965)
                    ·
                      refine ⟨1079486785582648502669237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2878631428220396007117965 1079486785582648502669237)
                      ·
                        rfl

theorem cell23_2102293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 1, 1, 3].length) (baseStart_2102293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102293 prefixEnd_2102293 := by exact prefixLift 2102293
  have htrace : WordTrace (prefixWord ++ tailWord_2102293) baseStart_2102293 baseEnd_2102293 := by
    simpa [prefixWord, tailWord_2102293, baseEnd_2102293] using wordTrace_append hprefix tailTrace_2102293
  have hstable : (prefixWord ++ tailWord_2102293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102293).length < 2 ^ (prefixWord ++ tailWord_2102293).sum := by decide
  have hdescent : baseEnd_2102293 < baseStart_2102293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102305 : List Nat := [1, 2, 3, 2, 3, 1, 11]
def baseStart_2102305 : Nat := 118140960795 + 2102305 * 2 ^ 59
def prefixEnd_2102305 : Nat := 4983230072969 + 3 ^ 40 * 2102305 * 2
def baseEnd_2102305 : Nat := 13327073424080277231101

theorem tailTrace_2102305 : CollatzResearch.WordTrace tailWord_2102305 prefixEnd_2102305 13327073424080277231101 := by
  unfold tailWord_2102305
  simp only [CollatzResearch.WordTrace]
  refine ⟨76677362648715504954068369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51118241765810336636045579 76677362648715504954068369)
  ·
    refine ⟨57508021986536628715551277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76677362648715504954068369 57508021986536628715551277)
    ·
      refine ⟨21565508244951235768331729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57508021986536628715551277 21565508244951235768331729)
      ·
        refine ⟨16174131183713426826248797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21565508244951235768331729 16174131183713426826248797)
        ·
          refine ⟨6065299193892535059843299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16174131183713426826248797 6065299193892535059843299)
          ·
            refine ⟨9097948790838802589764949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6065299193892535059843299 9097948790838802589764949)
            ·
              refine ⟨13327073424080277231101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 9097948790838802589764949 13327073424080277231101)
              ·
                rfl

theorem cell23_2102305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 11].length) (baseStart_2102305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102305 prefixEnd_2102305 := by exact prefixLift 2102305
  have htrace : WordTrace (prefixWord ++ tailWord_2102305) baseStart_2102305 baseEnd_2102305 := by
    simpa [prefixWord, tailWord_2102305, baseEnd_2102305] using wordTrace_append hprefix tailTrace_2102305
  have hstable : (prefixWord ++ tailWord_2102305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102305).length < 2 ^ (prefixWord ++ tailWord_2102305).sum := by decide
  have hdescent : baseEnd_2102305 < baseStart_2102305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102325 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_2102325 : Nat := 118140960795 + 2102325 * 2 ^ 59
def prefixEnd_2102325 : Nat := 4983230072969 + 3 ^ 40 * 2102325 * 2
def baseEnd_2102325 : Nat := 1079503216963592377469089

theorem tailTrace_2102325 : CollatzResearch.WordTrace tailWord_2102325 prefixEnd_2102325 1079503216963592377469089 := by
  unfold tailWord_2102325
  simp only [CollatzResearch.WordTrace]
  refine ⟨76678092108643048369796429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51118728072428698913197619 76678092108643048369796429)
  ·
    refine ⟨28754284540741143138673661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76678092108643048369796429 28754284540741143138673661)
    ·
      refine ⟨10782856702777928677002623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28754284540741143138673661 10782856702777928677002623)
      ·
        refine ⟨16174285054166893015503935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10782856702777928677002623 16174285054166893015503935)
        ·
          refine ⟨24261427581250339523255903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16174285054166893015503935 24261427581250339523255903)
          ·
            refine ⟨36392141371875509284883855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24261427581250339523255903 36392141371875509284883855)
            ·
              refine ⟨54588212057813263927325783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36392141371875509284883855 54588212057813263927325783)
              ·
                refine ⟨81882318086719895890988675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54588212057813263927325783 81882318086719895890988675)
                ·
                  refine ⟨122823477130079843836483013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81882318086719895890988675 122823477130079843836483013)
                  ·
                    refine ⟨23029401961889970719340565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122823477130079843836483013 23029401961889970719340565)
                    ·
                      refine ⟨1079503216963592377469089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23029401961889970719340565 1079503216963592377469089)
                      ·
                        rfl

theorem cell23_2102325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_2102325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102325 prefixEnd_2102325 := by exact prefixLift 2102325
  have htrace : WordTrace (prefixWord ++ tailWord_2102325) baseStart_2102325 baseEnd_2102325 := by
    simpa [prefixWord, tailWord_2102325, baseEnd_2102325] using wordTrace_append hprefix tailTrace_2102325
  have hstable : (prefixWord ++ tailWord_2102325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102325).length < 2 ^ (prefixWord ++ tailWord_2102325).sum := by decide
  have hdescent : baseEnd_2102325 < baseStart_2102325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102326 : List Nat := [5, 1, 2, 1, 1, 3, 1, 3, 2, 4]
def baseStart_2102326 : Nat := 118140960795 + 2102326 * 2 ^ 59
def prefixEnd_2102326 : Nat := 4983230072969 + 3 ^ 40 * 2102326 * 2
def baseEnd_2102326 : Nat := 359834576814748957852195

theorem tailTrace_2102326 : CollatzResearch.WordTrace tailWord_2102326 prefixEnd_2102326 359834576814748957852195 := by
  unfold tailWord_2102326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4792383036352464096286427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51118752387759617027055221 4792383036352464096286427)
  ·
    refine ⟨7188574554528696144429641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4792383036352464096286427 7188574554528696144429641)
    ·
      refine ⟨5391430915896522108322231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7188574554528696144429641 5391430915896522108322231)
      ·
        refine ⟨8087146373844783162483347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5391430915896522108322231 8087146373844783162483347)
        ·
          refine ⟨12130719560767174743725021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8087146373844783162483347 12130719560767174743725021)
          ·
            refine ⟨4549019835287690528896883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12130719560767174743725021 4549019835287690528896883)
            ·
              refine ⟨6823529752931535793345325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4549019835287690528896883 6823529752931535793345325)
              ·
                refine ⟨2558823657349325922504497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6823529752931535793345325 2558823657349325922504497)
                ·
                  refine ⟨1919117743011994441878373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2558823657349325922504497 1919117743011994441878373)
                  ·
                    refine ⟨359834576814748957852195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1919117743011994441878373 359834576814748957852195)
                    ·
                      rfl

theorem cell23_2102326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_2102326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102326 prefixEnd_2102326 := by exact prefixLift 2102326
  have htrace : WordTrace (prefixWord ++ tailWord_2102326) baseStart_2102326 baseEnd_2102326 := by
    simpa [prefixWord, tailWord_2102326, baseEnd_2102326] using wordTrace_append hprefix tailTrace_2102326
  have hstable : (prefixWord ++ tailWord_2102326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102326).length < 2 ^ (prefixWord ++ tailWord_2102326).sum := by decide
  have hdescent : baseEnd_2102326 < baseStart_2102326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102345 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 2, 2, 5]
def baseStart_2102345 : Nat := 118140960795 + 2102345 * 2 ^ 59
def prefixEnd_2102345 : Nat := 4983230072969 + 3 ^ 40 * 2102345 * 2
def baseEnd_2102345 : Nat := 1079513486576682299218997

theorem tailTrace_2102345 : CollatzResearch.WordTrace tailWord_2102345 prefixEnd_2102345 1079513486576682299218997 := by
  unfold tailWord_2102345
  simp only [CollatzResearch.WordTrace]
  refine ⟨76678821568570591785524489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51119214379047061190349659 76678821568570591785524489)
  ·
    refine ⟨57509116176427943839143367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76678821568570591785524489 57509116176427943839143367)
    ·
      refine ⟨86263674264641915758715051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57509116176427943839143367 86263674264641915758715051)
      ·
        refine ⟨129395511396962873638072577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86263674264641915758715051 129395511396962873638072577)
        ·
          refine ⟨97046633547722155228554433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129395511396962873638072577 97046633547722155228554433)
          ·
            refine ⟨72784975160791616421415825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97046633547722155228554433 72784975160791616421415825)
            ·
              refine ⟨54588731370593712316061869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72784975160791616421415825 54588731370593712316061869)
              ·
                refine ⟨20470774263972642118523201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54588731370593712316061869 20470774263972642118523201)
                ·
                  refine ⟨15353080697979481588892401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20470774263972642118523201 15353080697979481588892401)
                  ·
                    refine ⟨11514810523484611191669301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15353080697979481588892401 11514810523484611191669301)
                    ·
                      refine ⟨1079513486576682299218997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11514810523484611191669301 1079513486576682299218997)
                      ·
                        rfl

theorem cell23_2102345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_2102345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102345 prefixEnd_2102345 := by exact prefixLift 2102345
  have htrace : WordTrace (prefixWord ++ tailWord_2102345) baseStart_2102345 baseEnd_2102345 := by
    simpa [prefixWord, tailWord_2102345, baseEnd_2102345] using wordTrace_append hprefix tailTrace_2102345
  have hstable : (prefixWord ++ tailWord_2102345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102345).length < 2 ^ (prefixWord ++ tailWord_2102345).sum := by decide
  have hdescent : baseEnd_2102345 < baseStart_2102345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102349 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_2102349 : Nat := 118140960795 + 2102349 * 2 ^ 59
def prefixEnd_2102349 : Nat := 4983230072969 + 3 ^ 40 * 2102349 * 2
def baseEnd_2102349 : Nat := 1079515540499300283568979

theorem tailTrace_2102349 : CollatzResearch.WordTrace tailWord_2102349 prefixEnd_2102349 1079515540499300283568979 := by
  unfold tailWord_2102349
  simp only [CollatzResearch.WordTrace]
  refine ⟨76678967460556100468670101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51119311640370733645780067 76678967460556100468670101)
  ·
    refine ⟨3594326599713567209468911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76678967460556100468670101 3594326599713567209468911)
    ·
      refine ⟨5391489899570350814203367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3594326599713567209468911 5391489899570350814203367)
      ·
        refine ⟨8087234849355526221305051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5391489899570350814203367 8087234849355526221305051)
        ·
          refine ⟨12130852274033289331957577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8087234849355526221305051 12130852274033289331957577)
          ·
            refine ⟨9098139205524966998968183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12130852274033289331957577 9098139205524966998968183)
            ·
              refine ⟨13647208808287450498452275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9098139205524966998968183 13647208808287450498452275)
              ·
                refine ⟨20470813212431175747678413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13647208808287450498452275 20470813212431175747678413)
                ·
                  refine ⟨7676554954661690905379405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20470813212431175747678413 7676554954661690905379405)
                  ·
                    refine ⟨2878708107998134089517277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7676554954661690905379405 2878708107998134089517277)
                    ·
                      refine ⟨1079515540499300283568979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2878708107998134089517277 1079515540499300283568979)
                      ·
                        rfl

theorem cell23_2102349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_2102349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102349 prefixEnd_2102349 := by exact prefixLift 2102349
  have htrace : WordTrace (prefixWord ++ tailWord_2102349) baseStart_2102349 baseEnd_2102349 := by
    simpa [prefixWord, tailWord_2102349, baseEnd_2102349] using wordTrace_append hprefix tailTrace_2102349
  have hstable : (prefixWord ++ tailWord_2102349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102349).length < 2 ^ (prefixWord ++ tailWord_2102349).sum := by decide
  have hdescent : baseEnd_2102349 < baseStart_2102349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102355 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 4]
def baseStart_2102355 : Nat := 118140960795 + 2102355 * 2 ^ 59
def prefixEnd_2102355 : Nat := 4983230072969 + 3 ^ 40 * 2102355 * 2
def baseEnd_2102355 : Nat := 1079518621383227260093951

theorem tailTrace_2102355 : CollatzResearch.WordTrace tailWord_2102355 prefixEnd_2102355 1079518621383227260093951 := by
  unfold tailWord_2102355
  simp only [CollatzResearch.WordTrace]
  refine ⟨76679186298534363493388519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51119457532356242328925679 76679186298534363493388519)
  ·
    refine ⟨115018779447801545240082779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76679186298534363493388519 115018779447801545240082779)
    ·
      refine ⟨172528169171702317860124169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115018779447801545240082779 172528169171702317860124169)
      ·
        refine ⟨129396126878776738395093127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172528169171702317860124169 129396126878776738395093127)
        ·
          refine ⟨194094190318165107592639691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129396126878776738395093127 194094190318165107592639691)
          ·
            refine ⟨291141285477247661388959537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194094190318165107592639691 291141285477247661388959537)
            ·
              refine ⟨218355964107935746041719653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291141285477247661388959537 218355964107935746041719653)
              ·
                refine ⟨40941743270237952382822435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 218355964107935746041719653 40941743270237952382822435)
                ·
                  refine ⟨61412614905356928574233653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40941743270237952382822435 61412614905356928574233653)
                  ·
                    refine ⟨5757432647377212053834405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61412614905356928574233653 5757432647377212053834405)
                    ·
                      refine ⟨1079518621383227260093951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5757432647377212053834405 1079518621383227260093951)
                      ·
                        rfl

theorem cell23_2102355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 4].length) (baseStart_2102355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102355 prefixEnd_2102355 := by exact prefixLift 2102355
  have htrace : WordTrace (prefixWord ++ tailWord_2102355) baseStart_2102355 baseEnd_2102355 := by
    simpa [prefixWord, tailWord_2102355, baseEnd_2102355] using wordTrace_append hprefix tailTrace_2102355
  have hstable : (prefixWord ++ tailWord_2102355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102355).length < 2 ^ (prefixWord ++ tailWord_2102355).sum := by decide
  have hdescent : baseEnd_2102355 < baseStart_2102355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102382 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 1, 8]
def baseStart_2102382 : Nat := 118140960795 + 2102382 * 2 ^ 59
def prefixEnd_2102382 : Nat := 4983230072969 + 3 ^ 40 * 2102382 * 2
def baseEnd_2102382 : Nat := 359844161786966218152109

theorem tailTrace_2102382 : CollatzResearch.WordTrace tailWord_2102382 prefixEnd_2102382 359844161786966218152109 := by
  unfold tailWord_2102382
  simp only [CollatzResearch.WordTrace]
  refine ⟨9585021383679568388077675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51120114046291031403080933 9585021383679568388077675)
  ·
    refine ⟨14377532075519352582116513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9585021383679568388077675 14377532075519352582116513)
    ·
      refine ⟨10783149056639514436587385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14377532075519352582116513 10783149056639514436587385)
      ·
        refine ⟨8087361792479635827440539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10783149056639514436587385 8087361792479635827440539)
        ·
          refine ⟨12131042688719453741160809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8087361792479635827440539 12131042688719453741160809)
          ·
            refine ⟨9098282016539590305870607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12131042688719453741160809 9098282016539590305870607)
            ·
              refine ⟨13647423024809385458805911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9098282016539590305870607 13647423024809385458805911)
              ·
                refine ⟨20471134537214078188208867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13647423024809385458805911 20471134537214078188208867)
                ·
                  refine ⟨30706701805821117282313301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20471134537214078188208867 30706701805821117282313301)
                  ·
                    refine ⟨359844161786966218152109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30706701805821117282313301 359844161786966218152109)
                    ·
                      rfl

theorem cell23_2102382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_2102382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102382 prefixEnd_2102382 := by exact prefixLift 2102382
  have htrace : WordTrace (prefixWord ++ tailWord_2102382) baseStart_2102382 baseEnd_2102382 := by
    simpa [prefixWord, tailWord_2102382, baseEnd_2102382] using wordTrace_append hprefix tailTrace_2102382
  have hstable : (prefixWord ++ tailWord_2102382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102382).length < 2 ^ (prefixWord ++ tailWord_2102382).sum := by decide
  have hdescent : baseEnd_2102382 < baseStart_2102382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102415 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 8]
def baseStart_2102415 : Nat := 118140960795 + 2102415 * 2 ^ 59
def prefixEnd_2102415 : Nat := 4983230072969 + 3 ^ 40 * 2102415 * 2
def baseEnd_2102415 : Nat := 1079549430222497025343675

theorem tailTrace_2102415 : CollatzResearch.WordTrace tailWord_2102415 prefixEnd_2102415 1079549430222497025343675 := by
  unfold tailWord_2102415
  simp only [CollatzResearch.WordTrace]
  refine ⟨76681374678316993740572699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51120916452211329160381799 76681374678316993740572699)
  ·
    refine ⟨115022062017475490610859049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76681374678316993740572699 115022062017475490610859049)
    ·
      refine ⟨86266546513106617958144287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115022062017475490610859049 86266546513106617958144287)
      ·
        refine ⟨129399819769659926937216431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86266546513106617958144287 129399819769659926937216431)
        ·
          refine ⟨194099729654489890405824647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129399819769659926937216431 194099729654489890405824647)
          ·
            refine ⟨291149594481734835608736971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194099729654489890405824647 291149594481734835608736971)
            ·
              refine ⟨436724391722602253413105457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291149594481734835608736971 436724391722602253413105457)
              ·
                refine ⟨327543293791951690059829093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 436724391722602253413105457 327543293791951690059829093)
                ·
                  refine ⟨61414367585990941886217955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 327543293791951690059829093 61414367585990941886217955)
                  ·
                    refine ⟨92121551378986412829326933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61414367585990941886217955 92121551378986412829326933)
                    ·
                      refine ⟨1079549430222497025343675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 92121551378986412829326933 1079549430222497025343675)
                      ·
                        rfl

theorem cell23_2102415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_2102415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102415 prefixEnd_2102415 := by exact prefixLift 2102415
  have htrace : WordTrace (prefixWord ++ tailWord_2102415) baseStart_2102415 baseEnd_2102415 := by
    simpa [prefixWord, tailWord_2102415, baseEnd_2102415] using wordTrace_append hprefix tailTrace_2102415
  have hstable : (prefixWord ++ tailWord_2102415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102415).length < 2 ^ (prefixWord ++ tailWord_2102415).sum := by decide
  have hdescent : baseEnd_2102415 < baseStart_2102415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102423 : List Nat := [1, 1, 3, 3, 3, 1, 3, 2, 2, 2, 2]
def baseStart_2102423 : Nat := 118140960795 + 2102423 * 2 ^ 59
def prefixEnd_2102423 : Nat := 4983230072969 + 3 ^ 40 * 2102423 * 2
def baseEnd_2102423 : Nat := 1079553538067732994043639

theorem tailTrace_2102423 : CollatzResearch.WordTrace tailWord_2102423 prefixEnd_2102423 1079553538067732994043639 := by
  unfold tailWord_2102423
  simp only [CollatzResearch.WordTrace]
  refine ⟨76681666462288011106863923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51121110974858674071242615 76681666462288011106863923)
  ·
    refine ⟨115022499693432016660295885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76681666462288011106863923 115022499693432016660295885)
    ·
      refine ⟨43133437385037006247610957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115022499693432016660295885 43133437385037006247610957)
      ·
        refine ⟨16175039019388877342854109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43133437385037006247610957 16175039019388877342854109)
        ·
          refine ⟨6065639632270829003570291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16175039019388877342854109 6065639632270829003570291)
          ·
            refine ⟨9098459448406243505355437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6065639632270829003570291 9098459448406243505355437)
            ·
              refine ⟨3411922293152341314508289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9098459448406243505355437 3411922293152341314508289)
              ·
                refine ⟨2558941719864255985881217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3411922293152341314508289 2558941719864255985881217)
                ·
                  refine ⟨1919206289898191989410913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2558941719864255985881217 1919206289898191989410913)
                  ·
                    refine ⟨1439404717423643992058185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1919206289898191989410913 1439404717423643992058185)
                    ·
                      refine ⟨1079553538067732994043639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1439404717423643992058185 1079553538067732994043639)
                      ·
                        rfl

theorem cell23_2102423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_2102423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102423 prefixEnd_2102423 := by exact prefixLift 2102423
  have htrace : WordTrace (prefixWord ++ tailWord_2102423) baseStart_2102423 baseEnd_2102423 := by
    simpa [prefixWord, tailWord_2102423, baseEnd_2102423] using wordTrace_append hprefix tailTrace_2102423
  have hstable : (prefixWord ++ tailWord_2102423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102423).length < 2 ^ (prefixWord ++ tailWord_2102423).sum := by decide
  have hdescent : baseEnd_2102423 < baseStart_2102423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102429 : List Nat := [1, 4, 2, 1, 1, 2, 1, 6, 5]
def baseStart_2102429 : Nat := 118140960795 + 2102429 * 2 ^ 59
def prefixEnd_2102429 : Nat := 4983230072969 + 3 ^ 40 * 2102429 * 2
def baseEnd_2102429 : Nat := 119950735439073330063179

theorem tailTrace_2102429 : CollatzResearch.WordTrace tailWord_2102429 prefixEnd_2102429 119950735439073330063179 := by
  unfold tailWord_2102429
  simp only [CollatzResearch.WordTrace]
  refine ⟨76681885300266274131582341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51121256866844182754388227 76681885300266274131582341)
  ·
    refine ⟨14377853493799926399671689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76681885300266274131582341 14377853493799926399671689)
    ·
      refine ⟨10783390120349944799753767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14377853493799926399671689 10783390120349944799753767)
      ·
        refine ⟨16175085180524917199630651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10783390120349944799753767 16175085180524917199630651)
        ·
          refine ⟨24262627770787375799445977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16175085180524917199630651 24262627770787375799445977)
          ·
            refine ⟨18196970828090531849584483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24262627770787375799445977 18196970828090531849584483)
            ·
              refine ⟨27295456242135797774376725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18196970828090531849584483 27295456242135797774376725)
              ·
                refine ⟨1279474511350115520673909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27295456242135797774376725 1279474511350115520673909)
                ·
                  refine ⟨119950735439073330063179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1279474511350115520673909 119950735439073330063179)
                  ·
                    rfl

theorem cell23_2102429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_2102429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102429 prefixEnd_2102429 := by exact prefixLift 2102429
  have htrace : WordTrace (prefixWord ++ tailWord_2102429) baseStart_2102429 baseEnd_2102429 := by
    simpa [prefixWord, tailWord_2102429, baseEnd_2102429] using wordTrace_append hprefix tailTrace_2102429
  have hstable : (prefixWord ++ tailWord_2102429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102429).length < 2 ^ (prefixWord ++ tailWord_2102429).sum := by decide
  have hdescent : baseEnd_2102429 < baseStart_2102429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102479 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 2, 4, 2]
def baseStart_2102479 : Nat := 118140960795 + 2102479 * 2 ^ 59
def prefixEnd_2102479 : Nat := 4983230072969 + 3 ^ 40 * 2102479 * 2
def baseEnd_2102479 : Nat := 1079582292984384774943381

theorem tailTrace_2102479 : CollatzResearch.WordTrace tailWord_2102479 prefixEnd_2102479 1079582292984384774943381 := by
  unfold tailWord_2102479
  simp only [CollatzResearch.WordTrace]
  refine ⟨76683708950085132670902491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51122472633390088447268327 76683708950085132670902491)
  ·
    refine ⟨115025563425127699006353737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76683708950085132670902491 115025563425127699006353737)
    ·
      refine ⟨86269172568845774254765303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115025563425127699006353737 86269172568845774254765303)
      ·
        refine ⟨129403758853268661382147955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86269172568845774254765303 129403758853268661382147955)
        ·
          refine ⟨194105638279902992073221933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129403758853268661382147955 194105638279902992073221933)
          ·
            refine ⟨72789614354963622027458225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 194105638279902992073221933 72789614354963622027458225)
            ·
              refine ⟨54592210766222716520593669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72789614354963622027458225 54592210766222716520593669)
              ·
                refine ⟨10236039518666759347611313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54592210766222716520593669 10236039518666759347611313)
                ·
                  refine ⟨7677029639000069510708485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10236039518666759347611313 7677029639000069510708485)
                  ·
                    refine ⟨1439443057312513033257841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7677029639000069510708485 1439443057312513033257841)
                    ·
                      refine ⟨1079582292984384774943381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1439443057312513033257841 1079582292984384774943381)
                      ·
                        rfl

theorem cell23_2102479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 4, 2].length) (baseStart_2102479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102479 prefixEnd_2102479 := by exact prefixLift 2102479
  have htrace : WordTrace (prefixWord ++ tailWord_2102479) baseStart_2102479 baseEnd_2102479 := by
    simpa [prefixWord, tailWord_2102479, baseEnd_2102479] using wordTrace_append hprefix tailTrace_2102479
  have hstable : (prefixWord ++ tailWord_2102479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102479).length < 2 ^ (prefixWord ++ tailWord_2102479).sum := by decide
  have hdescent : baseEnd_2102479 < baseStart_2102479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102536 : List Nat := [2, 1, 3, 2, 4, 1, 2, 2, 6]
def baseStart_2102536 : Nat := 118140960795 + 2102536 * 2 ^ 59
def prefixEnd_2102536 : Nat := 4983230072969 + 3 ^ 40 * 2102536 * 2
def baseEnd_2102536 : Nat := 119956840153521227992291

theorem tailTrace_2102536 : CollatzResearch.WordTrace tailWord_2102536 prefixEnd_2102536 119956840153521227992291 := by
  unfold tailWord_2102536
  simp only [CollatzResearch.WordTrace]
  refine ⟨38342893955439315702863731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51123858607252420937151641 38342893955439315702863731)
  ·
    refine ⟨57514340933158973554295597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38342893955439315702863731 57514340933158973554295597)
    ·
      refine ⟨21567877849934615082860849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57514340933158973554295597 21567877849934615082860849)
      ·
        refine ⟨16175908387450961312145637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21567877849934615082860849 16175908387450961312145637)
        ·
          refine ⟨3032982822647055246027307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16175908387450961312145637 3032982822647055246027307)
          ·
            refine ⟨4549474233970582869040961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3032982822647055246027307 4549474233970582869040961)
            ·
              refine ⟨3412105675477937151780721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4549474233970582869040961 3412105675477937151780721)
              ·
                refine ⟨2559079256608452863835541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3412105675477937151780721 2559079256608452863835541)
                ·
                  refine ⟨119956840153521227992291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2559079256608452863835541 119956840153521227992291)
                  ·
                    rfl

theorem cell23_2102536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 6].length) (baseStart_2102536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102536 prefixEnd_2102536 := by exact prefixLift 2102536
  have htrace : WordTrace (prefixWord ++ tailWord_2102536) baseStart_2102536 baseEnd_2102536 := by
    simpa [prefixWord, tailWord_2102536, baseEnd_2102536] using wordTrace_append hprefix tailTrace_2102536
  have hstable : (prefixWord ++ tailWord_2102536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102536).length < 2 ^ (prefixWord ++ tailWord_2102536).sum := by decide
  have hdescent : baseEnd_2102536 < baseStart_2102536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102540 : List Nat := [2, 2, 1, 2, 2, 5, 2, 2, 1, 4]
def baseStart_2102540 : Nat := 118140960795 + 2102540 * 2 ^ 59
def prefixEnd_2102540 : Nat := 4983230072969 + 3 ^ 40 * 2102540 * 2
def baseEnd_2102540 : Nat := 359871205101436345426867

theorem tailTrace_2102540 : CollatzResearch.WordTrace tailWord_2102540 prefixEnd_2102540 359871205101436345426867 := by
  unfold tailWord_2102540
  simp only [CollatzResearch.WordTrace]
  refine ⟨38342966901432070044436537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51123955868576093392582049 38342966901432070044436537)
  ·
    refine ⟨28757225176074052533327403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38342966901432070044436537 28757225176074052533327403)
    ·
      refine ⟨43135837764111078799991105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28757225176074052533327403 43135837764111078799991105)
      ·
        refine ⟨32351878323083309099993329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43135837764111078799991105 32351878323083309099993329)
        ·
          refine ⟨24263908742312481824994997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32351878323083309099993329 24263908742312481824994997)
          ·
            refine ⟨2274741444591795171093281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24263908742312481824994997 2274741444591795171093281)
            ·
              refine ⟨1706056083443846378319961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2274741444591795171093281 1706056083443846378319961)
              ·
                refine ⟨1279542062582884783739971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1706056083443846378319961 1279542062582884783739971)
                ·
                  refine ⟨1919313093874327175609957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1279542062582884783739971 1919313093874327175609957)
                  ·
                    refine ⟨359871205101436345426867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1919313093874327175609957 359871205101436345426867)
                    ·
                      rfl

theorem cell23_2102540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 1, 4].length) (baseStart_2102540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102540 prefixEnd_2102540 := by exact prefixLift 2102540
  have htrace : WordTrace (prefixWord ++ tailWord_2102540) baseStart_2102540 baseEnd_2102540 := by
    simpa [prefixWord, tailWord_2102540, baseEnd_2102540] using wordTrace_append hprefix tailTrace_2102540
  have hstable : (prefixWord ++ tailWord_2102540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102540).length < 2 ^ (prefixWord ++ tailWord_2102540).sum := by decide
  have hdescent : baseEnd_2102540 < baseStart_2102540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102556 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 4, 3, 2]
def baseStart_2102556 : Nat := 118140960795 + 2102556 * 2 ^ 59
def prefixEnd_2102556 : Nat := 4983230072969 + 3 ^ 40 * 2102556 * 2
def baseEnd_2102556 : Nat := 1079621830994780973680527

theorem tailTrace_2102556 : CollatzResearch.WordTrace tailWord_2102556 prefixEnd_2102556 1079621830994780973680527 := by
  unfold tailWord_2102556
  simp only [CollatzResearch.WordTrace]
  refine ⟨38343258685403087410727761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51124344913870783214303681 38343258685403087410727761)
  ·
    refine ⟨28757444014052315558045821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38343258685403087410727761 28757444014052315558045821)
    ·
      refine ⟨10784041505269618334267183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28757444014052315558045821 10784041505269618334267183)
      ·
        refine ⟨16176062257904427501400775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10784041505269618334267183 16176062257904427501400775)
        ·
          refine ⟨24264093386856641252101163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16176062257904427501400775 24264093386856641252101163)
          ·
            refine ⟨36396140080284961878151745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24264093386856641252101163 36396140080284961878151745)
            ·
              refine ⟨27297105060213721408613809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36396140080284961878151745 27297105060213721408613809)
              ·
                refine ⟨20472828795160291056460357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27297105060213721408613809 20472828795160291056460357)
                ·
                  refine ⟨3838655399092554573086317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20472828795160291056460357 3838655399092554573086317)
                  ·
                    refine ⟨1439495774659707964907369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3838655399092554573086317 1439495774659707964907369)
                    ·
                      refine ⟨1079621830994780973680527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1439495774659707964907369 1079621830994780973680527)
                      ·
                        rfl

theorem cell23_2102556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_2102556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102556 prefixEnd_2102556 := by exact prefixLift 2102556
  have htrace : WordTrace (prefixWord ++ tailWord_2102556) baseStart_2102556 baseEnd_2102556 := by
    simpa [prefixWord, tailWord_2102556, baseEnd_2102556] using wordTrace_append hprefix tailTrace_2102556
  have hstable : (prefixWord ++ tailWord_2102556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102556).length < 2 ^ (prefixWord ++ tailWord_2102556).sum := by decide
  have hdescent : baseEnd_2102556 < baseStart_2102556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102579 : List Nat := [1, 1, 1, 2, 5, 2, 2, 2, 1, 6]
def baseStart_2102579 : Nat := 118140960795 + 2102579 * 2 ^ 59
def prefixEnd_2102579 : Nat := 4983230072969 + 3 ^ 40 * 2102579 * 2
def baseEnd_2102579 : Nat := 359877880349944794564307

theorem tailTrace_2102579 : CollatzResearch.WordTrace tailWord_2102579 prefixEnd_2102579 359877880349944794564307 := by
  unfold tailWord_2102579
  simp only [CollatzResearch.WordTrace]
  refine ⟨76687356249722849749542791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51124904166481899833028527 76687356249722849749542791)
  ·
    refine ⟨115031034374584274624314187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76687356249722849749542791 115031034374584274624314187)
    ·
      refine ⟨172546551561876411936471281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115031034374584274624314187 172546551561876411936471281)
      ·
        refine ⟨129409913671407308952353461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172546551561876411936471281 129409913671407308952353461)
        ·
          refine ⟨12132179406694435214283137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 129409913671407308952353461 12132179406694435214283137)
          ·
            refine ⟨9099134555020826410712353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12132179406694435214283137 9099134555020826410712353)
            ·
              refine ⟨6824350916265619808034265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9099134555020826410712353 6824350916265619808034265)
              ·
                refine ⟨5118263187199214856025699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6824350916265619808034265 5118263187199214856025699)
                ·
                  refine ⟨7677394780798822284038549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5118263187199214856025699 7677394780798822284038549)
                  ·
                    refine ⟨359877880349944794564307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7677394780798822284038549 359877880349944794564307)
                    ·
                      rfl

theorem cell23_2102579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 6].length) (baseStart_2102579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102579 prefixEnd_2102579 := by exact prefixLift 2102579
  have htrace : WordTrace (prefixWord ++ tailWord_2102579) baseStart_2102579 baseEnd_2102579 := by
    simpa [prefixWord, tailWord_2102579, baseEnd_2102579] using wordTrace_append hprefix tailTrace_2102579
  have hstable : (prefixWord ++ tailWord_2102579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102579).length < 2 ^ (prefixWord ++ tailWord_2102579).sum := by decide
  have hdescent : baseEnd_2102579 < baseStart_2102579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102586 : List Nat := [3, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4]
def baseStart_2102586 : Nat := 118140960795 + 2102586 * 2 ^ 59
def prefixEnd_2102586 : Nat := 4983230072969 + 3 ^ 40 * 2102586 * 2
def baseEnd_2102586 : Nat := 1079637235414415856305389

theorem tailTrace_2102586 : CollatzResearch.WordTrace tailWord_2102586 prefixEnd_2102586 1079637235414415856305389 := by
  unfold tailWord_2102586
  simp only [CollatzResearch.WordTrace]
  refine ⟨19171902890174372486261903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51125074373798326630031741 19171902890174372486261903)
  ·
    refine ⟨28757854335261558729392855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19171902890174372486261903 28757854335261558729392855)
    ·
      refine ⟨43136781502892338094089283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28757854335261558729392855 43136781502892338094089283)
      ·
        refine ⟨64705172254338507141133925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43136781502892338094089283 64705172254338507141133925)
        ·
          refine ⟨12132219797688470088962611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64705172254338507141133925 12132219797688470088962611)
          ·
            refine ⟨18198329696532705133443917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12132219797688470088962611 18198329696532705133443917)
            ·
              refine ⟨6824373636199764425041469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18198329696532705133443917 6824373636199764425041469)
              ·
                refine ⟨2559140113574911659390551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6824373636199764425041469 2559140113574911659390551)
                ·
                  refine ⟨3838710170362367489085827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2559140113574911659390551 3838710170362367489085827)
                  ·
                    refine ⟨5758065255543551233628741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3838710170362367489085827 5758065255543551233628741)
                    ·
                      refine ⟨1079637235414415856305389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5758065255543551233628741 1079637235414415856305389)
                      ·
                        rfl

theorem cell23_2102586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4].length) (baseStart_2102586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102586 prefixEnd_2102586 := by exact prefixLift 2102586
  have htrace : WordTrace (prefixWord ++ tailWord_2102586) baseStart_2102586 baseEnd_2102586 := by
    simpa [prefixWord, tailWord_2102586, baseEnd_2102586] using wordTrace_append hprefix tailTrace_2102586
  have hstable : (prefixWord ++ tailWord_2102586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102586).length < 2 ^ (prefixWord ++ tailWord_2102586).sum := by decide
  have hdescent : baseEnd_2102586 < baseStart_2102586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102592 : List Nat := [2, 1, 1, 2, 2, 1, 14]
def baseStart_2102592 : Nat := 118140960795 + 2102592 * 2 ^ 59
def prefixEnd_2102592 : Nat := 4983230072969 + 3 ^ 40 * 2102592 * 2
def baseEnd_2102592 : Nat := 13328892793806701639881

theorem tailTrace_2102592 : CollatzResearch.WordTrace tailWord_2102592 prefixEnd_2102592 13328892793806701639881 := by
  unfold tailWord_2102592
  simp only [CollatzResearch.WordTrace]
  refine ⟨38343915199337876484883015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51125220265783835313177353 38343915199337876484883015)
  ·
    refine ⟨57515872799006814727324523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38343915199337876484883015 57515872799006814727324523)
    ·
      refine ⟨86273809198510222090986785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57515872799006814727324523 86273809198510222090986785)
      ·
        refine ⟨64705356898882666568240089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86273809198510222090986785 64705356898882666568240089)
        ·
          refine ⟨48529017674161999926180067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64705356898882666568240089 48529017674161999926180067)
          ·
            refine ⟨72793526511242999889270101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48529017674161999926180067 72793526511242999889270101)
            ·
              refine ⟨13328892793806701639881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 72793526511242999889270101 13328892793806701639881)
              ·
                rfl

theorem cell23_2102592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 14].length) (baseStart_2102592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102592 prefixEnd_2102592 := by exact prefixLift 2102592
  have htrace : WordTrace (prefixWord ++ tailWord_2102592) baseStart_2102592 baseEnd_2102592 := by
    simpa [prefixWord, tailWord_2102592, baseEnd_2102592] using wordTrace_append hprefix tailTrace_2102592
  have hstable : (prefixWord ++ tailWord_2102592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102592).length < 2 ^ (prefixWord ++ tailWord_2102592).sum := by decide
  have hdescent : baseEnd_2102592 < baseStart_2102592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102637 : List Nat := [1, 5, 1, 1, 1, 3, 3, 3, 1, 2, 2]
def baseStart_2102637 : Nat := 118140960795 + 2102637 * 2 ^ 59
def prefixEnd_2102637 : Nat := 4983230072969 + 3 ^ 40 * 2102637 * 2
def baseEnd_2102637 : Nat := 1079663422927795156767655

theorem tailTrace_2102637 : CollatzResearch.WordTrace tailWord_2102637 prefixEnd_2102637 1079663422927795156767655 := by
  unfold tailWord_2102637
  simp only [CollatzResearch.WordTrace]
  refine ⟨76689471683512725655154165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51126314455675150436769443 76689471683512725655154165)
  ·
    refine ⟨7189637970329318030170703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76689471683512725655154165 7189637970329318030170703)
    ·
      refine ⟨10784456955493977045256055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7189637970329318030170703 10784456955493977045256055)
      ·
        refine ⟨16176685433240965567884083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10784456955493977045256055 16176685433240965567884083)
        ·
          refine ⟨24265028149861448351826125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16176685433240965567884083 24265028149861448351826125)
          ·
            refine ⟨9099385556198043131934797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24265028149861448351826125 9099385556198043131934797)
            ·
              refine ⟨3412269583574266174475549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9099385556198043131934797 3412269583574266174475549)
              ·
                refine ⟨1279601093840349815428331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3412269583574266174475549 1279601093840349815428331)
                ·
                  refine ⟨1919401640760524723142497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1279601093840349815428331 1919401640760524723142497)
                  ·
                    refine ⟨1439551230570393542356873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1919401640760524723142497 1439551230570393542356873)
                    ·
                      refine ⟨1079663422927795156767655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1439551230570393542356873 1079663422927795156767655)
                      ·
                        rfl

theorem cell23_2102637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_2102637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102637 prefixEnd_2102637 := by exact prefixLift 2102637
  have htrace : WordTrace (prefixWord ++ tailWord_2102637) baseStart_2102637 baseEnd_2102637 := by
    simpa [prefixWord, tailWord_2102637, baseEnd_2102637] using wordTrace_append hprefix tailTrace_2102637
  have hstable : (prefixWord ++ tailWord_2102637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102637).length < 2 ^ (prefixWord ++ tailWord_2102637).sum := by decide
  have hdescent : baseEnd_2102637 < baseStart_2102637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102653 : List Nat := [1, 4, 1, 1, 2, 2, 2, 4, 2, 1, 3]
def baseStart_2102653 : Nat := 118140960795 + 2102653 * 2 ^ 59
def prefixEnd_2102653 : Nat := 4983230072969 + 3 ^ 40 * 2102653 * 2
def baseEnd_2102653 : Nat := 1079671638618267094167581

theorem tailTrace_2102653 : CollatzResearch.WordTrace tailWord_2102653 prefixEnd_2102653 1079671638618267094167581 := by
  unfold tailWord_2102653
  simp only [CollatzResearch.WordTrace]
  refine ⟨76690055251454760387736613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51126703500969840258491075 76690055251454760387736613)
  ·
    refine ⟨14379385359647767572700615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76690055251454760387736613 14379385359647767572700615)
    ·
      refine ⟨21569078039471651359050923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14379385359647767572700615 21569078039471651359050923)
      ·
        refine ⟨32353617059207477038576385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21569078039471651359050923 32353617059207477038576385)
        ·
          refine ⟨24265212794405607778932289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32353617059207477038576385 24265212794405607778932289)
          ·
            refine ⟨18198909595804205834199217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24265212794405607778932289 18198909595804205834199217)
            ·
              refine ⟨13649182196853154375649413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18198909595804205834199217 13649182196853154375649413)
              ·
                refine ⟨2559221661909966445434265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13649182196853154375649413 2559221661909966445434265)
                ·
                  refine ⟨1919416246432474834075699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2559221661909966445434265 1919416246432474834075699)
                  ·
                    refine ⟨2879124369648712251113549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1919416246432474834075699 2879124369648712251113549)
                    ·
                      refine ⟨1079671638618267094167581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2879124369648712251113549 1079671638618267094167581)
                      ·
                        rfl

theorem cell23_2102653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_2102653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102653 prefixEnd_2102653 := by exact prefixLift 2102653
  have htrace : WordTrace (prefixWord ++ tailWord_2102653) baseStart_2102653 baseEnd_2102653 := by
    simpa [prefixWord, tailWord_2102653, baseEnd_2102653] using wordTrace_append hprefix tailTrace_2102653
  have hstable : (prefixWord ++ tailWord_2102653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102653).length < 2 ^ (prefixWord ++ tailWord_2102653).sum := by decide
  have hdescent : baseEnd_2102653 < baseStart_2102653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102674 : List Nat := [3, 2, 3, 3, 2, 1, 1, 2, 1, 2, 3]
def baseStart_2102674 : Nat := 118140960795 + 2102674 * 2 ^ 59
def prefixEnd_2102674 : Nat := 4983230072969 + 3 ^ 40 * 2102674 * 2
def baseEnd_2102674 : Nat := 1079682421712011512004985

theorem tailTrace_2102674 : CollatzResearch.WordTrace tailWord_2102674 prefixEnd_2102674 1079682421712011512004985 := by
  unfold tailWord_2102674
  simp only [CollatzResearch.WordTrace]
  refine ⟨19172705296094670243562769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51127214122919120649500717 19172705296094670243562769)
  ·
    refine ⟨14379528972071002682672077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19172705296094670243562769 14379528972071002682672077)
    ·
      refine ⟨5392323364526626006002029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14379528972071002682672077 5392323364526626006002029)
      ·
        refine ⟨2022121261697484752250761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5392323364526626006002029 2022121261697484752250761)
        ·
          refine ⟨1516590946273113564188071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2022121261697484752250761 1516590946273113564188071)
          ·
            refine ⟨2274886419409670346282107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1516590946273113564188071 2274886419409670346282107)
            ·
              refine ⟨3412329629114505519423161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2274886419409670346282107 3412329629114505519423161)
              ·
                refine ⟨2559247221835879139567371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3412329629114505519423161 2559247221835879139567371)
                ·
                  refine ⟨3838870832753818709351057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2559247221835879139567371 3838870832753818709351057)
                  ·
                    refine ⟨2879153124565364032013293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3838870832753818709351057 2879153124565364032013293)
                    ·
                      refine ⟨1079682421712011512004985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2879153124565364032013293 1079682421712011512004985)
                      ·
                        rfl

theorem cell23_2102674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_2102674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102674 prefixEnd_2102674 := by exact prefixLift 2102674
  have htrace : WordTrace (prefixWord ++ tailWord_2102674) baseStart_2102674 baseEnd_2102674 := by
    simpa [prefixWord, tailWord_2102674, baseEnd_2102674] using wordTrace_append hprefix tailTrace_2102674
  have hstable : (prefixWord ++ tailWord_2102674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102674).length < 2 ^ (prefixWord ++ tailWord_2102674).sum := by decide
  have hdescent : baseEnd_2102674 < baseStart_2102674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102680 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 3, 3, 2]
def baseStart_2102680 : Nat := 118140960795 + 2102680 * 2 ^ 59
def prefixEnd_2102680 : Nat := 4983230072969 + 3 ^ 40 * 2102680 * 2
def baseEnd_2102680 : Nat := 1079685502595938488529957

theorem tailTrace_2102680 : CollatzResearch.WordTrace tailWord_2102680 prefixEnd_2102680 1079685502595938488529957 := by
  unfold tailWord_2102680
  simp only [CollatzResearch.WordTrace]
  refine ⟨38345520011178471999484747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51127360014904629332646329 38345520011178471999484747)
  ·
    refine ⟨57518280016767707999227121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38345520011178471999484747 57518280016767707999227121)
    ·
      refine ⟨43138710012575780999420341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57518280016767707999227121 43138710012575780999420341)
      ·
        refine ⟨4044254063678979468695657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43138710012575780999420341 4044254063678979468695657)
        ·
          refine ⟨3033190547759234601521743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4044254063678979468695657 3033190547759234601521743)
          ·
            refine ⟨4549785821638851902282615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3033190547759234601521743 4549785821638851902282615)
            ·
              refine ⟨6824678732458277853423923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4549785821638851902282615 6824678732458277853423923)
              ·
                refine ⟨10237018098687416780135885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6824678732458277853423923 10237018098687416780135885)
                ·
                  refine ⟨3838881787007781292550957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10237018098687416780135885 3838881787007781292550957)
                  ·
                    refine ⟨1439580670127917984706609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3838881787007781292550957 1439580670127917984706609)
                    ·
                      refine ⟨1079685502595938488529957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1439580670127917984706609 1079685502595938488529957)
                      ·
                        rfl

theorem cell23_2102680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_2102680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102680 prefixEnd_2102680 := by exact prefixLift 2102680
  have htrace : WordTrace (prefixWord ++ tailWord_2102680) baseStart_2102680 baseEnd_2102680 := by
    simpa [prefixWord, tailWord_2102680, baseEnd_2102680] using wordTrace_append hprefix tailTrace_2102680
  have hstable : (prefixWord ++ tailWord_2102680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102680).length < 2 ^ (prefixWord ++ tailWord_2102680).sum := by decide
  have hdescent : baseEnd_2102680 < baseStart_2102680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102693 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 4, 2, 2]
def baseStart_2102693 : Nat := 118140960795 + 2102693 * 2 ^ 59
def prefixEnd_2102693 : Nat := 4983230072969 + 3 ^ 40 * 2102693 * 2
def baseEnd_2102693 : Nat := 1079692177844446937667397

theorem tailTrace_2102693 : CollatzResearch.WordTrace tailWord_2102693 prefixEnd_2102693 1079692177844446937667397 := by
  unfold tailWord_2102693
  simp only [CollatzResearch.WordTrace]
  refine ⟨76691514171309847219192733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51127676114206564812795155 76691514171309847219192733)
  ·
    refine ⟨28759317814241192707197275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76691514171309847219192733 28759317814241192707197275)
    ·
      refine ⟨43138976721361789060795913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28759317814241192707197275 43138976721361789060795913)
      ·
        refine ⟨32354232541021341795596935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43138976721361789060795913 32354232541021341795596935)
        ·
          refine ⟨48531348811532012693395403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32354232541021341795596935 48531348811532012693395403)
          ·
            refine ⟨72797023217298019040093105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48531348811532012693395403 72797023217298019040093105)
            ·
              refine ⟨54597767412973514280069829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72797023217298019040093105 54597767412973514280069829)
              ·
                refine ⟨10237081389932533927513093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54597767412973514280069829 10237081389932533927513093)
                ·
                  refine ⟨1919452760612350111408705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10237081389932533927513093 1919452760612350111408705)
                  ·
                    refine ⟨1439589570459262583556529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1919452760612350111408705 1439589570459262583556529)
                    ·
                      refine ⟨1079692177844446937667397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1439589570459262583556529 1079692177844446937667397)
                      ·
                        rfl

theorem cell23_2102693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 2, 2].length) (baseStart_2102693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102693 prefixEnd_2102693 := by exact prefixLift 2102693
  have htrace : WordTrace (prefixWord ++ tailWord_2102693) baseStart_2102693 baseEnd_2102693 := by
    simpa [prefixWord, tailWord_2102693, baseEnd_2102693] using wordTrace_append hprefix tailTrace_2102693
  have hstable : (prefixWord ++ tailWord_2102693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102693).length < 2 ^ (prefixWord ++ tailWord_2102693).sum := by decide
  have hdescent : baseEnd_2102693 < baseStart_2102693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102729 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 1, 7]
def baseStart_2102729 : Nat := 118140960795 + 2102729 * 2 ^ 59
def prefixEnd_2102729 : Nat := 4983230072969 + 3 ^ 40 * 2102729 * 2
def baseEnd_2102729 : Nat := 359903554382669598939077

theorem tailTrace_2102729 : CollatzResearch.WordTrace tailWord_2102729 prefixEnd_2102729 359903554382669598939077 := by
  unfold tailWord_2102729
  simp only [CollatzResearch.WordTrace]
  refine ⟨76692827199179425367503241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51128551466119616911668827 76692827199179425367503241)
  ·
    refine ⟨57519620399384569025627431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76692827199179425367503241 57519620399384569025627431)
    ·
      refine ⟨86279430599076853538441147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57519620399384569025627431 86279430599076853538441147)
      ·
        refine ⟨129419145898615280307661721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86279430599076853538441147 129419145898615280307661721)
        ·
          refine ⟨97064359423961460230746291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129419145898615280307661721 97064359423961460230746291)
          ·
            refine ⟨145596539135942190346119437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97064359423961460230746291 145596539135942190346119437)
            ·
              refine ⟨54598702175978321379794789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145596539135942190346119437 54598702175978321379794789)
              ·
                refine ⟨10237256657995935258711523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54598702175978321379794789 10237256657995935258711523)
                ·
                  refine ⟨15355884986993902888067285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10237256657995935258711523 15355884986993902888067285)
                  ·
                    refine ⟨359903554382669598939077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15355884986993902888067285 359903554382669598939077)
                    ·
                      rfl

theorem cell23_2102729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 7].length) (baseStart_2102729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102729 prefixEnd_2102729 := by exact prefixLift 2102729
  have htrace : WordTrace (prefixWord ++ tailWord_2102729) baseStart_2102729 baseEnd_2102729 := by
    simpa [prefixWord, tailWord_2102729, baseEnd_2102729] using wordTrace_append hprefix tailTrace_2102729
  have hstable : (prefixWord ++ tailWord_2102729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102729).length < 2 ^ (prefixWord ++ tailWord_2102729).sum := by decide
  have hdescent : baseEnd_2102729 < baseStart_2102729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102746 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 1, 7]
def baseStart_2102746 : Nat := 118140960795 + 2102746 * 2 ^ 59
def prefixEnd_2102746 : Nat := 4983230072969 + 3 ^ 40 * 2102746 * 2
def baseEnd_2102746 : Nat := 359906464106378410101551

theorem tailTrace_2102746 : CollatzResearch.WordTrace tailWord_2102746 prefixEnd_2102746 359906464106378410101551 := by
  unfold tailWord_2102746
  simp only [CollatzResearch.WordTrace]
  refine ⟨19173361810029459317718023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51128964826745224847248061 19173361810029459317718023)
  ·
    refine ⟨28760042715044188976577035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19173361810029459317718023 28760042715044188976577035)
    ·
      refine ⟨43140064072566283464865553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28760042715044188976577035 43140064072566283464865553)
      ·
        refine ⟨32355048054424712598649165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43140064072566283464865553 32355048054424712598649165)
        ·
          refine ⟨12133143020409267224493437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32355048054424712598649165 12133143020409267224493437)
          ·
            refine ⟨4549928632653475209185039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12133143020409267224493437 4549928632653475209185039)
            ·
              refine ⟨6824892948980212813777559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4549928632653475209185039 6824892948980212813777559)
              ·
                refine ⟨10237339423470319220666339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6824892948980212813777559 10237339423470319220666339)
                ·
                  refine ⟨15356009135205478830999509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10237339423470319220666339 15356009135205478830999509)
                  ·
                    refine ⟨359906464106378410101551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15356009135205478830999509 359906464106378410101551)
                    ·
                      rfl

theorem cell23_2102746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_2102746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102746 prefixEnd_2102746 := by exact prefixLift 2102746
  have htrace : WordTrace (prefixWord ++ tailWord_2102746) baseStart_2102746 baseEnd_2102746 := by
    simpa [prefixWord, tailWord_2102746, baseEnd_2102746] using wordTrace_append hprefix tailTrace_2102746
  have hstable : (prefixWord ++ tailWord_2102746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102746).length < 2 ^ (prefixWord ++ tailWord_2102746).sum := by decide
  have hdescent : baseEnd_2102746 < baseStart_2102746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102814 : List Nat := [4, 3, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_2102814 : Nat := 118140960795 + 2102814 * 2 ^ 59
def prefixEnd_2102814 : Nat := 4983230072969 + 3 ^ 40 * 2102814 * 2
def baseEnd_2102814 : Nat := 359918103001213654751447

theorem tailTrace_2102814 : CollatzResearch.WordTrace tailWord_2102814 prefixEnd_2102814 359918103001213654751447 := by
  unfold tailWord_2102814
  simp only [CollatzResearch.WordTrace]
  refine ⟨9586990925483935610543437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51130618269247656589564997 9586990925483935610543437)
  ·
    refine ⟨3595121597056475853953789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9586990925483935610543437 3595121597056475853953789)
    ·
      refine ⟨1348170598896178445232671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3595121597056475853953789 1348170598896178445232671)
      ·
        refine ⟨2022255898344267667849007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1348170598896178445232671 2022255898344267667849007)
        ·
          refine ⟨3033383847516401501773511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2022255898344267667849007 3033383847516401501773511)
          ·
            refine ⟨4550075771274602252660267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3033383847516401501773511 4550075771274602252660267)
            ·
              refine ⟨6825113656911903378990401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4550075771274602252660267 6825113656911903378990401)
              ·
                refine ⟨5118835242683927534242801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6825113656911903378990401 5118835242683927534242801)
                ·
                  refine ⟨3839126432012945650682101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5118835242683927534242801 3839126432012945650682101)
                  ·
                    refine ⟨359918103001213654751447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3839126432012945650682101 359918103001213654751447)
                    ·
                      rfl

theorem cell23_2102814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_2102814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102814 prefixEnd_2102814 := by exact prefixLift 2102814
  have htrace : WordTrace (prefixWord ++ tailWord_2102814) baseStart_2102814 baseEnd_2102814 := by
    simpa [prefixWord, tailWord_2102814, baseEnd_2102814] using wordTrace_append hprefix tailTrace_2102814
  have hstable : (prefixWord ++ tailWord_2102814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102814).length < 2 ^ (prefixWord ++ tailWord_2102814).sum := by decide
  have hdescent : baseEnd_2102814 < baseStart_2102814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102840 : List Nat := [2, 1, 2, 1, 4, 4, 2, 1, 6]
def baseStart_2102840 : Nat := 118140960795 + 2102840 * 2 ^ 59
def prefixEnd_2102840 : Nat := 4983230072969 + 3 ^ 40 * 2102840 * 2
def baseEnd_2102840 : Nat := 119974184388961984725469

theorem tailTrace_2102840 : CollatzResearch.WordTrace tailWord_2102840 prefixEnd_2102840 119974184388961984725469 := by
  unfold tailWord_2102840
  simp only [CollatzResearch.WordTrace]
  refine ⟨38348437850888645662396987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51131250467851527549862649 38348437850888645662396987)
  ·
    refine ⟨57522656776332968493595481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38348437850888645662396987 57522656776332968493595481)
    ·
      refine ⟨43141992582249726370196611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57522656776332968493595481 43141992582249726370196611)
      ·
        refine ⟨64712988873374589555294917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43141992582249726370196611 64712988873374589555294917)
        ·
          refine ⟨12133685413757735541617797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64712988873374589555294917 12133685413757735541617797)
          ·
            refine ⟨2275066015079575414053337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12133685413757735541617797 2275066015079575414053337)
            ·
              refine ⟨1706299511309681560540003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2275066015079575414053337 1706299511309681560540003)
              ·
                refine ⟨2559449266964522340810005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1706299511309681560540003 2559449266964522340810005)
                ·
                  refine ⟨119974184388961984725469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2559449266964522340810005 119974184388961984725469)
                  ·
                    rfl

theorem cell23_2102840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 6].length) (baseStart_2102840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102840 prefixEnd_2102840 := by exact prefixLift 2102840
  have htrace : WordTrace (prefixWord ++ tailWord_2102840) baseStart_2102840 baseEnd_2102840 := by
    simpa [prefixWord, tailWord_2102840, baseEnd_2102840] using wordTrace_append hprefix tailTrace_2102840
  have hstable : (prefixWord ++ tailWord_2102840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102840).length < 2 ^ (prefixWord ++ tailWord_2102840).sum := by decide
  have hdescent : baseEnd_2102840 < baseStart_2102840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102854 : List Nat := [6, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_2102854 : Nat := 118140960795 + 2102854 * 2 ^ 59
def prefixEnd_2102854 : Nat := 4983230072969 + 3 ^ 40 * 2102854 * 2
def baseEnd_2102854 : Nat := 1079774848229820807754157

theorem tailTrace_2102854 : CollatzResearch.WordTrace tailWord_2102854 prefixEnd_2102854 1079774848229820807754157 := by
  unfold tailWord_2102854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2396793322616455366118863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51131590882484381143869077 2396793322616455366118863)
  ·
    refine ⟨3595189983924683049178295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2396793322616455366118863 3595189983924683049178295)
    ·
      refine ⟨5392784975887024573767443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3595189983924683049178295 5392784975887024573767443)
      ·
        refine ⟨8089177463830536860651165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5392784975887024573767443 8089177463830536860651165)
        ·
          refine ⟨3033441548936451322744187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8089177463830536860651165 3033441548936451322744187)
          ·
            refine ⟨4550162323404676984116281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3033441548936451322744187 4550162323404676984116281)
            ·
              refine ⟨3412621742553507738087211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4550162323404676984116281 3412621742553507738087211)
              ·
                refine ⟨5118932613830261607130817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3412621742553507738087211 5118932613830261607130817)
                ·
                  refine ⟨3839199460372696205348113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5118932613830261607130817 3839199460372696205348113)
                  ·
                    refine ⟨2879399595279522154011085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3839199460372696205348113 2879399595279522154011085)
                    ·
                      refine ⟨1079774848229820807754157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2879399595279522154011085 1079774848229820807754157)
                      ·
                        rfl

theorem cell23_2102854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_2102854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102854 prefixEnd_2102854 := by exact prefixLift 2102854
  have htrace : WordTrace (prefixWord ++ tailWord_2102854) baseStart_2102854 baseEnd_2102854 := by
    simpa [prefixWord, tailWord_2102854, baseEnd_2102854] using wordTrace_append hprefix tailTrace_2102854
  have hstable : (prefixWord ++ tailWord_2102854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102854).length < 2 ^ (prefixWord ++ tailWord_2102854).sum := by decide
  have hdescent : baseEnd_2102854 < baseStart_2102854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102860 : List Nat := [2, 2, 1, 3, 1, 3, 1, 3, 2, 3, 2]
def baseStart_2102860 : Nat := 118140960795 + 2102860 * 2 ^ 59
def prefixEnd_2102860 : Nat := 4983230072969 + 3 ^ 40 * 2102860 * 2
def baseEnd_2102860 : Nat := 1079777929113747784279129

theorem tailTrace_2102860 : CollatzResearch.WordTrace tailWord_2102860 prefixEnd_2102860 1079777929113747784279129 := by
  unfold tailWord_2102860
  simp only [CollatzResearch.WordTrace]
  refine ⟨38348802580852417370261017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51131736774469889827014689 38348802580852417370261017)
  ·
    refine ⟨28761601935639313027695763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38348802580852417370261017 28761601935639313027695763)
    ·
      refine ⟨43142402903458969541543645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28761601935639313027695763 43142402903458969541543645)
      ·
        refine ⟨16178401088797113578078867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43142402903458969541543645 16178401088797113578078867)
        ·
          refine ⟨24267601633195670367118301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16178401088797113578078867 24267601633195670367118301)
          ·
            refine ⟨9100350612448376387669363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24267601633195670367118301 9100350612448376387669363)
            ·
              refine ⟨13650525918672564581504045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9100350612448376387669363 13650525918672564581504045)
              ·
                refine ⟨5118947219502211718064017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13650525918672564581504045 5118947219502211718064017)
                ·
                  refine ⟨3839210414626658788548013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5118947219502211718064017 3839210414626658788548013)
                  ·
                    refine ⟨1439703905484997045705505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3839210414626658788548013 1439703905484997045705505)
                    ·
                      refine ⟨1079777929113747784279129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1439703905484997045705505 1079777929113747784279129)
                      ·
                        rfl

theorem cell23_2102860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_2102860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102860 prefixEnd_2102860 := by exact prefixLift 2102860
  have htrace : WordTrace (prefixWord ++ tailWord_2102860) baseStart_2102860 baseEnd_2102860 := by
    simpa [prefixWord, tailWord_2102860, baseEnd_2102860] using wordTrace_append hprefix tailTrace_2102860
  have hstable : (prefixWord ++ tailWord_2102860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102860).length < 2 ^ (prefixWord ++ tailWord_2102860).sum := by decide
  have hdescent : baseEnd_2102860 < baseStart_2102860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102873 : List Nat := [1, 2, 1, 2, 2, 1, 1, 7, 1, 1, 4]
def baseStart_2102873 : Nat := 118140960795 + 2102873 * 2 ^ 59
def prefixEnd_2102873 : Nat := 4983230072969 + 3 ^ 40 * 2102873 * 2
def baseEnd_2102873 : Nat := 1079784604362256233416569

theorem tailTrace_2102873 : CollatzResearch.WordTrace tailWord_2102873 prefixEnd_2102873 1079784604362256233416569 := by
  unfold tailWord_2102873
  simp only [CollatzResearch.WordTrace]
  refine ⟨76698079310657737960745273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51132052873771825307163515 76698079310657737960745273)
  ·
    refine ⟨57523559482993303470558955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76698079310657737960745273 57523559482993303470558955)
    ·
      refine ⟨86285339224489955205838433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57523559482993303470558955 86285339224489955205838433)
      ·
        refine ⟨64714004418367466404378825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86285339224489955205838433 64714004418367466404378825)
        ·
          refine ⟨48535503313775599803284119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64714004418367466404378825 48535503313775599803284119)
          ·
            refine ⟨72803254970663399704926179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48535503313775599803284119 72803254970663399704926179)
            ·
              refine ⟨109204882455995099557389269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72803254970663399704926179 109204882455995099557389269)
              ·
                refine ⟨2559489432562385145876311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 109204882455995099557389269 2559489432562385145876311)
                ·
                  refine ⟨3839234148843577718814467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2559489432562385145876311 3839234148843577718814467)
                  ·
                    refine ⟨5758851223265366578221701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3839234148843577718814467 5758851223265366578221701)
                    ·
                      refine ⟨1079784604362256233416569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5758851223265366578221701 1079784604362256233416569)
                      ·
                        rfl

theorem cell23_2102873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 1, 4].length) (baseStart_2102873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102873 prefixEnd_2102873 := by exact prefixLift 2102873
  have htrace : WordTrace (prefixWord ++ tailWord_2102873) baseStart_2102873 baseEnd_2102873 := by
    simpa [prefixWord, tailWord_2102873, baseEnd_2102873] using wordTrace_append hprefix tailTrace_2102873
  have hstable : (prefixWord ++ tailWord_2102873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102873).length < 2 ^ (prefixWord ++ tailWord_2102873).sum := by decide
  have hdescent : baseEnd_2102873 < baseStart_2102873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102884 : List Nat := [2, 3, 1, 1, 2, 3, 4, 2, 1, 1, 3]
def baseStart_2102884 : Nat := 118140960795 + 2102884 * 2 ^ 59
def prefixEnd_2102884 : Nat := 4983230072969 + 3 ^ 40 * 2102884 * 2
def baseEnd_2102884 : Nat := 1079790252649455690379019

theorem tailTrace_2102884 : CollatzResearch.WordTrace tailWord_2102884 prefixEnd_2102884 1079790252649455690379019 := by
  unfold tailWord_2102884
  simp only [CollatzResearch.WordTrace]
  refine ⟨38349240256808943419697853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51132320342411924559597137 38349240256808943419697853)
  ·
    refine ⟨14380965096303353782386695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38349240256808943419697853 14380965096303353782386695)
    ·
      refine ⟨21571447644455030673580043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14380965096303353782386695 21571447644455030673580043)
      ·
        refine ⟨32357171466682546010370065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21571447644455030673580043 32357171466682546010370065)
        ·
          refine ⟨24267878600011909507777549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32357171466682546010370065 24267878600011909507777549)
          ·
            refine ⟨9100454475004466065416581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24267878600011909507777549 9100454475004466065416581)
            ·
              refine ⟨1706335214063337387265609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9100454475004466065416581 1706335214063337387265609)
              ·
                refine ⟨1279751410547503040449207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1706335214063337387265609 1279751410547503040449207)
                ·
                  refine ⟨1919627115821254560673811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1279751410547503040449207 1919627115821254560673811)
                  ·
                    refine ⟨2879440673731881841010717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1919627115821254560673811 2879440673731881841010717)
                    ·
                      refine ⟨1079790252649455690379019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2879440673731881841010717 1079790252649455690379019)
                      ·
                        rfl

theorem cell23_2102884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 1, 1, 3].length) (baseStart_2102884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102884 prefixEnd_2102884 := by exact prefixLift 2102884
  have htrace : WordTrace (prefixWord ++ tailWord_2102884) baseStart_2102884 baseEnd_2102884 := by
    simpa [prefixWord, tailWord_2102884, baseEnd_2102884] using wordTrace_append hprefix tailTrace_2102884
  have hstable : (prefixWord ++ tailWord_2102884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102884).length < 2 ^ (prefixWord ++ tailWord_2102884).sum := by decide
  have hdescent : baseEnd_2102884 < baseStart_2102884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102923 : List Nat := [1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 3]
def baseStart_2102923 : Nat := 118140960795 + 2102923 * 2 ^ 59
def prefixEnd_2102923 : Nat := 4983230072969 + 3 ^ 40 * 2102923 * 2
def baseEnd_2102923 : Nat := 1079810278394981037791339

theorem tailTrace_2102923 : CollatzResearch.WordTrace tailWord_2102923 prefixEnd_2102923 1079810278394981037791339 := by
  unfold tailWord_2102923
  simp only [CollatzResearch.WordTrace]
  refine ⟨76699902960476596500065423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51133268640317731000043615 76699902960476596500065423)
  ·
    refine ⟨115049854440714894750098135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76699902960476596500065423 115049854440714894750098135)
    ·
      refine ⟨172574781661072342125147203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115049854440714894750098135 172574781661072342125147203)
      ·
        refine ⟨258862172491608513187720805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172574781661072342125147203 258862172491608513187720805)
        ·
          refine ⟨48536657342176596222697651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 258862172491608513187720805 48536657342176596222697651)
          ·
            refine ⟨72804986013264894334046477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48536657342176596222697651 72804986013264894334046477)
            ·
              refine ⟨27301869754974335375267429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72804986013264894334046477 27301869754974335375267429)
              ·
                refine ⟨5119100579057687882862643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27301869754974335375267429 5119100579057687882862643)
                ·
                  refine ⟨7678650868586531824293965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5119100579057687882862643 7678650868586531824293965)
                  ·
                    refine ⟨2879494075719949434110237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7678650868586531824293965 2879494075719949434110237)
                    ·
                      refine ⟨1079810278394981037791339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2879494075719949434110237 1079810278394981037791339)
                      ·
                        rfl

theorem cell23_2102923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 3].length) (baseStart_2102923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102923 prefixEnd_2102923 := by exact prefixLift 2102923
  have htrace : WordTrace (prefixWord ++ tailWord_2102923) baseStart_2102923 baseEnd_2102923 := by
    simpa [prefixWord, tailWord_2102923, baseEnd_2102923] using wordTrace_append hprefix tailTrace_2102923
  have hstable : (prefixWord ++ tailWord_2102923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102923).length < 2 ^ (prefixWord ++ tailWord_2102923).sum := by decide
  have hdescent : baseEnd_2102923 < baseStart_2102923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102924 : List Nat := [2, 2, 1, 2, 1, 1, 6, 3, 1, 2, 2]
def baseStart_2102924 : Nat := 118140960795 + 2102924 * 2 ^ 59
def prefixEnd_2102924 : Nat := 4983230072969 + 3 ^ 40 * 2102924 * 2
def baseEnd_2102924 : Nat := 1079810791875635533878835

theorem tailTrace_2102924 : CollatzResearch.WordTrace tailWord_2102924 prefixEnd_2102924 1079810791875635533878835 := by
  unfold tailWord_2102924
  simp only [CollatzResearch.WordTrace]
  refine ⟨38349969716736486835425913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51133292955648649113901217 38349969716736486835425913)
  ·
    refine ⟨28762477287552365126569435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38349969716736486835425913 28762477287552365126569435)
    ·
      refine ⟨43143715931328547689854153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28762477287552365126569435 43143715931328547689854153)
      ·
        refine ⟨32357786948496410767390615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43143715931328547689854153 32357786948496410767390615)
        ·
          refine ⟨48536680422744616151085923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32357786948496410767390615 48536680422744616151085923)
          ·
            refine ⟨72805020634116924226628885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48536680422744616151085923 72805020634116924226628885)
            ·
              refine ⟨3412735342224230823123229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72805020634116924226628885 3412735342224230823123229)
              ·
                refine ⟨1279775753334086558671211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3412735342224230823123229 1279775753334086558671211)
                ·
                  refine ⟨1919663630001129838006817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1279775753334086558671211 1919663630001129838006817)
                  ·
                    refine ⟨1439747722500847378505113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1919663630001129838006817 1439747722500847378505113)
                    ·
                      refine ⟨1079810791875635533878835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1439747722500847378505113 1079810791875635533878835)
                      ·
                        rfl

theorem cell23_2102924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 1, 2, 2].length) (baseStart_2102924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102924 prefixEnd_2102924 := by exact prefixLift 2102924
  have htrace : WordTrace (prefixWord ++ tailWord_2102924) baseStart_2102924 baseEnd_2102924 := by
    simpa [prefixWord, tailWord_2102924, baseEnd_2102924] using wordTrace_append hprefix tailTrace_2102924
  have hstable : (prefixWord ++ tailWord_2102924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102924).length < 2 ^ (prefixWord ++ tailWord_2102924).sum := by decide
  have hdescent : baseEnd_2102924 < baseStart_2102924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102967 : List Nat := [1, 1, 3, 1, 5, 1, 1, 4, 1, 3, 2]
def baseStart_2102967 : Nat := 118140960795 + 2102967 * 2 ^ 59
def prefixEnd_2102967 : Nat := 4983230072969 + 3 ^ 40 * 2102967 * 2
def baseEnd_2102967 : Nat := 1079832871543778865641137

theorem tailTrace_2102967 : CollatzResearch.WordTrace tailWord_2102967 prefixEnd_2102967 1079832871543778865641137 := by
  unfold tailWord_2102967
  simp only [CollatzResearch.WordTrace]
  refine ⟨76701507772317192014667155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51134338514878128009778103 76701507772317192014667155)
  ·
    refine ⟨115052261658475788022000733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76701507772317192014667155 115052261658475788022000733)
    ·
      refine ⟨43144598121928420508250275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115052261658475788022000733 43144598121928420508250275)
      ·
        refine ⟨64716897182892630762375413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43144598121928420508250275 64716897182892630762375413)
        ·
          refine ⟨6067209110896184133972695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64716897182892630762375413 6067209110896184133972695)
          ·
            refine ⟨9100813666344276200959043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6067209110896184133972695 9100813666344276200959043)
            ·
              refine ⟨13651220499516414301438565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9100813666344276200959043 13651220499516414301438565)
              ·
                refine ⟨2559603843659327681519731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13651220499516414301438565 2559603843659327681519731)
                ·
                  refine ⟨3839405765488991522279597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2559603843659327681519731 3839405765488991522279597)
                  ·
                    refine ⟨1439777162058371820854849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3839405765488991522279597 1439777162058371820854849)
                    ·
                      refine ⟨1079832871543778865641137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1439777162058371820854849 1079832871543778865641137)
                      ·
                        rfl

theorem cell23_2102967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 3, 2].length) (baseStart_2102967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102967 prefixEnd_2102967 := by exact prefixLift 2102967
  have htrace : WordTrace (prefixWord ++ tailWord_2102967) baseStart_2102967 baseEnd_2102967 := by
    simpa [prefixWord, tailWord_2102967, baseEnd_2102967] using wordTrace_append hprefix tailTrace_2102967
  have hstable : (prefixWord ++ tailWord_2102967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102967).length < 2 ^ (prefixWord ++ tailWord_2102967).sum := by decide
  have hdescent : baseEnd_2102967 < baseStart_2102967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102983 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 5]
def baseStart_2102983 : Nat := 118140960795 + 2102983 * 2 ^ 59
def prefixEnd_2102983 : Nat := 4983230072969 + 3 ^ 40 * 2102983 * 2
def baseEnd_2102983 : Nat := 1079841087234250803041063

theorem tailTrace_2102983 : CollatzResearch.WordTrace tailWord_2102983 prefixEnd_2102983 1079841087234250803041063 := by
  unfold tailWord_2102983
  simp only [CollatzResearch.WordTrace]
  refine ⟨76702091340259226747249603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51134727560172817831499735 76702091340259226747249603)
  ·
    refine ⟨115053137010388840120874405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76702091340259226747249603 115053137010388840120874405)
    ·
      refine ⟨21572463189447907522663951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115053137010388840120874405 21572463189447907522663951)
      ·
        refine ⟨32358694784171861283995927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21572463189447907522663951 32358694784171861283995927)
        ·
          refine ⟨48538042176257791925993891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32358694784171861283995927 48538042176257791925993891)
          ·
            refine ⟨72807063264386687888990837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48538042176257791925993891 72807063264386687888990837)
            ·
              refine ⟨6825662181036251989592891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72807063264386687888990837 6825662181036251989592891)
              ·
                refine ⟨10238493271554377984389337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6825662181036251989592891 10238493271554377984389337)
                ·
                  refine ⟨7678869953665783488292003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10238493271554377984389337 7678869953665783488292003)
                  ·
                    refine ⟨11518304930498675232438005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7678869953665783488292003 11518304930498675232438005)
                    ·
                      refine ⟨1079841087234250803041063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11518304930498675232438005 1079841087234250803041063)
                      ·
                        rfl

theorem cell23_2102983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_2102983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2102983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2102983 prefixEnd_2102983 := by exact prefixLift 2102983
  have htrace : WordTrace (prefixWord ++ tailWord_2102983) baseStart_2102983 baseEnd_2102983 := by
    simpa [prefixWord, tailWord_2102983, baseEnd_2102983] using wordTrace_append hprefix tailTrace_2102983
  have hstable : (prefixWord ++ tailWord_2102983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102983).length < 2 ^ (prefixWord ++ tailWord_2102983).sum := by decide
  have hdescent : baseEnd_2102983 < baseStart_2102983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103043 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 5]
def baseStart_2103043 : Nat := 118140960795 + 2103043 * 2 ^ 59
def prefixEnd_2103043 : Nat := 4983230072969 + 3 ^ 40 * 2103043 * 2
def baseEnd_2103043 : Nat := 1079871896073520568290787

theorem tailTrace_2103043 : CollatzResearch.WordTrace tailWord_2103043 prefixEnd_2103043 1079871896073520568290787 := by
  unfold tailWord_2103043
  simp only [CollatzResearch.WordTrace]
  refine ⟨76704279720041856994433783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51136186480027904662955855 76704279720041856994433783)
  ·
    refine ⟨115056419580062785491650675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76704279720041856994433783 115056419580062785491650675)
    ·
      refine ⟨172584629370094178237476013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115056419580062785491650675 172584629370094178237476013)
      ·
        refine ⟨64719236013785316839053505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172584629370094178237476013 64719236013785316839053505)
        ·
          refine ⟨48539427010338987629290129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64719236013785316839053505 48539427010338987629290129)
          ·
            refine ⟨36404570257754240721967597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48539427010338987629290129 36404570257754240721967597)
            ·
              refine ⟨13651713846657840270737849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36404570257754240721967597 13651713846657840270737849)
              ·
                refine ⟨10238785384993380203053387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13651713846657840270737849 10238785384993380203053387)
                ·
                  refine ⟨15358178077490070304580081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10238785384993380203053387 15358178077490070304580081)
                  ·
                    refine ⟨11518633558117552728435061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15358178077490070304580081 11518633558117552728435061)
                    ·
                      refine ⟨1079871896073520568290787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11518633558117552728435061 1079871896073520568290787)
                      ·
                        rfl

theorem cell23_2103043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_2103043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103043 prefixEnd_2103043 := by exact prefixLift 2103043
  have htrace : WordTrace (prefixWord ++ tailWord_2103043) baseStart_2103043 baseEnd_2103043 := by
    simpa [prefixWord, tailWord_2103043, baseEnd_2103043] using wordTrace_append hprefix tailTrace_2103043
  have hstable : (prefixWord ++ tailWord_2103043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103043).length < 2 ^ (prefixWord ++ tailWord_2103043).sum := by decide
  have hdescent : baseEnd_2103043 < baseStart_2103043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103050 : List Nat := [3, 1, 2, 2, 1, 3, 2, 2, 2, 5]
def baseStart_2103050 : Nat := 118140960795 + 2103050 * 2 ^ 59
def prefixEnd_2103050 : Nat := 4983230072969 + 3 ^ 40 * 2103050 * 2
def baseEnd_2103050 : Nat := 359958496812700680301085

theorem tailTrace_2103050 : CollatzResearch.WordTrace tailWord_2103050 prefixEnd_2103050 359958496812700680301085 := by
  unfold tailWord_2103050
  simp only [CollatzResearch.WordTrace]
  refine ⟨19176133757754124297484651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51136356687344331459959069 19176133757754124297484651)
  ·
    refine ⟨28764200636631186446226977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19176133757754124297484651 28764200636631186446226977)
    ·
      refine ⟨21573150477473389834670233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28764200636631186446226977 21573150477473389834670233)
      ·
        refine ⟨16179862858105042376002675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21573150477473389834670233 16179862858105042376002675)
        ·
          refine ⟨24269794287157563564004013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16179862858105042376002675 24269794287157563564004013)
          ·
            refine ⟨9101172857684086336501505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24269794287157563564004013 9101172857684086336501505)
            ·
              refine ⟨6825879643263064752376129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9101172857684086336501505 6825879643263064752376129)
              ·
                refine ⟨5119409732447298564282097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6825879643263064752376129 5119409732447298564282097)
                ·
                  refine ⟨3839557299335473923211573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5119409732447298564282097 3839557299335473923211573)
                  ·
                    refine ⟨359958496812700680301085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3839557299335473923211573 359958496812700680301085)
                    ·
                      rfl

theorem cell23_2103050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_2103050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103050 prefixEnd_2103050 := by exact prefixLift 2103050
  have htrace : WordTrace (prefixWord ++ tailWord_2103050) baseStart_2103050 baseEnd_2103050 := by
    simpa [prefixWord, tailWord_2103050, baseEnd_2103050] using wordTrace_append hprefix tailTrace_2103050
  have hstable : (prefixWord ++ tailWord_2103050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103050).length < 2 ^ (prefixWord ++ tailWord_2103050).sum := by decide
  have hdescent : baseEnd_2103050 < baseStart_2103050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103113 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 1, 1, 8]
def baseStart_2103113 : Nat := 118140960795 + 2103113 * 2 ^ 59
def prefixEnd_2103113 : Nat := 4983230072969 + 3 ^ 40 * 2103113 * 2
def baseEnd_2103113 : Nat := 1079907839719335294415465

theorem tailTrace_2103113 : CollatzResearch.WordTrace tailWord_2103113 prefixEnd_2103113 1079907839719335294415465 := by
  unfold tailWord_2103113
  simp only [CollatzResearch.WordTrace]
  refine ⟨76706832829788258949481993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51137888553192172632987995 76706832829788258949481993)
  ·
    refine ⟨57530124622341194212111495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76706832829788258949481993 57530124622341194212111495)
    ·
      refine ⟨86295186933511791318167243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57530124622341194212111495 86295186933511791318167243)
      ·
        refine ⟨129442780400267686977250865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86295186933511791318167243 129442780400267686977250865)
        ·
          refine ⟨97082085300200765232938149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129442780400267686977250865 97082085300200765232938149)
          ·
            refine ⟨18202890993787643481175903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97082085300200765232938149 18202890993787643481175903)
            ·
              refine ⟨27304336490681465221763855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18202890993787643481175903 27304336490681465221763855)
              ·
                refine ⟨40956504736022197832645783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27304336490681465221763855 40956504736022197832645783)
                ·
                  refine ⟨61434757104033296748968675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40956504736022197832645783 61434757104033296748968675)
                  ·
                    refine ⟨92152135656049945123453013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61434757104033296748968675 92152135656049945123453013)
                    ·
                      refine ⟨1079907839719335294415465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 92152135656049945123453013 1079907839719335294415465)
                      ·
                        rfl

theorem cell23_2103113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_2103113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103113 prefixEnd_2103113 := by exact prefixLift 2103113
  have htrace : WordTrace (prefixWord ++ tailWord_2103113) baseStart_2103113 baseEnd_2103113 := by
    simpa [prefixWord, tailWord_2103113, baseEnd_2103113] using wordTrace_append hprefix tailTrace_2103113
  have hstable : (prefixWord ++ tailWord_2103113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103113).length < 2 ^ (prefixWord ++ tailWord_2103113).sum := by decide
  have hdescent : baseEnd_2103113 < baseStart_2103113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103137 : List Nat := [1, 2, 3, 1, 1, 1, 3, 4, 3, 1, 3]
def baseStart_2103137 : Nat := 118140960795 + 2103137 * 2 ^ 59
def prefixEnd_2103137 : Nat := 4983230072969 + 3 ^ 40 * 2103137 * 2
def baseEnd_2103137 : Nat := 1079920163255043200515355

theorem tailTrace_2103137 : CollatzResearch.WordTrace tailWord_2103137 prefixEnd_2103137 1079920163255043200515355 := by
  unfold tailWord_2103137
  simp only [CollatzResearch.WordTrace]
  refine ⟨76707708181701311048355665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51138472121134207365570443 76707708181701311048355665)
  ·
    refine ⟨57530781136275983286266749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76707708181701311048355665 57530781136275983286266749)
    ·
      refine ⟨21574042926103493732350031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57530781136275983286266749 21574042926103493732350031)
      ·
        refine ⟨32361064389155240598525047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21574042926103493732350031 32361064389155240598525047)
        ·
          refine ⟨48541596583732860897787571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32361064389155240598525047 48541596583732860897787571)
          ·
            refine ⟨72812394875599291346681357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48541596583732860897787571 72812394875599291346681357)
            ·
              refine ⟨27304648078349734255005509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72812394875599291346681357 27304648078349734255005509)
              ·
                refine ⟨5119621514690575172813533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27304648078349734255005509 5119621514690575172813533)
                ·
                  refine ⟨1919858068008965689805075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5119621514690575172813533 1919858068008965689805075)
                  ·
                    refine ⟨2879787102013448534707613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1919858068008965689805075 2879787102013448534707613)
                    ·
                      refine ⟨1079920163255043200515355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2879787102013448534707613 1079920163255043200515355)
                      ·
                        rfl

theorem cell23_2103137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_2103137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103137 prefixEnd_2103137 := by exact prefixLift 2103137
  have htrace : WordTrace (prefixWord ++ tailWord_2103137) baseStart_2103137 baseEnd_2103137 := by
    simpa [prefixWord, tailWord_2103137, baseEnd_2103137] using wordTrace_append hprefix tailTrace_2103137
  have hstable : (prefixWord ++ tailWord_2103137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103137).length < 2 ^ (prefixWord ++ tailWord_2103137).sum := by decide
  have hdescent : baseEnd_2103137 < baseStart_2103137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103147 : List Nat := [1, 1, 1, 1, 2, 2, 3, 5, 2, 3, 2]
def baseStart_2103147 : Nat := 118140960795 + 2103147 * 2 ^ 59
def prefixEnd_2103147 : Nat := 4983230072969 + 3 ^ 40 * 2103147 * 2
def baseEnd_2103147 : Nat := 1079925298061588161390309

theorem tailTrace_2103147 : CollatzResearch.WordTrace tailWord_2103147 prefixEnd_2103147 1079925298061588161390309 := by
  unfold tailWord_2103147
  simp only [CollatzResearch.WordTrace]
  refine ⟨76708072911665082756219695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51138715274443388504146463 76708072911665082756219695)
  ·
    refine ⟨115062109367497624134329543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76708072911665082756219695 115062109367497624134329543)
    ·
      refine ⟨172593164051246436201494315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115062109367497624134329543 172593164051246436201494315)
      ·
        refine ⟨258889746076869654302241473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172593164051246436201494315 258889746076869654302241473)
        ·
          refine ⟨194167309557652240726681105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258889746076869654302241473 194167309557652240726681105)
          ·
            refine ⟨145625482168239180545010829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194167309557652240726681105 145625482168239180545010829)
            ·
              refine ⟨54609555813089692704379061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145625482168239180545010829 54609555813089692704379061)
              ·
                refine ⟨5119645857477158691035537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54609555813089692704379061 5119645857477158691035537)
                ·
                  refine ⟨3839734393107869018276653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5119645857477158691035537 3839734393107869018276653)
                  ·
                    refine ⟨1439900397415450881853745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3839734393107869018276653 1439900397415450881853745)
                    ·
                      refine ⟨1079925298061588161390309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1439900397415450881853745 1079925298061588161390309)
                      ·
                        rfl

theorem cell23_2103147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 3, 2].length) (baseStart_2103147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103147 prefixEnd_2103147 := by exact prefixLift 2103147
  have htrace : WordTrace (prefixWord ++ tailWord_2103147) baseStart_2103147 baseEnd_2103147 := by
    simpa [prefixWord, tailWord_2103147, baseEnd_2103147] using wordTrace_append hprefix tailTrace_2103147
  have hstable : (prefixWord ++ tailWord_2103147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103147).length < 2 ^ (prefixWord ++ tailWord_2103147).sum := by decide
  have hdescent : baseEnd_2103147 < baseStart_2103147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103157 : List Nat := [1, 3, 4, 1, 1, 1, 1, 5, 1, 5]
def baseStart_2103157 : Nat := 118140960795 + 2103157 * 2 ^ 59
def prefixEnd_2103157 : Nat := 4983230072969 + 3 ^ 40 * 2103157 * 2
def baseEnd_2103157 : Nat := 359976810956044374088421

theorem tailTrace_2103157 : CollatzResearch.WordTrace tailWord_2103157 prefixEnd_2103157 359976810956044374088421 := by
  unfold tailWord_2103157
  simp only [CollatzResearch.WordTrace]
  refine ⟨76708437641628854464083725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51138958427752569642722483 76708437641628854464083725)
  ·
    refine ⟨28765664115610820424031397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76708437641628854464083725 28765664115610820424031397)
    ·
      refine ⟨5393562021677028829505887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28765664115610820424031397 5393562021677028829505887)
      ·
        refine ⟨8090343032515543244258831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5393562021677028829505887 8090343032515543244258831)
        ·
          refine ⟨12135514548773314866388247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8090343032515543244258831 12135514548773314866388247)
          ·
            refine ⟨18203271823159972299582371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12135514548773314866388247 18203271823159972299582371)
            ·
              refine ⟨27304907734739958449373557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18203271823159972299582371 27304907734739958449373557)
              ·
                refine ⟨2559835100131871104628771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27304907734739958449373557 2559835100131871104628771)
                ·
                  refine ⟨3839752650197806656943157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2559835100131871104628771 3839752650197806656943157)
                  ·
                    refine ⟨359976810956044374088421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3839752650197806656943157 359976810956044374088421)
                    ·
                      rfl

theorem cell23_2103157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_2103157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103157 prefixEnd_2103157 := by exact prefixLift 2103157
  have htrace : WordTrace (prefixWord ++ tailWord_2103157) baseStart_2103157 baseEnd_2103157 := by
    simpa [prefixWord, tailWord_2103157, baseEnd_2103157] using wordTrace_append hprefix tailTrace_2103157
  have hstable : (prefixWord ++ tailWord_2103157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103157).length < 2 ^ (prefixWord ++ tailWord_2103157).sum := by decide
  have hdescent : baseEnd_2103157 < baseStart_2103157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103180 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 2, 6, 3]
def baseStart_2103180 : Nat := 118140960795 + 2103180 * 2 ^ 59
def prefixEnd_2103180 : Nat := 4983230072969 + 3 ^ 40 * 2103180 * 2
def baseEnd_2103180 : Nat := 1079942242923186532277657

theorem tailTrace_2103180 : CollatzResearch.WordTrace tailWord_2103180 prefixEnd_2103180 1079942242923186532277657 := by
  unfold tailWord_2103180
  simp only [CollatzResearch.WordTrace]
  refine ⟨38354638260272764696085497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51139517680363686261447329 38354638260272764696085497)
  ·
    refine ⟨28765978695204573522064123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38354638260272764696085497 28765978695204573522064123)
    ·
      refine ⟨43148968042806860283096185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28765978695204573522064123 43148968042806860283096185)
      ·
        refine ⟨32361726032105145212322139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43148968042806860283096185 32361726032105145212322139)
        ·
          refine ⟨48542589048157717818483209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32361726032105145212322139 48542589048157717818483209)
          ·
            refine ⟨36406941786118288363862407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48542589048157717818483209 36406941786118288363862407)
            ·
              refine ⟨54610412679177432545793611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36406941786118288363862407 54610412679177432545793611)
              ·
                refine ⟨81915619018766148818690417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54610412679177432545793611 81915619018766148818690417)
                ·
                  refine ⟨61436714264074611614017813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81915619018766148818690417 61436714264074611614017813)
                  ·
                    refine ⟨2879845981128497419407085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61436714264074611614017813 2879845981128497419407085)
                    ·
                      refine ⟨1079942242923186532277657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2879845981128497419407085 1079942242923186532277657)
                      ·
                        rfl

theorem cell23_2103180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_2103180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103180 prefixEnd_2103180 := by exact prefixLift 2103180
  have htrace : WordTrace (prefixWord ++ tailWord_2103180) baseStart_2103180 baseEnd_2103180 := by
    simpa [prefixWord, tailWord_2103180, baseEnd_2103180] using wordTrace_append hprefix tailTrace_2103180
  have hstable : (prefixWord ++ tailWord_2103180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103180).length < 2 ^ (prefixWord ++ tailWord_2103180).sum := by decide
  have hdescent : baseEnd_2103180 < baseStart_2103180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103194 : List Nat := [3, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4]
def baseStart_2103194 : Nat := 118140960795 + 2103194 * 2 ^ 59
def prefixEnd_2103194 : Nat := 4983230072969 + 3 ^ 40 * 2103194 * 2
def baseEnd_2103194 : Nat := 1079949431652349477502593

theorem tailTrace_2103194 : CollatzResearch.WordTrace tailWord_2103194 prefixEnd_2103194 1079949431652349477502593 := by
  unfold tailWord_2103194
  simp only [CollatzResearch.WordTrace]
  refine ⟨19177446785623702445795159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51139858094996539855453757 19177446785623702445795159)
  ·
    refine ⟨28766170178435553668692739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19177446785623702445795159 28766170178435553668692739)
    ·
      refine ⟨43149255267653330503039109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28766170178435553668692739 43149255267653330503039109)
      ·
        refine ⟨8090485362684999469319833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43149255267653330503039109 8090485362684999469319833)
        ·
          refine ⟨6067864022013749601989875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8090485362684999469319833 6067864022013749601989875)
          ·
            refine ⟨9101796033020624402984813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6067864022013749601989875 9101796033020624402984813)
            ·
              refine ⟨3413173512382734151119305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9101796033020624402984813 3413173512382734151119305)
              ·
                refine ⟨2559880134287050613339479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3413173512382734151119305 2559880134287050613339479)
                ·
                  refine ⟨3839820201430575920009219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2559880134287050613339479 3839820201430575920009219)
                  ·
                    refine ⟨5759730302145863880013829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3839820201430575920009219 5759730302145863880013829)
                    ·
                      refine ⟨1079949431652349477502593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5759730302145863880013829 1079949431652349477502593)
                      ·
                        rfl

theorem cell23_2103194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_2103194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103194 prefixEnd_2103194 := by exact prefixLift 2103194
  have htrace : WordTrace (prefixWord ++ tailWord_2103194) baseStart_2103194 baseEnd_2103194 := by
    simpa [prefixWord, tailWord_2103194, baseEnd_2103194] using wordTrace_append hprefix tailTrace_2103194
  have hstable : (prefixWord ++ tailWord_2103194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103194).length < 2 ^ (prefixWord ++ tailWord_2103194).sum := by decide
  have hdescent : baseEnd_2103194 < baseStart_2103194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103207 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_2103207 : Nat := 118140960795 + 2103207 * 2 ^ 59
def prefixEnd_2103207 : Nat := 4983230072969 + 3 ^ 40 * 2103207 * 2
def baseEnd_2103207 : Nat := 1079956106900857926640033

theorem tailTrace_2103207 : CollatzResearch.WordTrace tailWord_2103207 prefixEnd_2103207 1079956106900857926640033 := by
  unfold tailWord_2103207
  simp only [CollatzResearch.WordTrace]
  refine ⟨76710261291447713003403875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51140174194298475335602583 76710261291447713003403875)
  ·
    refine ⟨115065391937171569505105813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76710261291447713003403875 115065391937171569505105813)
    ·
      refine ⟨5393690247054917320551835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 115065391937171569505105813 5393690247054917320551835)
      ·
        refine ⟨8090535370582375980827753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5393690247054917320551835 8090535370582375980827753)
        ·
          refine ⟨6067901527936781985620815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8090535370582375980827753 6067901527936781985620815)
          ·
            refine ⟨9101852291905172978431223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6067901527936781985620815 9101852291905172978431223)
            ·
              refine ⟨13652778437857759467646835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9101852291905172978431223 13652778437857759467646835)
              ·
                refine ⟨20479167656786639201470253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13652778437857759467646835 20479167656786639201470253)
                ·
                  refine ⟨7679687871294989700551345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20479167656786639201470253 7679687871294989700551345)
                  ·
                    refine ⟨5759765903471242275413509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7679687871294989700551345 5759765903471242275413509)
                    ·
                      refine ⟨1079956106900857926640033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5759765903471242275413509 1079956106900857926640033)
                      ·
                        rfl

theorem cell23_2103207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_2103207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103207 prefixEnd_2103207 := by exact prefixLift 2103207
  have htrace : WordTrace (prefixWord ++ tailWord_2103207) baseStart_2103207 baseEnd_2103207 := by
    simpa [prefixWord, tailWord_2103207, baseEnd_2103207] using wordTrace_append hprefix tailTrace_2103207
  have hstable : (prefixWord ++ tailWord_2103207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103207).length < 2 ^ (prefixWord ++ tailWord_2103207).sum := by decide
  have hdescent : baseEnd_2103207 < baseStart_2103207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103208 : List Nat := [2, 1, 6, 2, 1, 1, 3, 1, 1, 5]
def baseStart_2103208 : Nat := 118140960795 + 2103208 * 2 ^ 59
def prefixEnd_2103208 : Nat := 4983230072969 + 3 ^ 40 * 2103208 * 2
def baseEnd_2103208 : Nat := 359985540127170807575843

theorem tailTrace_2103208 : CollatzResearch.WordTrace tailWord_2103208 prefixEnd_2103208 359985540127170807575843 := by
  unfold tailWord_2103208
  simp only [CollatzResearch.WordTrace]
  refine ⟨38355148882222045087095139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51140198509629393449460185 38355148882222045087095139)
  ·
    refine ⟨57532723323333067630642709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38355148882222045087095139 57532723323333067630642709)
    ·
      refine ⟨2696846405781237545186377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57532723323333067630642709 2696846405781237545186377)
      ·
        refine ⟨2022634804335928158889783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2696846405781237545186377 2022634804335928158889783)
        ·
          refine ⟨3033952206503892238334675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2022634804335928158889783 3033952206503892238334675)
          ·
            refine ⟨4550928309755838357502013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3033952206503892238334675 4550928309755838357502013)
            ·
              refine ⟨1706598116158439384063255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4550928309755838357502013 1706598116158439384063255)
              ·
                refine ⟨2559897174237659076094883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1706598116158439384063255 2559897174237659076094883)
                ·
                  refine ⟨3839845761356488614142325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2559897174237659076094883 3839845761356488614142325)
                  ·
                    refine ⟨359985540127170807575843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3839845761356488614142325 359985540127170807575843)
                    ·
                      rfl

theorem cell23_2103208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_2103208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103208 prefixEnd_2103208 := by exact prefixLift 2103208
  have htrace : WordTrace (prefixWord ++ tailWord_2103208) baseStart_2103208 baseEnd_2103208 := by
    simpa [prefixWord, tailWord_2103208, baseEnd_2103208] using wordTrace_append hprefix tailTrace_2103208
  have hstable : (prefixWord ++ tailWord_2103208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103208).length < 2 ^ (prefixWord ++ tailWord_2103208).sum := by decide
  have hdescent : baseEnd_2103208 < baseStart_2103208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103244 : List Nat := [2, 2, 1, 4, 1, 3, 2, 1, 1, 3, 3]
def baseStart_2103244 : Nat := 118140960795 + 2103244 * 2 ^ 59
def prefixEnd_2103244 : Nat := 4983230072969 + 3 ^ 40 * 2103244 * 2
def baseEnd_2103244 : Nat := 1079975105685074281877363

theorem tailTrace_2103244 : CollatzResearch.WordTrace tailWord_2103244 prefixEnd_2103244 1079975105685074281877363 := by
  unfold tailWord_2103244
  simp only [CollatzResearch.WordTrace]
  refine ⟨38355805396156834161250393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51141073861542445548333857 38355805396156834161250393)
  ·
    refine ⟨28766854047117625620937795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38355805396156834161250393 28766854047117625620937795)
    ·
      refine ⟨43150281070676438431406693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28766854047117625620937795 43150281070676438431406693)
      ·
        refine ⟨8090677700751832205888755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43150281070676438431406693 8090677700751832205888755)
        ·
          refine ⟨12136016551127748308833133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8090677700751832205888755 12136016551127748308833133)
          ·
            refine ⟨4551006206672905615812425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12136016551127748308833133 4551006206672905615812425)
            ·
              refine ⟨3413254655004679211859319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4551006206672905615812425 3413254655004679211859319)
              ·
                refine ⟨5119881982507018817788979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3413254655004679211859319 5119881982507018817788979)
                ·
                  refine ⟨7679822973760528226683469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5119881982507018817788979 7679822973760528226683469)
                  ·
                    refine ⟨2879933615160198085006301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7679822973760528226683469 2879933615160198085006301)
                    ·
                      refine ⟨1079975105685074281877363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2879933615160198085006301 1079975105685074281877363)
                      ·
                        rfl

theorem cell23_2103244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_2103244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103244 prefixEnd_2103244 := by exact prefixLift 2103244
  have htrace : WordTrace (prefixWord ++ tailWord_2103244) baseStart_2103244 baseEnd_2103244 := by
    simpa [prefixWord, tailWord_2103244, baseEnd_2103244] using wordTrace_append hprefix tailTrace_2103244
  have hstable : (prefixWord ++ tailWord_2103244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103244).length < 2 ^ (prefixWord ++ tailWord_2103244).sum := by decide
  have hdescent : baseEnd_2103244 < baseStart_2103244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103278 : List Nat := [4, 1, 2, 1, 3, 3, 1, 2, 2, 1, 3]
def baseStart_2103278 : Nat := 118140960795 + 2103278 * 2 ^ 59
def prefixEnd_2103278 : Nat := 4983230072969 + 3 ^ 40 * 2103278 * 2
def baseEnd_2103278 : Nat := 1079992564027327148852207

theorem tailTrace_2103278 : CollatzResearch.WordTrace tailWord_2103278 prefixEnd_2103278 1079992564027327148852207 := by
  unfold tailWord_2103278
  simp only [CollatzResearch.WordTrace]
  refine ⟨9589106359273811516154811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51141900582793661419492325 9589106359273811516154811)
  ·
    refine ⟨14383659538910717274232217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9589106359273811516154811 14383659538910717274232217)
    ·
      refine ⟨10787744654183037955674163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14383659538910717274232217 10787744654183037955674163)
      ·
        refine ⟨16181616981274556933511245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10787744654183037955674163 16181616981274556933511245)
        ·
          refine ⟨6068106367977958850066717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16181616981274556933511245 6068106367977958850066717)
          ·
            refine ⟨2275539887991734568775019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6068106367977958850066717 2275539887991734568775019)
            ·
              refine ⟨3413309831987601853162529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2275539887991734568775019 3413309831987601853162529)
              ·
                refine ⟨2559982373990701389871897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3413309831987601853162529 2559982373990701389871897)
                ·
                  refine ⟨1919986780493026042403923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2559982373990701389871897 1919986780493026042403923)
                  ·
                    refine ⟨2879980170739539063605885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1919986780493026042403923 2879980170739539063605885)
                    ·
                      refine ⟨1079992564027327148852207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2879980170739539063605885 1079992564027327148852207)
                      ·
                        rfl

theorem cell23_2103278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_2103278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103278 prefixEnd_2103278 := by exact prefixLift 2103278
  have htrace : WordTrace (prefixWord ++ tailWord_2103278) baseStart_2103278 baseEnd_2103278 := by
    simpa [prefixWord, tailWord_2103278, baseEnd_2103278] using wordTrace_append hprefix tailTrace_2103278
  have hstable : (prefixWord ++ tailWord_2103278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103278).length < 2 ^ (prefixWord ++ tailWord_2103278).sum := by decide
  have hdescent : baseEnd_2103278 < baseStart_2103278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103294 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 2, 6]
def baseStart_2103294 : Nat := 118140960795 + 2103294 * 2 ^ 59
def prefixEnd_2103294 : Nat := 4983230072969 + 3 ^ 40 * 2103294 * 2
def baseEnd_2103294 : Nat := 360000259905933028750711

theorem tailTrace_2103294 : CollatzResearch.WordTrace tailWord_2103294 prefixEnd_2103294 360000259905933028750711 := by
  unfold tailWord_2103294
  simp only [CollatzResearch.WordTrace]
  refine ⟨9589179305266565857727617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51142289628088351241213957 9589179305266565857727617)
  ·
    refine ⟨7191884478949924393295713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9589179305266565857727617 7191884478949924393295713)
    ·
      refine ⟨5393913359212443294971785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7191884478949924393295713 5393913359212443294971785)
      ·
        refine ⟨4045435019409332471228839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5393913359212443294971785 4045435019409332471228839)
        ·
          refine ⟨6068152529113998706843259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4045435019409332471228839 6068152529113998706843259)
          ·
            refine ⟨9102228793670998060264889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6068152529113998706843259 9102228793670998060264889)
            ·
              refine ⟨6826671595253248545198667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9102228793670998060264889 6826671595253248545198667)
              ·
                refine ⟨10240007392879872817798001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6826671595253248545198667 10240007392879872817798001)
                ·
                  refine ⟨7680005544659904613348501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10240007392879872817798001 7680005544659904613348501)
                  ·
                    refine ⟨360000259905933028750711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7680005544659904613348501 360000259905933028750711)
                    ·
                      rfl

theorem cell23_2103294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_2103294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103294 prefixEnd_2103294 := by exact prefixLift 2103294
  have htrace : WordTrace (prefixWord ++ tailWord_2103294) baseStart_2103294 baseEnd_2103294 := by
    simpa [prefixWord, tailWord_2103294, baseEnd_2103294] using wordTrace_append hprefix tailTrace_2103294
  have hstable : (prefixWord ++ tailWord_2103294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103294).length < 2 ^ (prefixWord ++ tailWord_2103294).sum := by decide
  have hdescent : baseEnd_2103294 < baseStart_2103294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103297 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_2103297 : Nat := 118140960795 + 2103297 * 2 ^ 59
def prefixEnd_2103297 : Nat := 4983230072969 + 3 ^ 40 * 2103297 * 2
def baseEnd_2103297 : Nat := 1080002320159762574514619

theorem tailTrace_2103297 : CollatzResearch.WordTrace tailWord_2103297 prefixEnd_2103297 1080002320159762574514619 := by
  unfold tailWord_2103297
  simp only [CollatzResearch.WordTrace]
  refine ⟨76713543861121658374180145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51142362574081105582786763 76713543861121658374180145)
  ·
    refine ⟨57535157895841243780635109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76713543861121658374180145 57535157895841243780635109)
    ·
      refine ⟨10787842105470233208869083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57535157895841243780635109 10787842105470233208869083)
      ·
        refine ⟨16181763158205349813303625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10787842105470233208869083 16181763158205349813303625)
        ·
          refine ⟨12136322368654012359977719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16181763158205349813303625 12136322368654012359977719)
          ·
            refine ⟨18204483552981018539966579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12136322368654012359977719 18204483552981018539966579)
            ·
              refine ⟨27306725329471527809949869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18204483552981018539966579 27306725329471527809949869)
              ·
                refine ⟨10240021998551822928731201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27306725329471527809949869 10240021998551822928731201)
                ·
                  refine ⟨7680016498913867196548401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10240021998551822928731201 7680016498913867196548401)
                  ·
                    refine ⟨5760012374185400397411301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7680016498913867196548401 5760012374185400397411301)
                    ·
                      refine ⟨1080002320159762574514619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5760012374185400397411301 1080002320159762574514619)
                      ·
                        rfl

theorem cell23_2103297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_2103297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103297 prefixEnd_2103297 := by exact prefixLift 2103297
  have htrace : WordTrace (prefixWord ++ tailWord_2103297) baseStart_2103297 baseEnd_2103297 := by
    simpa [prefixWord, tailWord_2103297, baseEnd_2103297] using wordTrace_append hprefix tailTrace_2103297
  have hstable : (prefixWord ++ tailWord_2103297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103297).length < 2 ^ (prefixWord ++ tailWord_2103297).sum := by decide
  have hdescent : baseEnd_2103297 < baseStart_2103297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103301 : List Nat := [1, 3, 1, 1, 2, 6, 1, 1, 1, 4, 2]
def baseStart_2103301 : Nat := 118140960795 + 2103301 * 2 ^ 59
def prefixEnd_2103301 : Nat := 4983230072969 + 3 ^ 40 * 2103301 * 2
def baseEnd_2103301 : Nat := 1080004374082380558864601

theorem tailTrace_2103301 : CollatzResearch.WordTrace tailWord_2103301 prefixEnd_2103301 1080004374082380558864601 := by
  unfold tailWord_2103301
  simp only [CollatzResearch.WordTrace]
  refine ⟨76713689753107167057325757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51142459835404778038217171 76713689753107167057325757)
  ·
    refine ⟨28767633657415187646497159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76713689753107167057325757 28767633657415187646497159)
    ·
      refine ⟨43151450486122781469745739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28767633657415187646497159 43151450486122781469745739)
      ·
        refine ⟨64727175729184172204618609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43151450486122781469745739 64727175729184172204618609)
        ·
          refine ⟨48545381796888129153463957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64727175729184172204618609 48545381796888129153463957)
          ·
            refine ⟨2275564771729131054068623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48545381796888129153463957 2275564771729131054068623)
            ·
              refine ⟨3413347157593696581102935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2275564771729131054068623 3413347157593696581102935)
              ·
                refine ⟨5120020736390544871654403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3413347157593696581102935 5120020736390544871654403)
                ·
                  refine ⟨7680031104585817307481605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5120020736390544871654403 7680031104585817307481605)
                  ·
                    refine ⟨1440005832109840745152801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7680031104585817307481605 1440005832109840745152801)
                    ·
                      refine ⟨1080004374082380558864601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1440005832109840745152801 1080004374082380558864601)
                      ·
                        rfl

theorem cell23_2103301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 4, 2].length) (baseStart_2103301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103301 prefixEnd_2103301 := by exact prefixLift 2103301
  have htrace : WordTrace (prefixWord ++ tailWord_2103301) baseStart_2103301 baseEnd_2103301 := by
    simpa [prefixWord, tailWord_2103301, baseEnd_2103301] using wordTrace_append hprefix tailTrace_2103301
  have hstable : (prefixWord ++ tailWord_2103301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103301).length < 2 ^ (prefixWord ++ tailWord_2103301).sum := by decide
  have hdescent : baseEnd_2103301 < baseStart_2103301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103302 : List Nat := [6, 2, 1, 2, 2, 1, 2, 7]
def baseStart_2103302 : Nat := 118140960795 + 2103302 * 2 ^ 59
def prefixEnd_2103302 : Nat := 4983230072969 + 3 ^ 40 * 2103302 * 2
def baseEnd_2103302 : Nat := 40000181020853150183411

theorem tailTrace_2103302 : CollatzResearch.WordTrace tailWord_2103302 prefixEnd_2103302 40000181020853150183411 := by
  unfold tailWord_2103302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2397303944565735757128505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51142484150735696152074773 2397303944565735757128505)
  ·
    refine ⟨1797977958424301817846379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2397303944565735757128505 1797977958424301817846379)
    ·
      refine ⟨2696966937636452726769569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1797977958424301817846379 2696966937636452726769569)
      ·
        refine ⟨2022725203227339545077177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2696966937636452726769569 2022725203227339545077177)
        ·
          refine ⟨1517043902420504658807883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2022725203227339545077177 1517043902420504658807883)
          ·
            refine ⟨2275565853630756988211825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1517043902420504658807883 2275565853630756988211825)
            ·
              refine ⟨1706674390223067741158869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2275565853630756988211825 1706674390223067741158869)
              ·
                refine ⟨40000181020853150183411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1706674390223067741158869 40000181020853150183411)
                ·
                  rfl

theorem cell23_2103302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_2103302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103302 prefixEnd_2103302 := by exact prefixLift 2103302
  have htrace : WordTrace (prefixWord ++ tailWord_2103302) baseStart_2103302 baseEnd_2103302 := by
    simpa [prefixWord, tailWord_2103302, baseEnd_2103302] using wordTrace_append hprefix tailTrace_2103302
  have hstable : (prefixWord ++ tailWord_2103302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103302).length < 2 ^ (prefixWord ++ tailWord_2103302).sum := by decide
  have hdescent : baseEnd_2103302 < baseStart_2103302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103352 : List Nat := [2, 1, 2, 1, 7, 1, 2, 1, 2, 2, 2]
def baseStart_2103352 : Nat := 118140960795 + 2103352 * 2 ^ 59
def prefixEnd_2103352 : Nat := 4983230072969 + 3 ^ 40 * 2103352 * 2
def baseEnd_2103352 : Nat := 1080030561595759859326867

theorem tailTrace_2103352 : CollatzResearch.WordTrace tailWord_2103352 prefixEnd_2103352 1080030561595759859326867 := by
  unfold tailWord_2103352
  simp only [CollatzResearch.WordTrace]
  refine ⟨38357774937961201383716155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51143699917281601844954873 38357774937961201383716155)
  ·
    refine ⟨57536662406941802075574233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38357774937961201383716155 57536662406941802075574233)
    ·
      refine ⟨43152496805206351556680675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57536662406941802075574233 43152496805206351556680675)
      ·
        refine ⟨64728745207809527335021013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43152496805206351556680675 64728745207809527335021013)
        ·
          refine ⟨1517079965808035796914555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 64728745207809527335021013 1517079965808035796914555)
          ·
            refine ⟨2275619948712053695371833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1517079965808035796914555 2275619948712053695371833)
            ·
              refine ⟨1706714961534040271528875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2275619948712053695371833 1706714961534040271528875)
              ·
                refine ⟨2560072442301060407293313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1706714961534040271528875 2560072442301060407293313)
                ·
                  refine ⟨1920054331725795305469985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2560072442301060407293313 1920054331725795305469985)
                  ·
                    refine ⟨1440040748794346479102489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1920054331725795305469985 1440040748794346479102489)
                    ·
                      refine ⟨1080030561595759859326867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1440040748794346479102489 1080030561595759859326867)
                      ·
                        rfl

theorem cell23_2103352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 2, 2, 2].length) (baseStart_2103352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103352 prefixEnd_2103352 := by exact prefixLift 2103352
  have htrace : WordTrace (prefixWord ++ tailWord_2103352) baseStart_2103352 baseEnd_2103352 := by
    simpa [prefixWord, tailWord_2103352, baseEnd_2103352] using wordTrace_append hprefix tailTrace_2103352
  have hstable : (prefixWord ++ tailWord_2103352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103352).length < 2 ^ (prefixWord ++ tailWord_2103352).sum := by decide
  have hdescent : baseEnd_2103352 < baseStart_2103352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103374 : List Nat := [4, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4]
def baseStart_2103374 : Nat := 118140960795 + 2103374 * 2 ^ 59
def prefixEnd_2103374 : Nat := 4983230072969 + 3 ^ 40 * 2103374 * 2
def baseEnd_2103374 : Nat := 1080041858170158773251765

theorem tailTrace_2103374 : CollatzResearch.WordTrace tailWord_2103374 prefixEnd_2103374 1080041858170158773251765 := by
  unfold tailWord_2103374
  simp only [CollatzResearch.WordTrace]
  refine ⟨9589544035230337565591647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51144234854561800349822117 9589544035230337565591647)
  ·
    refine ⟨14384316052845506348387471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9589544035230337565591647 14384316052845506348387471)
    ·
      refine ⟨21576474079268259522581207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14384316052845506348387471 21576474079268259522581207)
      ·
        refine ⟨32364711118902389283871811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21576474079268259522581207 32364711118902389283871811)
        ·
          refine ⟨48547066678353583925807717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32364711118902389283871811 48547066678353583925807717)
          ·
            refine ⟨9102575002191296986088947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48547066678353583925807717 9102575002191296986088947)
            ·
              refine ⟨13653862503286945479133421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9102575002191296986088947 13653862503286945479133421)
              ·
                refine ⟨5120198438732604554675033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13653862503286945479133421 5120198438732604554675033)
                ·
                  refine ⟨3840148829049453416006275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5120198438732604554675033 3840148829049453416006275)
                  ·
                    refine ⟨5760223243574180124009413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3840148829049453416006275 5760223243574180124009413)
                    ·
                      refine ⟨1080041858170158773251765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5760223243574180124009413 1080041858170158773251765)
                      ·
                        rfl

theorem cell23_2103374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_2103374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103374 prefixEnd_2103374 := by exact prefixLift 2103374
  have htrace : WordTrace (prefixWord ++ tailWord_2103374) baseStart_2103374 baseEnd_2103374 := by
    simpa [prefixWord, tailWord_2103374, baseEnd_2103374] using wordTrace_append hprefix tailTrace_2103374
  have hstable : (prefixWord ++ tailWord_2103374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103374).length < 2 ^ (prefixWord ++ tailWord_2103374).sum := by decide
  have hdescent : baseEnd_2103374 < baseStart_2103374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103401 : List Nat := [1, 2, 1, 1, 1, 5, 3, 4, 1, 4]
def baseStart_2103401 : Nat := 118140960795 + 2103401 * 2 ^ 59
def prefixEnd_2103401 : Nat := 4983230072969 + 3 ^ 40 * 2103401 * 2
def baseEnd_2103401 : Nat := 360018574049276722538047

theorem tailTrace_2103401 : CollatzResearch.WordTrace tailWord_2103401 prefixEnd_2103401 360018574049276722538047 := by
  unfold tailWord_2103401
  simp only [CollatzResearch.WordTrace]
  refine ⟨76717337052744884135966057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51144891368496589423977371 76717337052744884135966057)
  ·
    refine ⟨57538002789558663101974543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76717337052744884135966057 57538002789558663101974543)
    ·
      refine ⟨86307004184337994652961815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57538002789558663101974543 86307004184337994652961815)
      ·
        refine ⟨129460506276506991979442723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86307004184337994652961815 129460506276506991979442723)
        ·
          refine ⟨194190759414760487969164085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129460506276506991979442723 194190759414760487969164085)
          ·
            refine ⟨18205383695133795747109133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 194190759414760487969164085 18205383695133795747109133)
            ·
              refine ⟨6827018885675173405165925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18205383695133795747109133 6827018885675173405165925)
              ·
                refine ⟨1280066041064095013468611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6827018885675173405165925 1280066041064095013468611)
                ·
                  refine ⟨1920099061596142520202917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1280066041064095013468611 1920099061596142520202917)
                  ·
                    refine ⟨360018574049276722538047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1920099061596142520202917 360018574049276722538047)
                    ·
                      rfl

theorem cell23_2103401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 1, 4].length) (baseStart_2103401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103401 prefixEnd_2103401 := by exact prefixLift 2103401
  have htrace : WordTrace (prefixWord ++ tailWord_2103401) baseStart_2103401 baseEnd_2103401 := by
    simpa [prefixWord, tailWord_2103401, baseEnd_2103401] using wordTrace_append hprefix tailTrace_2103401
  have hstable : (prefixWord ++ tailWord_2103401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103401).length < 2 ^ (prefixWord ++ tailWord_2103401).sum := by decide
  have hdescent : baseEnd_2103401 < baseStart_2103401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103448 : List Nat := [2, 1, 2, 4, 4, 1, 1, 2, 6]
def baseStart_2103448 : Nat := 118140960795 + 2103448 * 2 ^ 59
def prefixEnd_2103448 : Nat := 4983230072969 + 3 ^ 40 * 2103448 * 2
def baseEnd_2103448 : Nat := 120008872859843498191825

theorem tailTrace_2103448 : CollatzResearch.WordTrace tailWord_2103448 prefixEnd_2103448 120008872859843498191825 := by
  unfold tailWord_2103448
  simp only [CollatzResearch.WordTrace]
  refine ⟨38359525641787305581463499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51146034189049740775284665 38359525641787305581463499)
  ·
    refine ⟨57539288462680958372195249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38359525641787305581463499 57539288462680958372195249)
    ·
      refine ⟨43154466347010718779146437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57539288462680958372195249 43154466347010718779146437)
      ·
        refine ⟨8091462440064509771089957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43154466347010718779146437 8091462440064509771089957)
        ·
          refine ⟨1517149207512095582079367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8091462440064509771089957 1517149207512095582079367)
          ·
            refine ⟨2275723811268143373119051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1517149207512095582079367 2275723811268143373119051)
            ·
              refine ⟨3413585716902215059678577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2275723811268143373119051 3413585716902215059678577)
              ·
                refine ⟨2560189287676661294758933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3413585716902215059678577 2560189287676661294758933)
                ·
                  refine ⟨120008872859843498191825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2560189287676661294758933 120008872859843498191825)
                  ·
                    rfl

theorem cell23_2103448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 6].length) (baseStart_2103448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103448 prefixEnd_2103448 := by exact prefixLift 2103448
  have htrace : WordTrace (prefixWord ++ tailWord_2103448) baseStart_2103448 baseEnd_2103448 := by
    simpa [prefixWord, tailWord_2103448, baseEnd_2103448] using wordTrace_append hprefix tailTrace_2103448
  have hstable : (prefixWord ++ tailWord_2103448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103448).length < 2 ^ (prefixWord ++ tailWord_2103448).sum := by decide
  have hdescent : baseEnd_2103448 < baseStart_2103448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103458 : List Nat := [3, 3, 1, 3, 1, 1, 1, 3, 3, 1, 3]
def baseStart_2103458 : Nat := 118140960795 + 2103458 * 2 ^ 59
def prefixEnd_2103458 : Nat := 4983230072969 + 3 ^ 40 * 2103458 * 2
def baseEnd_2103458 : Nat := 1080084990545136444601379

theorem tailTrace_2103458 : CollatzResearch.WordTrace tailWord_2103458 prefixEnd_2103458 1080084990545136444601379 := by
  unfold tailWord_2103458
  simp only [CollatzResearch.WordTrace]
  refine ⟨19179854003384595717697757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51146277342358921913860685 19179854003384595717697757)
  ·
    refine ⟨7192445251269223394136659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19179854003384595717697757 7192445251269223394136659)
    ·
      refine ⟨10788667876903835091204989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7192445251269223394136659 10788667876903835091204989)
      ·
        refine ⟨4045750453838938159201871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10788667876903835091204989 4045750453838938159201871)
        ·
          refine ⟨6068625680758407238802807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4045750453838938159201871 6068625680758407238802807)
          ·
            refine ⟨9102938521137610858204211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6068625680758407238802807 9102938521137610858204211)
            ·
              refine ⟨13654407781706416287306317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9102938521137610858204211 13654407781706416287306317)
              ·
                refine ⟨5120402918139906107739869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13654407781706416287306317 5120402918139906107739869)
                ·
                  refine ⟨1920151094302464790402451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5120402918139906107739869 1920151094302464790402451)
                  ·
                    refine ⟨2880226641453697185603677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1920151094302464790402451 2880226641453697185603677)
                    ·
                      refine ⟨1080084990545136444601379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2880226641453697185603677 1080084990545136444601379)
                      ·
                        rfl

theorem cell23_2103458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_2103458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103458 prefixEnd_2103458 := by exact prefixLift 2103458
  have htrace : WordTrace (prefixWord ++ tailWord_2103458) baseStart_2103458 baseEnd_2103458 := by
    simpa [prefixWord, tailWord_2103458, baseEnd_2103458] using wordTrace_append hprefix tailTrace_2103458
  have hstable : (prefixWord ++ tailWord_2103458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103458).length < 2 ^ (prefixWord ++ tailWord_2103458).sum := by decide
  have hdescent : baseEnd_2103458 < baseStart_2103458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103481 : List Nat := [1, 2, 1, 4, 1, 2, 4, 2, 1, 1, 4]
def baseStart_2103481 : Nat := 118140960795 + 2103481 * 2 ^ 59
def prefixEnd_2103481 : Nat := 4983230072969 + 3 ^ 40 * 2103481 * 2
def baseEnd_2103481 : Nat := 1080096800600189854613773

theorem tailTrace_2103481 : CollatzResearch.WordTrace tailWord_2103481 prefixEnd_2103481 1080096800600189854613773 := by
  unfold tailWord_2103481
  simp only [CollatzResearch.WordTrace]
  refine ⟨76720254892455057798878297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51146836594970038532585531 76720254892455057798878297)
  ·
    refine ⟨57540191169341293349158723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76720254892455057798878297 57540191169341293349158723)
    ·
      refine ⟨86310286754011940023738085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57540191169341293349158723 86310286754011940023738085)
      ·
        refine ⟨16183178766377238754450891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86310286754011940023738085 16183178766377238754450891)
        ·
          refine ⟨24274768149565858131676337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16183178766377238754450891 24274768149565858131676337)
          ·
            refine ⟨18206076112174393598757253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24274768149565858131676337 18206076112174393598757253)
            ·
              refine ⟨3413639271032698799766985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18206076112174393598757253 3413639271032698799766985)
              ·
                refine ⟨2560229453274524099825239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3413639271032698799766985 2560229453274524099825239)
                ·
                  refine ⟨3840344179911786149737859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2560229453274524099825239 3840344179911786149737859)
                  ·
                    refine ⟨5760516269867679224606789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3840344179911786149737859 5760516269867679224606789)
                    ·
                      refine ⟨1080096800600189854613773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5760516269867679224606789 1080096800600189854613773)
                      ·
                        rfl

theorem cell23_2103481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_2103481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103481 prefixEnd_2103481 := by exact prefixLift 2103481
  have htrace : WordTrace (prefixWord ++ tailWord_2103481) baseStart_2103481 baseEnd_2103481 := by
    simpa [prefixWord, tailWord_2103481, baseEnd_2103481] using wordTrace_append hprefix tailTrace_2103481
  have hstable : (prefixWord ++ tailWord_2103481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103481).length < 2 ^ (prefixWord ++ tailWord_2103481).sum := by decide
  have hdescent : baseEnd_2103481 < baseStart_2103481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103492 : List Nat := [2, 3, 3, 1, 2, 3, 1, 3, 1, 1, 3]
def baseStart_2103492 : Nat := 118140960795 + 2103492 * 2 ^ 59
def prefixEnd_2103492 : Nat := 4983230072969 + 3 ^ 40 * 2103492 * 2
def baseEnd_2103492 : Nat := 1080102448887389311576223

theorem tailTrace_2103492 : CollatzResearch.WordTrace tailWord_2103492 prefixEnd_2103492 1080102448887389311576223 := by
  unfold tailWord_2103492
  simp only [CollatzResearch.WordTrace]
  refine ⟨38360328047707603338764365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51147104063610137785019153 38360328047707603338764365)
  ·
    refine ⟨14385123017890351252036637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38360328047707603338764365 14385123017890351252036637)
    ·
      refine ⟨5394421131708881719513739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14385123017890351252036637 5394421131708881719513739)
      ·
        refine ⟨8091631697563322579270609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5394421131708881719513739 8091631697563322579270609)
        ·
          refine ⟨6068723773172491934452957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8091631697563322579270609 6068723773172491934452957)
          ·
            refine ⟨2275771414939684475419859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6068723773172491934452957 2275771414939684475419859)
            ·
              refine ⟨3413657122409526713129789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2275771414939684475419859 3413657122409526713129789)
              ·
                refine ⟨1280121420903572517423671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3413657122409526713129789 1280121420903572517423671)
                ·
                  refine ⟨1920182131355358776135507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1280121420903572517423671 1920182131355358776135507)
                  ·
                    refine ⟨2880273197033038164203261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1920182131355358776135507 2880273197033038164203261)
                    ·
                      refine ⟨1080102448887389311576223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2880273197033038164203261 1080102448887389311576223)
                      ·
                        rfl

theorem cell23_2103492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_2103492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103492 prefixEnd_2103492 := by exact prefixLift 2103492
  have htrace : WordTrace (prefixWord ++ tailWord_2103492) baseStart_2103492 baseEnd_2103492 := by
    simpa [prefixWord, tailWord_2103492, baseEnd_2103492] using wordTrace_append hprefix tailTrace_2103492
  have hstable : (prefixWord ++ tailWord_2103492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103492).length < 2 ^ (prefixWord ++ tailWord_2103492).sum := by decide
  have hdescent : baseEnd_2103492 < baseStart_2103492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103507 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 6]
def baseStart_2103507 : Nat := 118140960795 + 2103507 * 2 ^ 59
def prefixEnd_2103507 : Nat := 4983230072969 + 3 ^ 40 * 2103507 * 2
def baseEnd_2103507 : Nat := 1080110151097206752888653

theorem tailTrace_2103507 : CollatzResearch.WordTrace tailWord_2103507 prefixEnd_2103507 1080110151097206752888653 := by
  unfold tailWord_2103507
  simp only [CollatzResearch.WordTrace]
  refine ⟨76721203190360864239324775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51147468793573909492883183 76721203190360864239324775)
  ·
    refine ⟨115081804785541296358987163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76721203190360864239324775 115081804785541296358987163)
    ·
      refine ⟨172622707178311944538480745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115081804785541296358987163 172622707178311944538480745)
      ·
        refine ⟨129467030383733958403860559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172622707178311944538480745 129467030383733958403860559)
        ·
          refine ⟨194200545575600937605790839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129467030383733958403860559 194200545575600937605790839)
          ·
            refine ⟨291300818363401406408686259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194200545575600937605790839 291300818363401406408686259)
            ·
              refine ⟨436951227545102109613029389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291300818363401406408686259 436951227545102109613029389)
              ·
                refine ⟨163856710329413291104886021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 436951227545102109613029389 163856710329413291104886021)
                ·
                  refine ⟨30723133186764992082166129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163856710329413291104886021 30723133186764992082166129)
                  ·
                    refine ⟨23042349890073744061624597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30723133186764992082166129 23042349890073744061624597)
                    ·
                      refine ⟨1080110151097206752888653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23042349890073744061624597 1080110151097206752888653)
                      ·
                        rfl

theorem cell23_2103507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_2103507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103507 prefixEnd_2103507 := by exact prefixLift 2103507
  have htrace : WordTrace (prefixWord ++ tailWord_2103507) baseStart_2103507 baseEnd_2103507 := by
    simpa [prefixWord, tailWord_2103507, baseEnd_2103507] using wordTrace_append hprefix tailTrace_2103507
  have hstable : (prefixWord ++ tailWord_2103507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103507).length < 2 ^ (prefixWord ++ tailWord_2103507).sum := by decide
  have hdescent : baseEnd_2103507 < baseStart_2103507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103525 : List Nat := [1, 3, 1, 4, 2, 3, 2, 1, 2, 4]
def baseStart_2103525 : Nat := 118140960795 + 2103525 * 2 ^ 59
def prefixEnd_2103525 : Nat := 4983230072969 + 3 ^ 40 * 2103525 * 2
def baseEnd_2103525 : Nat := 360039797916329227487857

theorem tailTrace_2103525 : CollatzResearch.WordTrace tailWord_2103525 prefixEnd_2103525 360039797916329227487857 := by
  unfold tailWord_2103525
  simp only [CollatzResearch.WordTrace]
  refine ⟨76721859704295653313480029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51147906469530435542320019 76721859704295653313480029)
  ·
    refine ⟨28770697389110869992555011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76721859704295653313480029 28770697389110869992555011)
    ·
      refine ⟨43156046083666304988832517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28770697389110869992555011 43156046083666304988832517)
      ·
        refine ⟨8091758640687432185406097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43156046083666304988832517 8091758640687432185406097)
        ·
          refine ⟨6068818980515574139054573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8091758640687432185406097 6068818980515574139054573)
          ·
            refine ⟨2275807117693340302145465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6068818980515574139054573 2275807117693340302145465)
            ·
              refine ⟨1706855338270005226609099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2275807117693340302145465 1706855338270005226609099)
              ·
                refine ⟨2560283007405007839913649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1706855338270005226609099 2560283007405007839913649)
                ·
                  refine ⟨1920212255553755879935237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2560283007405007839913649 1920212255553755879935237)
                  ·
                    refine ⟨360039797916329227487857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1920212255553755879935237 360039797916329227487857)
                    ·
                      rfl

theorem cell23_2103525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 2, 4].length) (baseStart_2103525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103525 prefixEnd_2103525 := by exact prefixLift 2103525
  have htrace : WordTrace (prefixWord ++ tailWord_2103525) baseStart_2103525 baseEnd_2103525 := by
    simpa [prefixWord, tailWord_2103525, baseEnd_2103525] using wordTrace_append hprefix tailTrace_2103525
  have hstable : (prefixWord ++ tailWord_2103525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103525).length < 2 ^ (prefixWord ++ tailWord_2103525).sum := by decide
  have hdescent : baseEnd_2103525 < baseStart_2103525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103564 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 2, 6]
def baseStart_2103564 : Nat := 118140960795 + 2103564 * 2 ^ 59
def prefixEnd_2103564 : Nat := 4983230072969 + 3 ^ 40 * 2103564 * 2
def baseEnd_2103564 : Nat := 360046473164837676625297

theorem tailTrace_2103564 : CollatzResearch.WordTrace tailWord_2103564 prefixEnd_2103564 360046473164837676625297 := by
  unfold tailWord_2103564
  simp only [CollatzResearch.WordTrace]
  refine ⟨38361641075577181487074873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51148854767436241982766497 38361641075577181487074873)
  ·
    refine ⟨28771230806682886115306155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38361641075577181487074873 28771230806682886115306155)
    ·
      refine ⟨43156846210024329172959233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28771230806682886115306155 43156846210024329172959233)
      ·
        refine ⟨32367634657518246879719425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43156846210024329172959233 32367634657518246879719425)
        ·
          refine ⟨24275725993138685159789569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32367634657518246879719425 24275725993138685159789569)
          ·
            refine ⟨18206794494854013869842177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24275725993138685159789569 18206794494854013869842177)
            ·
              refine ⟨13655095871140510402381633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18206794494854013869842177 13655095871140510402381633)
              ·
                refine ⟨10241321903355382801786225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13655095871140510402381633 10241321903355382801786225)
                ·
                  refine ⟨7680991427516537101339669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10241321903355382801786225 7680991427516537101339669)
                  ·
                    refine ⟨360046473164837676625297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7680991427516537101339669 360046473164837676625297)
                    ·
                      rfl

theorem cell23_2103564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_2103564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103564 prefixEnd_2103564 := by exact prefixLift 2103564
  have htrace : WordTrace (prefixWord ++ tailWord_2103564) baseStart_2103564 baseEnd_2103564 := by
    simpa [prefixWord, tailWord_2103564, baseEnd_2103564] using wordTrace_append hprefix tailTrace_2103564
  have hstable : (prefixWord ++ tailWord_2103564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103564).length < 2 ^ (prefixWord ++ tailWord_2103564).sum := by decide
  have hdescent : baseEnd_2103564 < baseStart_2103564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103582 : List Nat := [4, 3, 2, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_2103582 : Nat := 118140960795 + 2103582 * 2 ^ 59
def prefixEnd_2103582 : Nat := 4983230072969 + 3 ^ 40 * 2103582 * 2
def baseEnd_2103582 : Nat := 1080148662146293959450809

theorem tailTrace_2103582 : CollatzResearch.WordTrace tailWord_2103582 prefixEnd_2103582 1080148662146293959450809 := by
  unfold tailWord_2103582
  simp only [CollatzResearch.WordTrace]
  refine ⟨9590492333136144006038125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51149292443392768032203333 9590492333136144006038125)
  ·
    refine ⟨3596434624926054002264297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9590492333136144006038125 3596434624926054002264297)
    ·
      refine ⟨2697325968694540501698223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3596434624926054002264297 2697325968694540501698223)
      ·
        refine ⟨4045988953041810752547335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2697325968694540501698223 4045988953041810752547335)
        ·
          refine ⟨6068983429562716128821003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4045988953041810752547335 6068983429562716128821003)
          ·
            refine ⟨9103475144344074193231505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6068983429562716128821003 9103475144344074193231505)
            ·
              refine ⟨6827606358258055644923629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9103475144344074193231505 6827606358258055644923629)
              ·
                refine ⟨2560352384346770866846361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6827606358258055644923629 2560352384346770866846361)
                ·
                  refine ⟨1920264288260078150134771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2560352384346770866846361 1920264288260078150134771)
                  ·
                    refine ⟨2880396432390117225202157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1920264288260078150134771 2880396432390117225202157)
                    ·
                      refine ⟨1080148662146293959450809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2880396432390117225202157 1080148662146293959450809)
                      ·
                        rfl

theorem cell23_2103582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_2103582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103582 prefixEnd_2103582 := by exact prefixLift 2103582
  have htrace : WordTrace (prefixWord ++ tailWord_2103582) baseStart_2103582 baseEnd_2103582 := by
    simpa [prefixWord, tailWord_2103582, baseEnd_2103582] using wordTrace_append hprefix tailTrace_2103582
  have hstable : (prefixWord ++ tailWord_2103582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103582).length < 2 ^ (prefixWord ++ tailWord_2103582).sum := by decide
  have hdescent : baseEnd_2103582 < baseStart_2103582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103588 : List Nat := [2, 3, 1, 3, 1, 2, 1, 3, 1, 4, 2]
def baseStart_2103588 : Nat := 118140960795 + 2103588 * 2 ^ 59
def prefixEnd_2103588 : Nat := 4983230072969 + 3 ^ 40 * 2103588 * 2
def baseEnd_2103588 : Nat := 1080151743030220935975781

theorem tailTrace_2103588 : CollatzResearch.WordTrace tailWord_2103588 prefixEnd_2103588 1080151743030220935975781 := by
  unfold tailWord_2103588
  simp only [CollatzResearch.WordTrace]
  refine ⟨38362078751533707536511709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51149438335378276715348945 38362078751533707536511709)
  ·
    refine ⟨14385779531825140326191891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38362078751533707536511709 14385779531825140326191891)
    ·
      refine ⟨21578669297737710489287837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14385779531825140326191891 21578669297737710489287837)
      ·
        refine ⟨8092000986651641433482939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21578669297737710489287837 8092000986651641433482939)
        ·
          refine ⟨12138001479977462150224409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8092000986651641433482939 12138001479977462150224409)
          ·
            refine ⟨9103501109983096612668307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12138001479977462150224409 9103501109983096612668307)
            ·
              refine ⟨13655251664974644919002461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9103501109983096612668307 13655251664974644919002461)
              ·
                refine ⟨5120719374365491844625923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13655251664974644919002461 5120719374365491844625923)
                ·
                  refine ⟨7681079061548237766938885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5120719374365491844625923 7681079061548237766938885)
                  ·
                    refine ⟨1440202324040294581301041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7681079061548237766938885 1440202324040294581301041)
                    ·
                      refine ⟨1080151743030220935975781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1440202324040294581301041 1080151743030220935975781)
                      ·
                        rfl

theorem cell23_2103588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_2103588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103588 prefixEnd_2103588 := by exact prefixLift 2103588
  have htrace : WordTrace (prefixWord ++ tailWord_2103588) baseStart_2103588 baseEnd_2103588 := by
    simpa [prefixWord, tailWord_2103588, baseEnd_2103588] using wordTrace_append hprefix tailTrace_2103588
  have hstable : (prefixWord ++ tailWord_2103588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103588).length < 2 ^ (prefixWord ++ tailWord_2103588).sum := by decide
  have hdescent : baseEnd_2103588 < baseStart_2103588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103631 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 2, 5, 2]
def baseStart_2103631 : Nat := 118140960795 + 2103631 * 2 ^ 59
def prefixEnd_2103631 : Nat := 4983230072969 + 3 ^ 40 * 2103631 * 2
def baseEnd_2103631 : Nat := 1080173822698364267738083

theorem tailTrace_2103631 : CollatzResearch.WordTrace tailWord_2103631 prefixEnd_2103631 1080173822698364267738083 := by
  unfold tailWord_2103631
  simp only [CollatzResearch.WordTrace]
  refine ⟨76725725841911633416838747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51150483894607755611225831 76725725841911633416838747)
  ·
    refine ⟨115088588762867450125258121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76725725841911633416838747 115088588762867450125258121)
    ·
      refine ⟨86316441572150587593943591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115088588762867450125258121 86316441572150587593943591)
      ·
        refine ⟨129474662358225881390915387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86316441572150587593943591 129474662358225881390915387)
        ·
          refine ⟨194211993537338822086373081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129474662358225881390915387 194211993537338822086373081)
          ·
            refine ⟨145658995153004116564779811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194211993537338822086373081 145658995153004116564779811)
            ·
              refine ⟨218488492729506174847169717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145658995153004116564779811 218488492729506174847169717)
              ·
                refine ⟨20483296193391203891922161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 218488492729506174847169717 20483296193391203891922161)
                ·
                  refine ⟨15362472145043402918941621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20483296193391203891922161 15362472145043402918941621)
                  ·
                    refine ⟨1440231763597819023650777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15362472145043402918941621 1440231763597819023650777)
                    ·
                      refine ⟨1080173822698364267738083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1440231763597819023650777 1080173822698364267738083)
                      ·
                        rfl

theorem cell23_2103631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 5, 2].length) (baseStart_2103631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103631 prefixEnd_2103631 := by exact prefixLift 2103631
  have htrace : WordTrace (prefixWord ++ tailWord_2103631) baseStart_2103631 baseEnd_2103631 := by
    simpa [prefixWord, tailWord_2103631, baseEnd_2103631] using wordTrace_append hprefix tailTrace_2103631
  have hstable : (prefixWord ++ tailWord_2103631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103631).length < 2 ^ (prefixWord ++ tailWord_2103631).sum := by decide
  have hdescent : baseEnd_2103631 < baseStart_2103631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103661 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_2103661 : Nat := 118140960795 + 2103661 * 2 ^ 59
def prefixEnd_2103661 : Nat := 4983230072969 + 3 ^ 40 * 2103661 * 2
def baseEnd_2103661 : Nat := 1080189227117999150362945

theorem tailTrace_2103661 : CollatzResearch.WordTrace tailWord_2103661 prefixEnd_2103661 1080189227117999150362945 := by
  unfold tailWord_2103661
  simp only [CollatzResearch.WordTrace]
  refine ⟨76726820031802948540430837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51151213354535299026953891 76726820031802948540430837)
  ·
    refine ⟨7193139377981526425665391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76726820031802948540430837 7193139377981526425665391)
    ·
      refine ⟨10789709066972289638498087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7193139377981526425665391 10789709066972289638498087)
      ·
        refine ⟨16184563600458434457747131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10789709066972289638498087 16184563600458434457747131)
        ·
          refine ⟨24276845400687651686620697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16184563600458434457747131 24276845400687651686620697)
          ·
            refine ⟨18207634050515738764965523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24276845400687651686620697 18207634050515738764965523)
            ·
              refine ⟨27311451075773608147448285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18207634050515738764965523 27311451075773608147448285)
              ·
                refine ⟨10241794153415103055293107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27311451075773608147448285 10241794153415103055293107)
                ·
                  refine ⟨15362691230122654582939661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10241794153415103055293107 15362691230122654582939661)
                  ·
                    refine ⟨5761009211295995468602373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15362691230122654582939661 5761009211295995468602373)
                    ·
                      refine ⟨1080189227117999150362945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5761009211295995468602373 1080189227117999150362945)
                      ·
                        rfl

theorem cell23_2103661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_2103661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103661 prefixEnd_2103661 := by exact prefixLift 2103661
  have htrace : WordTrace (prefixWord ++ tailWord_2103661) baseStart_2103661 baseEnd_2103661 := by
    simpa [prefixWord, tailWord_2103661, baseEnd_2103661] using wordTrace_append hprefix tailTrace_2103661
  have hstable : (prefixWord ++ tailWord_2103661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103661).length < 2 ^ (prefixWord ++ tailWord_2103661).sum := by decide
  have hdescent : baseEnd_2103661 < baseStart_2103661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103768 : List Nat := [2, 1, 2, 2, 2, 1, 1, 6, 1, 1, 4]
def baseStart_2103768 : Nat := 118140960795 + 2103768 * 2 ^ 59
def prefixEnd_2103768 : Nat := 4983230072969 + 3 ^ 40 * 2103768 * 2
def baseEnd_2103768 : Nat := 1080244169548030231724953

theorem tailTrace_2103768 : CollatzResearch.WordTrace tailWord_2103768 prefixEnd_2103768 1080244169548030231724953 := by
  unfold tailWord_2103768
  simp only [CollatzResearch.WordTrace]
  refine ⟨38365361321207652907287979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51153815094943537209717305 38365361321207652907287979)
  ·
    refine ⟨57548041981811479360931969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38365361321207652907287979 57548041981811479360931969)
    ·
      refine ⟨43161031486358609520698977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57548041981811479360931969 43161031486358609520698977)
      ·
        refine ⟨32370773614768957140524233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43161031486358609520698977 32370773614768957140524233)
        ·
          refine ⟨24278080211076717855393175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32370773614768957140524233 24278080211076717855393175)
          ·
            refine ⟨36417120316615076783089763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24278080211076717855393175 36417120316615076783089763)
            ·
              refine ⟨54625680474922615174634645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36417120316615076783089763 54625680474922615174634645)
              ·
                refine ⟨2560578772261997586310999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54625680474922615174634645 2560578772261997586310999)
                ·
                  refine ⟨3840868158392996379466499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2560578772261997586310999 3840868158392996379466499)
                  ·
                    refine ⟨5761302237589494569199749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3840868158392996379466499 5761302237589494569199749)
                    ·
                      refine ⟨1080244169548030231724953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5761302237589494569199749 1080244169548030231724953)
                      ·
                        rfl

theorem cell23_2103768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_2103768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103768 prefixEnd_2103768 := by exact prefixLift 2103768
  have htrace : WordTrace (prefixWord ++ tailWord_2103768) baseStart_2103768 baseEnd_2103768 := by
    simpa [prefixWord, tailWord_2103768, baseEnd_2103768] using wordTrace_append hprefix tailTrace_2103768
  have hstable : (prefixWord ++ tailWord_2103768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103768).length < 2 ^ (prefixWord ++ tailWord_2103768).sum := by decide
  have hdescent : baseEnd_2103768 < baseStart_2103768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103779 : List Nat := [1, 1, 1, 6, 3, 1, 2, 3, 1, 1, 3]
def baseStart_2103779 : Nat := 118140960795 + 2103779 * 2 ^ 59
def prefixEnd_2103779 : Nat := 4983230072969 + 3 ^ 40 * 2103779 * 2
def baseEnd_2103779 : Nat := 1080249817835229688687403

theorem tailTrace_2103779 : CollatzResearch.WordTrace tailWord_2103779 prefixEnd_2103779 1080249817835229688687403 := by
  unfold tailWord_2103779
  simp only [CollatzResearch.WordTrace]
  refine ⟨76731123845375454693226391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51154082563583636462150927 76731123845375454693226391)
  ·
    refine ⟨115096685768063182039839587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76731123845375454693226391 115096685768063182039839587)
    ·
      refine ⟨172645028652094773059759381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115096685768063182039839587 172645028652094773059759381)
      ·
        refine ⟨8092735718066942487176221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 172645028652094773059759381 8092735718066942487176221)
        ·
          refine ⟨3034775894275103432691083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8092735718066942487176221 3034775894275103432691083)
          ·
            refine ⟨4552163841412655149036625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3034775894275103432691083 4552163841412655149036625)
            ·
              refine ⟨3414122881059491361777469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4552163841412655149036625 3414122881059491361777469)
              ·
                refine ⟨1280296080397309260666551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3414122881059491361777469 1280296080397309260666551)
                ·
                  refine ⟨1920444120595963890999827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1280296080397309260666551 1920444120595963890999827)
                  ·
                    refine ⟨2880666180893945836499741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1920444120595963890999827 2880666180893945836499741)
                    ·
                      refine ⟨1080249817835229688687403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2880666180893945836499741 1080249817835229688687403)
                      ·
                        rfl

theorem cell23_2103779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_2103779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103779 prefixEnd_2103779 := by exact prefixLift 2103779
  have htrace : WordTrace (prefixWord ++ tailWord_2103779) baseStart_2103779 baseEnd_2103779 := by
    simpa [prefixWord, tailWord_2103779, baseEnd_2103779] using wordTrace_append hprefix tailTrace_2103779
  have hstable : (prefixWord ++ tailWord_2103779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103779).length < 2 ^ (prefixWord ++ tailWord_2103779).sum := by decide
  have hdescent : baseEnd_2103779 < baseStart_2103779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103798 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_2103798 : Nat := 118140960795 + 2103798 * 2 ^ 59
def prefixEnd_2103798 : Nat := 4983230072969 + 3 ^ 40 * 2103798 * 2
def baseEnd_2103798 : Nat := 1080259573967665114349815

theorem tailTrace_2103798 : CollatzResearch.WordTrace tailWord_2103798 prefixEnd_2103798 1080259573967665114349815 := by
  unfold tailWord_2103798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4795738552019163808635503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51154544554871080625445365 4795738552019163808635503)
  ·
    refine ⟨7193607828028745712953255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4795738552019163808635503 7193607828028745712953255)
    ·
      refine ⟨10790411742043118569429883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7193607828028745712953255 10790411742043118569429883)
      ·
        refine ⟨16185617613064677854144825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10790411742043118569429883 16185617613064677854144825)
        ·
          refine ⟨12139213209798508390608619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16185617613064677854144825 12139213209798508390608619)
          ·
            refine ⟨18208819814697762585912929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12139213209798508390608619 18208819814697762585912929)
            ·
              refine ⟨13656614861023321939434697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18208819814697762585912929 13656614861023321939434697)
              ·
                refine ⟨10242461145767491454576023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13656614861023321939434697 10242461145767491454576023)
                ·
                  refine ⟨15363691718651237181864035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10242461145767491454576023 15363691718651237181864035)
                  ·
                    refine ⟨23045537577976855772796053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15363691718651237181864035 23045537577976855772796053)
                    ·
                      refine ⟨1080259573967665114349815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23045537577976855772796053 1080259573967665114349815)
                      ·
                        rfl

theorem cell23_2103798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_2103798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103798 prefixEnd_2103798 := by exact prefixLift 2103798
  have htrace : WordTrace (prefixWord ++ tailWord_2103798) baseStart_2103798 baseEnd_2103798 := by
    simpa [prefixWord, tailWord_2103798, baseEnd_2103798] using wordTrace_append hprefix tailTrace_2103798
  have hstable : (prefixWord ++ tailWord_2103798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103798).length < 2 ^ (prefixWord ++ tailWord_2103798).sum := by decide
  have hdescent : baseEnd_2103798 < baseStart_2103798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103822 : List Nat := [4, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3]
def baseStart_2103822 : Nat := 118140960795 + 2103822 * 2 ^ 59
def prefixEnd_2103822 : Nat := 4983230072969 + 3 ^ 40 * 2103822 * 2
def baseEnd_2103822 : Nat := 1080271897503373020449705

theorem tailTrace_2103822 : CollatzResearch.WordTrace tailWord_2103822 prefixEnd_2103822 1080271897503373020449705 := by
  unfold tailWord_2103822
  simp only [CollatzResearch.WordTrace]
  refine ⟨9591586523027459129630215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51155128122813115358027813 9591586523027459129630215)
  ·
    refine ⟨14387379784541188694445323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9591586523027459129630215 14387379784541188694445323)
    ·
      refine ⟨21581069676811783041667985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14387379784541188694445323 21581069676811783041667985)
      ·
        refine ⟨16185802257608837281250989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21581069676811783041667985 16185802257608837281250989)
        ·
          refine ⟨6069675846603313980469121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16185802257608837281250989 6069675846603313980469121)
          ·
            refine ⟨4552256884952485485351841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6069675846603313980469121 4552256884952485485351841)
            ·
              refine ⟨3414192663714364114013881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4552256884952485485351841 3414192663714364114013881)
              ·
                refine ⟨2560644497785773085510411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3414192663714364114013881 2560644497785773085510411)
                ·
                  refine ⟨3840966746678659628265617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2560644497785773085510411 3840966746678659628265617)
                  ·
                    refine ⟨2880725060008994721199213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3840966746678659628265617 2880725060008994721199213)
                    ·
                      refine ⟨1080271897503373020449705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2880725060008994721199213 1080271897503373020449705)
                      ·
                        rfl

theorem cell23_2103822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_2103822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103822 prefixEnd_2103822 := by exact prefixLift 2103822
  have htrace : WordTrace (prefixWord ++ tailWord_2103822) baseStart_2103822 baseEnd_2103822 := by
    simpa [prefixWord, tailWord_2103822, baseEnd_2103822] using wordTrace_append hprefix tailTrace_2103822
  have hstable : (prefixWord ++ tailWord_2103822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103822).length < 2 ^ (prefixWord ++ tailWord_2103822).sum := by decide
  have hdescent : baseEnd_2103822 < baseStart_2103822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103836 : List Nat := [2, 2, 3, 1, 2, 4, 1, 3, 1, 2, 2]
def baseStart_2103836 : Nat := 118140960795 + 2103836 * 2 ^ 59
def prefixEnd_2103836 : Nat := 4983230072969 + 3 ^ 40 * 2103836 * 2
def baseEnd_2103836 : Nat := 1080279086232535965674641

theorem tailTrace_2103836 : CollatzResearch.WordTrace tailWord_2103836 prefixEnd_2103836 1080279086232535965674641 := by
  unfold tailWord_2103836
  simp only [CollatzResearch.WordTrace]
  refine ⟨38366601403084476714025681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51155468537445968952034241 38366601403084476714025681)
  ·
    refine ⟨28774951052313357535519261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38366601403084476714025681 28774951052313357535519261)
    ·
      refine ⟨10790606644617509075819723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28774951052313357535519261 10790606644617509075819723)
      ·
        refine ⟨16185909966926263613729585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10790606644617509075819723 16185909966926263613729585)
        ·
          refine ⟨12139432475194697710297189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16185909966926263613729585 12139432475194697710297189)
          ·
            refine ⟨2276143589099005820680723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12139432475194697710297189 2276143589099005820680723)
            ·
              refine ⟨3414215383648508731021085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2276143589099005820680723 3414215383648508731021085)
              ·
                refine ⟨1280330768868190774132907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3414215383648508731021085 1280330768868190774132907)
                ·
                  refine ⟨1920496153302286161199361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1280330768868190774132907 1920496153302286161199361)
                  ·
                    refine ⟨1440372114976714620899521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1920496153302286161199361 1440372114976714620899521)
                    ·
                      refine ⟨1080279086232535965674641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1440372114976714620899521 1080279086232535965674641)
                      ·
                        rfl

theorem cell23_2103836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_2103836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103836 prefixEnd_2103836 := by exact prefixLift 2103836
  have htrace : WordTrace (prefixWord ++ tailWord_2103836) baseStart_2103836 baseEnd_2103836 := by
    simpa [prefixWord, tailWord_2103836, baseEnd_2103836] using wordTrace_append hprefix tailTrace_2103836
  have hstable : (prefixWord ++ tailWord_2103836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103836).length < 2 ^ (prefixWord ++ tailWord_2103836).sum := by decide
  have hdescent : baseEnd_2103836 < baseStart_2103836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103851 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 4, 6]
def baseStart_2103851 : Nat := 118140960795 + 2103851 * 2 ^ 59
def prefixEnd_2103851 : Nat := 4983230072969 + 3 ^ 40 * 2103851 * 2
def baseEnd_2103851 : Nat := 360095596147451135662357

theorem tailTrace_2103851 : CollatzResearch.WordTrace tailWord_2103851 prefixEnd_2103851 360095596147451135662357 := by
  unfold tailWord_2103851
  simp only [CollatzResearch.WordTrace]
  refine ⟨76733749901114610989847407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51155833267409740659898271 76733749901114610989847407)
  ·
    refine ⟨115100624851671916484771111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76733749901114610989847407 115100624851671916484771111)
    ·
      refine ⟨172650937277507874727156667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115100624851671916484771111 172650937277507874727156667)
      ·
        refine ⟨258976405916261812090735001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172650937277507874727156667 258976405916261812090735001)
        ·
          refine ⟨194232304437196359068051251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258976405916261812090735001 194232304437196359068051251)
          ·
            refine ⟨291348456655794538602076877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194232304437196359068051251 291348456655794538602076877)
            ·
              refine ⟨109255671245922951975778829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 291348456655794538602076877 109255671245922951975778829)
              ·
                refine ⟨40970876717221106990917061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109255671245922951975778829 40970876717221106990917061)
                ·
                  refine ⟨7682039384478957560796949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40970876717221106990917061 7682039384478957560796949)
                  ·
                    refine ⟨360095596147451135662357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7682039384478957560796949 360095596147451135662357)
                    ·
                      rfl

theorem cell23_2103851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 6].length) (baseStart_2103851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103851 prefixEnd_2103851 := by exact prefixLift 2103851
  have htrace : WordTrace (prefixWord ++ tailWord_2103851) baseStart_2103851 baseEnd_2103851 := by
    simpa [prefixWord, tailWord_2103851, baseEnd_2103851] using wordTrace_append hprefix tailTrace_2103851
  have hstable : (prefixWord ++ tailWord_2103851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103851).length < 2 ^ (prefixWord ++ tailWord_2103851).sum := by decide
  have hdescent : baseEnd_2103851 < baseStart_2103851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103869 : List Nat := [1, 4, 1, 3, 2, 1, 4, 1, 2, 1, 3]
def baseStart_2103869 : Nat := 118140960795 + 2103869 * 2 ^ 59
def prefixEnd_2103869 : Nat := 4983230072969 + 3 ^ 40 * 2103869 * 2
def baseEnd_2103869 : Nat := 1080296031094134336561989

theorem tailTrace_2103869 : CollatzResearch.WordTrace tailWord_2103869 prefixEnd_2103869 1080296031094134336561989 := by
  unfold tailWord_2103869
  simp only [CollatzResearch.WordTrace]
  refine ⟨76734406415049400064002661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51156270943366266709335107 76734406415049400064002661)
  ·
    refine ⟨14387701202821762512000499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76734406415049400064002661 14387701202821762512000499)
    ·
      refine ⟨21581551804232643768000749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14387701202821762512000499 21581551804232643768000749)
      ·
        refine ⟨8093081926587241413000281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21581551804232643768000749 8093081926587241413000281)
        ·
          refine ⟨6069811444940431059750211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8093081926587241413000281 6069811444940431059750211)
          ·
            refine ⟨9104717167410646589625317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6069811444940431059750211 9104717167410646589625317)
            ·
              refine ⟨1707134468889496235554747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9104717167410646589625317 1707134468889496235554747)
              ·
                refine ⟨2560701703334244353332121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1707134468889496235554747 2560701703334244353332121)
                ·
                  refine ⟨1920526277500683264999091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2560701703334244353332121 1920526277500683264999091)
                  ·
                    refine ⟨2880789416251024897498637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1920526277500683264999091 2880789416251024897498637)
                    ·
                      refine ⟨1080296031094134336561989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2880789416251024897498637 1080296031094134336561989)
                      ·
                        rfl

theorem cell23_2103869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_2103869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103869 prefixEnd_2103869 := by exact prefixLift 2103869
  have htrace : WordTrace (prefixWord ++ tailWord_2103869) baseStart_2103869 baseEnd_2103869 := by
    simpa [prefixWord, tailWord_2103869, baseEnd_2103869] using wordTrace_append hprefix tailTrace_2103869
  have hstable : (prefixWord ++ tailWord_2103869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103869).length < 2 ^ (prefixWord ++ tailWord_2103869).sum := by decide
  have hdescent : baseEnd_2103869 < baseStart_2103869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103879 : List Nat := [1, 1, 4, 1, 4, 3, 1, 2, 1, 3, 2]
def baseStart_2103879 : Nat := 118140960795 + 2103879 * 2 ^ 59
def prefixEnd_2103879 : Nat := 4983230072969 + 3 ^ 40 * 2103879 * 2
def baseEnd_2103879 : Nat := 1080301165900679297436943

theorem tailTrace_2103879 : CollatzResearch.WordTrace tailWord_2103879 prefixEnd_2103879 1080301165900679297436943 := by
  unfold tailWord_2103879
  simp only [CollatzResearch.WordTrace]
  refine ⟨76734771145013171771866691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51156514096675447847911127 76734771145013171771866691)
  ·
    refine ⟨115102156717519757657800037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76734771145013171771866691 115102156717519757657800037)
    ·
      refine ⟨21581654384534954560837507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115102156717519757657800037 21581654384534954560837507)
      ·
        refine ⟨32372481576802431841256261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21581654384534954560837507 32372481576802431841256261)
        ·
          refine ⟨6069840295650455970235549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32372481576802431841256261 6069840295650455970235549)
          ·
            refine ⟨2276190110868920988838331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6069840295650455970235549 2276190110868920988838331)
            ·
              refine ⟨3414285166303381483257497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2276190110868920988838331 3414285166303381483257497)
              ·
                refine ⟨2560713874727536112443123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3414285166303381483257497 2560713874727536112443123)
                ·
                  refine ⟨3841070812091304168664685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2560713874727536112443123 3841070812091304168664685)
                  ·
                    refine ⟨1440401554534239063249257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3841070812091304168664685 1440401554534239063249257)
                    ·
                      refine ⟨1080301165900679297436943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1440401554534239063249257 1080301165900679297436943)
                      ·
                        rfl

theorem cell23_2103879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 3, 2].length) (baseStart_2103879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103879 prefixEnd_2103879 := by exact prefixLift 2103879
  have htrace : WordTrace (prefixWord ++ tailWord_2103879) baseStart_2103879 baseEnd_2103879 := by
    simpa [prefixWord, tailWord_2103879, baseEnd_2103879] using wordTrace_append hprefix tailTrace_2103879
  have hstable : (prefixWord ++ tailWord_2103879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103879).length < 2 ^ (prefixWord ++ tailWord_2103879).sum := by decide
  have hdescent : baseEnd_2103879 < baseStart_2103879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103892 : List Nat := [2, 4, 1, 1, 1, 4, 1, 2, 1, 4, 2]
def baseStart_2103892 : Nat := 118140960795 + 2103892 * 2 ^ 59
def prefixEnd_2103892 : Nat := 4983230072969 + 3 ^ 40 * 2103892 * 2
def baseEnd_2103892 : Nat := 1080307841149187746574383

theorem tailTrace_2103892 : CollatzResearch.WordTrace tailWord_2103892 prefixEnd_2103892 1080307841149187746574383 := by
  unfold tailWord_2103892
  simp only [CollatzResearch.WordTrace]
  refine ⟨38367622646983037496044965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51156830195977383328059953 38367622646983037496044965)
  ·
    refine ⟨7193929246309319530508431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38367622646983037496044965 7193929246309319530508431)
    ·
      refine ⟨10790893869463979295762647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7193929246309319530508431 10790893869463979295762647)
      ·
        refine ⟨16186340804195968943643971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10790893869463979295762647 16186340804195968943643971)
        ·
          refine ⟨24279511206293953415465957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16186340804195968943643971 24279511206293953415465957)
          ·
            refine ⟨4552408351180116265399867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24279511206293953415465957 4552408351180116265399867)
            ·
              refine ⟨6828612526770174398099801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4552408351180116265399867 6828612526770174398099801)
              ·
                refine ⟨5121459395077630798574851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6828612526770174398099801 5121459395077630798574851)
                ·
                  refine ⟨7682189092616446197862277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5121459395077630798574851 7682189092616446197862277)
                  ·
                    refine ⟨1440410454865583662099177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7682189092616446197862277 1440410454865583662099177)
                    ·
                      refine ⟨1080307841149187746574383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1440410454865583662099177 1080307841149187746574383)
                      ·
                        rfl

theorem cell23_2103892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_2103892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103892 prefixEnd_2103892 := by exact prefixLift 2103892
  have htrace : WordTrace (prefixWord ++ tailWord_2103892) baseStart_2103892 baseEnd_2103892 := by
    simpa [prefixWord, tailWord_2103892, baseEnd_2103892] using wordTrace_append hprefix tailTrace_2103892
  have hstable : (prefixWord ++ tailWord_2103892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103892).length < 2 ^ (prefixWord ++ tailWord_2103892).sum := by decide
  have hdescent : baseEnd_2103892 < baseStart_2103892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103965 : List Nat := [1, 4, 2, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_2103965 : Nat := 118140960795 + 2103965 * 2 ^ 59
def prefixEnd_2103965 : Nat := 4983230072969 + 3 ^ 40 * 2103965 * 2
def baseEnd_2103965 : Nat := 1080345325236965960961547

theorem tailTrace_2103965 : CollatzResearch.WordTrace tailWord_2103965 prefixEnd_2103965 1080345325236965960961547 := by
  unfold tailWord_2103965
  simp only [CollatzResearch.WordTrace]
  refine ⟨76737907822701608459497349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51158605215134405639664899 76737907822701608459497349)
  ·
    refine ⟨14388357716756551586155753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76737907822701608459497349 14388357716756551586155753)
    ·
      refine ⟨10791268287567413689616815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14388357716756551586155753 10791268287567413689616815)
      ·
        refine ⟨16186902431351120534425223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10791268287567413689616815 16186902431351120534425223)
        ·
          refine ⟨24280353647026680801637835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16186902431351120534425223 24280353647026680801637835)
          ·
            refine ⟨36420530470540021202456753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24280353647026680801637835 36420530470540021202456753)
            ·
              refine ⟨27315397852905015901842565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36420530470540021202456753 27315397852905015901842565)
              ·
                refine ⟨5121637097419690481595481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27315397852905015901842565 5121637097419690481595481)
                ·
                  refine ⟨3841227823064767861196611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5121637097419690481595481 3841227823064767861196611)
                  ·
                    refine ⟨5761841734597151791794917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3841227823064767861196611 5761841734597151791794917)
                    ·
                      refine ⟨1080345325236965960961547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5761841734597151791794917 1080345325236965960961547)
                      ·
                        rfl

theorem cell23_2103965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_2103965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103965 prefixEnd_2103965 := by exact prefixLift 2103965
  have htrace : WordTrace (prefixWord ++ tailWord_2103965) baseStart_2103965 baseEnd_2103965 := by
    simpa [prefixWord, tailWord_2103965, baseEnd_2103965] using wordTrace_append hprefix tailTrace_2103965
  have hstable : (prefixWord ++ tailWord_2103965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103965).length < 2 ^ (prefixWord ++ tailWord_2103965).sum := by decide
  have hdescent : baseEnd_2103965 < baseStart_2103965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103982 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_2103982 : Nat := 118140960795 + 2103982 * 2 ^ 59
def prefixEnd_2103982 : Nat := 4983230072969 + 3 ^ 40 * 2103982 * 2
def baseEnd_2103982 : Nat := 1080354054408092394448969

theorem tailTrace_2103982 : CollatzResearch.WordTrace tailWord_2103982 prefixEnd_2103982 1080354054408092394448969 := by
  unfold tailWord_2103982
  simp only [CollatzResearch.WordTrace]
  refine ⟨9592315982955002545358275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51159018575760013575244133 9592315982955002545358275)
  ·
    refine ⟨14388473974432503818037413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9592315982955002545358275 14388473974432503818037413)
    ·
      refine ⟨2697838870206094465882015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14388473974432503818037413 2697838870206094465882015)
      ·
        refine ⟨4046758305309141698823023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2697838870206094465882015 4046758305309141698823023)
        ·
          refine ⟨6070137457963712548234535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4046758305309141698823023 6070137457963712548234535)
          ·
            refine ⟨9105206186945568822351803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6070137457963712548234535 9105206186945568822351803)
            ·
              refine ⟨13657809280418353233527705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9105206186945568822351803 13657809280418353233527705)
              ·
                refine ⟨10243356960313764925145779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13657809280418353233527705 10243356960313764925145779)
                ·
                  refine ⟨15365035440470647387718669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10243356960313764925145779 15365035440470647387718669)
                  ·
                    refine ⟨5761888290176492770394501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15365035440470647387718669 5761888290176492770394501)
                    ·
                      refine ⟨1080354054408092394448969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5761888290176492770394501 1080354054408092394448969)
                      ·
                        rfl

theorem cell23_2103982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_2103982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2103982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2103982 prefixEnd_2103982 := by exact prefixLift 2103982
  have htrace : WordTrace (prefixWord ++ tailWord_2103982) baseStart_2103982 baseEnd_2103982 := by
    simpa [prefixWord, tailWord_2103982, baseEnd_2103982] using wordTrace_append hprefix tailTrace_2103982
  have hstable : (prefixWord ++ tailWord_2103982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103982).length < 2 ^ (prefixWord ++ tailWord_2103982).sum := by decide
  have hdescent : baseEnd_2103982 < baseStart_2103982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104042 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 6, 3, 2]
def baseStart_2104042 : Nat := 118140960795 + 2104042 * 2 ^ 59
def prefixEnd_2104042 : Nat := 4983230072969 + 3 ^ 40 * 2104042 * 2
def baseEnd_2104042 : Nat := 1080384863247362159698693

theorem tailTrace_2104042 : CollatzResearch.WordTrace tailWord_2104042 prefixEnd_2104042 1080384863247362159698693 := by
  unfold tailWord_2104042
  simp only [CollatzResearch.WordTrace]
  refine ⟨19185179060855662652512595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51160477495615100406700253 19185179060855662652512595)
  ·
    refine ⟨28777768591283493978768893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19185179060855662652512595 28777768591283493978768893)
    ·
      refine ⟨10791663221731310242038335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28777768591283493978768893 10791663221731310242038335)
      ·
        refine ⟨16187494832596965363057503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10791663221731310242038335 16187494832596965363057503)
        ·
          refine ⟨24281242248895448044586255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16187494832596965363057503 24281242248895448044586255)
          ·
            refine ⟨36421863373343172066879383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24281242248895448044586255 36421863373343172066879383)
            ·
              refine ⟨54632795060014758100319075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36421863373343172066879383 54632795060014758100319075)
              ·
                refine ⟨81949192590022137150478613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54632795060014758100319075 81949192590022137150478613)
                ·
                  refine ⟨3841368402657287678928685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81949192590022137150478613 3841368402657287678928685)
                  ·
                    refine ⟨1440513150996482879598257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3841368402657287678928685 1440513150996482879598257)
                    ·
                      refine ⟨1080384863247362159698693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1440513150996482879598257 1080384863247362159698693)
                      ·
                        rfl

theorem cell23_2104042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_2104042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104042 prefixEnd_2104042 := by exact prefixLift 2104042
  have htrace : WordTrace (prefixWord ++ tailWord_2104042) baseStart_2104042 baseEnd_2104042 := by
    simpa [prefixWord, tailWord_2104042, baseEnd_2104042] using wordTrace_append hprefix tailTrace_2104042
  have hstable : (prefixWord ++ tailWord_2104042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104042).length < 2 ^ (prefixWord ++ tailWord_2104042).sum := by decide
  have hdescent : baseEnd_2104042 < baseStart_2104042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104053 : List Nat := [1, 3, 6, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_2104053 : Nat := 118140960795 + 2104053 * 2 ^ 59
def prefixEnd_2104053 : Nat := 4983230072969 + 3 ^ 40 * 2104053 * 2
def baseEnd_2104053 : Nat := 1080390511534561616661143

theorem tailTrace_2104053 : CollatzResearch.WordTrace tailWord_2104053 prefixEnd_2104053 1080390511534561616661143 := by
  unfold tailWord_2104053
  simp only [CollatzResearch.WordTrace]
  refine ⟨76741117446382799488700813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51160744964255199659133875 76741117446382799488700813)
  ·
    refine ⟨28777919042393549808262805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76741117446382799488700813 28777919042393549808262805)
    ·
      refine ⟨1348964955112197647262319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28777919042393549808262805 1348964955112197647262319)
      ·
        refine ⟨2023447432668296470893479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1348964955112197647262319 2023447432668296470893479)
        ·
          refine ⟨3035171149002444706340219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2023447432668296470893479 3035171149002444706340219)
          ·
            refine ⟨4552756723503667059510329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3035171149002444706340219 4552756723503667059510329)
            ·
              refine ⟨3414567542627750294632747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4552756723503667059510329 3414567542627750294632747)
              ·
                refine ⟨5121851313941625441949121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3414567542627750294632747 5121851313941625441949121)
                ·
                  refine ⟨3841388485456219081461841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5121851313941625441949121 3841388485456219081461841)
                  ·
                    refine ⟨2881041364092164311096381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3841388485456219081461841 2881041364092164311096381)
                    ·
                      refine ⟨1080390511534561616661143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2881041364092164311096381 1080390511534561616661143)
                      ·
                        rfl

theorem cell23_2104053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_2104053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104053 prefixEnd_2104053 := by exact prefixLift 2104053
  have htrace : WordTrace (prefixWord ++ tailWord_2104053) baseStart_2104053 baseEnd_2104053 := by
    simpa [prefixWord, tailWord_2104053, baseEnd_2104053] using wordTrace_append hprefix tailTrace_2104053
  have hstable : (prefixWord ++ tailWord_2104053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104053).length < 2 ^ (prefixWord ++ tailWord_2104053).sum := by decide
  have hdescent : baseEnd_2104053 < baseStart_2104053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104085 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 3, 2, 4]
def baseStart_2104085 : Nat := 118140960795 + 2104085 * 2 ^ 59
def prefixEnd_2104085 : Nat := 4983230072969 + 3 ^ 40 * 2104085 * 2
def baseEnd_2104085 : Nat := 1080406942915505491460995

theorem tailTrace_2104085 : CollatzResearch.WordTrace tailWord_2104085 prefixEnd_2104085 1080406942915505491460995 := by
  unfold tailWord_2104085
  simp only [CollatzResearch.WordTrace]
  refine ⟨76742284582266868953865709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51161523054844579302577139 76742284582266868953865709)
  ·
    refine ⟨28778356718350075857699641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76742284582266868953865709 28778356718350075857699641)
    ·
      refine ⟨21583767538762556893274731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28778356718350075857699641 21583767538762556893274731)
      ·
        refine ⟨32375651308143835339912097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21583767538762556893274731 32375651308143835339912097)
        ·
          refine ⟨24281738481107876504934073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32375651308143835339912097 24281738481107876504934073)
          ·
            refine ⟨18211303860830907378700555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24281738481107876504934073 18211303860830907378700555)
            ·
              refine ⟨27316955791246361068050833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18211303860830907378700555 27316955791246361068050833)
              ·
                refine ⟨20487716843434770801038125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27316955791246361068050833 20487716843434770801038125)
                ·
                  refine ⟨7682893816288039050389297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20487716843434770801038125 7682893816288039050389297)
                  ·
                    refine ⟨5762170362216029287791973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7682893816288039050389297 5762170362216029287791973)
                    ·
                      refine ⟨1080406942915505491460995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5762170362216029287791973 1080406942915505491460995)
                      ·
                        rfl

theorem cell23_2104085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_2104085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104085 prefixEnd_2104085 := by exact prefixLift 2104085
  have htrace : WordTrace (prefixWord ++ tailWord_2104085) baseStart_2104085 baseEnd_2104085 := by
    simpa [prefixWord, tailWord_2104085, baseEnd_2104085] using wordTrace_append hprefix tailTrace_2104085
  have hstable : (prefixWord ++ tailWord_2104085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104085).length < 2 ^ (prefixWord ++ tailWord_2104085).sum := by decide
  have hdescent : baseEnd_2104085 < baseStart_2104085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104092 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 3, 2, 3]
def baseStart_2104092 : Nat := 118140960795 + 2104092 * 2 ^ 59
def prefixEnd_2104092 : Nat := 4983230072969 + 3 ^ 40 * 2104092 * 2
def baseEnd_2104092 : Nat := 1080410537280086964073463

theorem tailTrace_2104092 : CollatzResearch.WordTrace tailWord_2104092 prefixEnd_2104092 1080410537280086964073463 := by
  unfold tailWord_2104092
  simp only [CollatzResearch.WordTrace]
  refine ⟨38371269946620754574685265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51161693262161006099580353 38371269946620754574685265)
  ·
    refine ⟨28778452459965565931013949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38371269946620754574685265 28778452459965565931013949)
    ·
      refine ⟨10791919672487087224130231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28778452459965565931013949 10791919672487087224130231)
      ·
        refine ⟨16187879508730630836195347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10791919672487087224130231 16187879508730630836195347)
        ·
          refine ⟨24281819263095946254293021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16187879508730630836195347 24281819263095946254293021)
          ·
            refine ⟨9105682223660979845359883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24281819263095946254293021 9105682223660979845359883)
            ·
              refine ⟨13658523335491469768039825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9105682223660979845359883 13658523335491469768039825)
              ·
                refine ⟨10243892501618602326029869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13658523335491469768039825 10243892501618602326029869)
                ·
                  refine ⟨3841459688106975872261201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10243892501618602326029869 3841459688106975872261201)
                  ·
                    refine ⟨2881094766080231904195901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3841459688106975872261201 2881094766080231904195901)
                    ·
                      refine ⟨1080410537280086964073463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2881094766080231904195901 1080410537280086964073463)
                      ·
                        rfl

theorem cell23_2104092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_2104092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104092 prefixEnd_2104092 := by exact prefixLift 2104092
  have htrace : WordTrace (prefixWord ++ tailWord_2104092) baseStart_2104092 baseEnd_2104092 := by
    simpa [prefixWord, tailWord_2104092, baseEnd_2104092] using wordTrace_append hprefix tailTrace_2104092
  have hstable : (prefixWord ++ tailWord_2104092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104092).length < 2 ^ (prefixWord ++ tailWord_2104092).sum := by decide
  have hdescent : baseEnd_2104092 < baseStart_2104092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104095 : List Nat := [1, 1, 2, 4, 2, 2, 3, 8]
def baseStart_2104095 : Nat := 118140960795 + 2104095 * 2 ^ 59
def prefixEnd_2104095 : Nat := 4983230072969 + 3 ^ 40 * 2104095 * 2
def baseEnd_2104095 : Nat := 40015262137853720456887

theorem tailTrace_2104095 : CollatzResearch.WordTrace tailWord_2104095 prefixEnd_2104095 40015262137853720456887 := by
  unfold tailWord_2104095
  simp only [CollatzResearch.WordTrace]
  refine ⟨76742649312230640661729739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51161766208153760441153159 76742649312230640661729739)
  ·
    refine ⟨115113973968345960992594609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76742649312230640661729739 115113973968345960992594609)
    ·
      refine ⟨86335480476259470744445957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115113973968345960992594609 86335480476259470744445957)
      ·
        refine ⟨16187902589298650764583617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86335480476259470744445957 16187902589298650764583617)
        ·
          refine ⟨12140926941973988073437713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16187902589298650764583617 12140926941973988073437713)
          ·
            refine ⟨9105695206480491055078285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12140926941973988073437713 9105695206480491055078285)
            ·
              refine ⟨3414635702430184145654357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9105695206480491055078285 3414635702430184145654357)
              ·
                refine ⟨40015262137853720456887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3414635702430184145654357 40015262137853720456887)
                ·
                  rfl

theorem cell23_2104095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 8].length) (baseStart_2104095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104095 prefixEnd_2104095 := by exact prefixLift 2104095
  have htrace : WordTrace (prefixWord ++ tailWord_2104095) baseStart_2104095 baseEnd_2104095 := by
    simpa [prefixWord, tailWord_2104095, baseEnd_2104095] using wordTrace_append hprefix tailTrace_2104095
  have hstable : (prefixWord ++ tailWord_2104095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104095).length < 2 ^ (prefixWord ++ tailWord_2104095).sum := by decide
  have hdescent : baseEnd_2104095 < baseStart_2104095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104105 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 5, 3, 3]
def baseStart_2104105 : Nat := 118140960795 + 2104105 * 2 ^ 59
def prefixEnd_2104105 : Nat := 4983230072969 + 3 ^ 40 * 2104105 * 2
def baseEnd_2104105 : Nat := 1080417212528595413210903

theorem tailTrace_2104105 : CollatzResearch.WordTrace tailWord_2104105 prefixEnd_2104105 1080417212528595413210903 := by
  unfold tailWord_2104105
  simp only [CollatzResearch.WordTrace]
  refine ⟨76743014042194412369593769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51162009361462941579729179 76743014042194412369593769)
  ·
    refine ⟨57557260531645809277195327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76743014042194412369593769 57557260531645809277195327)
    ·
      refine ⟨86335890797468713915792991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57557260531645809277195327 86335890797468713915792991)
      ·
        refine ⟨129503836196203070873689487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86335890797468713915792991 129503836196203070873689487)
        ·
          refine ⟨194255754294304606310534231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129503836196203070873689487 194255754294304606310534231)
          ·
            refine ⟨291383631441456909465801347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194255754294304606310534231 291383631441456909465801347)
            ·
              refine ⟨437075447162185364198702021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291383631441456909465801347 437075447162185364198702021)
              ·
                refine ⟨81951646342909755787256629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 437075447162185364198702021 81951646342909755787256629)
                ·
                  refine ⟨7682966844647789605055309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81951646342909755787256629 7682966844647789605055309)
                  ·
                    refine ⟨2881112566742921101895741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7682966844647789605055309 2881112566742921101895741)
                    ·
                      refine ⟨1080417212528595413210903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2881112566742921101895741 1080417212528595413210903)
                      ·
                        rfl

theorem cell23_2104105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 3, 3].length) (baseStart_2104105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104105 prefixEnd_2104105 := by exact prefixLift 2104105
  have htrace : WordTrace (prefixWord ++ tailWord_2104105) baseStart_2104105 baseEnd_2104105 := by
    simpa [prefixWord, tailWord_2104105, baseEnd_2104105] using wordTrace_append hprefix tailTrace_2104105
  have hstable : (prefixWord ++ tailWord_2104105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104105).length < 2 ^ (prefixWord ++ tailWord_2104105).sum := by decide
  have hdescent : baseEnd_2104105 < baseStart_2104105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104126 : List Nat := [4, 2, 1, 2, 3, 1, 1, 3, 1, 2, 3]
def baseStart_2104126 : Nat := 118140960795 + 2104126 * 2 ^ 59
def prefixEnd_2104126 : Nat := 4983230072969 + 3 ^ 40 * 2104126 * 2
def baseEnd_2104126 : Nat := 1080427995622339831048307

theorem tailTrace_2104126 : CollatzResearch.WordTrace tailWord_2104126 prefixEnd_2104126 1080427995622339831048307 := by
  unfold tailWord_2104126
  simp only [CollatzResearch.WordTrace]
  refine ⟨9592972496889791619513529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51162519983412221970738821 9592972496889791619513529)
  ·
    refine ⟨7194729372667343714635147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9592972496889791619513529 7194729372667343714635147)
    ·
      refine ⟨10792094059001015571952721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7194729372667343714635147 10792094059001015571952721)
      ·
        refine ⟨8094070544250761678964541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10792094059001015571952721 8094070544250761678964541)
        ·
          refine ⟨3035276454094035629611703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8094070544250761678964541 3035276454094035629611703)
          ·
            refine ⟨4552914681141053444417555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3035276454094035629611703 4552914681141053444417555)
            ·
              refine ⟨6829372021711580166626333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4552914681141053444417555 6829372021711580166626333)
              ·
                refine ⟨2561014508141842562484875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6829372021711580166626333 2561014508141842562484875)
                ·
                  refine ⟨3841521762212763843727313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2561014508141842562484875 3841521762212763843727313)
                  ·
                    refine ⟨2881141321659572882795485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3841521762212763843727313 2881141321659572882795485)
                    ·
                      refine ⟨1080427995622339831048307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2881141321659572882795485 1080427995622339831048307)
                      ·
                        rfl

theorem cell23_2104126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_2104126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104126 prefixEnd_2104126 := by exact prefixLift 2104126
  have htrace : WordTrace (prefixWord ++ tailWord_2104126) baseStart_2104126 baseEnd_2104126 := by
    simpa [prefixWord, tailWord_2104126, baseEnd_2104126] using wordTrace_append hprefix tailTrace_2104126
  have hstable : (prefixWord ++ tailWord_2104126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104126).length < 2 ^ (prefixWord ++ tailWord_2104126).sum := by decide
  have hdescent : baseEnd_2104126 < baseStart_2104126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104156 : List Nat := [2, 2, 4, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_2104156 : Nat := 118140960795 + 2104156 * 2 ^ 59
def prefixEnd_2104156 : Nat := 4983230072969 + 3 ^ 40 * 2104156 * 2
def baseEnd_2104156 : Nat := 1080443400041974713673169

theorem tailTrace_2104156 : CollatzResearch.WordTrace tailWord_2104156 prefixEnd_2104156 1080443400041974713673169 := by
  unfold tailWord_2104156
  simp only [CollatzResearch.WordTrace]
  refine ⟨38372437082504824039850161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51163249443339765386466881 38372437082504824039850161)
  ·
    refine ⟨28779327811878618029887621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38372437082504824039850161 28779327811878618029887621)
    ·
      refine ⟨5396123964727240880603929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28779327811878618029887621 5396123964727240880603929)
      ·
        refine ⟨4047092973545430660452947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5396123964727240880603929 4047092973545430660452947)
        ·
          refine ⟨6070639460318145990679421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4047092973545430660452947 6070639460318145990679421)
          ·
            refine ⟨2276489797619304746504783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6070639460318145990679421 2276489797619304746504783)
            ·
              refine ⟨3414734696428957119757175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2276489797619304746504783 3414734696428957119757175)
              ·
                refine ⟨5122102044643435679635763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3414734696428957119757175 5122102044643435679635763)
                ·
                  refine ⟨7683153066965153519453645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5122102044643435679635763 7683153066965153519453645)
                  ·
                    refine ⟨2881182400111932569795117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7683153066965153519453645 2881182400111932569795117)
                    ·
                      refine ⟨1080443400041974713673169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2881182400111932569795117 1080443400041974713673169)
                      ·
                        rfl

theorem cell23_2104156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_2104156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104156 prefixEnd_2104156 := by exact prefixLift 2104156
  have htrace : WordTrace (prefixWord ++ tailWord_2104156) baseStart_2104156 baseEnd_2104156 := by
    simpa [prefixWord, tailWord_2104156, baseEnd_2104156] using wordTrace_append hprefix tailTrace_2104156
  have hstable : (prefixWord ++ tailWord_2104156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104156).length < 2 ^ (prefixWord ++ tailWord_2104156).sum := by decide
  have hdescent : baseEnd_2104156 < baseStart_2104156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104175 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 4]
def baseStart_2104175 : Nat := 118140960795 + 2104175 * 2 ^ 59
def prefixEnd_2104175 : Nat := 4983230072969 + 3 ^ 40 * 2104175 * 2
def baseEnd_2104175 : Nat := 1080453156174410139335581

theorem tailTrace_2104175 : CollatzResearch.WordTrace tailWord_2104175 prefixEnd_2104175 1080453156174410139335581 := by
  unfold tailWord_2104175
  simp only [CollatzResearch.WordTrace]
  refine ⟨76745567151940814324641979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51163711434627209549761319 76745567151940814324641979)
  ·
    refine ⟨115118350727911221486962969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76745567151940814324641979 115118350727911221486962969)
    ·
      refine ⟨86338763045933416115222227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115118350727911221486962969 86338763045933416115222227)
      ·
        refine ⟨129508144568900124172833341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86338763045933416115222227 129508144568900124172833341)
        ·
          refine ⟨48565554213337546564812503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129508144568900124172833341 48565554213337546564812503)
          ·
            refine ⟨72848331320006319847218755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48565554213337546564812503 72848331320006319847218755)
            ·
              refine ⟨109272496980009479770828133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72848331320006319847218755 109272496980009479770828133)
              ·
                refine ⟨20488593183751777457030275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109272496980009479770828133 20488593183751777457030275)
                ·
                  refine ⟨30732889775627666185545413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20488593183751777457030275 30732889775627666185545413)
                  ·
                    refine ⟨5762416832930187409789765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30732889775627666185545413 5762416832930187409789765)
                    ·
                      refine ⟨1080453156174410139335581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5762416832930187409789765 1080453156174410139335581)
                      ·
                        rfl

theorem cell23_2104175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 4].length) (baseStart_2104175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104175 prefixEnd_2104175 := by exact prefixLift 2104175
  have htrace : WordTrace (prefixWord ++ tailWord_2104175) baseStart_2104175 baseEnd_2104175 := by
    simpa [prefixWord, tailWord_2104175, baseEnd_2104175] using wordTrace_append hprefix tailTrace_2104175
  have hstable : (prefixWord ++ tailWord_2104175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104175).length < 2 ^ (prefixWord ++ tailWord_2104175).sum := by decide
  have hdescent : baseEnd_2104175 < baseStart_2104175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104179 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 4, 2, 2]
def baseStart_2104179 : Nat := 118140960795 + 2104179 * 2 ^ 59
def prefixEnd_2104179 : Nat := 4983230072969 + 3 ^ 40 * 2104179 * 2
def baseEnd_2104179 : Nat := 1080455210097028123685563

theorem tailTrace_2104179 : CollatzResearch.WordTrace tailWord_2104179 prefixEnd_2104179 1080455210097028123685563 := by
  unfold tailWord_2104179
  simp only [CollatzResearch.WordTrace]
  refine ⟨76745713043926323007787591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51163808695950882005191727 76745713043926323007787591)
  ·
    refine ⟨115118569565889484511681387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76745713043926323007787591 115118569565889484511681387)
    ·
      refine ⟨172677854348834226767522081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115118569565889484511681387 172677854348834226767522081)
      ·
        refine ⟨129508390761625670075641561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172677854348834226767522081 129508390761625670075641561)
        ·
          refine ⟨97131293071219252556731171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129508390761625670075641561 97131293071219252556731171)
          ·
            refine ⟨145696939606828878835096757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97131293071219252556731171 145696939606828878835096757)
            ·
              refine ⟨13659088088140207390790321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 145696939606828878835096757 13659088088140207390790321)
              ·
                refine ⟨10244316066105155543092741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13659088088140207390790321 10244316066105155543092741)
                ·
                  refine ⟨1920809262394716664329889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10244316066105155543092741 1920809262394716664329889)
                  ·
                    refine ⟨1440606946796037498247417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1920809262394716664329889 1440606946796037498247417)
                    ·
                      refine ⟨1080455210097028123685563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1440606946796037498247417 1080455210097028123685563)
                      ·
                        rfl

theorem cell23_2104179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 2, 2].length) (baseStart_2104179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104179 prefixEnd_2104179 := by exact prefixLift 2104179
  have htrace : WordTrace (prefixWord ++ tailWord_2104179) baseStart_2104179 baseEnd_2104179 := by
    simpa [prefixWord, tailWord_2104179, baseEnd_2104179] using wordTrace_append hprefix tailTrace_2104179
  have hstable : (prefixWord ++ tailWord_2104179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104179).length < 2 ^ (prefixWord ++ tailWord_2104179).sum := by decide
  have hdescent : baseEnd_2104179 < baseStart_2104179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104195 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 7]
def baseStart_2104195 : Nat := 118140960795 + 2104195 * 2 ^ 59
def prefixEnd_2104195 : Nat := 4983230072969 + 3 ^ 40 * 2104195 * 2
def baseEnd_2104195 : Nat := 1080463425787500061085489

theorem tailTrace_2104195 : CollatzResearch.WordTrace tailWord_2104195 prefixEnd_2104195 1080463425787500061085489 := by
  unfold tailWord_2104195
  simp only [CollatzResearch.WordTrace]
  refine ⟨76746296611868357740370039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51164197741245571826913359 76746296611868357740370039)
  ·
    refine ⟨115119444917802536610555059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76746296611868357740370039 115119444917802536610555059)
    ·
      refine ⟨172679167376703804915832589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115119444917802536610555059 172679167376703804915832589)
      ·
        refine ⟨64754687766263926843437221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172679167376703804915832589 64754687766263926843437221)
        ·
          refine ⟨12141503956174486283144479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64754687766263926843437221 12141503956174486283144479)
          ·
            refine ⟨18212255934261729424716719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12141503956174486283144479 18212255934261729424716719)
            ·
              refine ⟨27318383901392594137075079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18212255934261729424716719 27318383901392594137075079)
              ·
                refine ⟨40977575852088891205612619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27318383901392594137075079 40977575852088891205612619)
                ·
                  refine ⟨61466363778133336808418929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40977575852088891205612619 61466363778133336808418929)
                  ·
                    refine ⟨46099772833600002606314197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61466363778133336808418929 46099772833600002606314197)
                    ·
                      refine ⟨1080463425787500061085489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46099772833600002606314197 1080463425787500061085489)
                      ·
                        rfl

theorem cell23_2104195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_2104195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104195 prefixEnd_2104195 := by exact prefixLift 2104195
  have htrace : WordTrace (prefixWord ++ tailWord_2104195) baseStart_2104195 baseEnd_2104195 := by
    simpa [prefixWord, tailWord_2104195, baseEnd_2104195] using wordTrace_append hprefix tailTrace_2104195
  have hstable : (prefixWord ++ tailWord_2104195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104195).length < 2 ^ (prefixWord ++ tailWord_2104195).sum := by decide
  have hdescent : baseEnd_2104195 < baseStart_2104195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104196 : List Nat := [2, 3, 2, 1, 1, 1, 1, 6, 2, 2, 2]
def baseStart_2104196 : Nat := 118140960795 + 2104196 * 2 ^ 59
def prefixEnd_2104196 : Nat := 4983230072969 + 3 ^ 40 * 2104196 * 2
def baseEnd_2104196 : Nat := 1080463939268154557172985

theorem tailTrace_2104196 : CollatzResearch.WordTrace tailWord_2104196 prefixEnd_2104196 1080463939268154557172985 := by
  unfold tailWord_2104196
  simp only [CollatzResearch.WordTrace]
  refine ⟨38373166542432367455578221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51164222056576489940770961 38373166542432367455578221)
  ·
    refine ⟨14389937453412137795841833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38373166542432367455578221 14389937453412137795841833)
    ·
      refine ⟨10792453090059103346881375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14389937453412137795841833 10792453090059103346881375)
      ·
        refine ⟨16188679635088655020322063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10792453090059103346881375 16188679635088655020322063)
        ·
          refine ⟨24283019452632982530483095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16188679635088655020322063 24283019452632982530483095)
          ·
            refine ⟨36424529178949473795724643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24283019452632982530483095 36424529178949473795724643)
            ·
              refine ⟨54636793768424210693586965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36424529178949473795724643 54636793768424210693586965)
              ·
                refine ⟨2561099707894884876261889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54636793768424210693586965 2561099707894884876261889)
                ·
                  refine ⟨1920824780921163657196417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2561099707894884876261889 1920824780921163657196417)
                  ·
                    refine ⟨1440618585690872742897313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1920824780921163657196417 1440618585690872742897313)
                    ·
                      refine ⟨1080463939268154557172985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1440618585690872742897313 1080463939268154557172985)
                      ·
                        rfl

theorem cell23_2104196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_2104196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104196 prefixEnd_2104196 := by exact prefixLift 2104196
  have htrace : WordTrace (prefixWord ++ tailWord_2104196) baseStart_2104196 baseEnd_2104196 := by
    simpa [prefixWord, tailWord_2104196, baseEnd_2104196] using wordTrace_append hprefix tailTrace_2104196
  have hstable : (prefixWord ++ tailWord_2104196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104196).length < 2 ^ (prefixWord ++ tailWord_2104196).sum := by decide
  have hdescent : baseEnd_2104196 < baseStart_2104196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104213 : List Nat := [1, 3, 2, 1, 1, 4, 4, 1, 2, 2, 2]
def baseStart_2104213 : Nat := 118140960795 + 2104213 * 2 ^ 59
def prefixEnd_2104213 : Nat := 4983230072969 + 3 ^ 40 * 2104213 * 2
def baseEnd_2104213 : Nat := 1080472668439280990660407

theorem tailTrace_2104213 : CollatzResearch.WordTrace tailWord_2104213 prefixEnd_2104213 1080472668439280990660407 := by
  unfold tailWord_2104213
  simp only [CollatzResearch.WordTrace]
  refine ⟨76746953125803146814525293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51164635417202097876350195 76746953125803146814525293)
  ·
    refine ⟨28780107422176180055446985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76746953125803146814525293 28780107422176180055446985)
    ·
      refine ⟨21585080566632135041585239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28780107422176180055446985 21585080566632135041585239)
      ·
        refine ⟨32377620849948202562377859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21585080566632135041585239 32377620849948202562377859)
        ·
          refine ⟨48566431274922303843566789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32377620849948202562377859 48566431274922303843566789)
          ·
            refine ⟨9106205864047931970668773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48566431274922303843566789 9106205864047931970668773)
            ·
              refine ⟨1707413599508987244500395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9106205864047931970668773 1707413599508987244500395)
              ·
                refine ⟨2561120399263480866750593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1707413599508987244500395 2561120399263480866750593)
                ·
                  refine ⟨1920840299447610650062945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2561120399263480866750593 1920840299447610650062945)
                  ·
                    refine ⟨1440630224585707987547209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1920840299447610650062945 1440630224585707987547209)
                    ·
                      refine ⟨1080472668439280990660407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1440630224585707987547209 1080472668439280990660407)
                      ·
                        rfl

theorem cell23_2104213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 2, 2, 2].length) (baseStart_2104213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104213 prefixEnd_2104213 := by exact prefixLift 2104213
  have htrace : WordTrace (prefixWord ++ tailWord_2104213) baseStart_2104213 baseEnd_2104213 := by
    simpa [prefixWord, tailWord_2104213, baseEnd_2104213] using wordTrace_append hprefix tailTrace_2104213
  have hstable : (prefixWord ++ tailWord_2104213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104213).length < 2 ^ (prefixWord ++ tailWord_2104213).sum := by decide
  have hdescent : baseEnd_2104213 < baseStart_2104213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104253 : List Nat := [1, 4, 1, 2, 4, 2, 2, 2, 5]
def baseStart_2104253 : Nat := 118140960795 + 2104253 * 2 ^ 59
def prefixEnd_2104253 : Nat := 4983230072969 + 3 ^ 40 * 2104253 * 2
def baseEnd_2104253 : Nat := 120054800851717870462247

theorem tailTrace_2104253 : CollatzResearch.WordTrace tailWord_2104253 prefixEnd_2104253 120054800851717870462247 := by
  unfold tailWord_2104253
  simp only [CollatzResearch.WordTrace]
  refine ⟨76748412045658233645981413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51165608030438822430654275 76748412045658233645981413)
  ·
    refine ⟨14390327258560918808621515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76748412045658233645981413 14390327258560918808621515)
    ·
      refine ⟨21585490887841378212932273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14390327258560918808621515 21585490887841378212932273)
      ·
        refine ⟨16189118165881033659699205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21585490887841378212932273 16189118165881033659699205)
        ·
          refine ⟨3035459656102693811193601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16189118165881033659699205 3035459656102693811193601)
          ·
            refine ⟨2276594742077020358395201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3035459656102693811193601 2276594742077020358395201)
            ·
              refine ⟨1707446056557765268796401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2276594742077020358395201 1707446056557765268796401)
              ·
                refine ⟨1280584542418323951597301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1707446056557765268796401 1280584542418323951597301)
                ·
                  refine ⟨120054800851717870462247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1280584542418323951597301 120054800851717870462247)
                  ·
                    rfl

theorem cell23_2104253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_2104253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104253 prefixEnd_2104253 := by exact prefixLift 2104253
  have htrace : WordTrace (prefixWord ++ tailWord_2104253) baseStart_2104253 baseEnd_2104253 := by
    simpa [prefixWord, tailWord_2104253, baseEnd_2104253] using wordTrace_append hprefix tailTrace_2104253
  have hstable : (prefixWord ++ tailWord_2104253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104253).length < 2 ^ (prefixWord ++ tailWord_2104253).sum := by decide
  have hdescent : baseEnd_2104253 < baseStart_2104253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104272 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 3]
def baseStart_2104272 : Nat := 118140960795 + 2104272 * 2 ^ 59
def prefixEnd_2104272 : Nat := 4983230072969 + 3 ^ 40 * 2104272 * 2
def baseEnd_2104272 : Nat := 1080502963797896259822635

theorem tailTrace_2104272 : CollatzResearch.WordTrace tailWord_2104272 prefixEnd_2104272 1080502963797896259822635 := by
  unfold tailWord_2104272
  simp only [CollatzResearch.WordTrace]
  refine ⟨38374552516294699945461535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51166070021726266593948713 38374552516294699945461535)
  ·
    refine ⟨57561828774442049918192303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38374552516294699945461535 57561828774442049918192303)
    ·
      refine ⟨86342743161663074877288455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57561828774442049918192303 86342743161663074877288455)
      ·
        refine ⟨129514114742494612315932683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86342743161663074877288455 129514114742494612315932683)
        ·
          refine ⟨194271172113741918473899025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129514114742494612315932683 194271172113741918473899025)
          ·
            refine ⟨145703379085306438855424269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194271172113741918473899025 145703379085306438855424269)
            ·
              refine ⟨54638767156989914570784101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145703379085306438855424269 54638767156989914570784101)
              ·
                refine ⟨10244768841935608982022019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54638767156989914570784101 10244768841935608982022019)
                ·
                  refine ⟨15367153262903413473033029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10244768841935608982022019 15367153262903413473033029)
                  ·
                    refine ⟨2881341236794390026193693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15367153262903413473033029 2881341236794390026193693)
                    ·
                      refine ⟨1080502963797896259822635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2881341236794390026193693 1080502963797896259822635)
                      ·
                        rfl

theorem cell23_2104272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 3].length) (baseStart_2104272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104272 prefixEnd_2104272 := by exact prefixLift 2104272
  have htrace : WordTrace (prefixWord ++ tailWord_2104272) baseStart_2104272 baseEnd_2104272 := by
    simpa [prefixWord, tailWord_2104272, baseEnd_2104272] using wordTrace_append hprefix tailTrace_2104272
  have hstable : (prefixWord ++ tailWord_2104272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104272).length < 2 ^ (prefixWord ++ tailWord_2104272).sum := by decide
  have hdescent : baseEnd_2104272 < baseStart_2104272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104296 : List Nat := [2, 1, 4, 1, 1, 1, 3, 5, 1, 4]
def baseStart_2104296 : Nat := 118140960795 + 2104296 * 2 ^ 59
def prefixEnd_2104296 : Nat := 4983230072969 + 3 ^ 40 * 2104296 * 2
def baseEnd_2104296 : Nat := 360171762444534721974175

theorem tailTrace_2104296 : CollatzResearch.WordTrace tailWord_2104296 prefixEnd_2104296 360171762444534721974175 := by
  unfold tailWord_2104296
  simp only [CollatzResearch.WordTrace]
  refine ⟨38374990192251225994898371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51166653589668301326531161 38374990192251225994898371)
  ·
    refine ⟨57562485288376838992347557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38374990192251225994898371 57562485288376838992347557)
    ·
      refine ⟨10792965991570657311065167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57562485288376838992347557 10792965991570657311065167)
      ·
        refine ⟨16189448987355985966597751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10792965991570657311065167 16189448987355985966597751)
        ·
          refine ⟨24284173481033978949896627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16189448987355985966597751 24284173481033978949896627)
          ·
            refine ⟨36426260221550968424844941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24284173481033978949896627 36426260221550968424844941)
            ·
              refine ⟨13659847583081613159316853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36426260221550968424844941 13659847583081613159316853)
              ·
                refine ⟨1280610710913901233685955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13659847583081613159316853 1280610710913901233685955)
                ·
                  refine ⟨1920916066370851850528933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1280610710913901233685955 1920916066370851850528933)
                  ·
                    refine ⟨360171762444534721974175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1920916066370851850528933 360171762444534721974175)
                    ·
                      rfl

theorem cell23_2104296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_2104296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104296 prefixEnd_2104296 := by exact prefixLift 2104296
  have htrace : WordTrace (prefixWord ++ tailWord_2104296) baseStart_2104296 baseEnd_2104296 := by
    simpa [prefixWord, tailWord_2104296, baseEnd_2104296] using wordTrace_append hprefix tailTrace_2104296
  have hstable : (prefixWord ++ tailWord_2104296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104296).length < 2 ^ (prefixWord ++ tailWord_2104296).sum := by decide
  have hdescent : baseEnd_2104296 < baseStart_2104296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104346 : List Nat := [3, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2]
def baseStart_2104346 : Nat := 118140960795 + 2104346 * 2 ^ 59
def prefixEnd_2104346 : Nat := 4983230072969 + 3 ^ 40 * 2104346 * 2
def baseEnd_2104346 : Nat := 1080540961366328970297295

theorem tailTrace_2104346 : CollatzResearch.WordTrace tailWord_2104346 prefixEnd_2104346 1080540961366328970297295 := by
  unfold tailWord_2104346
  simp only [CollatzResearch.WordTrace]
  refine ⟨19187951008580327632279223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51167869356214207019411261 19187951008580327632279223)
  ·
    refine ⟨28781926512870491448418835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19187951008580327632279223 28781926512870491448418835)
    ·
      refine ⟨43172889769305737172628253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28781926512870491448418835 43172889769305737172628253)
      ·
        refine ⟨16189833663489651439735595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43172889769305737172628253 16189833663489651439735595)
        ·
          refine ⟨24284750495234477159603393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16189833663489651439735595 24284750495234477159603393)
          ·
            refine ⟨18213562871425857869702545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24284750495234477159603393 18213562871425857869702545)
            ·
              refine ⟨13660172153569393402276909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18213562871425857869702545 13660172153569393402276909)
              ·
                refine ⟨5122564557588522525853841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13660172153569393402276909 5122564557588522525853841)
                ·
                  refine ⟨3841923418191391894390381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5122564557588522525853841 3841923418191391894390381)
                  ·
                    refine ⟨1440721281821771960396393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3841923418191391894390381 1440721281821771960396393)
                    ·
                      refine ⟨1080540961366328970297295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1440721281821771960396393 1080540961366328970297295)
                      ·
                        rfl

theorem cell23_2104346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_2104346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104346 prefixEnd_2104346 := by exact prefixLift 2104346
  have htrace : WordTrace (prefixWord ++ tailWord_2104346) baseStart_2104346 baseEnd_2104346 := by
    simpa [prefixWord, tailWord_2104346, baseEnd_2104346] using wordTrace_append hprefix tailTrace_2104346
  have hstable : (prefixWord ++ tailWord_2104346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104346).length < 2 ^ (prefixWord ++ tailWord_2104346).sum := by decide
  have hdescent : baseEnd_2104346 < baseStart_2104346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104356 : List Nat := [2, 3, 1, 4, 1, 1, 2, 3, 1, 5]
def baseStart_2104356 : Nat := 118140960795 + 2104356 * 2 ^ 59
def prefixEnd_2104356 : Nat := 4983230072969 + 3 ^ 40 * 2104356 * 2
def baseEnd_2104356 : Nat := 360182032057624643724083

theorem tailTrace_2104356 : CollatzResearch.WordTrace tailWord_2104356 prefixEnd_2104356 360182032057624643724083 := by
  unfold tailWord_2104356
  simp only [CollatzResearch.WordTrace]
  refine ⟨38376084382142541118490461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51168112509523388157987281 38376084382142541118490461)
  ·
    refine ⟨14391031643303452919433923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38376084382142541118490461 14391031643303452919433923)
    ·
      refine ⟨21586547464955179379150885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14391031643303452919433923 21586547464955179379150885)
      ·
        refine ⟨4047477649679096133590791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21586547464955179379150885 4047477649679096133590791)
        ·
          refine ⟨6071216474518644200386187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4047477649679096133590791 6071216474518644200386187)
          ·
            refine ⟨9106824711777966300579281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6071216474518644200386187 9106824711777966300579281)
            ·
              refine ⟨6830118533833474725434461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9106824711777966300579281 6830118533833474725434461)
              ·
                refine ⟨2561294450187553022037923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6830118533833474725434461 2561294450187553022037923)
                ·
                  refine ⟨3841941675281329533056885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2561294450187553022037923 3841941675281329533056885)
                  ·
                    refine ⟨360182032057624643724083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3841941675281329533056885 360182032057624643724083)
                    ·
                      rfl

theorem cell23_2104356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_2104356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104356 prefixEnd_2104356 := by exact prefixLift 2104356
  have htrace : WordTrace (prefixWord ++ tailWord_2104356) baseStart_2104356 baseEnd_2104356 := by
    simpa [prefixWord, tailWord_2104356, baseEnd_2104356] using wordTrace_append hprefix tailTrace_2104356
  have hstable : (prefixWord ++ tailWord_2104356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104356).length < 2 ^ (prefixWord ++ tailWord_2104356).sum := by decide
  have hdescent : baseEnd_2104356 < baseStart_2104356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104369 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 4, 4]
def baseStart_2104369 : Nat := 118140960795 + 2104369 * 2 ^ 59
def prefixEnd_2104369 : Nat := 4983230072969 + 3 ^ 40 * 2104369 * 2
def baseEnd_2104369 : Nat := 360184257140460793436563

theorem tailTrace_2104369 : CollatzResearch.WordTrace tailWord_2104369 prefixEnd_2104369 360184257140460793436563 := by
  unfold tailWord_2104369
  simp only [CollatzResearch.WordTrace]
  refine ⟨76752642913237985457204161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51168428608825323638136107 76752642913237985457204161)
  ·
    refine ⟨57564482184928489092903121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76752642913237985457204161 57564482184928489092903121)
    ·
      refine ⟨43173361638696366819677341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57564482184928489092903121 43173361638696366819677341)
      ·
        refine ⟨16190010614511137557379003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43173361638696366819677341 16190010614511137557379003)
        ·
          refine ⟨24285015921766706336068505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16190010614511137557379003 24285015921766706336068505)
          ·
            refine ⟨18213761941325029752051379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24285015921766706336068505 18213761941325029752051379)
            ·
              refine ⟨27320642911987544628077069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18213761941325029752051379 27320642911987544628077069)
              ·
                refine ⟨10245241091995329235528901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27320642911987544628077069 10245241091995329235528901)
                ·
                  refine ⟨1920982704749124231661669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10245241091995329235528901 1920982704749124231661669)
                  ·
                    refine ⟨360184257140460793436563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1920982704749124231661669 360184257140460793436563)
                    ·
                      rfl

theorem cell23_2104369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 4].length) (baseStart_2104369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104369 prefixEnd_2104369 := by exact prefixLift 2104369
  have htrace : WordTrace (prefixWord ++ tailWord_2104369) baseStart_2104369 baseEnd_2104369 := by
    simpa [prefixWord, tailWord_2104369, baseEnd_2104369] using wordTrace_append hprefix tailTrace_2104369
  have hstable : (prefixWord ++ tailWord_2104369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104369).length < 2 ^ (prefixWord ++ tailWord_2104369).sum := by decide
  have hdescent : baseEnd_2104369 < baseStart_2104369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104370 : List Nat := [3, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3]
def baseStart_2104370 : Nat := 118140960795 + 2104370 * 2 ^ 59
def prefixEnd_2104370 : Nat := 4983230072969 + 3 ^ 40 * 2104370 * 2
def baseEnd_2104370 : Nat := 1080553284902036876397185

theorem tailTrace_2104370 : CollatzResearch.WordTrace tailWord_2104370 prefixEnd_2104370 1080553284902036876397185 := by
  unfold tailWord_2104370
  simp only [CollatzResearch.WordTrace]
  refine ⟨19188169846558590656997641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51168452924156241751993709 19188169846558590656997641)
  ·
    refine ⟨14391127384918942992748231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19188169846558590656997641 14391127384918942992748231)
    ·
      refine ⟨21586691077378414489122347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14391127384918942992748231 21586691077378414489122347)
      ·
        refine ⟨32380036616067621733683521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21586691077378414489122347 32380036616067621733683521)
        ·
          refine ⟨24285027462050716300262641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32380036616067621733683521 24285027462050716300262641)
          ·
            refine ⟨18213770596538037225196981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24285027462050716300262641 18213770596538037225196981)
            ·
              refine ⟨1707540993425440989862217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18213770596538037225196981 1707540993425440989862217)
              ·
                refine ⟨1280655745069080742396663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1707540993425440989862217 1280655745069080742396663)
                ·
                  refine ⟨1920983617603621113594995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1280655745069080742396663 1920983617603621113594995)
                  ·
                    refine ⟨2881475426405431670392493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1920983617603621113594995 2881475426405431670392493)
                    ·
                      refine ⟨1080553284902036876397185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2881475426405431670392493 1080553284902036876397185)
                      ·
                        rfl

theorem cell23_2104370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3].length) (baseStart_2104370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104370 prefixEnd_2104370 := by exact prefixLift 2104370
  have htrace : WordTrace (prefixWord ++ tailWord_2104370) baseStart_2104370 baseEnd_2104370 := by
    simpa [prefixWord, tailWord_2104370, baseEnd_2104370] using wordTrace_append hprefix tailTrace_2104370
  have hstable : (prefixWord ++ tailWord_2104370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104370).length < 2 ^ (prefixWord ++ tailWord_2104370).sum := by decide
  have hdescent : baseEnd_2104370 < baseStart_2104370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104390 : List Nat := [6, 1, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_2104390 : Nat := 118140960795 + 2104390 * 2 ^ 59
def prefixEnd_2104390 : Nat := 4983230072969 + 3 ^ 40 * 2104390 * 2
def baseEnd_2104390 : Nat := 360187851505042266049031

theorem tailTrace_2104390 : CollatzResearch.WordTrace tailWord_2104390 prefixEnd_2104390 360187851505042266049031 := by
  unfold tailWord_2104390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2398544026442559563866207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51168939230774604029145749 2398544026442559563866207)
  ·
    refine ⟨3597816039663839345799311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2398544026442559563866207 3597816039663839345799311)
    ·
      refine ⟨5396724059495759018698967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3597816039663839345799311 5396724059495759018698967)
      ·
        refine ⟨8095086089243638528048451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5396724059495759018698967 8095086089243638528048451)
        ·
          refine ⟨12142629133865457792072677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8095086089243638528048451 12142629133865457792072677)
          ·
            refine ⟨2276742962599773336013627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12142629133865457792072677 2276742962599773336013627)
            ·
              refine ⟨3415114443899660004020441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2276742962599773336013627 3415114443899660004020441)
              ·
                refine ⟨2561335832924745003015331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3415114443899660004020441 2561335832924745003015331)
                ·
                  refine ⟨3842003749387117504522997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2561335832924745003015331 3842003749387117504522997)
                  ·
                    refine ⟨360187851505042266049031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3842003749387117504522997 360187851505042266049031)
                    ·
                      rfl

theorem cell23_2104390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_2104390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104390 prefixEnd_2104390 := by exact prefixLift 2104390
  have htrace : WordTrace (prefixWord ++ tailWord_2104390) baseStart_2104390 baseEnd_2104390 := by
    simpa [prefixWord, tailWord_2104390, baseEnd_2104390] using wordTrace_append hprefix tailTrace_2104390
  have hstable : (prefixWord ++ tailWord_2104390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104390).length < 2 ^ (prefixWord ++ tailWord_2104390).sum := by decide
  have hdescent : baseEnd_2104390 < baseStart_2104390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104429 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 2, 7]
def baseStart_2104429 : Nat := 118140960795 + 2104429 * 2 ^ 59
def prefixEnd_2104429 : Nat := 4983230072969 + 3 ^ 40 * 2104429 * 2
def baseEnd_2104429 : Nat := 360194526753550715186471

theorem tailTrace_2104429 : CollatzResearch.WordTrace tailWord_2104429 prefixEnd_2104429 360194526753550715186471 := by
  unfold tailWord_2104429
  simp only [CollatzResearch.WordTrace]
  refine ⟨76754831293020615704388341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51169887528680410469592227 76754831293020615704388341)
  ·
    refine ⟨7195765433720682722286407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76754831293020615704388341 7195765433720682722286407)
    ·
      refine ⟨10793648150581024083429611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7195765433720682722286407 10793648150581024083429611)
      ·
        refine ⟨16190472225871536125144417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10793648150581024083429611 16190472225871536125144417)
        ·
          refine ⟨12142854169403652093858313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16190472225871536125144417 12142854169403652093858313)
          ·
            refine ⟨9107140627052739070393735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12142854169403652093858313 9107140627052739070393735)
            ·
              refine ⟨13660710940579108605590603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9107140627052739070393735 13660710940579108605590603)
              ·
                refine ⟨20491066410868662908385905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13660710940579108605590603 20491066410868662908385905)
                ·
                  refine ⟨15368299808151497181289429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20491066410868662908385905 15368299808151497181289429)
                  ·
                    refine ⟨360194526753550715186471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15368299808151497181289429 360194526753550715186471)
                    ·
                      rfl

theorem cell23_2104429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_2104429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104429 prefixEnd_2104429 := by exact prefixLift 2104429
  have htrace : WordTrace (prefixWord ++ tailWord_2104429) baseStart_2104429 baseEnd_2104429 := by
    simpa [prefixWord, tailWord_2104429, baseEnd_2104429] using wordTrace_append hprefix tailTrace_2104429
  have hstable : (prefixWord ++ tailWord_2104429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104429).length < 2 ^ (prefixWord ++ tailWord_2104429).sum := by decide
  have hdescent : baseEnd_2104429 < baseStart_2104429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104469 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 1, 6, 3]
def baseStart_2104469 : Nat := 118140960795 + 2104469 * 2 ^ 59
def prefixEnd_2104469 : Nat := 4983230072969 + 3 ^ 40 * 2104469 * 2
def baseEnd_2104469 : Nat := 1080604119486831989059229

theorem tailTrace_2104469 : CollatzResearch.WordTrace tailWord_2104469 prefixEnd_2104469 1080604119486831989059229 := by
  unfold tailWord_2104469
  simp only [CollatzResearch.WordTrace]
  refine ⟨76756290212875702535844461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51170860141917135023896307 76756290212875702535844461)
  ·
    refine ⟨28783608829828388450941673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76756290212875702535844461 28783608829828388450941673)
    ·
      refine ⟨21587706622371291338206255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28783608829828388450941673 21587706622371291338206255)
      ·
        refine ⟨32381559933556937007309383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21587706622371291338206255 32381559933556937007309383)
        ·
          refine ⟨48572339900335405510964075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32381559933556937007309383 48572339900335405510964075)
          ·
            refine ⟨72858509850503108266446113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48572339900335405510964075 72858509850503108266446113)
            ·
              refine ⟨54643882387877331199834585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72858509850503108266446113 54643882387877331199834585)
              ·
                refine ⟨40982911790907998399875939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54643882387877331199834585 40982911790907998399875939)
                ·
                  refine ⟨61474367686361997599813909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40982911790907998399875939 61474367686361997599813909)
                  ·
                    refine ⟨2881610985298218637491277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61474367686361997599813909 2881610985298218637491277)
                    ·
                      refine ⟨1080604119486831989059229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2881610985298218637491277 1080604119486831989059229)
                      ·
                        rfl

theorem cell23_2104469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_2104469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104469 prefixEnd_2104469 := by exact prefixLift 2104469
  have htrace : WordTrace (prefixWord ++ tailWord_2104469) baseStart_2104469 baseEnd_2104469 := by
    simpa [prefixWord, tailWord_2104469, baseEnd_2104469] using wordTrace_append hprefix tailTrace_2104469
  have hstable : (prefixWord ++ tailWord_2104469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104469).length < 2 ^ (prefixWord ++ tailWord_2104469).sum := by decide
  have hdescent : baseEnd_2104469 < baseStart_2104469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104519 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 6, 5]
def baseStart_2104519 : Nat := 118140960795 + 2104519 * 2 ^ 59
def prefixEnd_2104519 : Nat := 4983230072969 + 3 ^ 40 * 2104519 * 2
def baseEnd_2104519 : Nat := 360209931173185597811333

theorem tailTrace_2104519 : CollatzResearch.WordTrace tailWord_2104519 prefixEnd_2104519 360209931173185597811333 := by
  unfold tailWord_2104519
  simp only [CollatzResearch.WordTrace]
  refine ⟨76758113862694561075164611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51172075908463040716776407 76758113862694561075164611)
  ·
    refine ⟨115137170794041841612746917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76758113862694561075164611 115137170794041841612746917)
    ·
      refine ⟨21588219523882845302390047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115137170794041841612746917 21588219523882845302390047)
      ·
        refine ⟨32382329285824267953585071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21588219523882845302390047 32382329285824267953585071)
        ·
          refine ⟨48573493928736401930377607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32382329285824267953585071 48573493928736401930377607)
          ·
            refine ⟨72860240893104602895566411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48573493928736401930377607 72860240893104602895566411)
            ·
              refine ⟨109290361339656904343349617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72860240893104602895566411 109290361339656904343349617)
              ·
                refine ⟨81967771004742678257512213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109290361339656904343349617 81967771004742678257512213)
                ·
                  refine ⟨3842239265847313043320885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81967771004742678257512213 3842239265847313043320885)
                  ·
                    refine ⟨360209931173185597811333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3842239265847313043320885 360209931173185597811333)
                    ·
                      rfl

theorem cell23_2104519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_2104519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104519 prefixEnd_2104519 := by exact prefixLift 2104519
  have htrace : WordTrace (prefixWord ++ tailWord_2104519) baseStart_2104519 baseEnd_2104519 := by
    simpa [prefixWord, tailWord_2104519, baseEnd_2104519] using wordTrace_append hprefix tailTrace_2104519
  have hstable : (prefixWord ++ tailWord_2104519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104519).length < 2 ^ (prefixWord ++ tailWord_2104519).sum := by decide
  have hdescent : baseEnd_2104519 < baseStart_2104519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104529 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 1, 2, 5]
def baseStart_2104529 : Nat := 118140960795 + 2104529 * 2 ^ 59
def prefixEnd_2104529 : Nat := 4983230072969 + 3 ^ 40 * 2104529 * 2
def baseEnd_2104529 : Nat := 1080634928326101754308953

theorem tailTrace_2104529 : CollatzResearch.WordTrace tailWord_2104529 prefixEnd_2104529 1080634928326101754308953 := by
  unfold tailWord_2104529
  simp only [CollatzResearch.WordTrace]
  refine ⟨76758478592658332783028641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51172319061772221855352427 76758478592658332783028641)
  ·
    refine ⟨57568858944493749587271481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76758478592658332783028641 57568858944493749587271481)
    ·
      refine ⟨43176644208370312190453611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57568858944493749587271481 43176644208370312190453611)
      ·
        refine ⟨64764966312555468285680417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43176644208370312190453611 64764966312555468285680417)
        ·
          refine ⟨48573724734416601214260313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64764966312555468285680417 48573724734416601214260313)
          ·
            refine ⟨36430293550812450910695235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48573724734416601214260313 36430293550812450910695235)
            ·
              refine ⟨54645440326218676366042853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36430293550812450910695235 54645440326218676366042853)
              ·
                refine ⟨10246020061166001818633035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54645440326218676366042853 10246020061166001818633035)
                ·
                  refine ⟨15369030091749002727949553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10246020061166001818633035 15369030091749002727949553)
                  ·
                    refine ⟨11526772568811752045962165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15369030091749002727949553 11526772568811752045962165)
                    ·
                      refine ⟨1080634928326101754308953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11526772568811752045962165 1080634928326101754308953)
                      ·
                        rfl

theorem cell23_2104529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_2104529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104529 prefixEnd_2104529 := by exact prefixLift 2104529
  have htrace : WordTrace (prefixWord ++ tailWord_2104529) baseStart_2104529 baseEnd_2104529 := by
    simpa [prefixWord, tailWord_2104529, baseEnd_2104529] using wordTrace_append hprefix tailTrace_2104529
  have hstable : (prefixWord ++ tailWord_2104529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104529).length < 2 ^ (prefixWord ++ tailWord_2104529).sum := by decide
  have hdescent : baseEnd_2104529 < baseStart_2104529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104551 : List Nat := [1, 1, 5, 3, 3, 1, 2, 1, 2, 2, 2]
def baseStart_2104551 : Nat := 118140960795 + 2104551 * 2 ^ 59
def prefixEnd_2104551 : Nat := 4983230072969 + 3 ^ 40 * 2104551 * 2
def baseEnd_2104551 : Nat := 1080646224900500668233853

theorem tailTrace_2104551 : CollatzResearch.WordTrace tailWord_2104551 prefixEnd_2104551 1080646224900500668233853 := by
  unfold tailWord_2104551
  simp only [CollatzResearch.WordTrace]
  refine ⟨76759280998578630540329507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51172853999052420360219671 76759280998578630540329507)
  ·
    refine ⟨115138921497867945810494261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76759280998578630540329507 115138921497867945810494261)
    ·
      refine ⟨10794273890425119919733837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115138921497867945810494261 10794273890425119919733837)
      ·
        refine ⟨4047852708909419969900189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10794273890425119919733837 4047852708909419969900189)
        ·
          refine ⟨1517944765841032488712571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4047852708909419969900189 1517944765841032488712571)
          ·
            refine ⟨2276917148761548733068857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1517944765841032488712571 2276917148761548733068857)
            ·
              refine ⟨1707687861571161549801643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2276917148761548733068857 1707687861571161549801643)
              ·
                refine ⟨2561531792356742324702465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1707687861571161549801643 2561531792356742324702465)
                ·
                  refine ⟨1921148844267556743526849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2561531792356742324702465 1921148844267556743526849)
                  ·
                    refine ⟨1440861633200667557645137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1921148844267556743526849 1440861633200667557645137)
                    ·
                      refine ⟨1080646224900500668233853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1440861633200667557645137 1080646224900500668233853)
                      ·
                        rfl

theorem cell23_2104551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_2104551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104551 prefixEnd_2104551 := by exact prefixLift 2104551
  have htrace : WordTrace (prefixWord ++ tailWord_2104551) baseStart_2104551 baseEnd_2104551 := by
    simpa [prefixWord, tailWord_2104551, baseEnd_2104551] using wordTrace_append hprefix tailTrace_2104551
  have hstable : (prefixWord ++ tailWord_2104551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104551).length < 2 ^ (prefixWord ++ tailWord_2104551).sum := by decide
  have hdescent : baseEnd_2104551 < baseStart_2104551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104600 : List Nat := [2, 1, 2, 3, 1, 4, 1, 4, 1, 4]
def baseStart_2104600 : Nat := 118140960795 + 2104600 * 2 ^ 59
def prefixEnd_2104600 : Nat := 4983230072969 + 3 ^ 40 * 2104600 * 2
def baseEnd_2104600 : Nat := 360223795150856992173709

theorem tailTrace_2104600 : CollatzResearch.WordTrace tailWord_2104600 prefixEnd_2104600 360223795150856992173709 := by
  unfold tailWord_2104600
  simp only [CollatzResearch.WordTrace]
  refine ⟨38380534087700555954431627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51174045450267407939242169 38380534087700555954431627)
  ·
    refine ⟨57570801131550833931647441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38380534087700555954431627 57570801131550833931647441)
    ·
      refine ⟨43178100848663125448735581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57570801131550833931647441 43178100848663125448735581)
      ·
        refine ⟨16191787818248672043275843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43178100848663125448735581 16191787818248672043275843)
        ·
          refine ⟨24287681727373008064913765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16191787818248672043275843 24287681727373008064913765)
          ·
            refine ⟨4553940323882439012171331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24287681727373008064913765 4553940323882439012171331)
            ·
              refine ⟨6830910485823658518256997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4553940323882439012171331 6830910485823658518256997)
              ·
                refine ⟨1280795716091935972173187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6830910485823658518256997 1280795716091935972173187)
                ·
                  refine ⟨1921193574137903958259781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1280795716091935972173187 1921193574137903958259781)
                  ·
                    refine ⟨360223795150856992173709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1921193574137903958259781 360223795150856992173709)
                    ·
                      rfl

theorem cell23_2104600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 1, 4].length) (baseStart_2104600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104600 prefixEnd_2104600 := by exact prefixLift 2104600
  have htrace : WordTrace (prefixWord ++ tailWord_2104600) baseStart_2104600 baseEnd_2104600 := by
    simpa [prefixWord, tailWord_2104600, baseEnd_2104600] using wordTrace_append hprefix tailTrace_2104600
  have hstable : (prefixWord ++ tailWord_2104600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104600).length < 2 ^ (prefixWord ++ tailWord_2104600).sum := by decide
  have hdescent : baseEnd_2104600 < baseStart_2104600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104666 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5]
def baseStart_2104666 : Nat := 118140960795 + 2104666 * 2 ^ 59
def prefixEnd_2104666 : Nat := 4983230072969 + 3 ^ 40 * 2104666 * 2
def baseEnd_2104666 : Nat := 1080705275175767718295823

theorem tailTrace_2104666 : CollatzResearch.WordTrace tailWord_2104666 prefixEnd_2104666 1080705275175767718295823 := by
  unfold tailWord_2104666
  simp only [CollatzResearch.WordTrace]
  refine ⟨19190868848290501295191463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51175650262108003453843901 19190868848290501295191463)
  ·
    refine ⟨28786303272435751942787195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19190868848290501295191463 28786303272435751942787195)
    ·
      refine ⟨43179454908653627914180793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28786303272435751942787195 43179454908653627914180793)
      ·
        refine ⟨32384591181490220935635595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43179454908653627914180793 32384591181490220935635595)
        ·
          refine ⟨48576886772235331403453393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32384591181490220935635595 48576886772235331403453393)
          ·
            refine ⟨36432665079176498552590045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48576886772235331403453393 36432665079176498552590045)
            ·
              refine ⟨13662249404691186957221267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36432665079176498552590045 13662249404691186957221267)
              ·
                refine ⟨20493374107036780435831901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13662249404691186957221267 20493374107036780435831901)
                ·
                  refine ⟨7685015290138792663436963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20493374107036780435831901 7685015290138792663436963)
                  ·
                    refine ⟨11527522935208188995155445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7685015290138792663436963 11527522935208188995155445)
                    ·
                      refine ⟨1080705275175767718295823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11527522935208188995155445 1080705275175767718295823)
                      ·
                        rfl

theorem cell23_2104666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_2104666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104666 prefixEnd_2104666 := by exact prefixLift 2104666
  have htrace : WordTrace (prefixWord ++ tailWord_2104666) baseStart_2104666 baseEnd_2104666 := by
    simpa [prefixWord, tailWord_2104666, baseEnd_2104666] using wordTrace_append hprefix tailTrace_2104666
  have hstable : (prefixWord ++ tailWord_2104666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104666).length < 2 ^ (prefixWord ++ tailWord_2104666).sum := by decide
  have hdescent : baseEnd_2104666 < baseStart_2104666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104673 : List Nat := [1, 2, 3, 1, 1, 1, 1, 7, 2, 4]
def baseStart_2104673 : Nat := 118140960795 + 2104673 * 2 ^ 59
def prefixEnd_2104673 : Nat := 4983230072969 + 3 ^ 40 * 2104673 * 2
def baseEnd_2104673 : Nat := 360236289846783063636097

theorem tailTrace_2104673 : CollatzResearch.WordTrace tailWord_2104673 prefixEnd_2104673 360236289846783063636097 := by
  unfold tailWord_2104673
  simp only [CollatzResearch.WordTrace]
  refine ⟨76763730704136645376270673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51175820469424430250847115 76763730704136645376270673)
  ·
    refine ⟨57572798028102484032203005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76763730704136645376270673 57572798028102484032203005)
    ·
      refine ⟨21589799260538431512076127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57572798028102484032203005 21589799260538431512076127)
      ·
        refine ⟨32384698890807647268114191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21589799260538431512076127 32384698890807647268114191)
        ·
          refine ⟨48577048336211470902171287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32384698890807647268114191 48577048336211470902171287)
          ·
            refine ⟨72865572504317206353256931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48577048336211470902171287 72865572504317206353256931)
            ·
              refine ⟨109298358756475809529885397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72865572504317206353256931 109298358756475809529885397)
              ·
                refine ⟨2561680283354901785856689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 109298358756475809529885397 2561680283354901785856689)
                ·
                  refine ⟨1921260212516176339392517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2561680283354901785856689 1921260212516176339392517)
                  ·
                    refine ⟨360236289846783063636097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1921260212516176339392517 360236289846783063636097)
                    ·
                      rfl

theorem cell23_2104673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_2104673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104673 prefixEnd_2104673 := by exact prefixLift 2104673
  have htrace : WordTrace (prefixWord ++ tailWord_2104673) baseStart_2104673 baseEnd_2104673 := by
    simpa [prefixWord, tailWord_2104673, baseEnd_2104673] using wordTrace_append hprefix tailTrace_2104673
  have hstable : (prefixWord ++ tailWord_2104673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104673).length < 2 ^ (prefixWord ++ tailWord_2104673).sum := by decide
  have hdescent : baseEnd_2104673 < baseStart_2104673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104716 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 2, 7]
def baseStart_2104716 : Nat := 118140960795 + 2104716 * 2 ^ 59
def prefixEnd_2104716 : Nat := 4983230072969 + 3 ^ 40 * 2104716 * 2
def baseEnd_2104716 : Nat := 360243649736164174223531

theorem tailTrace_2104716 : CollatzResearch.WordTrace tailWord_2104716 prefixEnd_2104716 360243649736164174223531 := by
  unfold tailWord_2104716
  simp only [CollatzResearch.WordTrace]
  refine ⟨38382649521490431860043001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51176866028653909146724001 38382649521490431860043001)
  ·
    refine ⟨28786987141117823895032251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38382649521490431860043001 28786987141117823895032251)
    ·
      refine ⟨43180480711676735842548377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28786987141117823895032251 43180480711676735842548377)
      ·
        refine ⟨32385360533757551881911283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43180480711676735842548377 32385360533757551881911283)
        ·
          refine ⟨48578040800636327822866925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32385360533757551881911283 48578040800636327822866925)
          ·
            refine ⟨18216765300238622933575097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48578040800636327822866925 18216765300238622933575097)
            ·
              refine ⟨13662573975178967200181323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18216765300238622933575097 13662573975178967200181323)
              ·
                refine ⟨20493860962768450800271985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13662573975178967200181323 20493860962768450800271985)
                ·
                  refine ⟨15370395722076338100203989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20493860962768450800271985 15370395722076338100203989)
                  ·
                    refine ⟨360243649736164174223531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15370395722076338100203989 360243649736164174223531)
                    ·
                      rfl

theorem cell23_2104716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_2104716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104716 prefixEnd_2104716 := by exact prefixLift 2104716
  have htrace : WordTrace (prefixWord ++ tailWord_2104716) baseStart_2104716 baseEnd_2104716 := by
    simpa [prefixWord, tailWord_2104716, baseEnd_2104716] using wordTrace_append hprefix tailTrace_2104716
  have hstable : (prefixWord ++ tailWord_2104716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104716).length < 2 ^ (prefixWord ++ tailWord_2104716).sum := by decide
  have hdescent : baseEnd_2104716 < baseStart_2104716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104724 : List Nat := [2, 4, 2, 1, 2, 3, 2, 1, 2, 4]
def baseStart_2104724 : Nat := 118140960795 + 2104724 * 2 ^ 59
def prefixEnd_2104724 : Nat := 4983230072969 + 3 ^ 40 * 2104724 * 2
def baseEnd_2104724 : Nat := 360245019017909497123519

theorem tailTrace_2104724 : CollatzResearch.WordTrace tailWord_2104724 prefixEnd_2104724 360245019017909497123519 := by
  unfold tailWord_2104724
  simp only [CollatzResearch.WordTrace]
  refine ⟨38382795413475940543188613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51177060551301254057584817 38382795413475940543188613)
  ·
    refine ⟨7196774140026738851847865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38382795413475940543188613 7196774140026738851847865)
    ·
      refine ⟨5397580605020054138885899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7196774140026738851847865 5397580605020054138885899)
      ·
        refine ⟨8096370907530081208328849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5397580605020054138885899 8096370907530081208328849)
        ·
          refine ⟨6072278180647560906246637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8096370907530081208328849 6072278180647560906246637)
          ·
            refine ⟨2277104317742835339842489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6072278180647560906246637 2277104317742835339842489)
            ·
              refine ⟨1707828238307126504881867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2277104317742835339842489 1707828238307126504881867)
              ·
                refine ⟨2561742357460689757322801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1707828238307126504881867 2561742357460689757322801)
                ·
                  refine ⟨1921306768095517317992101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2561742357460689757322801 1921306768095517317992101)
                  ·
                    refine ⟨360245019017909497123519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1921306768095517317992101 360245019017909497123519)
                    ·
                      rfl

theorem cell23_2104724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_2104724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104724 prefixEnd_2104724 := by exact prefixLift 2104724
  have htrace : WordTrace (prefixWord ++ tailWord_2104724) baseStart_2104724 baseEnd_2104724 := by
    simpa [prefixWord, tailWord_2104724, baseEnd_2104724] using wordTrace_append hprefix tailTrace_2104724
  have hstable : (prefixWord ++ tailWord_2104724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104724).length < 2 ^ (prefixWord ++ tailWord_2104724).sum := by decide
  have hdescent : baseEnd_2104724 < baseStart_2104724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104764 : List Nat := [2, 2, 2, 4, 2, 1, 2, 2, 2, 1, 3]
def baseStart_2104764 : Nat := 118140960795 + 2104764 * 2 ^ 59
def prefixEnd_2104764 : Nat := 4983230072969 + 3 ^ 40 * 2104764 * 2
def baseEnd_2104764 : Nat := 1080755596279908334870373

theorem tailTrace_2104764 : CollatzResearch.WordTrace tailWord_2104764 prefixEnd_2104764 1080755596279908334870373 := by
  unfold tailWord_2104764
  simp only [CollatzResearch.WordTrace]
  refine ⟨38383524873403483958916673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51178033164537978611888897 38383524873403483958916673)
  ·
    refine ⟨28787643655052612969187505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38383524873403483958916673 28787643655052612969187505)
    ·
      refine ⟨21590732741289459726890629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28787643655052612969187505 21590732741289459726890629)
      ·
        refine ⟨4048262388991773698791993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21590732741289459726890629 4048262388991773698791993)
        ·
          refine ⟨3036196791743830274093995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4048262388991773698791993 3036196791743830274093995)
          ·
            refine ⟨4554295187615745411140993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3036196791743830274093995 4554295187615745411140993)
            ·
              refine ⟨3415721390711809058355745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4554295187615745411140993 3415721390711809058355745)
              ·
                refine ⟨2561791043033856793766809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3415721390711809058355745 2561791043033856793766809)
                ·
                  refine ⟨1921343282275392595325107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2561791043033856793766809 1921343282275392595325107)
                  ·
                    refine ⟨2882014923413088892987661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1921343282275392595325107 2882014923413088892987661)
                    ·
                      refine ⟨1080755596279908334870373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2882014923413088892987661 1080755596279908334870373)
                      ·
                        rfl

theorem cell23_2104764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_2104764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104764 prefixEnd_2104764 := by exact prefixLift 2104764
  have htrace : WordTrace (prefixWord ++ tailWord_2104764) baseStart_2104764 baseEnd_2104764 := by
    simpa [prefixWord, tailWord_2104764, baseEnd_2104764] using wordTrace_append hprefix tailTrace_2104764
  have hstable : (prefixWord ++ tailWord_2104764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104764).length < 2 ^ (prefixWord ++ tailWord_2104764).sum := by decide
  have hdescent : baseEnd_2104764 < baseStart_2104764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104793 : List Nat := [1, 2, 1, 2, 4, 3, 1, 2, 7]
def baseStart_2104793 : Nat := 118140960795 + 2104793 * 2 ^ 59
def prefixEnd_2104793 : Nat := 4983230072969 + 3 ^ 40 * 2104793 * 2
def baseEnd_2104793 : Nat := 120085609690987635711971

theorem tailTrace_2104793 : CollatzResearch.WordTrace tailWord_2104793 prefixEnd_2104793 120085609690987635711971 := by
  unfold tailWord_2104793
  simp only [CollatzResearch.WordTrace]
  refine ⟨76768107463701905870639033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51178738309134603913759355 76768107463701905870639033)
  ·
    refine ⟨57576080597776429402979275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76768107463701905870639033 57576080597776429402979275)
    ·
      refine ⟨86364120896664644104468913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57576080597776429402979275 86364120896664644104468913)
      ·
        refine ⟨64773090672498483078351685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86364120896664644104468913 64773090672498483078351685)
        ·
          refine ⟨12144954501093465577190941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64773090672498483078351685 12144954501093465577190941)
          ·
            refine ⟨4554357937910049591446603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12144954501093465577190941 4554357937910049591446603)
            ·
              refine ⟨6831536906865074387169905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4554357937910049591446603 6831536906865074387169905)
              ·
                refine ⟨5123652680148805790377429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6831536906865074387169905 5123652680148805790377429)
                ·
                  refine ⟨120085609690987635711971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5123652680148805790377429 120085609690987635711971)
                  ·
                    rfl

theorem cell23_2104793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 7].length) (baseStart_2104793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104793 prefixEnd_2104793 := by exact prefixLift 2104793
  have htrace : WordTrace (prefixWord ++ tailWord_2104793) baseStart_2104793 baseEnd_2104793 := by
    simpa [prefixWord, tailWord_2104793, baseEnd_2104793] using wordTrace_append hprefix tailTrace_2104793
  have hstable : (prefixWord ++ tailWord_2104793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104793).length < 2 ^ (prefixWord ++ tailWord_2104793).sum := by decide
  have hdescent : baseEnd_2104793 < baseStart_2104793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104821 : List Nat := [1, 3, 5, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_2104821 : Nat := 118140960795 + 2104821 * 2 ^ 59
def prefixEnd_2104821 : Nat := 4983230072969 + 3 ^ 40 * 2104821 * 2
def baseEnd_2104821 : Nat := 1080784864677214611857611

theorem tailTrace_2104821 : CollatzResearch.WordTrace tailWord_2104821 prefixEnd_2104821 1080784864677214611857611 := by
  unfold tailWord_2104821
  simp only [CollatzResearch.WordTrace]
  refine ⟨76769128707600466652658317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51179419138400311101772211 76769128707600466652658317)
  ·
    refine ⟨28788423265350174994746869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76769128707600466652658317 28788423265350174994746869)
    ·
      refine ⟨2698914681126578905757519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28788423265350174994746869 2698914681126578905757519)
      ·
        refine ⟨4048372021689868358636279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2698914681126578905757519 4048372021689868358636279)
        ·
          refine ⟨6072558032534802537954419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4048372021689868358636279 6072558032534802537954419)
          ·
            refine ⟨9108837048802203806931629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6072558032534802537954419 9108837048802203806931629)
            ·
              refine ⟨3415813893300826427599361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9108837048802203806931629 3415813893300826427599361)
              ·
                refine ⟨2561860419975619820699521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3415813893300826427599361 2561860419975619820699521)
                ·
                  refine ⟨1921395314981714865524641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2561860419975619820699521 1921395314981714865524641)
                  ·
                    refine ⟨1441046486236286149143481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1921395314981714865524641 1441046486236286149143481)
                    ·
                      refine ⟨1080784864677214611857611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1441046486236286149143481 1080784864677214611857611)
                      ·
                        rfl

theorem cell23_2104821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_2104821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104821 prefixEnd_2104821 := by exact prefixLift 2104821
  have htrace : WordTrace (prefixWord ++ tailWord_2104821) baseStart_2104821 baseEnd_2104821 := by
    simpa [prefixWord, tailWord_2104821, baseEnd_2104821] using wordTrace_append hprefix tailTrace_2104821
  have hstable : (prefixWord ++ tailWord_2104821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104821).length < 2 ^ (prefixWord ++ tailWord_2104821).sum := by decide
  have hdescent : baseEnd_2104821 < baseStart_2104821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104860 : List Nat := [2, 2, 3, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_2104860 : Nat := 118140960795 + 2104860 * 2 ^ 59
def prefixEnd_2104860 : Nat := 4983230072969 + 3 ^ 40 * 2104860 * 2
def baseEnd_2104860 : Nat := 1080804890422739959269931

theorem tailTrace_2104860 : CollatzResearch.WordTrace tailWord_2104860 prefixEnd_2104860 1080804890422739959269931 := by
  unfold tailWord_2104860
  simp only [CollatzResearch.WordTrace]
  refine ⟨38385275577229588156664017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51180367436306117542218689 38385275577229588156664017)
  ·
    refine ⟨28788956682922191117498013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38385275577229588156664017 28788956682922191117498013)
    ·
      refine ⟨10795858756095821669061755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28788956682922191117498013 10795858756095821669061755)
      ·
        refine ⟨16193788134143732503592633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10795858756095821669061755 16193788134143732503592633)
        ·
          refine ⟨12145341100607799377694475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16193788134143732503592633 12145341100607799377694475)
          ·
            refine ⟨18218011650911699066541713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12145341100607799377694475 18218011650911699066541713)
            ·
              refine ⟨13663508738183774299906285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18218011650911699066541713 13663508738183774299906285)
              ·
                refine ⟨5123815776818915362464857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13663508738183774299906285 5123815776818915362464857)
                ·
                  refine ⟨3842861832614186521848643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5123815776818915362464857 3842861832614186521848643)
                  ·
                    refine ⟨5764292748921279782772965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3842861832614186521848643 5764292748921279782772965)
                    ·
                      refine ⟨1080804890422739959269931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5764292748921279782772965 1080804890422739959269931)
                      ·
                        rfl

theorem cell23_2104860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_2104860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104860 prefixEnd_2104860 := by exact prefixLift 2104860
  have htrace : WordTrace (prefixWord ++ tailWord_2104860) baseStart_2104860 baseEnd_2104860 := by
    simpa [prefixWord, tailWord_2104860, baseEnd_2104860] using wordTrace_append hprefix tailTrace_2104860
  have hstable : (prefixWord ++ tailWord_2104860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104860).length < 2 ^ (prefixWord ++ tailWord_2104860).sum := by decide
  have hdescent : baseEnd_2104860 < baseStart_2104860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104883 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 8]
def baseStart_2104883 : Nat := 118140960795 + 2104883 * 2 ^ 59
def prefixEnd_2104883 : Nat := 4983230072969 + 3 ^ 40 * 2104883 * 2
def baseEnd_2104883 : Nat := 120090744497532596586925

theorem tailTrace_2104883 : CollatzResearch.WordTrace tailWord_2104883 prefixEnd_2104883 120090744497532596586925 := by
  unfold tailWord_2104883
  simp only [CollatzResearch.WordTrace]
  refine ⟨76771390033375851241415303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51180926688917234160943535 76771390033375851241415303)
  ·
    refine ⟨115157085050063776862122955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76771390033375851241415303 115157085050063776862122955)
    ·
      refine ⟨172735627575095665293184433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115157085050063776862122955 172735627575095665293184433)
      ·
        refine ⟨129551720681321748969888325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172735627575095665293184433 129551720681321748969888325)
        ·
          refine ⟨24290947627747827931854061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129551720681321748969888325 24290947627747827931854061)
          ·
            refine ⟨9109105360405435474445273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24290947627747827931854061 9109105360405435474445273)
            ·
              refine ⟨6831829020304076605833955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9109105360405435474445273 6831829020304076605833955)
              ·
                refine ⟨10247743530456114908750933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6831829020304076605833955 10247743530456114908750933)
                ·
                  refine ⟨120090744497532596586925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10247743530456114908750933 120090744497532596586925)
                  ·
                    rfl

theorem cell23_2104883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 8].length) (baseStart_2104883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104883 prefixEnd_2104883 := by exact prefixLift 2104883
  have htrace : WordTrace (prefixWord ++ tailWord_2104883) baseStart_2104883 baseEnd_2104883 := by
    simpa [prefixWord, tailWord_2104883, baseEnd_2104883] using wordTrace_append hprefix tailTrace_2104883
  have hstable : (prefixWord ++ tailWord_2104883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104883).length < 2 ^ (prefixWord ++ tailWord_2104883).sum := by decide
  have hdescent : baseEnd_2104883 < baseStart_2104883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104887 : List Nat := [1, 1, 3, 1, 2, 6, 1, 1, 3, 4]
def baseStart_2104887 : Nat := 118140960795 + 2104887 * 2 ^ 59
def prefixEnd_2104887 : Nat := 4983230072969 + 3 ^ 40 * 2104887 * 2
def baseEnd_2104887 : Nat := 360272918133470451210769

theorem tailTrace_2104887 : CollatzResearch.WordTrace tailWord_2104887 prefixEnd_2104887 360272918133470451210769 := by
  unfold tailWord_2104887
  simp only [CollatzResearch.WordTrace]
  refine ⟨76771535925361359924560915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51181023950240906616373943 76771535925361359924560915)
  ·
    refine ⟨115157303888042039886841373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76771535925361359924560915 115157303888042039886841373)
    ·
      refine ⟨43183988958015764957565515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115157303888042039886841373 43183988958015764957565515)
      ·
        refine ⟨64775983437023647436348273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43183988958015764957565515 64775983437023647436348273)
        ·
          refine ⟨48581987577767735577261205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64775983437023647436348273 48581987577767735577261205)
          ·
            refine ⟨2277280667707862605184119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48581987577767735577261205 2277280667707862605184119)
            ·
              refine ⟨3415921001561793907776179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2277280667707862605184119 3415921001561793907776179)
              ·
                refine ⟨5123881502342690861664269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3415921001561793907776179 5123881502342690861664269)
                ·
                  refine ⟨1921455563378509073124101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5123881502342690861664269 1921455563378509073124101)
                  ·
                    refine ⟨360272918133470451210769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1921455563378509073124101 360272918133470451210769)
                    ·
                      rfl

theorem cell23_2104887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 4].length) (baseStart_2104887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104887 prefixEnd_2104887 := by exact prefixLift 2104887
  have htrace : WordTrace (prefixWord ++ tailWord_2104887) baseStart_2104887 baseEnd_2104887 := by
    simpa [prefixWord, tailWord_2104887, baseEnd_2104887] using wordTrace_append hprefix tailTrace_2104887
  have hstable : (prefixWord ++ tailWord_2104887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104887).length < 2 ^ (prefixWord ++ tailWord_2104887).sum := by decide
  have hdescent : baseEnd_2104887 < baseStart_2104887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104937 : List Nat := [1, 2, 1, 1, 1, 4, 4, 2, 2, 3, 2]
def baseStart_2104937 : Nat := 118140960795 + 2104937 * 2 ^ 59
def prefixEnd_2104937 : Nat := 4983230072969 + 3 ^ 40 * 2104937 * 2
def baseEnd_2104937 : Nat := 1080844428433136158007077

theorem tailTrace_2104937 : CollatzResearch.WordTrace tailWord_2104937 prefixEnd_2104937 1080844428433136158007077 := by
  unfold tailWord_2104937
  simp only [CollatzResearch.WordTrace]
  refine ⟨76773359575180218463881065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51182239716786812309254043 76773359575180218463881065)
  ·
    refine ⟨57580019681385163847910799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76773359575180218463881065 57580019681385163847910799)
    ·
      refine ⟨86370029522077745771866199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57580019681385163847910799 86370029522077745771866199)
      ·
        refine ⟨129555044283116618657799299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86370029522077745771866199 129555044283116618657799299)
        ·
          refine ⟨194332566424674927986698949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129555044283116618657799299 194332566424674927986698949)
          ·
            refine ⟨36437356204626548997506053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 194332566424674927986698949 36437356204626548997506053)
            ·
              refine ⟨6832004288367477937032385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36437356204626548997506053 6832004288367477937032385)
              ·
                refine ⟨5124003216275608452774289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6832004288367477937032385 5124003216275608452774289)
                ·
                  refine ⟨3843002412206706339580717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5124003216275608452774289 3843002412206706339580717)
                  ·
                    refine ⟨1441125904577514877342769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3843002412206706339580717 1441125904577514877342769)
                    ·
                      refine ⟨1080844428433136158007077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1441125904577514877342769 1080844428433136158007077)
                      ·
                        rfl

theorem cell23_2104937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 3, 2].length) (baseStart_2104937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104937 prefixEnd_2104937 := by exact prefixLift 2104937
  have htrace : WordTrace (prefixWord ++ tailWord_2104937) baseStart_2104937 baseEnd_2104937 := by
    simpa [prefixWord, tailWord_2104937, baseEnd_2104937] using wordTrace_append hprefix tailTrace_2104937
  have hstable : (prefixWord ++ tailWord_2104937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104937).length < 2 ^ (prefixWord ++ tailWord_2104937).sum := by decide
  have hdescent : baseEnd_2104937 < baseStart_2104937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104943 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 5, 6]
def baseStart_2104943 : Nat := 118140960795 + 2104943 * 2 ^ 59
def prefixEnd_2104943 : Nat := 4983230072969 + 3 ^ 40 * 2104943 * 2
def baseEnd_2104943 : Nat := 360282503105687711510683

theorem tailTrace_2104943 : CollatzResearch.WordTrace tailWord_2104943 prefixEnd_2104943 360282503105687711510683 := by
  unfold tailWord_2104943
  simp only [CollatzResearch.WordTrace]
  refine ⟨76773578413158481488599483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51182385608772320992399655 76773578413158481488599483)
  ·
    refine ⟨115160367619737722232899225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76773578413158481488599483 115160367619737722232899225)
    ·
      refine ⟨86370275714803291674674419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115160367619737722232899225 86370275714803291674674419)
      ·
        refine ⟨129555413572204937512011629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86370275714803291674674419 129555413572204937512011629)
        ·
          refine ⟨48583280089576851567004361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129555413572204937512011629 48583280089576851567004361)
          ·
            refine ⟨36437460067182638675253271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48583280089576851567004361 36437460067182638675253271)
            ·
              refine ⟨54656190100773958012879907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36437460067182638675253271 54656190100773958012879907)
              ·
                refine ⟨81984285151160937019319861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54656190100773958012879907 81984285151160937019319861)
                ·
                  refine ⟨7686026732921337845561237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81984285151160937019319861 7686026732921337845561237)
                  ·
                    refine ⟨360282503105687711510683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7686026732921337845561237 360282503105687711510683)
                    ·
                      rfl

theorem cell23_2104943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 6].length) (baseStart_2104943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104943 prefixEnd_2104943 := by exact prefixLift 2104943
  have htrace : WordTrace (prefixWord ++ tailWord_2104943) baseStart_2104943 baseEnd_2104943 := by
    simpa [prefixWord, tailWord_2104943, baseEnd_2104943] using wordTrace_append hprefix tailTrace_2104943
  have hstable : (prefixWord ++ tailWord_2104943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104943).length < 2 ^ (prefixWord ++ tailWord_2104943).sum := by decide
  have hdescent : baseEnd_2104943 < baseStart_2104943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104960 : List Nat := [2, 1, 1, 2, 1, 4, 4, 1, 1, 6]
def baseStart_2104960 : Nat := 118140960795 + 2104960 * 2 ^ 59
def prefixEnd_2104960 : Nat := 4983230072969 + 3 ^ 40 * 2104960 * 2
def baseEnd_2104960 : Nat := 360285412829396522673157

theorem tailTrace_2104960 : CollatzResearch.WordTrace tailWord_2104960 prefixEnd_2104960 360285412829396522673157 := by
  unfold tailWord_2104960
  simp only [CollatzResearch.WordTrace]
  refine ⟨38387099227048446695984167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51182798969397928927978889 38387099227048446695984167)
  ·
    refine ⟨57580648840572670043976251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38387099227048446695984167 57580648840572670043976251)
    ·
      refine ⟨86370973260859005065964377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57580648840572670043976251 86370973260859005065964377)
      ·
        refine ⟨64778229945644253799473283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86370973260859005065964377 64778229945644253799473283)
        ·
          refine ⟨97167344918466380699209925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64778229945644253799473283 97167344918466380699209925)
          ·
            refine ⟨18218877172212446381101861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97167344918466380699209925 18218877172212446381101861)
            ·
              refine ⟨3416039469789833696456599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18218877172212446381101861 3416039469789833696456599)
              ·
                refine ⟨5124059204684750544684899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3416039469789833696456599 5124059204684750544684899)
                ·
                  refine ⟨7686088807027125817027349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5124059204684750544684899 7686088807027125817027349)
                  ·
                    refine ⟨360285412829396522673157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7686088807027125817027349 360285412829396522673157)
                    ·
                      rfl

theorem cell23_2104960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 1, 6].length) (baseStart_2104960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104960 prefixEnd_2104960 := by exact prefixLift 2104960
  have htrace : WordTrace (prefixWord ++ tailWord_2104960) baseStart_2104960 baseEnd_2104960 := by
    simpa [prefixWord, tailWord_2104960, baseEnd_2104960] using wordTrace_append hprefix tailTrace_2104960
  have hstable : (prefixWord ++ tailWord_2104960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104960).length < 2 ^ (prefixWord ++ tailWord_2104960).sum := by decide
  have hdescent : baseEnd_2104960 < baseStart_2104960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104978 : List Nat := [3, 2, 3, 1, 3, 1, 2, 3, 1, 1, 3]
def baseStart_2104978 : Nat := 118140960795 + 2104978 * 2 ^ 59
def prefixEnd_2104978 : Nat := 4983230072969 + 3 ^ 40 * 2104978 * 2
def baseEnd_2104978 : Nat := 1080865481139970497594389

theorem tailTrace_2104978 : CollatzResearch.WordTrace tailWord_2104978 prefixEnd_2104978 1080865481139970497594389 := by
  unfold tailWord_2104978
  simp only [CollatzResearch.WordTrace]
  refine ⟨19193713742007920616530897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51183236645354454977415725 19193713742007920616530897)
  ·
    refine ⟨14395285306505940462398173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19193713742007920616530897 14395285306505940462398173)
    ·
      refine ⟨5398231989939727673399315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14395285306505940462398173 5398231989939727673399315)
      ·
        refine ⟨8097347984909591510098973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5398231989939727673399315 8097347984909591510098973)
        ·
          refine ⟨3036505494341096816287115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8097347984909591510098973 3036505494341096816287115)
          ·
            refine ⟨4554758241511645224430673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3036505494341096816287115 4554758241511645224430673)
            ·
              refine ⟨3416068681133733918323005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4554758241511645224430673 3416068681133733918323005)
              ·
                refine ⟨1281025755425150219371127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3416068681133733918323005 1281025755425150219371127)
                ·
                  refine ⟨1921538633137725329056691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1281025755425150219371127 1921538633137725329056691)
                  ·
                    refine ⟨2882307949706587993585037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1921538633137725329056691 2882307949706587993585037)
                    ·
                      refine ⟨1080865481139970497594389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2882307949706587993585037 1080865481139970497594389)
                      ·
                        rfl

theorem cell23_2104978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_2104978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104978 prefixEnd_2104978 := by exact prefixLift 2104978
  have htrace : WordTrace (prefixWord ++ tailWord_2104978) baseStart_2104978 baseEnd_2104978 := by
    simpa [prefixWord, tailWord_2104978, baseEnd_2104978] using wordTrace_append hprefix tailTrace_2104978
  have hstable : (prefixWord ++ tailWord_2104978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104978).length < 2 ^ (prefixWord ++ tailWord_2104978).sum := by decide
  have hdescent : baseEnd_2104978 < baseStart_2104978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104984 : List Nat := [2, 1, 2, 4, 1, 2, 4, 1, 1, 1, 4]
def baseStart_2104984 : Nat := 118140960795 + 2104984 * 2 ^ 59
def prefixEnd_2104984 : Nat := 4983230072969 + 3 ^ 40 * 2104984 * 2
def baseEnd_2104984 : Nat := 1080868562023897474119361

theorem tailTrace_2104984 : CollatzResearch.WordTrace tailWord_2104984 prefixEnd_2104984 1080868562023897474119361 := by
  unfold tailWord_2104984
  simp only [CollatzResearch.WordTrace]
  refine ⟨38387536903004972745421003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51183382537339963660561337 38387536903004972745421003)
  ·
    refine ⟨57581305354507459118131505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38387536903004972745421003 57581305354507459118131505)
    ·
      refine ⟨43185979015880594338598629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57581305354507459118131505 43185979015880594338598629)
      ·
        refine ⟨8097371065477611438487243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43185979015880594338598629 8097371065477611438487243)
        ·
          refine ⟨12146056598216417157730865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8097371065477611438487243 12146056598216417157730865)
          ·
            refine ⟨9109542448662312868298149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12146056598216417157730865 9109542448662312868298149)
            ·
              refine ⟨1708039209124183662805903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9109542448662312868298149 1708039209124183662805903)
              ·
                refine ⟨2562058813686275494208855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1708039209124183662805903 2562058813686275494208855)
                ·
                  refine ⟨3843088220529413241313283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2562058813686275494208855 3843088220529413241313283)
                  ·
                    refine ⟨5764632330794119861969925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3843088220529413241313283 5764632330794119861969925)
                    ·
                      refine ⟨1080868562023897474119361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5764632330794119861969925 1080868562023897474119361)
                      ·
                        rfl

theorem cell23_2104984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_2104984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2104984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2104984 prefixEnd_2104984 := by exact prefixLift 2104984
  have htrace : WordTrace (prefixWord ++ tailWord_2104984) baseStart_2104984 baseEnd_2104984 := by
    simpa [prefixWord, tailWord_2104984, baseEnd_2104984] using wordTrace_append hprefix tailTrace_2104984
  have hstable : (prefixWord ++ tailWord_2104984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104984).length < 2 ^ (prefixWord ++ tailWord_2104984).sum := by decide
  have hdescent : baseEnd_2104984 < baseStart_2104984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105014 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_2105014 : Nat := 118140960795 + 2105014 * 2 ^ 59
def prefixEnd_2105014 : Nat := 4983230072969 + 3 ^ 40 * 2105014 * 2
def baseEnd_2105014 : Nat := 1080883966443532356744223

theorem tailTrace_2105014 : CollatzResearch.WordTrace tailWord_2105014 prefixEnd_2105014 1080883966443532356744223 := by
  unfold tailWord_2105014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4798510499743828788402131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51184111997267507076289397 4798510499743828788402131)
  ·
    refine ⟨7197765749615743182603197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4798510499743828788402131 7197765749615743182603197)
    ·
      refine ⟨2699162156105903693476199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7197765749615743182603197 2699162156105903693476199)
      ·
        refine ⟨4048743234158855540214299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2699162156105903693476199 4048743234158855540214299)
        ·
          refine ⟨6073114851238283310321449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4048743234158855540214299 6073114851238283310321449)
          ·
            refine ⟨4554836138428712482741087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6073114851238283310321449 4554836138428712482741087)
            ·
              refine ⟨6832254207643068724111631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4554836138428712482741087 6832254207643068724111631)
              ·
                refine ⟨10248381311464603086167447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6832254207643068724111631 10248381311464603086167447)
                ·
                  refine ⟨15372571967196904629251171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10248381311464603086167447 15372571967196904629251171)
                  ·
                    refine ⟨23058857950795356943876757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15372571967196904629251171 23058857950795356943876757)
                    ·
                      refine ⟨1080883966443532356744223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23058857950795356943876757 1080883966443532356744223)
                      ·
                        rfl

theorem cell23_2105014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_2105014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105014 prefixEnd_2105014 := by exact prefixLift 2105014
  have htrace : WordTrace (prefixWord ++ tailWord_2105014) baseStart_2105014 baseEnd_2105014 := by
    simpa [prefixWord, tailWord_2105014, baseEnd_2105014] using wordTrace_append hprefix tailTrace_2105014
  have hstable : (prefixWord ++ tailWord_2105014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105014).length < 2 ^ (prefixWord ++ tailWord_2105014).sum := by decide
  have hdescent : baseEnd_2105014 < baseStart_2105014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105017 : List Nat := [1, 2, 1, 4, 1, 1, 5, 1, 1, 3, 3]
def baseStart_2105017 : Nat := 118140960795 + 2105017 * 2 ^ 59
def prefixEnd_2105017 : Nat := 4983230072969 + 3 ^ 40 * 2105017 * 2
def baseEnd_2105017 : Nat := 1080885506885495845006709

theorem tailTrace_2105017 : CollatzResearch.WordTrace tailWord_2105017 prefixEnd_2105017 1080885506885495845006709 := by
  unfold tailWord_2105017
  simp only [CollatzResearch.WordTrace]
  refine ⟨76776277414890392126793305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51184184943260261417862203 76776277414890392126793305)
  ·
    refine ⟨57582208061167794095094979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76776277414890392126793305 57582208061167794095094979)
    ·
      refine ⟨86373312091751691142642469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57582208061167794095094979 86373312091751691142642469)
      ·
        refine ⟨16194996017203442089245463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86373312091751691142642469 16194996017203442089245463)
        ·
          refine ⟨24292494025805163133868195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16194996017203442089245463 24292494025805163133868195)
          ·
            refine ⟨36438741038707744700802293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24292494025805163133868195 36438741038707744700802293)
            ·
              refine ⟨3416131972378851065700215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36438741038707744700802293 3416131972378851065700215)
              ·
                refine ⟨5124197958568276598550323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3416131972378851065700215 5124197958568276598550323)
                ·
                  refine ⟨7686296937852414897825485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5124197958568276598550323 7686296937852414897825485)
                  ·
                    refine ⟨2882361351694655586684557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7686296937852414897825485 2882361351694655586684557)
                    ·
                      refine ⟨1080885506885495845006709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2882361351694655586684557 1080885506885495845006709)
                      ·
                        rfl

theorem cell23_2105017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_2105017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105017 prefixEnd_2105017 := by exact prefixLift 2105017
  have htrace : WordTrace (prefixWord ++ tailWord_2105017) baseStart_2105017 baseEnd_2105017 := by
    simpa [prefixWord, tailWord_2105017, baseEnd_2105017] using wordTrace_append hprefix tailTrace_2105017
  have hstable : (prefixWord ++ tailWord_2105017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105017).length < 2 ^ (prefixWord ++ tailWord_2105017).sum := by decide
  have hdescent : baseEnd_2105017 < baseStart_2105017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105052 : List Nat := [2, 2, 5, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_2105052 : Nat := 118140960795 + 2105052 * 2 ^ 59
def prefixEnd_2105052 : Nat := 4983230072969 + 3 ^ 40 * 2105052 * 2
def baseEnd_2105052 : Nat := 1080903478708403208069049

theorem tailTrace_2105052 : CollatzResearch.WordTrace tailWord_2105052 prefixEnd_2105052 1080903478708403208069049 := by
  unfold tailWord_2105052
  simp only [CollatzResearch.WordTrace]
  refine ⟨38388776984881796552158705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51185035979842395402878273 38388776984881796552158705)
  ·
    refine ⟨28791582738661347414119029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38388776984881796552158705 28791582738661347414119029)
    ·
      refine ⟨2699210881749501320073659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28791582738661347414119029 2699210881749501320073659)
      ·
        refine ⟨4048816322624251980110489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2699210881749501320073659 4048816322624251980110489)
        ·
          refine ⟨3036612241968188985082867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4048816322624251980110489 3036612241968188985082867)
          ·
            refine ⟨4554918362952283477624301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3036612241968188985082867 4554918362952283477624301)
            ·
              refine ⟨1708094386107106304109113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4554918362952283477624301 1708094386107106304109113)
              ·
                refine ⟨1281070789580329728081835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1708094386107106304109113 1281070789580329728081835)
                ·
                  refine ⟨1921606184370494592122753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1281070789580329728081835 1921606184370494592122753)
                  ·
                    refine ⟨1441204638277870944092065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1921606184370494592122753 1441204638277870944092065)
                    ·
                      refine ⟨1080903478708403208069049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1441204638277870944092065 1080903478708403208069049)
                      ·
                        rfl

theorem cell23_2105052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_2105052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105052 prefixEnd_2105052 := by exact prefixLift 2105052
  have htrace : WordTrace (prefixWord ++ tailWord_2105052) baseStart_2105052 baseEnd_2105052 := by
    simpa [prefixWord, tailWord_2105052, baseEnd_2105052] using wordTrace_append hprefix tailTrace_2105052
  have hstable : (prefixWord ++ tailWord_2105052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105052).length < 2 ^ (prefixWord ++ tailWord_2105052).sum := by decide
  have hdescent : baseEnd_2105052 < baseStart_2105052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105060 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 1, 3, 5]
def baseStart_2105060 : Nat := 118140960795 + 2105060 * 2 ^ 59
def prefixEnd_2105060 : Nat := 4983230072969 + 3 ^ 40 * 2105060 * 2
def baseEnd_2105060 : Nat := 1080907586553639176769011

theorem tailTrace_2105060 : CollatzResearch.WordTrace tailWord_2105060 prefixEnd_2105060 1080907586553639176769011 := by
  unfold tailWord_2105060
  simp only [CollatzResearch.WordTrace]
  refine ⟨38388922876867305235304317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51185230502489740313739089 38388922876867305235304317)
  ·
    refine ⟨14395846078825239463239119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38388922876867305235304317 14395846078825239463239119)
    ·
      refine ⟨21593769118237859194858679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14395846078825239463239119 21593769118237859194858679)
      ·
        refine ⟨32390653677356788792288019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21593769118237859194858679 32390653677356788792288019)
        ·
          refine ⟨48585980516035183188432029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32390653677356788792288019 48585980516035183188432029)
          ·
            refine ⟨18219742693513193695662011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48585980516035183188432029 18219742693513193695662011)
            ·
              refine ⟨27329614040269790543493017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18219742693513193695662011 27329614040269790543493017)
              ·
                refine ⟨20497210530202342907619763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27329614040269790543493017 20497210530202342907619763)
                ·
                  refine ⟨30745815795303514361429645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20497210530202342907619763 30745815795303514361429645)
                  ·
                    refine ⟨11529680923238817885536117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30745815795303514361429645 11529680923238817885536117)
                    ·
                      refine ⟨1080907586553639176769011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11529680923238817885536117 1080907586553639176769011)
                      ·
                        rfl

theorem cell23_2105060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_2105060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105060 prefixEnd_2105060 := by exact prefixLift 2105060
  have htrace : WordTrace (prefixWord ++ tailWord_2105060) baseStart_2105060 baseEnd_2105060 := by
    simpa [prefixWord, tailWord_2105060, baseEnd_2105060] using wordTrace_append hprefix tailTrace_2105060
  have hstable : (prefixWord ++ tailWord_2105060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105060).length < 2 ^ (prefixWord ++ tailWord_2105060).sum := by decide
  have hdescent : baseEnd_2105060 < baseStart_2105060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105074 : List Nat := [3, 2, 1, 3, 1, 1, 2, 3, 1, 4, 2]
def baseStart_2105074 : Nat := 118140960795 + 2105074 * 2 ^ 59
def prefixEnd_2105074 : Nat := 4983230072969 + 3 ^ 40 * 2105074 * 2
def baseEnd_2105074 : Nat := 1080914775282802121993947

theorem tailTrace_2105074 : CollatzResearch.WordTrace tailWord_2105074 prefixEnd_2105074 1080914775282802121993947 := by
  unfold tailWord_2105074
  simp only [CollatzResearch.WordTrace]
  refine ⟨19194589093920972715404569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51185570917122593907745517 19194589093920972715404569)
  ·
    refine ⟨14395941820440729536553427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19194589093920972715404569 14395941820440729536553427)
    ·
      refine ⟨21593912730661094304830141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14395941820440729536553427 21593912730661094304830141)
      ·
        refine ⟨8097717273997910364311303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21593912730661094304830141 8097717273997910364311303)
        ·
          refine ⟨12146575910996865546466955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8097717273997910364311303 12146575910996865546466955)
          ·
            refine ⟨18219863866495298319700433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12146575910996865546466955 18219863866495298319700433)
            ·
              refine ⟨13664897899871473739775325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18219863866495298319700433 13664897899871473739775325)
              ·
                refine ⟨5124336712451802652415747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13664897899871473739775325 5124336712451802652415747)
                ·
                  refine ⟨7686505068677703978623621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5124336712451802652415747 7686505068677703978623621)
                  ·
                    refine ⟨1441219700377069495991929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7686505068677703978623621 1441219700377069495991929)
                    ·
                      refine ⟨1080914775282802121993947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1441219700377069495991929 1080914775282802121993947)
                      ·
                        rfl

theorem cell23_2105074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_2105074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105074 prefixEnd_2105074 := by exact prefixLift 2105074
  have htrace : WordTrace (prefixWord ++ tailWord_2105074) baseStart_2105074 baseEnd_2105074 := by
    simpa [prefixWord, tailWord_2105074, baseEnd_2105074] using wordTrace_append hprefix tailTrace_2105074
  have hstable : (prefixWord ++ tailWord_2105074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105074).length < 2 ^ (prefixWord ++ tailWord_2105074).sum := by decide
  have hdescent : baseEnd_2105074 < baseStart_2105074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105078 : List Nat := [5, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2]
def baseStart_2105078 : Nat := 118140960795 + 2105078 * 2 ^ 59
def prefixEnd_2105078 : Nat := 4983230072969 + 3 ^ 40 * 2105078 * 2
def baseEnd_2105078 : Nat := 1080916829205420106343929

theorem tailTrace_2105078 : CollatzResearch.WordTrace tailWord_2105078 prefixEnd_2105078 1080916829205420106343929 := by
  unfold tailWord_2105078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4798656391729337471547743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51185668178446266363175925 4798656391729337471547743)
  ·
    refine ⟨7197984587594006207321615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4798656391729337471547743 7197984587594006207321615)
    ·
      refine ⟨10796976881391009310982423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7197984587594006207321615 10796976881391009310982423)
      ·
        refine ⟨16195465322086513966473635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10796976881391009310982423 16195465322086513966473635)
        ·
          refine ⟨24293197983129770949710453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16195465322086513966473635 24293197983129770949710453)
          ·
            refine ⟨2277487310918416026535355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24293197983129770949710453 2277487310918416026535355)
            ·
              refine ⟨3416230966377624039803033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2277487310918416026535355 3416230966377624039803033)
              ·
                refine ⟨2562173224783218029852275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3416230966377624039803033 2562173224783218029852275)
                ·
                  refine ⟨3843259837174827044778413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2562173224783218029852275 3843259837174827044778413)
                  ·
                    refine ⟨1441222438940560141791905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3843259837174827044778413 1441222438940560141791905)
                    ·
                      refine ⟨1080916829205420106343929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1441222438940560141791905 1080916829205420106343929)
                      ·
                        rfl

theorem cell23_2105078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_2105078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105078 prefixEnd_2105078 := by exact prefixLift 2105078
  have htrace : WordTrace (prefixWord ++ tailWord_2105078) baseStart_2105078 baseEnd_2105078 := by
    simpa [prefixWord, tailWord_2105078, baseEnd_2105078] using wordTrace_append hprefix tailTrace_2105078
  have hstable : (prefixWord ++ tailWord_2105078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105078).length < 2 ^ (prefixWord ++ tailWord_2105078).sum := by decide
  have hdescent : baseEnd_2105078 < baseStart_2105078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105097 : List Nat := [1, 2, 1, 1, 3, 2, 1, 7, 5]
def baseStart_2105097 : Nat := 118140960795 + 2105097 * 2 ^ 59
def prefixEnd_2105097 : Nat := 4983230072969 + 3 ^ 40 * 2105097 * 2
def baseEnd_2105097 : Nat := 120102953926428392445149

theorem tailTrace_2105097 : CollatzResearch.WordTrace tailWord_2105097 prefixEnd_2105097 120102953926428392445149 := by
  unfold tailWord_2105097
  simp only [CollatzResearch.WordTrace]
  refine ⟨76779195254600565789705545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51186130169733710526470363 76779195254600565789705545)
  ·
    refine ⟨57584396440950424342279159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76779195254600565789705545 57584396440950424342279159)
    ·
      refine ⟨86376594661425636513418739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57584396440950424342279159 86376594661425636513418739)
      ·
        refine ⟨129564891992138454770128109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86376594661425636513418739 129564891992138454770128109)
        ·
          refine ⟨48586834497051920538798041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129564891992138454770128109 48586834497051920538798041)
          ·
            refine ⟨36440125872788940404098531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48586834497051920538798041 36440125872788940404098531)
            ·
              refine ⟨54660188809183410606147797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36440125872788940404098531 54660188809183410606147797)
              ·
                refine ⟨1281098175215236186081589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 54660188809183410606147797 1281098175215236186081589)
                ·
                  refine ⟨120102953926428392445149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1281098175215236186081589 120102953926428392445149)
                  ·
                    rfl

theorem cell23_2105097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 5].length) (baseStart_2105097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105097 prefixEnd_2105097 := by exact prefixLift 2105097
  have htrace : WordTrace (prefixWord ++ tailWord_2105097) baseStart_2105097 baseEnd_2105097 := by
    simpa [prefixWord, tailWord_2105097, baseEnd_2105097] using wordTrace_append hprefix tailTrace_2105097
  have hstable : (prefixWord ++ tailWord_2105097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105097).length < 2 ^ (prefixWord ++ tailWord_2105097).sum := by decide
  have hdescent : baseEnd_2105097 < baseStart_2105097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105114 : List Nat := [3, 1, 1, 3, 2, 3, 1, 4, 5]
def baseStart_2105114 : Nat := 118140960795 + 2105114 * 2 ^ 59
def prefixEnd_2105114 : Nat := 4983230072969 + 3 ^ 40 * 2105114 * 2
def baseEnd_2105114 : Nat := 120103923834331329499307

theorem tailTrace_2105114 : CollatzResearch.WordTrace tailWord_2105114 prefixEnd_2105114 120103923834331329499307 := by
  unfold tailWord_2105114
  simp only [CollatzResearch.WordTrace]
  refine ⟨19194953823884744423268599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51186543530359318462049597 19194953823884744423268599)
  ·
    refine ⟨28792430735827116634902899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19194953823884744423268599 28792430735827116634902899)
    ·
      refine ⟨43188646103740674952354349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28792430735827116634902899 43188646103740674952354349)
      ·
        refine ⟨16195742288902753107132881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43188646103740674952354349 16195742288902753107132881)
        ·
          refine ⟨12146806716677064830349661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16195742288902753107132881 12146806716677064830349661)
          ·
            refine ⟨4555052518753899311381123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12146806716677064830349661 4555052518753899311381123)
            ·
              refine ⟨6832578778130848967071685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4555052518753899311381123 6832578778130848967071685)
              ·
                refine ⟨1281108520899534181325941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6832578778130848967071685 1281108520899534181325941)
                ·
                  refine ⟨120103923834331329499307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1281108520899534181325941 120103923834331329499307)
                  ·
                    rfl

theorem cell23_2105114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 5].length) (baseStart_2105114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105114 prefixEnd_2105114 := by exact prefixLift 2105114
  have htrace : WordTrace (prefixWord ++ tailWord_2105114) baseStart_2105114 baseEnd_2105114 := by
    simpa [prefixWord, tailWord_2105114, baseEnd_2105114] using wordTrace_append hprefix tailTrace_2105114
  have hstable : (prefixWord ++ tailWord_2105114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105114).length < 2 ^ (prefixWord ++ tailWord_2105114).sum := by decide
  have hdescent : baseEnd_2105114 < baseStart_2105114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105124 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 2, 3, 3]
def baseStart_2105124 : Nat := 118140960795 + 2105124 * 2 ^ 59
def prefixEnd_2105124 : Nat := 4983230072969 + 3 ^ 40 * 2105124 * 2
def baseEnd_2105124 : Nat := 1080940449315526926368717

theorem tailTrace_2105124 : CollatzResearch.WordTrace tailWord_2105124 prefixEnd_2105124 1080940449315526926368717 := by
  unfold tailWord_2105124
  simp only [CollatzResearch.WordTrace]
  refine ⟨38390090012751374700469213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51186786683668499600625617 38390090012751374700469213)
  ·
    refine ⟨14396283754781765512675955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38390090012751374700469213 14396283754781765512675955)
    ·
      refine ⟨21594425632172648269013933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14396283754781765512675955 21594425632172648269013933)
      ·
        refine ⟨8097909612064743100880225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21594425632172648269013933 8097909612064743100880225)
        ·
          refine ⟨6073432209048557325660169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8097909612064743100880225 6073432209048557325660169)
          ·
            refine ⟨4555074156786417994245127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6073432209048557325660169 4555074156786417994245127)
            ·
              refine ⟨6832611235179626991367691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4555074156786417994245127 6832611235179626991367691)
              ·
                refine ⟨10248916852769440487051537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6832611235179626991367691 10248916852769440487051537)
                ·
                  refine ⟨7686687639577080365288653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10248916852769440487051537 7686687639577080365288653)
                  ·
                    refine ⟨2882507864841405136983245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7686687639577080365288653 2882507864841405136983245)
                    ·
                      refine ⟨1080940449315526926368717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2882507864841405136983245 1080940449315526926368717)
                      ·
                        rfl

theorem cell23_2105124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_2105124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105124 prefixEnd_2105124 := by exact prefixLift 2105124
  have htrace : WordTrace (prefixWord ++ tailWord_2105124) baseStart_2105124 baseEnd_2105124 := by
    simpa [prefixWord, tailWord_2105124, baseEnd_2105124] using wordTrace_append hprefix tailTrace_2105124
  have hstable : (prefixWord ++ tailWord_2105124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105124).length < 2 ^ (prefixWord ++ tailWord_2105124).sum := by decide
  have hdescent : baseEnd_2105124 < baseStart_2105124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105144 : List Nat := [2, 1, 2, 1, 3, 5, 1, 1, 2, 5]
def baseStart_2105144 : Nat := 118140960795 + 2105144 * 2 ^ 59
def prefixEnd_2105144 : Nat := 4983230072969 + 3 ^ 40 * 2105144 * 2
def baseEnd_2105144 : Nat := 360316906309538949372875

theorem tailTrace_2105144 : CollatzResearch.WordTrace tailWord_2105144 prefixEnd_2105144 360316906309538949372875 := by
  unfold tailWord_2105144
  simp only [CollatzResearch.WordTrace]
  refine ⟨38390454742715146408333243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51187272990286861877777657 38390454742715146408333243)
  ·
    refine ⟨57585682114072719612499865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38390454742715146408333243 57585682114072719612499865)
    ·
      refine ⟨43189261585554539709374899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57585682114072719612499865 43189261585554539709374899)
      ·
        refine ⟨64783892378331809564062349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43189261585554539709374899 64783892378331809564062349)
        ·
          refine ⟨24293959641874428586523381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64783892378331809564062349 24293959641874428586523381)
          ·
            refine ⟨2277558716425727679986567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24293959641874428586523381 2277558716425727679986567)
            ·
              refine ⟨3416338074638591519979851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2277558716425727679986567 3416338074638591519979851)
              ·
                refine ⟨5124507111957887279969777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3416338074638591519979851 5124507111957887279969777)
                ·
                  refine ⟨3843380333968415459977333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5124507111957887279969777 3843380333968415459977333)
                  ·
                    refine ⟨360316906309538949372875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3843380333968415459977333 360316906309538949372875)
                    ·
                      rfl

theorem cell23_2105144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 2, 5].length) (baseStart_2105144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105144 prefixEnd_2105144 := by exact prefixLift 2105144
  have htrace : WordTrace (prefixWord ++ tailWord_2105144) baseStart_2105144 baseEnd_2105144 := by
    simpa [prefixWord, tailWord_2105144, baseEnd_2105144] using wordTrace_append hprefix tailTrace_2105144
  have hstable : (prefixWord ++ tailWord_2105144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105144).length < 2 ^ (prefixWord ++ tailWord_2105144).sum := by decide
  have hdescent : baseEnd_2105144 < baseStart_2105144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105157 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 5, 4]
def baseStart_2105157 : Nat := 118140960795 + 2105157 * 2 ^ 59
def prefixEnd_2105157 : Nat := 4983230072969 + 3 ^ 40 * 2105157 * 2
def baseEnd_2105157 : Nat := 360319131392375099085355

theorem tailTrace_2105157 : CollatzResearch.WordTrace tailWord_2105157 prefixEnd_2105157 360319131392375099085355 := by
  unfold tailWord_2105157
  simp only [CollatzResearch.WordTrace]
  refine ⟨76781383634383196036889725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51187589089588797357926483 76781383634383196036889725)
  ·
    refine ⟨28793018862893698513833647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76781383634383196036889725 28793018862893698513833647)
    ·
      refine ⟨43189528294340547770750471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28793018862893698513833647 43189528294340547770750471)
      ·
        refine ⟨64784292441510821656125707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43189528294340547770750471 64784292441510821656125707)
        ·
          refine ⟨97176438662266232484188561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64784292441510821656125707 97176438662266232484188561)
          ·
            refine ⟨72882328996699674363141421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97176438662266232484188561 72882328996699674363141421)
            ·
              refine ⟨27330873373762377886178033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72882328996699674363141421 27330873373762377886178033)
              ·
                refine ⟨20498155030321783414633525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27330873373762377886178033 20498155030321783414633525)
                ·
                  refine ⟨1921702034092667195121893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20498155030321783414633525 1921702034092667195121893)
                  ·
                    refine ⟨360319131392375099085355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1921702034092667195121893 360319131392375099085355)
                    ·
                      rfl

theorem cell23_2105157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 4].length) (baseStart_2105157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105157 prefixEnd_2105157 := by exact prefixLift 2105157
  have htrace : WordTrace (prefixWord ++ tailWord_2105157) baseStart_2105157 baseEnd_2105157 := by
    simpa [prefixWord, tailWord_2105157, baseEnd_2105157] using wordTrace_append hprefix tailTrace_2105157
  have hstable : (prefixWord ++ tailWord_2105157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105157).length < 2 ^ (prefixWord ++ tailWord_2105157).sum := by decide
  have hdescent : baseEnd_2105157 < baseStart_2105157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105277 : List Nat := [1, 4, 1, 2, 3, 12]
def baseStart_2105277 : Nat := 118140960795 + 2105277 * 2 ^ 59
def prefixEnd_2105277 : Nat := 4983230072969 + 3 ^ 40 * 2105277 * 2
def baseEnd_2105277 : Nat := 4448637908871048673891

theorem tailTrace_2105277 : CollatzResearch.WordTrace tailWord_2105277 prefixEnd_2105277 4448637908871048673891 := by
  unfold tailWord_2105277
  simp only [CollatzResearch.WordTrace]
  refine ⟨76785760393948456531258085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51190506929298971020838723 76785760393948456531258085)
  ·
    refine ⟨14397330073865335599610891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76785760393948456531258085 14397330073865335599610891)
    ·
      refine ⟨21595995110798003399416337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14397330073865335599610891 21595995110798003399416337)
      ·
        refine ⟨16196996333098502549562253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21595995110798003399416337 16196996333098502549562253)
        ·
          refine ⟨6073873624911938456085845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16196996333098502549562253 6073873624911938456085845)
          ·
            refine ⟨4448637908871048673891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 6073873624911938456085845 4448637908871048673891)
            ·
              rfl

theorem cell23_2105277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 12].length) (baseStart_2105277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105277 prefixEnd_2105277 := by exact prefixLift 2105277
  have htrace : WordTrace (prefixWord ++ tailWord_2105277) baseStart_2105277 baseEnd_2105277 := by
    simpa [prefixWord, tailWord_2105277, baseEnd_2105277] using wordTrace_append hprefix tailTrace_2105277
  have hstable : (prefixWord ++ tailWord_2105277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105277).length < 2 ^ (prefixWord ++ tailWord_2105277).sum := by decide
  have hdescent : baseEnd_2105277 < baseStart_2105277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105301 : List Nat := [1, 3, 2, 3, 2, 2, 2, 1, 1, 2, 4]
def baseStart_2105301 : Nat := 118140960795 + 2105301 * 2 ^ 59
def prefixEnd_2105301 : Nat := 4983230072969 + 3 ^ 40 * 2105301 * 2
def baseEnd_2105301 : Nat := 1081031335391372733855403

theorem tailTrace_2105301 : CollatzResearch.WordTrace tailWord_2105301 prefixEnd_2105301 1081031335391372733855403 := by
  unfold tailWord_2105301
  simp only [CollatzResearch.WordTrace]
  refine ⟨76786635745861508630131757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51191090497241005753421171 76786635745861508630131757)
  ·
    refine ⟨28794988404698065736299409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76786635745861508630131757 28794988404698065736299409)
    ·
      refine ⟨21596241303523549302224557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28794988404698065736299409 21596241303523549302224557)
      ·
        refine ⟨8098590488821330988334209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21596241303523549302224557 8098590488821330988334209)
        ·
          refine ⟨6073942866615998241250657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8098590488821330988334209 6073942866615998241250657)
          ·
            refine ⟨4555457149961998680937993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6073942866615998241250657 4555457149961998680937993)
            ·
              refine ⟨3416592862471499010703495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4555457149961998680937993 3416592862471499010703495)
              ·
                refine ⟨5124889293707248516055243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3416592862471499010703495 5124889293707248516055243)
                ·
                  refine ⟨7687333940560872774082865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5124889293707248516055243 7687333940560872774082865)
                  ·
                    refine ⟨5765500455420654580562149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7687333940560872774082865 5765500455420654580562149)
                    ·
                      refine ⟨1081031335391372733855403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5765500455420654580562149 1081031335391372733855403)
                      ·
                        rfl

theorem cell23_2105301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_2105301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105301 prefixEnd_2105301 := by exact prefixLift 2105301
  have htrace : WordTrace (prefixWord ++ tailWord_2105301) baseStart_2105301 baseEnd_2105301 := by
    simpa [prefixWord, tailWord_2105301, baseEnd_2105301] using wordTrace_append hprefix tailTrace_2105301
  have hstable : (prefixWord ++ tailWord_2105301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105301).length < 2 ^ (prefixWord ++ tailWord_2105301).sum := by decide
  have hdescent : baseEnd_2105301 < baseStart_2105301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105325 : List Nat := [1, 5, 1, 4, 1, 1, 1, 3, 1, 2, 3]
def baseStart_2105325 : Nat := 118140960795 + 2105325 * 2 ^ 59
def prefixEnd_2105325 : Nat := 4983230072969 + 3 ^ 40 * 2105325 * 2
def baseEnd_2105325 : Nat := 1081043658927080639955293

theorem tailTrace_2105325 : CollatzResearch.WordTrace tailWord_2105325 prefixEnd_2105325 1081043658927080639955293 := by
  unfold tailWord_2105325
  simp only [CollatzResearch.WordTrace]
  refine ⟨76787511097774560729005429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51191674065183040486003619 76787511097774560729005429)
  ·
    refine ⟨7198829165416365068344259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76787511097774560729005429 7198829165416365068344259)
    ·
      refine ⟨10798243748124547602516389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7198829165416365068344259 10798243748124547602516389)
      ·
        refine ⟨2024670702773352675471823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10798243748124547602516389 2024670702773352675471823)
        ·
          refine ⟨3037006054160029013207735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2024670702773352675471823 3037006054160029013207735)
          ·
            refine ⟨4555509081240043519811603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3037006054160029013207735 4555509081240043519811603)
            ·
              refine ⟨6833263621860065279717405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4555509081240043519811603 6833263621860065279717405)
              ·
                refine ⟨2562473858197524479894027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6833263621860065279717405 2562473858197524479894027)
                ·
                  refine ⟨3843710787296286719841041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2562473858197524479894027 3843710787296286719841041)
                  ·
                    refine ⟨2882783090472215039880781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3843710787296286719841041 2882783090472215039880781)
                    ·
                      refine ⟨1081043658927080639955293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2882783090472215039880781 1081043658927080639955293)
                      ·
                        rfl

theorem cell23_2105325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_2105325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105325 prefixEnd_2105325 := by exact prefixLift 2105325
  have htrace : WordTrace (prefixWord ++ tailWord_2105325) baseStart_2105325 baseEnd_2105325 := by
    simpa [prefixWord, tailWord_2105325, baseEnd_2105325] using wordTrace_append hprefix tailTrace_2105325
  have hstable : (prefixWord ++ tailWord_2105325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105325).length < 2 ^ (prefixWord ++ tailWord_2105325).sum := by decide
  have hdescent : baseEnd_2105325 < baseStart_2105325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105365 : List Nat := [1, 3, 2, 1, 5, 1, 2, 2, 1, 3, 2]
def baseStart_2105365 : Nat := 118140960795 + 2105365 * 2 ^ 59
def prefixEnd_2105365 : Nat := 4983230072969 + 3 ^ 40 * 2105365 * 2
def baseEnd_2105365 : Nat := 1081064198153260483455109

theorem tailTrace_2105365 : CollatzResearch.WordTrace tailWord_2105365 prefixEnd_2105365 1081064198153260483455109 := by
  unfold tailWord_2105365
  simp only [CollatzResearch.WordTrace]
  refine ⟨76788970017629647560461549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51192646678419765040307699 76788970017629647560461549)
  ·
    refine ⟨28795863756611117835173081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76788970017629647560461549 28795863756611117835173081)
    ·
      refine ⟨21596897817458338376379811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28795863756611117835173081 21596897817458338376379811)
      ·
        refine ⟨32395346726187507564569717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21596897817458338376379811 32395346726187507564569717)
        ·
          refine ⟨3037063755580078834178411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32395346726187507564569717 3037063755580078834178411)
          ·
            refine ⟨4555595633370118251267617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3037063755580078834178411 4555595633370118251267617)
            ·
              refine ⟨3416696725027588688450713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4555595633370118251267617 3416696725027588688450713)
              ·
                refine ⟨2562522543770691516338035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3416696725027588688450713 2562522543770691516338035)
                ·
                  refine ⟨3843783815656037274507053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2562522543770691516338035 3843783815656037274507053)
                  ·
                    refine ⟨1441418930871013977940145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3843783815656037274507053 1441418930871013977940145)
                    ·
                      refine ⟨1081064198153260483455109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1441418930871013977940145 1081064198153260483455109)
                      ·
                        rfl

theorem cell23_2105365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 3, 2].length) (baseStart_2105365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105365 prefixEnd_2105365 := by exact prefixLift 2105365
  have htrace : WordTrace (prefixWord ++ tailWord_2105365) baseStart_2105365 baseEnd_2105365 := by
    simpa [prefixWord, tailWord_2105365, baseEnd_2105365] using wordTrace_append hprefix tailTrace_2105365
  have hstable : (prefixWord ++ tailWord_2105365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105365).length < 2 ^ (prefixWord ++ tailWord_2105365).sum := by decide
  have hdescent : baseEnd_2105365 < baseStart_2105365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105378 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 6, 2, 2]
def baseStart_2105378 : Nat := 118140960795 + 2105378 * 2 ^ 59
def prefixEnd_2105378 : Nat := 4983230072969 + 3 ^ 40 * 2105378 * 2
def baseEnd_2105378 : Nat := 1081070873401768932592549

theorem tailTrace_2105378 : CollatzResearch.WordTrace tailWord_2105378 prefixEnd_2105378 1081070873401768932592549 := by
  unfold tailWord_2105378
  simp only [CollatzResearch.WordTrace]
  refine ⟨19197361041645637695171197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51192962777721700520456525 19197361041645637695171197)
  ·
    refine ⟨7199010390617114135689199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19197361041645637695171197 7199010390617114135689199)
    ·
      refine ⟨10798515585925671203533799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7199010390617114135689199 10798515585925671203533799)
      ·
        refine ⟨16197773378888506805300699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10798515585925671203533799 16197773378888506805300699)
        ·
          refine ⟨24296660068332760207951049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16197773378888506805300699 24296660068332760207951049)
          ·
            refine ⟨18222495051249570155963287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24296660068332760207951049 18222495051249570155963287)
            ·
              refine ⟨27333742576874355233944931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18222495051249570155963287 27333742576874355233944931)
              ·
                refine ⟨41000613865311532850917397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27333742576874355233944931 41000613865311532850917397)
                ·
                  refine ⟨1921903774936478102386753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41000613865311532850917397 1921903774936478102386753)
                  ·
                    refine ⟨1441427831202358576790065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1921903774936478102386753 1441427831202358576790065)
                    ·
                      refine ⟨1081070873401768932592549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1441427831202358576790065 1081070873401768932592549)
                      ·
                        rfl

theorem cell23_2105378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_2105378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105378 prefixEnd_2105378 := by exact prefixLift 2105378
  have htrace : WordTrace (prefixWord ++ tailWord_2105378) baseStart_2105378 baseEnd_2105378 := by
    simpa [prefixWord, tailWord_2105378, baseEnd_2105378] using wordTrace_append hprefix tailTrace_2105378
  have hstable : (prefixWord ++ tailWord_2105378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105378).length < 2 ^ (prefixWord ++ tailWord_2105378).sum := by decide
  have hdescent : baseEnd_2105378 < baseStart_2105378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105464 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 2, 4, 4]
def baseStart_2105464 : Nat := 118140960795 + 2105464 * 2 ^ 59
def prefixEnd_2105464 : Nat := 4983230072969 + 3 ^ 40 * 2105464 * 2
def baseEnd_2105464 : Nat := 1081115032738055596117153

theorem tailTrace_2105464 : CollatzResearch.WordTrace tailWord_2105464 prefixEnd_2105464 1081115032738055596117153 := by
  unfold tailWord_2105464
  simp only [CollatzResearch.WordTrace]
  refine ⟨38396290422135493734157723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51195053896180658312210297 38396290422135493734157723)
  ·
    refine ⟨57594435633203240601236585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38396290422135493734157723 57594435633203240601236585)
    ·
      refine ⟨43195826724902430450927439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57594435633203240601236585 43195826724902430450927439)
      ·
        refine ⟨64793740087353645676391159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43195826724902430450927439 64793740087353645676391159)
        ·
          refine ⟨97190610131030468514586739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64793740087353645676391159 97190610131030468514586739)
          ·
            refine ⟨145785915196545702771880109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97190610131030468514586739 145785915196545702771880109)
            ·
              refine ⟨54669718198704638539455041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145785915196545702771880109 54669718198704638539455041)
              ·
                refine ⟨41002288649028478904591281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54669718198704638539455041 41002288649028478904591281)
                ·
                  refine ⟨30751716486771359178443461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41002288649028478904591281 30751716486771359178443461)
                  ·
                    refine ⟨5765946841269629845958149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30751716486771359178443461 5765946841269629845958149)
                    ·
                      refine ⟨1081115032738055596117153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5765946841269629845958149 1081115032738055596117153)
                      ·
                        rfl

theorem cell23_2105464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_2105464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105464 prefixEnd_2105464 := by exact prefixLift 2105464
  have htrace : WordTrace (prefixWord ++ tailWord_2105464) baseStart_2105464 baseEnd_2105464 := by
    simpa [prefixWord, tailWord_2105464, baseEnd_2105464] using wordTrace_append hprefix tailTrace_2105464
  have hstable : (prefixWord ++ tailWord_2105464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105464).length < 2 ^ (prefixWord ++ tailWord_2105464).sum := by decide
  have hdescent : baseEnd_2105464 < baseStart_2105464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105468 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 2, 4, 2]
def baseStart_2105468 : Nat := 118140960795 + 2105468 * 2 ^ 59
def prefixEnd_2105468 : Nat := 4983230072969 + 3 ^ 40 * 2105468 * 2
def baseEnd_2105468 : Nat := 1081117086660673580467135

theorem tailTrace_2105468 : CollatzResearch.WordTrace tailWord_2105468 prefixEnd_2105468 1081117086660673580467135 := by
  unfold tailWord_2105468
  simp only [CollatzResearch.WordTrace]
  refine ⟨38396363368128248075730529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51195151157504330767640705 38396363368128248075730529)
  ·
    refine ⟨28797272526096186056797897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38396363368128248075730529 28797272526096186056797897)
    ·
      refine ⟨21597954394572139542598423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28797272526096186056797897 21597954394572139542598423)
      ·
        refine ⟨32396931591858209313897635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21597954394572139542598423 32396931591858209313897635)
        ·
          refine ⟨48595397387787313970846453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32396931591858209313897635 48595397387787313970846453)
          ·
            refine ⟨4555818505105060684766855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48595397387787313970846453 4555818505105060684766855)
            ·
              refine ⟨6833727757657591027150283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4555818505105060684766855 6833727757657591027150283)
              ·
                refine ⟨10250591636486386540725425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6833727757657591027150283 10250591636486386540725425)
                ·
                  refine ⟨7687943727364789905544069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10250591636486386540725425 7687943727364789905544069)
                  ·
                    refine ⟨1441489448880898107289513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7687943727364789905544069 1441489448880898107289513)
                    ·
                      refine ⟨1081117086660673580467135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1441489448880898107289513 1081117086660673580467135)
                      ·
                        rfl

theorem cell23_2105468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 2, 4, 2].length) (baseStart_2105468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105468 prefixEnd_2105468 := by exact prefixLift 2105468
  have htrace : WordTrace (prefixWord ++ tailWord_2105468) baseStart_2105468 baseEnd_2105468 := by
    simpa [prefixWord, tailWord_2105468, baseEnd_2105468] using wordTrace_append hprefix tailTrace_2105468
  have hstable : (prefixWord ++ tailWord_2105468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105468).length < 2 ^ (prefixWord ++ tailWord_2105468).sum := by decide
  have hdescent : baseEnd_2105468 < baseStart_2105468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105541 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 3, 1, 4]
def baseStart_2105541 : Nat := 118140960795 + 2105541 * 2 ^ 59
def prefixEnd_2105541 : Nat := 4983230072969 + 3 ^ 40 * 2105541 * 2
def baseEnd_2105541 : Nat := 1081154570748451794854299

theorem tailTrace_2105541 : CollatzResearch.WordTrace tailWord_2105541 prefixEnd_2105541 1081154570748451794854299 := by
  unfold tailWord_2105541
  simp only [CollatzResearch.WordTrace]
  refine ⟨76795389264992029618868477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51196926176661353079245651 76795389264992029618868477)
  ·
    refine ⟨28798270974372011107075679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76795389264992029618868477 28798270974372011107075679)
    ·
      refine ⟨43197406461558016660613519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28798270974372011107075679 43197406461558016660613519)
      ·
        refine ⟨64796109692337024990920279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43197406461558016660613519 64796109692337024990920279)
        ·
          refine ⟨97194164538505537486380419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64796109692337024990920279 97194164538505537486380419)
          ·
            refine ⟨145791246807758306229570629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97194164538505537486380419 145791246807758306229570629)
            ·
              refine ⟨27335858776454682418044493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145791246807758306229570629 27335858776454682418044493)
              ·
                refine ⟨10250947041170505906766685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27335858776454682418044493 10250947041170505906766685)
                ·
                  refine ⟨3844105140438939715037507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10250947041170505906766685 3844105140438939715037507)
                  ·
                    refine ⟨5766157710658409572556261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3844105140438939715037507 5766157710658409572556261)
                    ·
                      refine ⟨1081154570748451794854299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5766157710658409572556261 1081154570748451794854299)
                      ·
                        rfl

theorem cell23_2105541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_2105541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105541 prefixEnd_2105541 := by exact prefixLift 2105541
  have htrace : WordTrace (prefixWord ++ tailWord_2105541) baseStart_2105541 baseEnd_2105541 := by
    simpa [prefixWord, tailWord_2105541, baseEnd_2105541] using wordTrace_append hprefix tailTrace_2105541
  have hstable : (prefixWord ++ tailWord_2105541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105541).length < 2 ^ (prefixWord ++ tailWord_2105541).sum := by decide
  have hdescent : baseEnd_2105541 < baseStart_2105541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105551 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 6, 4]
def baseStart_2105551 : Nat := 118140960795 + 2105551 * 2 ^ 59
def prefixEnd_2105551 : Nat := 4983230072969 + 3 ^ 40 * 2105551 * 2
def baseEnd_2105551 : Nat := 360386568518332251909751

theorem tailTrace_2105551 : CollatzResearch.WordTrace tailWord_2105551 prefixEnd_2105551 360386568518332251909751 := by
  unfold tailWord_2105551
  simp only [CollatzResearch.WordTrace]
  refine ⟨76795753994955801326732507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51197169329970534217821671 76795753994955801326732507)
  ·
    refine ⟨115193630992433701990098761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76795753994955801326732507 115193630992433701990098761)
    ·
      refine ⟨86395223244325276492574071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115193630992433701990098761 86395223244325276492574071)
      ·
        refine ⟨129592834866487914738861107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86395223244325276492574071 129592834866487914738861107)
        ·
          refine ⟨194389252299731872108291661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129592834866487914738861107 194389252299731872108291661)
          ·
            refine ⟨72895969612399452040609373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 194389252299731872108291661 72895969612399452040609373)
            ·
              refine ⟨27335988604649794515228515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72895969612399452040609373 27335988604649794515228515)
              ·
                refine ⟨41003982906974691772842773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27335988604649794515228515 41003982906974691772842773)
                ·
                  refine ⟨1922061698764438676852005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41003982906974691772842773 1922061698764438676852005)
                  ·
                    refine ⟨360386568518332251909751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1922061698764438676852005 360386568518332251909751)
                    ·
                      rfl

theorem cell23_2105551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 4].length) (baseStart_2105551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105551 prefixEnd_2105551 := by exact prefixLift 2105551
  have htrace : WordTrace (prefixWord ++ tailWord_2105551) baseStart_2105551 baseEnd_2105551 := by
    simpa [prefixWord, tailWord_2105551, baseEnd_2105551] using wordTrace_append hprefix tailTrace_2105551
  have hstable : (prefixWord ++ tailWord_2105551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105551).length < 2 ^ (prefixWord ++ tailWord_2105551).sum := by decide
  have hdescent : baseEnd_2105551 < baseStart_2105551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105561 : List Nat := [1, 2, 1, 2, 3, 1, 3, 3, 1, 1, 5]
def baseStart_2105561 : Nat := 118140960795 + 2105561 * 2 ^ 59
def prefixEnd_2105561 : Nat := 4983230072969 + 3 ^ 40 * 2105561 * 2
def baseEnd_2105561 : Nat := 1081164840361541716604207

theorem tailTrace_2105561 : CollatzResearch.WordTrace tailWord_2105561 prefixEnd_2105561 1081164840361541716604207 := by
  unfold tailWord_2105561
  simp only [CollatzResearch.WordTrace]
  refine ⟨76796118724919573034596537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51197412483279715356397691 76796118724919573034596537)
  ·
    refine ⟨57597089043689679775947403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76796118724919573034596537 57597089043689679775947403)
    ·
      refine ⟨86395633565534519663921105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57597089043689679775947403 86395633565534519663921105)
      ·
        refine ⟨64796725174150889747940829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86395633565534519663921105 64796725174150889747940829)
        ·
          refine ⟨24298771940306583655477811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64796725174150889747940829 24298771940306583655477811)
          ·
            refine ⟨36448157910459875483216717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24298771940306583655477811 36448157910459875483216717)
            ·
              refine ⟨13668059216422453306206269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36448157910459875483216717 13668059216422453306206269)
              ·
                refine ⟨5125522206158419989827351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13668059216422453306206269 5125522206158419989827351)
                ·
                  refine ⟨7688283309237629984741027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5125522206158419989827351 7688283309237629984741027)
                  ·
                    refine ⟨11532424963856444977111541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7688283309237629984741027 11532424963856444977111541)
                    ·
                      refine ⟨1081164840361541716604207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11532424963856444977111541 1081164840361541716604207)
                      ·
                        rfl

theorem cell23_2105561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_2105561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105561 prefixEnd_2105561 := by exact prefixLift 2105561
  have htrace : WordTrace (prefixWord ++ tailWord_2105561) baseStart_2105561 baseEnd_2105561 := by
    simpa [prefixWord, tailWord_2105561, baseEnd_2105561] using wordTrace_append hprefix tailTrace_2105561
  have hstable : (prefixWord ++ tailWord_2105561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105561).length < 2 ^ (prefixWord ++ tailWord_2105561).sum := by decide
  have hdescent : baseEnd_2105561 < baseStart_2105561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105568 : List Nat := [2, 1, 1, 3, 1, 3, 2, 4, 2, 4]
def baseStart_2105568 : Nat := 118140960795 + 2105568 * 2 ^ 59
def prefixEnd_2105568 : Nat := 4983230072969 + 3 ^ 40 * 2105568 * 2
def baseEnd_2105568 : Nat := 360389478242041063072225

theorem tailTrace_2105568 : CollatzResearch.WordTrace tailWord_2105568 prefixEnd_2105568 360389478242041063072225 := by
  unfold tailWord_2105568
  simp only [CollatzResearch.WordTrace]
  refine ⟨38398187017947106615050679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51197582690596142153400905 38398187017947106615050679)
  ·
    refine ⟨57597280526920659922576019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38398187017947106615050679 57597280526920659922576019)
    ·
      refine ⟨86395920790380989883864029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57597280526920659922576019 86395920790380989883864029)
      ·
        refine ⟨32398470296392871206449011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86395920790380989883864029 32398470296392871206449011)
        ·
          refine ⟨48597705444589306809673517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32398470296392871206449011 48597705444589306809673517)
          ·
            refine ⟨18224139541720990053627569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48597705444589306809673517 18224139541720990053627569)
            ·
              refine ⟨13668104656290742540220677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18224139541720990053627569 13668104656290742540220677)
              ·
                refine ⟨2562769623054514226291377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13668104656290742540220677 2562769623054514226291377)
                ·
                  refine ⟨1922077217290885669718533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2562769623054514226291377 1922077217290885669718533)
                  ·
                    refine ⟨360389478242041063072225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1922077217290885669718533 360389478242041063072225)
                    ·
                      rfl

theorem cell23_2105568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 2, 4].length) (baseStart_2105568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105568 prefixEnd_2105568 := by exact prefixLift 2105568
  have htrace : WordTrace (prefixWord ++ tailWord_2105568) baseStart_2105568 baseEnd_2105568 := by
    simpa [prefixWord, tailWord_2105568, baseEnd_2105568] using wordTrace_append hprefix tailTrace_2105568
  have hstable : (prefixWord ++ tailWord_2105568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105568).length < 2 ^ (prefixWord ++ tailWord_2105568).sum := by decide
  have hdescent : baseEnd_2105568 < baseStart_2105568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105578 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 3, 2, 3]
def baseStart_2105578 : Nat := 118140960795 + 2105578 * 2 ^ 59
def prefixEnd_2105578 : Nat := 4983230072969 + 3 ^ 40 * 2105578 * 2
def baseEnd_2105578 : Nat := 1081173569532668150091629

theorem tailTrace_2105578 : CollatzResearch.WordTrace tailWord_2105578 prefixEnd_2105578 1081173569532668150091629 := by
  unfold tailWord_2105578
  simp only [CollatzResearch.WordTrace]
  refine ⟨19199184691464496234491347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51197825843905323291976925 19199184691464496234491347)
  ·
    refine ⟨28798777037196744351737021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19199184691464496234491347 28798777037196744351737021)
    ·
      refine ⟨10799541388948779131901383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28798777037196744351737021 10799541388948779131901383)
      ·
        refine ⟨16199312083423168697852075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10799541388948779131901383 16199312083423168697852075)
        ·
          refine ⟨24298968125134753046778113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16199312083423168697852075 24298968125134753046778113)
          ·
            refine ⟨18224226093851064785083585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24298968125134753046778113 18224226093851064785083585)
            ·
              refine ⟨13668169570388298588812689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18224226093851064785083585 13668169570388298588812689)
              ·
                refine ⟨10251127177791223941609517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13668169570388298588812689 10251127177791223941609517)
                ·
                  refine ⟨3844172691671708978103569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10251127177791223941609517 3844172691671708978103569)
                  ·
                    refine ⟨2883129518753781733577677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3844172691671708978103569 2883129518753781733577677)
                    ·
                      refine ⟨1081173569532668150091629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2883129518753781733577677 1081173569532668150091629)
                      ·
                        rfl

theorem cell23_2105578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_2105578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105578 prefixEnd_2105578 := by exact prefixLift 2105578
  have htrace : WordTrace (prefixWord ++ tailWord_2105578) baseStart_2105578 baseEnd_2105578 := by
    simpa [prefixWord, tailWord_2105578, baseEnd_2105578] using wordTrace_append hprefix tailTrace_2105578
  have hstable : (prefixWord ++ tailWord_2105578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105578).length < 2 ^ (prefixWord ++ tailWord_2105578).sum := by decide
  have hdescent : baseEnd_2105578 < baseStart_2105578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105585 : List Nat := [1, 2, 2, 2, 2, 1, 6, 1, 2, 4]
def baseStart_2105585 : Nat := 118140960795 + 2105585 * 2 ^ 59
def prefixEnd_2105585 : Nat := 4983230072969 + 3 ^ 40 * 2105585 * 2
def baseEnd_2105585 : Nat := 360392387965749874234699

theorem tailTrace_2105585 : CollatzResearch.WordTrace tailWord_2105585 prefixEnd_2105585 360392387965749874234699 := by
  unfold tailWord_2105585
  simp only [CollatzResearch.WordTrace]
  refine ⟨76796994076832625133470209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51197996051221750088980139 76796994076832625133470209)
  ·
    refine ⟨57597745557624468850102657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76796994076832625133470209 57597745557624468850102657)
    ·
      refine ⟨43198309168218351637576993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57597745557624468850102657 43198309168218351637576993)
      ·
        refine ⟨32398731876163763728182745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43198309168218351637576993 32398731876163763728182745)
        ·
          refine ⟨24299048907122822796137059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32398731876163763728182745 24299048907122822796137059)
          ·
            refine ⟨36448573360684234194205589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24299048907122822796137059 36448573360684234194205589)
            ·
              refine ⟨1708526876282073477853387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36448573360684234194205589 1708526876282073477853387)
              ·
                refine ⟨2562790314423110216780081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1708526876282073477853387 2562790314423110216780081)
                ·
                  refine ⟨1922092735817332662585061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2562790314423110216780081 1922092735817332662585061)
                  ·
                    refine ⟨360392387965749874234699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1922092735817332662585061 360392387965749874234699)
                    ·
                      rfl

theorem cell23_2105585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 2, 4].length) (baseStart_2105585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105585 prefixEnd_2105585 := by exact prefixLift 2105585
  have htrace : WordTrace (prefixWord ++ tailWord_2105585) baseStart_2105585 baseEnd_2105585 := by
    simpa [prefixWord, tailWord_2105585, baseEnd_2105585] using wordTrace_append hprefix tailTrace_2105585
  have hstable : (prefixWord ++ tailWord_2105585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105585).length < 2 ^ (prefixWord ++ tailWord_2105585).sum := by decide
  have hdescent : baseEnd_2105585 < baseStart_2105585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105608 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 3, 3, 3]
def baseStart_2105608 : Nat := 118140960795 + 2105608 * 2 ^ 59
def prefixEnd_2105608 : Nat := 4983230072969 + 3 ^ 40 * 2105608 * 2
def baseEnd_2105608 : Nat := 1081188973952303032716491

theorem tailTrace_2105608 : CollatzResearch.WordTrace tailWord_2105608 prefixEnd_2105608 1081188973952303032716491 := by
  unfold tailWord_2105608
  simp only [CollatzResearch.WordTrace]
  refine ⟨38398916477874650030778739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51198555303832866707704985 38398916477874650030778739)
  ·
    refine ⟨57598374716811975046168109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38398916477874650030778739 57598374716811975046168109)
    ·
      refine ⟨21599390518804490642313041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57598374716811975046168109 21599390518804490642313041)
      ·
        refine ⟨16199542889103367981734781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21599390518804490642313041 16199542889103367981734781)
        ·
          refine ⟨6074828583413762993150543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16199542889103367981734781 6074828583413762993150543)
          ·
            refine ⟨9112242875120644489725815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6074828583413762993150543 9112242875120644489725815)
            ·
              refine ⟨13668364312680966734588723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9112242875120644489725815 13668364312680966734588723)
              ·
                refine ⟨20502546469021450101883085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13668364312680966734588723 20502546469021450101883085)
                ·
                  refine ⟨7688454925883043788206157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20502546469021450101883085 7688454925883043788206157)
                  ·
                    refine ⟨2883170597206141420577309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7688454925883043788206157 2883170597206141420577309)
                    ·
                      refine ⟨1081188973952303032716491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2883170597206141420577309 1081188973952303032716491)
                      ·
                        rfl

theorem cell23_2105608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_2105608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105608 prefixEnd_2105608 := by exact prefixLift 2105608
  have htrace : WordTrace (prefixWord ++ tailWord_2105608) baseStart_2105608 baseEnd_2105608 := by
    simpa [prefixWord, tailWord_2105608, baseEnd_2105608] using wordTrace_append hprefix tailTrace_2105608
  have hstable : (prefixWord ++ tailWord_2105608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105608).length < 2 ^ (prefixWord ++ tailWord_2105608).sum := by decide
  have hdescent : baseEnd_2105608 < baseStart_2105608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105621 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 2, 2, 5]
def baseStart_2105621 : Nat := 118140960795 + 2105621 * 2 ^ 59
def prefixEnd_2105621 : Nat := 4983230072969 + 3 ^ 40 * 2105621 * 2
def baseEnd_2105621 : Nat := 1081195649200811481853931

theorem tailTrace_2105621 : CollatzResearch.WordTrace tailWord_2105621 prefixEnd_2105621 1081195649200811481853931 := by
  unfold tailWord_2105621
  simp only [CollatzResearch.WordTrace]
  refine ⟨76798307104702203281780717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51198871403134802187853811 76798307104702203281780717)
  ·
    refine ⟨28799365164263326230667769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76798307104702203281780717 28799365164263326230667769)
    ·
      refine ⟨21599523873197494673000827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28799365164263326230667769 21599523873197494673000827)
      ·
        refine ⟨32399285809796242009501241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21599523873197494673000827 32399285809796242009501241)
        ·
          refine ⟨24299464357347181507125931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32399285809796242009501241 24299464357347181507125931)
          ·
            refine ⟨36449196536020772260688897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24299464357347181507125931 36449196536020772260688897)
            ·
              refine ⟨27336897402015579195516673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36449196536020772260688897 27336897402015579195516673)
              ·
                refine ⟨20502673051511684396637505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27336897402015579195516673 20502673051511684396637505)
                ·
                  refine ⟨15377004788633763297478129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20502673051511684396637505 15377004788633763297478129)
                  ·
                    refine ⟨11532753591475322473108597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15377004788633763297478129 11532753591475322473108597)
                    ·
                      refine ⟨1081195649200811481853931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11532753591475322473108597 1081195649200811481853931)
                      ·
                        rfl

theorem cell23_2105621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_2105621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105621 prefixEnd_2105621 := by exact prefixLift 2105621
  have htrace : WordTrace (prefixWord ++ tailWord_2105621) baseStart_2105621 baseEnd_2105621 := by
    simpa [prefixWord, tailWord_2105621, baseEnd_2105621] using wordTrace_append hprefix tailTrace_2105621
  have hstable : (prefixWord ++ tailWord_2105621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105621).length < 2 ^ (prefixWord ++ tailWord_2105621).sum := by decide
  have hdescent : baseEnd_2105621 < baseStart_2105621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105639 : List Nat := [1, 1, 8, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_2105639 : Nat := 118140960795 + 2105639 * 2 ^ 59
def prefixEnd_2105639 : Nat := 4983230072969 + 3 ^ 40 * 2105639 * 2
def baseEnd_2105639 : Nat := 1081204891852592411428849

theorem tailTrace_2105639 : CollatzResearch.WordTrace tailWord_2105639 prefixEnd_2105639 1081204891852592411428849 := by
  unfold tailWord_2105639
  simp only [CollatzResearch.WordTrace]
  refine ⟨76798963618636992355935971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51199309079091328237290647 76798963618636992355935971)
  ·
    refine ⟨115198445427955488533903957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76798963618636992355935971 115198445427955488533903957)
    ·
      refine ⟨1349981782358853381256687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 115198445427955488533903957 1349981782358853381256687)
      ·
        refine ⟨2024972673538280071885031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1349981782358853381256687 2024972673538280071885031)
        ·
          refine ⟨3037459010307420107827547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2024972673538280071885031 3037459010307420107827547)
          ·
            refine ⟨4556188515461130161741321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3037459010307420107827547 4556188515461130161741321)
            ·
              refine ⟨3417141386595847621305991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4556188515461130161741321 3417141386595847621305991)
              ·
                refine ⟨5125712079893771431958987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3417141386595847621305991 5125712079893771431958987)
                ·
                  refine ⟨7688568119840657147938481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5125712079893771431958987 7688568119840657147938481)
                  ·
                    refine ⟨5766426089880492860953861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7688568119840657147938481 5766426089880492860953861)
                    ·
                      refine ⟨1081204891852592411428849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5766426089880492860953861 1081204891852592411428849)
                      ·
                        rfl

theorem cell23_2105639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_2105639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105639 prefixEnd_2105639 := by exact prefixLift 2105639
  have htrace : WordTrace (prefixWord ++ tailWord_2105639) baseStart_2105639 baseEnd_2105639 := by
    simpa [prefixWord, tailWord_2105639, baseEnd_2105639] using wordTrace_append hprefix tailTrace_2105639
  have hstable : (prefixWord ++ tailWord_2105639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105639).length < 2 ^ (prefixWord ++ tailWord_2105639).sum := by decide
  have hdescent : baseEnd_2105639 < baseStart_2105639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105642 : List Nat := [3, 1, 4, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_2105642 : Nat := 118140960795 + 2105642 * 2 ^ 59
def prefixEnd_2105642 : Nat := 4983230072969 + 3 ^ 40 * 2105642 * 2
def baseEnd_2105642 : Nat := 1081206432294555899691335

theorem tailTrace_2105642 : CollatzResearch.WordTrace tailWord_2105642 prefixEnd_2105642 1081206432294555899691335 := by
  unfold tailWord_2105642
  simp only [CollatzResearch.WordTrace]
  refine ⟨19199768259406530967073795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51199382025084082578863453 19199768259406530967073795)
  ·
    refine ⟨28799652389109796450610693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19199768259406530967073795 28799652389109796450610693)
    ·
      refine ⟨5399934822958086834489505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28799652389109796450610693 5399934822958086834489505)
      ·
        refine ⟨4049951117218565125867129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5399934822958086834489505 4049951117218565125867129)
        ·
          refine ⟨3037463337913923844400347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4049951117218565125867129 3037463337913923844400347)
          ·
            refine ⟨4556195006870885766600521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3037463337913923844400347 4556195006870885766600521)
            ·
              refine ⟨3417146255153164324950391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4556195006870885766600521 3417146255153164324950391)
              ·
                refine ⟨5125719382729746487425587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3417146255153164324950391 5125719382729746487425587)
                ·
                  refine ⟨7688579074094619731138381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5125719382729746487425587 7688579074094619731138381)
                  ·
                    refine ⟨2883217152785482399176893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7688579074094619731138381 2883217152785482399176893)
                    ·
                      refine ⟨1081206432294555899691335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2883217152785482399176893 1081206432294555899691335)
                      ·
                        rfl

theorem cell23_2105642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_2105642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105642 prefixEnd_2105642 := by exact prefixLift 2105642
  have htrace : WordTrace (prefixWord ++ tailWord_2105642) baseStart_2105642 baseEnd_2105642 := by
    simpa [prefixWord, tailWord_2105642, baseEnd_2105642] using wordTrace_append hprefix tailTrace_2105642
  have hstable : (prefixWord ++ tailWord_2105642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105642).length < 2 ^ (prefixWord ++ tailWord_2105642).sum := by decide
  have hdescent : baseEnd_2105642 < baseStart_2105642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105652 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 3, 3, 2]
def baseStart_2105652 : Nat := 118140960795 + 2105652 * 2 ^ 59
def prefixEnd_2105652 : Nat := 4983230072969 + 3 ^ 40 * 2105652 * 2
def baseEnd_2105652 : Nat := 1081211567101100860566289

theorem tailTrace_2105652 : CollatzResearch.WordTrace tailWord_2105652 prefixEnd_2105652 1081211567101100860566289 := by
  unfold tailWord_2105652
  simp only [CollatzResearch.WordTrace]
  refine ⟨38399718883794947788079605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51199625178393263717439473 38399718883794947788079605)
  ·
    refine ⟨3599973645355776355132463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38399718883794947788079605 3599973645355776355132463)
    ·
      refine ⟨5399960468033664532698695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3599973645355776355132463 5399960468033664532698695)
      ·
        refine ⟨8099940702050496799048043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5399960468033664532698695 8099940702050496799048043)
        ·
          refine ⟨12149911053075745198572065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8099940702050496799048043 12149911053075745198572065)
          ·
            refine ⟨9112433289806808898929049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12149911053075745198572065 9112433289806808898929049)
            ·
              refine ⟨6834324967355106674196787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9112433289806808898929049 6834324967355106674196787)
              ·
                refine ⟨10251487451032660011295181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6834324967355106674196787 10251487451032660011295181)
                ·
                  refine ⟨3844307794137247504235693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10251487451032660011295181 3844307794137247504235693)
                  ·
                    refine ⟨1441615422801467814088385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3844307794137247504235693 1441615422801467814088385)
                    ·
                      refine ⟨1081211567101100860566289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1441615422801467814088385 1081211567101100860566289)
                      ·
                        rfl

theorem cell23_2105652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_2105652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105652 prefixEnd_2105652 := by exact prefixLift 2105652
  have htrace : WordTrace (prefixWord ++ tailWord_2105652) baseStart_2105652 baseEnd_2105652 := by
    simpa [prefixWord, tailWord_2105652, baseEnd_2105652] using wordTrace_append hprefix tailTrace_2105652
  have hstable : (prefixWord ++ tailWord_2105652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105652).length < 2 ^ (prefixWord ++ tailWord_2105652).sum := by decide
  have hdescent : baseEnd_2105652 < baseStart_2105652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105671 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 9]
def baseStart_2105671 : Nat := 118140960795 + 2105671 * 2 ^ 59
def prefixEnd_2105671 : Nat := 4983230072969 + 3 ^ 40 * 2105671 * 2
def baseEnd_2105671 : Nat := 120135702581504031803189

theorem tailTrace_2105671 : CollatzResearch.WordTrace tailWord_2105671 prefixEnd_2105671 120135702581504031803189 := by
  unfold tailWord_2105671
  simp only [CollatzResearch.WordTrace]
  refine ⟨76800130754521061821100867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51200087169680707880733911 76800130754521061821100867)
  ·
    refine ⟨115200196131781592731651301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76800130754521061821100867 115200196131781592731651301)
    ·
      refine ⟨21600036774709048637184619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115200196131781592731651301 21600036774709048637184619)
      ·
        refine ⟨32400055162063572955776929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21600036774709048637184619 32400055162063572955776929)
        ·
          refine ⟨24300041371547679716832697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32400055162063572955776929 24300041371547679716832697)
          ·
            refine ⟨18225031028660759787624523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24300041371547679716832697 18225031028660759787624523)
            ·
              refine ⟨27337546542991139681436785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18225031028660759787624523 27337546542991139681436785)
              ·
                refine ⟨20503159907243354761077589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27337546542991139681436785 20503159907243354761077589)
                ·
                  refine ⟨120135702581504031803189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20503159907243354761077589 120135702581504031803189)
                  ·
                    rfl

theorem cell23_2105671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 9].length) (baseStart_2105671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105671 prefixEnd_2105671 := by exact prefixLift 2105671
  have htrace : WordTrace (prefixWord ++ tailWord_2105671) baseStart_2105671 baseEnd_2105671 := by
    simpa [prefixWord, tailWord_2105671, baseEnd_2105671] using wordTrace_append hprefix tailTrace_2105671
  have hstable : (prefixWord ++ tailWord_2105671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105671).length < 2 ^ (prefixWord ++ tailWord_2105671).sum := by decide
  have hdescent : baseEnd_2105671 < baseStart_2105671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105699 : List Nat := [1, 1, 1, 5, 2, 1, 5, 1, 2, 2, 2]
def baseStart_2105699 : Nat := 118140960795 + 2105699 * 2 ^ 59
def prefixEnd_2105699 : Nat := 4983230072969 + 3 ^ 40 * 2105699 * 2
def baseEnd_2105699 : Nat := 1081235700691862176678573

theorem tailTrace_2105699 : CollatzResearch.WordTrace tailWord_2105699 prefixEnd_2105699 1081235700691862176678573 := by
  unfold tailWord_2105699
  simp only [CollatzResearch.WordTrace]
  refine ⟨76801151998419622603120151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51200767998946415068746767 76801151998419622603120151)
  ·
    refine ⟨115201727997629433904680227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76801151998419622603120151 115201727997629433904680227)
    ·
      refine ⟨172802591996444150857020341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115201727997629433904680227 172802591996444150857020341)
      ·
        refine ⟨16200242999666639142845657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 172802591996444150857020341 16200242999666639142845657)
        ·
          refine ⟨12150182249749979357134243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16200242999666639142845657 12150182249749979357134243)
          ·
            refine ⟨18225273374624969035701365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12150182249749979357134243 18225273374624969035701365)
            ·
              refine ⟨1708619378871090847097003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18225273374624969035701365 1708619378871090847097003)
              ·
                refine ⟨2562929068306636270645505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1708619378871090847097003 2562929068306636270645505)
                ·
                  refine ⟨1922196801229977202984129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2562929068306636270645505 1922196801229977202984129)
                  ·
                    refine ⟨1441647600922482902238097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1922196801229977202984129 1441647600922482902238097)
                    ·
                      refine ⟨1081235700691862176678573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1441647600922482902238097 1081235700691862176678573)
                      ·
                        rfl

theorem cell23_2105699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_2105699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105699 prefixEnd_2105699 := by exact prefixLift 2105699
  have htrace : WordTrace (prefixWord ++ tailWord_2105699) baseStart_2105699 baseEnd_2105699 := by
    simpa [prefixWord, tailWord_2105699, baseEnd_2105699] using wordTrace_append hprefix tailTrace_2105699
  have hstable : (prefixWord ++ tailWord_2105699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105699).length < 2 ^ (prefixWord ++ tailWord_2105699).sum := by decide
  have hdescent : baseEnd_2105699 < baseStart_2105699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105711 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 7]
def baseStart_2105711 : Nat := 118140960795 + 2105711 * 2 ^ 59
def prefixEnd_2105711 : Nat := 4983230072969 + 3 ^ 40 * 2105711 * 2
def baseEnd_2105711 : Nat := 1081241862459716129728517

theorem tailTrace_2105711 : CollatzResearch.WordTrace tailWord_2105711 prefixEnd_2105711 1081241862459716129728517 := by
  unfold tailWord_2105711
  simp only [CollatzResearch.WordTrace]
  refine ⟨76801589674376148652556987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51201059782917432435037991 76801589674376148652556987)
  ·
    refine ⟨115202384511564222978835481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76801589674376148652556987 115202384511564222978835481)
    ·
      refine ⟨86401788383673167234126611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115202384511564222978835481 86401788383673167234126611)
      ·
        refine ⟨129602682575509750851189917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86401788383673167234126611 129602682575509750851189917)
        ·
          refine ⟨48601005965816156569196219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129602682575509750851189917 48601005965816156569196219)
          ·
            refine ⟨72901508948724234853794329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48601005965816156569196219 72901508948724234853794329)
            ·
              refine ⟨54676131711543176140345747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72901508948724234853794329 54676131711543176140345747)
              ·
                refine ⟨82014197567314764210518621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54676131711543176140345747 82014197567314764210518621)
                ·
                  refine ⟨30755324087743036578944483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82014197567314764210518621 30755324087743036578944483)
                  ·
                    refine ⟨46132986131614554868416725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30755324087743036578944483 46132986131614554868416725)
                    ·
                      refine ⟨1081241862459716129728517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46132986131614554868416725 1081241862459716129728517)
                      ·
                        rfl

theorem cell23_2105711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_2105711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105711 prefixEnd_2105711 := by exact prefixLift 2105711
  have htrace : WordTrace (prefixWord ++ tailWord_2105711) baseStart_2105711 baseEnd_2105711 := by
    simpa [prefixWord, tailWord_2105711, baseEnd_2105711] using wordTrace_append hprefix tailTrace_2105711
  have hstable : (prefixWord ++ tailWord_2105711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105711).length < 2 ^ (prefixWord ++ tailWord_2105711).sum := by decide
  have hdescent : baseEnd_2105711 < baseStart_2105711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105750 : List Nat := [5, 3, 1, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_2105750 : Nat := 118140960795 + 2105750 * 2 ^ 59
def prefixEnd_2105750 : Nat := 4983230072969 + 3 ^ 40 * 2105750 * 2
def baseEnd_2105750 : Nat := 1081261888205241477140839

theorem tailTrace_2105750 : CollatzResearch.WordTrace tailWord_2105750 prefixEnd_2105750 1081261888205241477140839 := by
  unfold tailWord_2105750
  simp only [CollatzResearch.WordTrace]
  refine ⟨4800188257577178644576669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51202008080823238875484469 4800188257577178644576669)
  ·
    refine ⟨1800070596591441991716251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4800188257577178644576669 1800070596591441991716251)
    ·
      refine ⟨2700105894887162987574377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1800070596591441991716251 2700105894887162987574377)
      ·
        refine ⟨2025079421165372240680783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2700105894887162987574377 2025079421165372240680783)
        ·
          refine ⟨3037619131748058361021175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2025079421165372240680783 3037619131748058361021175)
          ·
            refine ⟨4556428697622087541531763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3037619131748058361021175 4556428697622087541531763)
            ·
              refine ⟨6834643046433131312297645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4556428697622087541531763 6834643046433131312297645)
              ·
                refine ⟨2562991142412424242111617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6834643046433131312297645 2562991142412424242111617)
                ·
                  refine ⟨1922243356809318181583713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2562991142412424242111617 1922243356809318181583713)
                  ·
                    refine ⟨1441682517606988636187785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1922243356809318181583713 1441682517606988636187785)
                    ·
                      refine ⟨1081261888205241477140839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1441682517606988636187785 1081261888205241477140839)
                      ·
                        rfl

theorem cell23_2105750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_2105750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105750 prefixEnd_2105750 := by exact prefixLift 2105750
  have htrace : WordTrace (prefixWord ++ tailWord_2105750) baseStart_2105750 baseEnd_2105750 := by
    simpa [prefixWord, tailWord_2105750, baseEnd_2105750] using wordTrace_append hprefix tailTrace_2105750
  have hstable : (prefixWord ++ tailWord_2105750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105750).length < 2 ^ (prefixWord ++ tailWord_2105750).sum := by decide
  have hdescent : baseEnd_2105750 < baseStart_2105750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105799 : List Nat := [1, 1, 4, 1, 1, 4, 4, 2, 1, 4]
def baseStart_2105799 : Nat := 118140960795 + 2105799 * 2 ^ 59
def prefixEnd_2105799 : Nat := 4983230072969 + 3 ^ 40 * 2105799 * 2
def baseEnd_2105799 : Nat := 360429016252437261809371

theorem tailTrace_2105799 : CollatzResearch.WordTrace tailWord_2105799 prefixEnd_2105799 360429016252437261809371 := by
  unfold tailWord_2105799
  simp only [CollatzResearch.WordTrace]
  refine ⟨76804799298057339681760451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51203199532038226454506967 76804799298057339681760451)
  ·
    refine ⟨115207198947086009522640677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76804799298057339681760451 115207198947086009522640677)
    ·
      refine ⟨21601349802578626785495127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115207198947086009522640677 21601349802578626785495127)
      ·
        refine ⟨32402024703867940178242691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21601349802578626785495127 32402024703867940178242691)
        ·
          refine ⟨48603037055801910267364037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32402024703867940178242691 48603037055801910267364037)
          ·
            refine ⟨9113069447962858175130757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48603037055801910267364037 9113069447962858175130757)
            ·
              refine ⟨1708700521493035907837017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9113069447962858175130757 1708700521493035907837017)
              ·
                refine ⟨1281525391119776930877763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1708700521493035907837017 1281525391119776930877763)
                ·
                  refine ⟨1922288086679665396316645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1281525391119776930877763 1922288086679665396316645)
                  ·
                    refine ⟨360429016252437261809371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1922288086679665396316645 360429016252437261809371)
                    ·
                      rfl

theorem cell23_2105799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_2105799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105799 prefixEnd_2105799 := by exact prefixLift 2105799
  have htrace : WordTrace (prefixWord ++ tailWord_2105799) baseStart_2105799 baseEnd_2105799 := by
    simpa [prefixWord, tailWord_2105799, baseEnd_2105799] using wordTrace_append hprefix tailTrace_2105799
  have hstable : (prefixWord ++ tailWord_2105799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105799).length < 2 ^ (prefixWord ++ tailWord_2105799).sum := by decide
  have hdescent : baseEnd_2105799 < baseStart_2105799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105818 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7]
def baseStart_2105818 : Nat := 118140960795 + 2105818 * 2 ^ 59
def prefixEnd_2105818 : Nat := 4983230072969 + 3 ^ 40 * 2105818 * 2
def baseEnd_2105818 : Nat := 1081296804889747211090525

theorem tailTrace_2105818 : CollatzResearch.WordTrace tailWord_2105818 prefixEnd_2105818 1081296804889747211090525 := by
  unfold tailWord_2105818
  simp only [CollatzResearch.WordTrace]
  refine ⟨19201373071247126481675527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51203661523325670617801405 19201373071247126481675527)
  ·
    refine ⟨28802059606870689722513291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19201373071247126481675527 28802059606870689722513291)
    ·
      refine ⟨43203089410306034583769937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28802059606870689722513291 43203089410306034583769937)
      ·
        refine ⟨32402317057729525937827453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43203089410306034583769937 32402317057729525937827453)
        ·
          refine ⟨12150868896648572226685295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32402317057729525937827453 12150868896648572226685295)
          ·
            refine ⟨18226303344972858340027943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12150868896648572226685295 18226303344972858340027943)
            ·
              refine ⟨27339455017459287510041915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18226303344972858340027943 27339455017459287510041915)
              ·
                refine ⟨41009182526188931265062873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27339455017459287510041915 41009182526188931265062873)
                ·
                  refine ⟨30756886894641698448797155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41009182526188931265062873 30756886894641698448797155)
                  ·
                    refine ⟨46135330341962547673195733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30756886894641698448797155 46135330341962547673195733)
                    ·
                      refine ⟨1081296804889747211090525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46135330341962547673195733 1081296804889747211090525)
                      ·
                        rfl

theorem cell23_2105818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_2105818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105818 prefixEnd_2105818 := by exact prefixLift 2105818
  have htrace : WordTrace (prefixWord ++ tailWord_2105818) baseStart_2105818 baseEnd_2105818 := by
    simpa [prefixWord, tailWord_2105818, baseEnd_2105818] using wordTrace_append hprefix tailTrace_2105818
  have hstable : (prefixWord ++ tailWord_2105818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105818).length < 2 ^ (prefixWord ++ tailWord_2105818).sum := by decide
  have hdescent : baseEnd_2105818 < baseStart_2105818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105825 : List Nat := [1, 2, 3, 1, 2, 2, 2, 4, 1, 5]
def baseStart_2105825 : Nat := 118140960795 + 2105825 * 2 ^ 59
def prefixEnd_2105825 : Nat := 4983230072969 + 3 ^ 40 * 2105825 * 2
def baseEnd_2105825 : Nat := 360433466418109561234331

theorem tailTrace_2105825 : CollatzResearch.WordTrace tailWord_2105825 prefixEnd_2105825 360433466418109561234331 := by
  unfold tailWord_2105825
  simp only [CollatzResearch.WordTrace]
  refine ⟨76805747595963146122206929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51203831730642097414804619 76805747595963146122206929)
  ·
    refine ⟨57604310696972359591655197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76805747595963146122206929 57604310696972359591655197)
    ·
      refine ⟨21601616511364634846870699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57604310696972359591655197 21601616511364634846870699)
      ·
        refine ⟨32402424767046952270306049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21601616511364634846870699 32402424767046952270306049)
        ·
          refine ⟨24301818575285214202729537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32402424767046952270306049 24301818575285214202729537)
          ·
            refine ⟨18226363931463910652047153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24301818575285214202729537 18226363931463910652047153)
            ·
              refine ⟨13669772948597932989035365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18226363931463910652047153 13669772948597932989035365)
              ·
                refine ⟨2563082427862112435444131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13669772948597932989035365 2563082427862112435444131)
                ·
                  refine ⟨3844623641793168653166197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2563082427862112435444131 3844623641793168653166197)
                  ·
                    refine ⟨360433466418109561234331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3844623641793168653166197 360433466418109561234331)
                    ·
                      rfl

theorem cell23_2105825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_2105825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105825 prefixEnd_2105825 := by exact prefixLift 2105825
  have htrace : WordTrace (prefixWord ++ tailWord_2105825) baseStart_2105825 baseEnd_2105825 := by
    simpa [prefixWord, tailWord_2105825, baseEnd_2105825] using wordTrace_append hprefix tailTrace_2105825
  have hstable : (prefixWord ++ tailWord_2105825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105825).length < 2 ^ (prefixWord ++ tailWord_2105825).sum := by decide
  have hdescent : baseEnd_2105825 < baseStart_2105825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105832 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 1, 5, 2]
def baseStart_2105832 : Nat := 118140960795 + 2105832 * 2 ^ 59
def prefixEnd_2105832 : Nat := 4983230072969 + 3 ^ 40 * 2105832 * 2
def baseEnd_2105832 : Nat := 1081303993618910156315461

theorem tailTrace_2105832 : CollatzResearch.WordTrace tailWord_2105832 prefixEnd_2105832 1081303993618910156315461 := by
  unfold tailWord_2105832
  simp only [CollatzResearch.WordTrace]
  refine ⟨38403001453468893158855875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51204001937958524211807833 38403001453468893158855875)
  ·
    refine ⟨57604502180203339738283813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38403001453468893158855875 57604502180203339738283813)
    ·
      refine ⟨10800844158788126200928215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57604502180203339738283813 10800844158788126200928215)
      ·
        refine ⟨16201266238182189301392323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10800844158788126200928215 16201266238182189301392323)
        ·
          refine ⟨24301899357273283952088485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16201266238182189301392323 24301899357273283952088485)
          ·
            refine ⟨4556606129488740741016591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24301899357273283952088485 4556606129488740741016591)
            ·
              refine ⟨6834909194233111111524887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4556606129488740741016591 6834909194233111111524887)
              ·
                refine ⟨10252363791349666667287331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6834909194233111111524887 10252363791349666667287331)
                ·
                  refine ⟨15378545687024500000930997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10252363791349666667287331 15378545687024500000930997)
                  ·
                    refine ⟨1441738658158546875087281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15378545687024500000930997 1441738658158546875087281)
                    ·
                      refine ⟨1081303993618910156315461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1441738658158546875087281 1081303993618910156315461)
                      ·
                        rfl

theorem cell23_2105832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_2105832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105832 prefixEnd_2105832 := by exact prefixLift 2105832
  have htrace : WordTrace (prefixWord ++ tailWord_2105832) baseStart_2105832 baseEnd_2105832 := by
    simpa [prefixWord, tailWord_2105832, baseEnd_2105832] using wordTrace_append hprefix tailTrace_2105832
  have hstable : (prefixWord ++ tailWord_2105832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105832).length < 2 ^ (prefixWord ++ tailWord_2105832).sum := by decide
  have hdescent : baseEnd_2105832 < baseStart_2105832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105855 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 4, 4]
def baseStart_2105855 : Nat := 118140960795 + 2105855 * 2 ^ 59
def prefixEnd_2105855 : Nat := 4983230072969 + 3 ^ 40 * 2105855 * 2
def baseEnd_2105855 : Nat := 360438601224654522109285

theorem tailTrace_2105855 : CollatzResearch.WordTrace tailWord_2105855 prefixEnd_2105855 360438601224654522109285 := by
  unfold tailWord_2105855
  simp only [CollatzResearch.WordTrace]
  refine ⟨76806841785854461245799019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51204561190569640830532679 76806841785854461245799019)
  ·
    refine ⟨115210262678781691868698529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76806841785854461245799019 115210262678781691868698529)
    ·
      refine ⟨86407697009086268901523897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115210262678781691868698529 86407697009086268901523897)
      ·
        refine ⟨64805772756814701676142923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86407697009086268901523897 64805772756814701676142923)
        ·
          refine ⟨97208659135222052514214385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64805772756814701676142923 97208659135222052514214385)
          ·
            refine ⟨72906494351416539385660789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97208659135222052514214385 72906494351416539385660789)
            ·
              refine ⟨6834983845445300567405699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72906494351416539385660789 6834983845445300567405699)
              ·
                refine ⟨10252475768167950851108549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6834983845445300567405699 10252475768167950851108549)
                ·
                  refine ⟨1922339206531490784582853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10252475768167950851108549 1922339206531490784582853)
                  ·
                    refine ⟨360438601224654522109285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1922339206531490784582853 360438601224654522109285)
                    ·
                      rfl

theorem cell23_2105855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 4].length) (baseStart_2105855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105855 prefixEnd_2105855 := by exact prefixLift 2105855
  have htrace : WordTrace (prefixWord ++ tailWord_2105855) baseStart_2105855 baseEnd_2105855 := by
    simpa [prefixWord, tailWord_2105855, baseEnd_2105855] using wordTrace_append hprefix tailTrace_2105855
  have hstable : (prefixWord ++ tailWord_2105855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105855).length < 2 ^ (prefixWord ++ tailWord_2105855).sum := by decide
  have hdescent : baseEnd_2105855 < baseStart_2105855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105865 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 3, 2, 3]
def baseStart_2105865 : Nat := 118140960795 + 2105865 * 2 ^ 59
def prefixEnd_2105865 : Nat := 4983230072969 + 3 ^ 40 * 2105865 * 2
def baseEnd_2105865 : Nat := 1081320938480508527202809

theorem tailTrace_2105865 : CollatzResearch.WordTrace tailWord_2105865 prefixEnd_2105865 1081320938480508527202809 := by
  unfold tailWord_2105865
  simp only [CollatzResearch.WordTrace]
  refine ⟨76807206515818232953663049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51204804343878821969108699 76807206515818232953663049)
  ·
    refine ⟨57605404886863674715247287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76807206515818232953663049 57605404886863674715247287)
    ·
      refine ⟨86408107330295512072870931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57605404886863674715247287 86408107330295512072870931)
      ·
        refine ⟨129612160995443268109306397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86408107330295512072870931 129612160995443268109306397)
        ·
          refine ⟨48604560373291225540989899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129612160995443268109306397 48604560373291225540989899)
          ·
            refine ⟨72906840559936838311484849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48604560373291225540989899 72906840559936838311484849)
            ·
              refine ⟨54680130419952628733613637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72906840559936838311484849 54680130419952628733613637)
              ·
                refine ⟨10252524453741117887552557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54680130419952628733613637 10252524453741117887552557)
                ·
                  refine ⟨3844696670152919207832209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10252524453741117887552557 3844696670152919207832209)
                  ·
                    refine ⟨2883522502614689405874157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3844696670152919207832209 2883522502614689405874157)
                    ·
                      refine ⟨1081320938480508527202809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2883522502614689405874157 1081320938480508527202809)
                      ·
                        rfl

theorem cell23_2105865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 2, 3].length) (baseStart_2105865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105865 prefixEnd_2105865 := by exact prefixLift 2105865
  have htrace : WordTrace (prefixWord ++ tailWord_2105865) baseStart_2105865 baseEnd_2105865 := by
    simpa [prefixWord, tailWord_2105865, baseEnd_2105865] using wordTrace_append hprefix tailTrace_2105865
  have hstable : (prefixWord ++ tailWord_2105865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105865).length < 2 ^ (prefixWord ++ tailWord_2105865).sum := by decide
  have hdescent : baseEnd_2105865 < baseStart_2105865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105882 : List Nat := [3, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3]
def baseStart_2105882 : Nat := 118140960795 + 2105882 * 2 ^ 59
def prefixEnd_2105882 : Nat := 4983230072969 + 3 ^ 40 * 2105882 * 2
def baseEnd_2105882 : Nat := 1081329667651634960690231

theorem tailTrace_2105882 : CollatzResearch.WordTrace tailWord_2105882 prefixEnd_2105882 1081329667651634960690231 := by
  unfold tailWord_2105882
  simp only [CollatzResearch.WordTrace]
  refine ⟨19201956639189161214257975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51205217704504429904687933 19201956639189161214257975)
  ·
    refine ⟨28802934958783741821386963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19201956639189161214257975 28802934958783741821386963)
    ·
      refine ⟨43204402438175612732080445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28802934958783741821386963 43204402438175612732080445)
      ·
        refine ⟨16201650914315854774530167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43204402438175612732080445 16201650914315854774530167)
        ·
          refine ⟨24302476371473782161795251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16201650914315854774530167 24302476371473782161795251)
          ·
            refine ⟨36453714557210673242692877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24302476371473782161795251 36453714557210673242692877)
            ·
              refine ⟨13670142958954002466009829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36453714557210673242692877 13670142958954002466009829)
              ·
                refine ⟨2563151804803875462376843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13670142958954002466009829 2563151804803875462376843)
                ·
                  refine ⟨3844727707205813193565265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2563151804803875462376843 3844727707205813193565265)
                  ·
                    refine ⟨2883545780404359895173949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3844727707205813193565265 2883545780404359895173949)
                    ·
                      refine ⟨1081329667651634960690231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2883545780404359895173949 1081329667651634960690231)
                      ·
                        rfl

theorem cell23_2105882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_2105882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105882 prefixEnd_2105882 := by exact prefixLift 2105882
  have htrace : WordTrace (prefixWord ++ tailWord_2105882) baseStart_2105882 baseEnd_2105882 := by
    simpa [prefixWord, tailWord_2105882, baseEnd_2105882] using wordTrace_append hprefix tailTrace_2105882
  have hstable : (prefixWord ++ tailWord_2105882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105882).length < 2 ^ (prefixWord ++ tailWord_2105882).sum := by decide
  have hdescent : baseEnd_2105882 < baseStart_2105882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105885 : List Nat := [1, 4, 2, 2, 1, 3, 1, 9]
def baseStart_2105885 : Nat := 118140960795 + 2105885 * 2 ^ 59
def prefixEnd_2105885 : Nat := 4983230072969 + 3 ^ 40 * 2105885 * 2
def baseEnd_2105885 : Nat := 40049304003466609220471

theorem tailTrace_2105885 : CollatzResearch.WordTrace tailWord_2105885 prefixEnd_2105885 40049304003466609220471 := by
  unfold tailWord_2105885
  simp only [CollatzResearch.WordTrace]
  refine ⟨76807935975745776369391109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51205290650497184246260739 76807935975745776369391109)
  ·
    refine ⟨14401487995452333069260833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76807935975745776369391109 14401487995452333069260833)
    ·
      refine ⟨10801115996589249801945625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14401487995452333069260833 10801115996589249801945625)
      ·
        refine ⟨8100836997441937351459219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10801115996589249801945625 8100836997441937351459219)
        ·
          refine ⟨12151255496162906027188829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8100836997441937351459219 12151255496162906027188829)
          ·
            refine ⟨4556720811061089760195811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12151255496162906027188829 4556720811061089760195811)
            ·
              refine ⟨6835081216591634640293717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4556720811061089760195811 6835081216591634640293717)
              ·
                refine ⟨40049304003466609220471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6835081216591634640293717 40049304003466609220471)
                ·
                  rfl

theorem cell23_2105885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 9].length) (baseStart_2105885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105885 prefixEnd_2105885 := by exact prefixLift 2105885
  have htrace : WordTrace (prefixWord ++ tailWord_2105885) baseStart_2105885 baseEnd_2105885 := by
    simpa [prefixWord, tailWord_2105885, baseEnd_2105885] using wordTrace_append hprefix tailTrace_2105885
  have hstable : (prefixWord ++ tailWord_2105885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105885).length < 2 ^ (prefixWord ++ tailWord_2105885).sum := by decide
  have hdescent : baseEnd_2105885 < baseStart_2105885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105902 : List Nat := [4, 1, 3, 1, 3, 2, 9]
def baseStart_2105902 : Nat := 118140960795 + 2105902 * 2 ^ 59
def prefixEnd_2105902 : Nat := 4983230072969 + 3 ^ 40 * 2105902 * 2
def baseEnd_2105902 : Nat := 13349875768700307190619

theorem tailTrace_2105902 : CollatzResearch.WordTrace tailWord_2105902 prefixEnd_2105902 13349875768700307190619 := by
  unfold tailWord_2105902
  simp only [CollatzResearch.WordTrace]
  refine ⟨9601069502085523534094995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51205704011122792181839973 9601069502085523534094995)
  ·
    refine ⟨14401604253128285301142493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9601069502085523534094995 14401604253128285301142493)
    ·
      refine ⟨5400601594923106987928435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14401604253128285301142493 5400601594923106987928435)
      ·
        refine ⟨8100902392384660481892653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5400601594923106987928435 8100902392384660481892653)
        ·
          refine ⟨3037838397144247680709745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8100902392384660481892653 3037838397144247680709745)
          ·
            refine ⟨2278378797858185760532309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3037838397144247680709745 2278378797858185760532309)
            ·
              refine ⟨13349875768700307190619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2278378797858185760532309 13349875768700307190619)
              ·
                rfl

theorem cell23_2105902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 9].length) (baseStart_2105902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105902 prefixEnd_2105902 := by exact prefixLift 2105902
  have htrace : WordTrace (prefixWord ++ tailWord_2105902) baseStart_2105902 baseEnd_2105902 := by
    simpa [prefixWord, tailWord_2105902, baseEnd_2105902] using wordTrace_append hprefix tailTrace_2105902
  have hstable : (prefixWord ++ tailWord_2105902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105902).length < 2 ^ (prefixWord ++ tailWord_2105902).sum := by decide
  have hdescent : baseEnd_2105902 < baseStart_2105902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
