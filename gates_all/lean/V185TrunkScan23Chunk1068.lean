import V185TrunkScan23Chunk1067

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6322000 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 4]
def baseStart_6322000 : Nat := 118140960795 + 6322000 * 2 ^ 59
def prefixEnd_6322000 : Nat := 4983230072969 + 3 ^ 40 * 6322000 * 2
def baseEnd_6322000 : Nat := 3246224697724370379625657

theorem tailTrace_6322000 : CollatzResearch.WordTrace tailWord_6322000 prefixEnd_6322000 3246224697724370379625657 := by
  unfold tailWord_6322000
  simp only [CollatzResearch.WordTrace]
  refine ⟨115291141548240593242437727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153721522064320790989916969 115291141548240593242437727)
  ·
    refine ⟨172936712322360889863656591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115291141548240593242437727 172936712322360889863656591)
    ·
      refine ⟨259405068483541334795484887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172936712322360889863656591 259405068483541334795484887)
      ·
        refine ⟨389107602725312002193227331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259405068483541334795484887 389107602725312002193227331)
        ·
          refine ⟨583661404087968003289840997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389107602725312002193227331 583661404087968003289840997)
          ·
            refine ⟨109436513266494000616845187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 583661404087968003289840997 109436513266494000616845187)
            ·
              refine ⟨164154769899741000925267781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109436513266494000616845187 164154769899741000925267781)
              ·
                refine ⟨30779019356201437673487709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164154769899741000925267781 30779019356201437673487709)
                ·
                  refine ⟨11542132258575539127557891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30779019356201437673487709 11542132258575539127557891)
                  ·
                    refine ⟨17313198387863308691336837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11542132258575539127557891 17313198387863308691336837)
                    ·
                      refine ⟨3246224697724370379625657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17313198387863308691336837 3246224697724370379625657)
                      ·
                        rfl

theorem cell23_6322000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 4].length) (baseStart_6322000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322000 prefixEnd_6322000 := by exact prefixLift 6322000
  have htrace : WordTrace (prefixWord ++ tailWord_6322000) baseStart_6322000 baseEnd_6322000 := by
    simpa [prefixWord, tailWord_6322000, baseEnd_6322000] using wordTrace_append hprefix tailTrace_6322000
  have hstable : (prefixWord ++ tailWord_6322000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322000).length < 2 ^ (prefixWord ++ tailWord_6322000).sum := by decide
  have hdescent : baseEnd_6322000 < baseStart_6322000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322010 : List Nat := [3, 1, 1, 2, 1, 3, 2, 3, 1, 6]
def baseStart_6322010 : Nat := 118140960795 + 6322010 * 2 ^ 59
def prefixEnd_6322010 : Nat := 4983230072969 + 3 ^ 40 * 6322010 * 2
def baseEnd_6322010 : Nat := 1082076610843638446833537

theorem tailTrace_6322010 : CollatzResearch.WordTrace tailWord_6322010 prefixEnd_6322010 1082076610843638446833537 := by
  unfold tailWord_6322010
  simp only [CollatzResearch.WordTrace]
  refine ⟨57645661956611239548184871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153721765217629972128492989 57645661956611239548184871)
  ·
    refine ⟨86468492934916859322277307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57645661956611239548184871 86468492934916859322277307)
    ·
      refine ⟨129702739402375288983415961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86468492934916859322277307 129702739402375288983415961)
      ·
        refine ⟨97277054551781466737561971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129702739402375288983415961 97277054551781466737561971)
        ·
          refine ⟨145915581827672200106342957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97277054551781466737561971 145915581827672200106342957)
          ·
            refine ⟨54718343185377075039878609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145915581827672200106342957 54718343185377075039878609)
            ·
              refine ⟨41038757389032806279908957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54718343185377075039878609 41038757389032806279908957)
              ·
                refine ⟨15389534020887302354965859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41038757389032806279908957 15389534020887302354965859)
                ·
                  refine ⟨23084301031330953532448789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15389534020887302354965859 23084301031330953532448789)
                  ·
                    refine ⟨1082076610843638446833537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23084301031330953532448789 1082076610843638446833537)
                    ·
                      rfl

theorem cell23_6322010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_6322010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322010 prefixEnd_6322010 := by exact prefixLift 6322010
  have htrace : WordTrace (prefixWord ++ tailWord_6322010) baseStart_6322010 baseEnd_6322010 := by
    simpa [prefixWord, tailWord_6322010, baseEnd_6322010] using wordTrace_append hprefix tailTrace_6322010
  have hstable : (prefixWord ++ tailWord_6322010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322010).length < 2 ^ (prefixWord ++ tailWord_6322010).sum := by decide
  have hdescent : baseEnd_6322010 < baseStart_6322010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322080 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 5]
def baseStart_6322080 : Nat := 118140960795 + 6322080 * 2 ^ 59
def prefixEnd_6322080 : Nat := 4983230072969 + 3 ^ 40 * 6322080 * 2
def baseEnd_6322080 : Nat := 3246265776176730066625289

theorem tailTrace_6322080 : CollatzResearch.WordTrace tailWord_6322080 prefixEnd_6322080 3246265776176730066625289 := by
  unfold tailWord_6322080
  simp only [CollatzResearch.WordTrace]
  refine ⟨115292600468095680073893847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153723467290794240098525129 115292600468095680073893847)
  ·
    refine ⟨172938900702143520110840771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115292600468095680073893847 172938900702143520110840771)
    ·
      refine ⟨259408351053215280166261157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172938900702143520110840771 259408351053215280166261157)
      ·
        refine ⟨48639065822477865031173967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259408351053215280166261157 48639065822477865031173967)
        ·
          refine ⟨72958598733716797546760951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48639065822477865031173967 72958598733716797546760951)
          ·
            refine ⟨109437898100575196320141427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72958598733716797546760951 109437898100575196320141427)
            ·
              refine ⟨164156847150862794480212141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109437898100575196320141427 164156847150862794480212141)
              ·
                refine ⟨61558817681573547930079553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164156847150862794480212141 61558817681573547930079553)
                ·
                  refine ⟨46169113261180160947559665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61558817681573547930079553 46169113261180160947559665)
                  ·
                    refine ⟨34626834945885120710669749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46169113261180160947559665 34626834945885120710669749)
                    ·
                      refine ⟨3246265776176730066625289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34626834945885120710669749 3246265776176730066625289)
                      ·
                        rfl

theorem cell23_6322080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_6322080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322080 prefixEnd_6322080 := by exact prefixLift 6322080
  have htrace : WordTrace (prefixWord ++ tailWord_6322080) baseStart_6322080 baseEnd_6322080 := by
    simpa [prefixWord, tailWord_6322080, baseEnd_6322080] using wordTrace_append hprefix tailTrace_6322080
  have hstable : (prefixWord ++ tailWord_6322080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322080).length < 2 ^ (prefixWord ++ tailWord_6322080).sum := by decide
  have hdescent : baseEnd_6322080 < baseStart_6322080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322088 : List Nat := [2, 1, 6, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_6322088 : Nat := 118140960795 + 6322088 * 2 ^ 59
def prefixEnd_6322088 : Nat := 4983230072969 + 3 ^ 40 * 6322088 * 2
def baseEnd_6322088 : Nat := 3246269884021966035325253

theorem tailTrace_6322088 : CollatzResearch.WordTrace tailWord_6322088 prefixEnd_6322088 3246269884021966035325253 := by
  unfold tailWord_6322088
  simp only [CollatzResearch.WordTrace]
  refine ⟨115292746360081188757039459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153723661813441585009385945 115292746360081188757039459)
  ·
    refine ⟨172939119540121783135559189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115292746360081188757039459 172939119540121783135559189)
    ·
      refine ⟨8106521228443208584479337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 172939119540121783135559189 8106521228443208584479337)
      ·
        refine ⟨6079890921332406438359503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8106521228443208584479337 6079890921332406438359503)
        ·
          refine ⟨9119836381998609657539255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6079890921332406438359503 9119836381998609657539255)
          ·
            refine ⟨13679754572997914486308883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9119836381998609657539255 13679754572997914486308883)
            ·
              refine ⟨20519631859496871729463325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13679754572997914486308883 20519631859496871729463325)
              ·
                refine ⟨7694861947311326898548747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20519631859496871729463325 7694861947311326898548747)
                ·
                  refine ⟨11542292920966990347823121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7694861947311326898548747 11542292920966990347823121)
                  ·
                    refine ⟨8656719690725242760867341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11542292920966990347823121 8656719690725242760867341)
                    ·
                      refine ⟨3246269884021966035325253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8656719690725242760867341 3246269884021966035325253)
                      ·
                        rfl

theorem cell23_6322088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_6322088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322088 prefixEnd_6322088 := by exact prefixLift 6322088
  have htrace : WordTrace (prefixWord ++ tailWord_6322088) baseStart_6322088 baseEnd_6322088 := by
    simpa [prefixWord, tailWord_6322088, baseEnd_6322088] using wordTrace_append hprefix tailTrace_6322088
  have hstable : (prefixWord ++ tailWord_6322088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322088).length < 2 ^ (prefixWord ++ tailWord_6322088).sum := by decide
  have hdescent : baseEnd_6322088 < baseStart_6322088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322101 : List Nat := [1, 3, 3, 2, 1, 2, 3, 2, 2, 1, 3]
def baseStart_6322101 : Nat := 118140960795 + 6322101 * 2 ^ 59
def prefixEnd_6322101 : Nat := 4983230072969 + 3 ^ 40 * 6322101 * 2
def baseEnd_6322101 : Nat := 3246276559270474484462693

theorem tailTrace_6322101 : CollatzResearch.WordTrace tailWord_6322101 prefixEnd_6322101 3246276559270474484462693 := by
  unfold tailWord_6322101
  simp only [CollatzResearch.WordTrace]
  refine ⟨230585966869115280734302157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153723977912743520489534771 230585966869115280734302157)
  ·
    refine ⟨86469737575918230275363309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230585966869115280734302157 86469737575918230275363309)
    ·
      refine ⟨32426151590969336353261241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86469737575918230275363309 32426151590969336353261241)
      ·
        refine ⟨24319613693227002264945931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32426151590969336353261241 24319613693227002264945931)
        ·
          refine ⟨36479420539840503397418897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24319613693227002264945931 36479420539840503397418897)
          ·
            refine ⟨27359565404880377548064173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36479420539840503397418897 27359565404880377548064173)
            ·
              refine ⟨10259837026830141580524065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27359565404880377548064173 10259837026830141580524065)
              ·
                refine ⟨7694877770122606185393049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10259837026830141580524065 7694877770122606185393049)
                ·
                  refine ⟨5771158327591954639044787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7694877770122606185393049 5771158327591954639044787)
                  ·
                    refine ⟨8656737491387931958567181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5771158327591954639044787 8656737491387931958567181)
                    ·
                      refine ⟨3246276559270474484462693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8656737491387931958567181 3246276559270474484462693)
                      ·
                        rfl

theorem cell23_6322101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_6322101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322101 prefixEnd_6322101 := by exact prefixLift 6322101
  have htrace : WordTrace (prefixWord ++ tailWord_6322101) baseStart_6322101 baseEnd_6322101 := by
    simpa [prefixWord, tailWord_6322101, baseEnd_6322101] using wordTrace_append hprefix tailTrace_6322101
  have hstable : (prefixWord ++ tailWord_6322101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322101).length < 2 ^ (prefixWord ++ tailWord_6322101).sum := by decide
  have hdescent : baseEnd_6322101 < baseStart_6322101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322107 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 5, 4, 2]
def baseStart_6322107 : Nat := 118140960795 + 6322107 * 2 ^ 59
def prefixEnd_6322107 : Nat := 4983230072969 + 3 ^ 40 * 6322107 * 2
def baseEnd_6322107 : Nat := 3246279640154401460987665

theorem tailTrace_6322107 : CollatzResearch.WordTrace tailWord_6322107 prefixEnd_6322107 3246279640154401460987665 := by
  unfold tailWord_6322107
  simp only [CollatzResearch.WordTrace]
  refine ⟨230586185707093543759020575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153724123804729029172680383 230586185707093543759020575)
  ·
    refine ⟨345879278560640315638530863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230586185707093543759020575 345879278560640315638530863)
    ·
      refine ⟨518818917840960473457796295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345879278560640315638530863 518818917840960473457796295)
      ·
        refine ⟨778228376761440710186694443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518818917840960473457796295 778228376761440710186694443)
        ·
          refine ⟨1167342565142161065280041665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778228376761440710186694443 1167342565142161065280041665)
          ·
            refine ⟨875506923856620798960031249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1167342565142161065280041665 875506923856620798960031249)
            ·
              refine ⟨656630192892465599220023437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 875506923856620798960031249 656630192892465599220023437)
              ·
                refine ⟨246236322334674599707508789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 656630192892465599220023437 246236322334674599707508789)
                ·
                  refine ⟨23084655218875743722578949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 246236322334674599707508789 23084655218875743722578949)
                  ·
                    refine ⟨4328372853539201947983553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23084655218875743722578949 4328372853539201947983553)
                    ·
                      refine ⟨3246279640154401460987665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4328372853539201947983553 3246279640154401460987665)
                      ·
                        rfl

theorem cell23_6322107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 4, 2].length) (baseStart_6322107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322107 prefixEnd_6322107 := by exact prefixLift 6322107
  have htrace : WordTrace (prefixWord ++ tailWord_6322107) baseStart_6322107 baseEnd_6322107 := by
    simpa [prefixWord, tailWord_6322107, baseEnd_6322107] using wordTrace_append hprefix tailTrace_6322107
  have hstable : (prefixWord ++ tailWord_6322107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322107).length < 2 ^ (prefixWord ++ tailWord_6322107).sum := by decide
  have hdescent : baseEnd_6322107 < baseStart_6322107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322177 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 4, 5]
def baseStart_6322177 : Nat := 118140960795 + 6322177 * 2 ^ 59
def prefixEnd_6322177 : Nat := 4983230072969 + 3 ^ 40 * 6322177 * 2
def baseEnd_6322177 : Nat := 1082105194600072062370781

theorem tailTrace_6322177 : CollatzResearch.WordTrace tailWord_6322177 prefixEnd_6322177 1082105194600072062370781 := by
  unfold tailWord_6322177
  simp only [CollatzResearch.WordTrace]
  refine ⟨230588738816839945714068785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153725825877893297142712523 230588738816839945714068785)
  ·
    refine ⟨172941554112629959285551589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230588738816839945714068785 172941554112629959285551589)
    ·
      refine ⟨32426541396118117366040923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172941554112629959285551589 32426541396118117366040923)
      ·
        refine ⟨48639812094177176049061385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32426541396118117366040923 48639812094177176049061385)
        ·
          refine ⟨36479859070632882036796039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48639812094177176049061385 36479859070632882036796039)
          ·
            refine ⟨54719788605949323055194059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36479859070632882036796039 54719788605949323055194059)
            ·
              refine ⟨82079682908923984582791089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54719788605949323055194059 82079682908923984582791089)
              ·
                refine ⟨61559762181692988437093317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82079682908923984582791089 61559762181692988437093317)
                ·
                  refine ⟨11542455409067435331954997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61559762181692988437093317 11542455409067435331954997)
                  ·
                    refine ⟨1082105194600072062370781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11542455409067435331954997 1082105194600072062370781)
                    ·
                      rfl

theorem cell23_6322177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_6322177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322177 prefixEnd_6322177 := by exact prefixLift 6322177
  have htrace : WordTrace (prefixWord ++ tailWord_6322177) baseStart_6322177 baseEnd_6322177 := by
    simpa [prefixWord, tailWord_6322177, baseEnd_6322177] using wordTrace_append hprefix tailTrace_6322177
  have hstable : (prefixWord ++ tailWord_6322177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322177).length < 2 ^ (prefixWord ++ tailWord_6322177).sum := by decide
  have hdescent : baseEnd_6322177 < baseStart_6322177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322215 : List Nat := [1, 1, 7, 1, 2, 2, 2, 2, 5]
def baseStart_6322215 : Nat := 118140960795 + 6322215 * 2 ^ 59
def prefixEnd_6322215 : Nat := 4983230072969 + 3 ^ 40 * 6322215 * 2
def baseEnd_6322215 : Nat := 360703899562787448715241

theorem tailTrace_6322215 : CollatzResearch.WordTrace tailWord_6322215 prefixEnd_6322215 360703899562787448715241 := by
  unfold tailWord_6322215
  simp only [CollatzResearch.WordTrace]
  refine ⟨230590124790702278203952099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153726749860468185469301399 230590124790702278203952099)
  ·
    refine ⟨345885187186053417305928149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230590124790702278203952099 345885187186053417305928149)
    ·
      refine ⟨8106684074673126968107691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 345885187186053417305928149 8106684074673126968107691)
      ·
        refine ⟨12160026112009690452161537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8106684074673126968107691 12160026112009690452161537)
        ·
          refine ⟨9120019584007267839121153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12160026112009690452161537 9120019584007267839121153)
          ·
            refine ⟨6840014688005450879340865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9120019584007267839121153 6840014688005450879340865)
            ·
              refine ⟨5130011016004088159505649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6840014688005450879340865 5130011016004088159505649)
              ·
                refine ⟨3847508262003066119629237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5130011016004088159505649 3847508262003066119629237)
                ·
                  refine ⟨360703899562787448715241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3847508262003066119629237 360703899562787448715241)
                  ·
                    rfl

theorem cell23_6322215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 5].length) (baseStart_6322215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322215 prefixEnd_6322215 := by exact prefixLift 6322215
  have htrace : WordTrace (prefixWord ++ tailWord_6322215) baseStart_6322215 baseEnd_6322215 := by
    simpa [prefixWord, tailWord_6322215, baseEnd_6322215] using wordTrace_append hprefix tailTrace_6322215
  have hstable : (prefixWord ++ tailWord_6322215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322215).length < 2 ^ (prefixWord ++ tailWord_6322215).sum := by decide
  have hdescent : baseEnd_6322215 < baseStart_6322215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322241 : List Nat := [1, 2, 5, 1, 2, 2, 1, 2, 3, 4]
def baseStart_6322241 : Nat := 118140960795 + 6322241 * 2 ^ 59
def prefixEnd_6322241 : Nat := 4983230072969 + 3 ^ 40 * 6322241 * 2
def baseEnd_6322241 : Nat := 1082116148854034645570683

theorem tailTrace_6322241 : CollatzResearch.WordTrace tailWord_6322241 prefixEnd_6322241 1082116148854034645570683 := by
  unfold tailWord_6322241
  simp only [CollatzResearch.WordTrace]
  refine ⟨230591073088608084644398577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153727382059072056429599051 230591073088608084644398577)
  ·
    refine ⟨172943304816456063483298933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230591073088608084644398577 172943304816456063483298933)
    ·
      refine ⟨16213434826542755951559275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172943304816456063483298933 16213434826542755951559275)
      ·
        refine ⟨24320152239814133927338913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16213434826542755951559275 24320152239814133927338913)
        ·
          refine ⟨18240114179860600445504185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24320152239814133927338913 18240114179860600445504185)
          ·
            refine ⟨13680085634895450334128139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18240114179860600445504185 13680085634895450334128139)
            ·
              refine ⟨20520128452343175501192209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13680085634895450334128139 20520128452343175501192209)
              ·
                refine ⟨15390096339257381625894157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20520128452343175501192209 15390096339257381625894157)
                ·
                  refine ⟨5771286127221518109710309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15390096339257381625894157 5771286127221518109710309)
                  ·
                    refine ⟨1082116148854034645570683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5771286127221518109710309 1082116148854034645570683)
                    ·
                      rfl

theorem cell23_6322241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_6322241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322241 prefixEnd_6322241 := by exact prefixLift 6322241
  have htrace : WordTrace (prefixWord ++ tailWord_6322241) baseStart_6322241 baseEnd_6322241 := by
    simpa [prefixWord, tailWord_6322241, baseEnd_6322241] using wordTrace_append hprefix tailTrace_6322241
  have hstable : (prefixWord ++ tailWord_6322241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322241).length < 2 ^ (prefixWord ++ tailWord_6322241).sum := by decide
  have hdescent : baseEnd_6322241 < baseStart_6322241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322281 : List Nat := [1, 2, 1, 1, 1, 5, 4, 1, 3, 1, 3]
def baseStart_6322281 : Nat := 118140960795 + 6322281 * 2 ^ 59
def prefixEnd_6322281 : Nat := 4983230072969 + 3 ^ 40 * 6322281 * 2
def baseEnd_6322281 : Nat := 3246368985788283780211865

theorem tailTrace_6322281 : CollatzResearch.WordTrace tailWord_6322281 prefixEnd_6322281 3246368985788283780211865 := by
  unfold tailWord_6322281
  simp only [CollatzResearch.WordTrace]
  refine ⟨230592532008463171475854697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153728354672308780983903131 230592532008463171475854697)
  ·
    refine ⟨172944399006347378606891023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230592532008463171475854697 172944399006347378606891023)
    ·
      refine ⟨259416598509521067910336535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172944399006347378606891023 259416598509521067910336535)
      ·
        refine ⟨389124897764281601865504803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259416598509521067910336535 389124897764281601865504803)
        ·
          refine ⟨583687346646422402798257205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389124897764281601865504803 583687346646422402798257205)
          ·
            refine ⟨54720688748102100262336613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 583687346646422402798257205 54720688748102100262336613)
            ·
              refine ⟨10260129140269143799188115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54720688748102100262336613 10260129140269143799188115)
              ·
                refine ⟨15390193710403715698782173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10260129140269143799188115 15390193710403715698782173)
                ·
                  refine ⟨5771322641401393387043315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15390193710403715698782173 5771322641401393387043315)
                  ·
                    refine ⟨8656983962102090080564973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5771322641401393387043315 8656983962102090080564973)
                    ·
                      refine ⟨3246368985788283780211865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8656983962102090080564973 3246368985788283780211865)
                      ·
                        rfl

theorem cell23_6322281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 1, 3].length) (baseStart_6322281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322281 prefixEnd_6322281 := by exact prefixLift 6322281
  have htrace : WordTrace (prefixWord ++ tailWord_6322281) baseStart_6322281 baseEnd_6322281 := by
    simpa [prefixWord, tailWord_6322281, baseEnd_6322281] using wordTrace_append hprefix tailTrace_6322281
  have hstable : (prefixWord ++ tailWord_6322281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322281).length < 2 ^ (prefixWord ++ tailWord_6322281).sum := by decide
  have hdescent : baseEnd_6322281 < baseStart_6322281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322301 : List Nat := [1, 4, 1, 1, 3, 3, 2, 2, 1, 5]
def baseStart_6322301 : Nat := 118140960795 + 6322301 * 2 ^ 59
def prefixEnd_6322301 : Nat := 4983230072969 + 3 ^ 40 * 6322301 * 2
def baseEnd_6322301 : Nat := 1082126418467124567320591

theorem tailTrace_6322301 : CollatzResearch.WordTrace tailWord_6322301 prefixEnd_6322301 1082126418467124567320591 := by
  unfold tailWord_6322301
  simp only [CollatzResearch.WordTrace]
  refine ⟨230593261468390714891582757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153728840978927143261055171 230593261468390714891582757)
  ·
    refine ⟨43236236525323259042171767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230593261468390714891582757 43236236525323259042171767)
    ·
      refine ⟨64854354787984888563257651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43236236525323259042171767 64854354787984888563257651)
      ·
        refine ⟨97281532181977332844886477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64854354787984888563257651 97281532181977332844886477)
        ·
          refine ⟨36480574568241499816832429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97281532181977332844886477 36480574568241499816832429)
          ·
            refine ⟨13680215463090562431312161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36480574568241499816832429 13680215463090562431312161)
            ·
              refine ⟨10260161597317921823484121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13680215463090562431312161 10260161597317921823484121)
              ·
                refine ⟨7695121197988441367613091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10260161597317921823484121 7695121197988441367613091)
                ·
                  refine ⟨11542681796982662051419637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7695121197988441367613091 11542681796982662051419637)
                  ·
                    refine ⟨1082126418467124567320591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11542681796982662051419637 1082126418467124567320591)
                    ·
                      rfl

theorem cell23_6322301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_6322301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322301 prefixEnd_6322301 := by exact prefixLift 6322301
  have htrace : WordTrace (prefixWord ++ tailWord_6322301) baseStart_6322301 baseEnd_6322301 := by
    simpa [prefixWord, tailWord_6322301, baseEnd_6322301] using wordTrace_append hprefix tailTrace_6322301
  have hstable : (prefixWord ++ tailWord_6322301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322301).length < 2 ^ (prefixWord ++ tailWord_6322301).sum := by decide
  have hdescent : baseEnd_6322301 < baseStart_6322301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322304 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 1, 8, 2]
def baseStart_6322304 : Nat := 118140960795 + 6322304 * 2 ^ 59
def prefixEnd_6322304 : Nat := 4983230072969 + 3 ^ 40 * 6322304 * 2
def baseEnd_6322304 : Nat := 3246380795843337190224259

theorem tailTrace_6322304 : CollatzResearch.WordTrace tailWord_6322304 prefixEnd_6322304 3246380795843337190224259 := by
  unfold tailWord_6322304
  simp only [CollatzResearch.WordTrace]
  refine ⟨115296685443689923201970983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153728913924919897602627977 115296685443689923201970983)
  ·
    refine ⟨172945028165534884802956475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115296685443689923201970983 172945028165534884802956475)
    ·
      refine ⟨259417542248302327204434713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172945028165534884802956475 259417542248302327204434713)
      ·
        refine ⟨194563156686226745403326035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259417542248302327204434713 194563156686226745403326035)
        ·
          refine ⟨291844735029340118104989053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194563156686226745403326035 291844735029340118104989053)
          ·
            refine ⟨109441775636002544289370895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291844735029340118104989053 109441775636002544289370895)
            ·
              refine ⟨164162663454003816434056343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109441775636002544289370895 164162663454003816434056343)
              ·
                refine ⟨246243995181005724651084515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164162663454003816434056343 246243995181005724651084515)
                ·
                  refine ⟨369365992771508586976626773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246243995181005724651084515 369365992771508586976626773)
                  ·
                    refine ⟨4328507727791116253632345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 369365992771508586976626773 4328507727791116253632345)
                    ·
                      refine ⟨3246380795843337190224259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4328507727791116253632345 3246380795843337190224259)
                      ·
                        rfl

theorem cell23_6322304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 8, 2].length) (baseStart_6322304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322304 prefixEnd_6322304 := by exact prefixLift 6322304
  have htrace : WordTrace (prefixWord ++ tailWord_6322304) baseStart_6322304 baseEnd_6322304 := by
    simpa [prefixWord, tailWord_6322304, baseEnd_6322304] using wordTrace_append hprefix tailTrace_6322304
  have hstable : (prefixWord ++ tailWord_6322304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322304).length < 2 ^ (prefixWord ++ tailWord_6322304).sum := by decide
  have hdescent : baseEnd_6322304 < baseStart_6322304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322326 : List Nat := [5, 3, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_6322326 : Nat := 118140960795 + 6322326 * 2 ^ 59
def prefixEnd_6322326 : Nat := 4983230072969 + 3 ^ 40 * 6322326 * 2
def baseEnd_6322326 : Nat := 1082130697472578701383053

theorem tailTrace_6322326 : CollatzResearch.WordTrace tailWord_6322326 prefixEnd_6322326 1082130697472578701383053 := by
  unfold tailWord_6322326
  simp only [CollatzResearch.WordTrace]
  refine ⟨14412135830831259010077677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153729448862200096107495221 14412135830831259010077677)
  ·
    refine ⟨5404550936561722128779129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14412135830831259010077677 5404550936561722128779129)
    ·
      refine ⟨4053413202421291596584347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5404550936561722128779129 4053413202421291596584347)
      ·
        refine ⟨6080119803631937394876521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4053413202421291596584347 6080119803631937394876521)
        ·
          refine ⟨4560089852723953046157391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6080119803631937394876521 4560089852723953046157391)
          ·
            refine ⟨6840134779085929569236087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4560089852723953046157391 6840134779085929569236087)
            ·
              refine ⟨10260202168628894353854131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6840134779085929569236087 10260202168628894353854131)
              ·
                refine ⟨15390303252943341530781197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10260202168628894353854131 15390303252943341530781197)
                ·
                  refine ⟨5771363719853753074042949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15390303252943341530781197 5771363719853753074042949)
                  ·
                    refine ⟨1082130697472578701383053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5771363719853753074042949 1082130697472578701383053)
                    ·
                      rfl

theorem cell23_6322326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_6322326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322326 prefixEnd_6322326 := by exact prefixLift 6322326
  have htrace : WordTrace (prefixWord ++ tailWord_6322326) baseStart_6322326 baseEnd_6322326 := by
    simpa [prefixWord, tailWord_6322326, baseEnd_6322326] using wordTrace_append hprefix tailTrace_6322326
  have hstable : (prefixWord ++ tailWord_6322326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322326).length < 2 ^ (prefixWord ++ tailWord_6322326).sum := by decide
  have hdescent : baseEnd_6322326 < baseStart_6322326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322394 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4]
def baseStart_6322394 : Nat := 118140960795 + 6322394 * 2 ^ 59
def prefixEnd_6322394 : Nat := 4983230072969 + 3 ^ 40 * 6322394 * 2
def baseEnd_6322394 : Nat := 3246427009102241838098845

theorem tailTrace_6322394 : CollatzResearch.WordTrace tailWord_6322394 prefixEnd_6322394 3246427009102241838098845 := by
  unfold tailWord_6322394
  simp only [CollatzResearch.WordTrace]
  refine ⟨57649163364263447943679559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153731102304702527849812157 57649163364263447943679559)
  ·
    refine ⟨86473745046395171915519339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57649163364263447943679559 86473745046395171915519339)
    ·
      refine ⟨129710617569592757873279009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86473745046395171915519339 129710617569592757873279009)
      ·
        refine ⟨97282963177194568404959257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129710617569592757873279009 97282963177194568404959257)
        ·
          refine ⟨72962222382895926303719443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97282963177194568404959257 72962222382895926303719443)
          ·
            refine ⟨109443333574343889455579165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72962222382895926303719443 109443333574343889455579165)
            ·
              refine ⟨41041250090378958545842187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109443333574343889455579165 41041250090378958545842187)
              ·
                refine ⟨61561875135568437818763281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41041250090378958545842187 61561875135568437818763281)
                ·
                  refine ⟨46171406351676328364072461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61561875135568437818763281 46171406351676328364072461)
                  ·
                    refine ⟨17314277381878623136527173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46171406351676328364072461 17314277381878623136527173)
                    ·
                      refine ⟨3246427009102241838098845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17314277381878623136527173 3246427009102241838098845)
                      ·
                        rfl

theorem cell23_6322394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_6322394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322394 prefixEnd_6322394 := by exact prefixLift 6322394
  have htrace : WordTrace (prefixWord ++ tailWord_6322394) baseStart_6322394 baseEnd_6322394 := by
    simpa [prefixWord, tailWord_6322394, baseEnd_6322394] using wordTrace_append hprefix tailTrace_6322394
  have hstable : (prefixWord ++ tailWord_6322394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322394).length < 2 ^ (prefixWord ++ tailWord_6322394).sum := by decide
  have hdescent : baseEnd_6322394 < baseStart_6322394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322402 : List Nat := [3, 3, 4, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_6322402 : Nat := 118140960795 + 6322402 * 2 ^ 59
def prefixEnd_6322402 : Nat := 4983230072969 + 3 ^ 40 * 6322402 * 2
def baseEnd_6322402 : Nat := 3246431116947477806798809

theorem tailTrace_6322402 : CollatzResearch.WordTrace tailWord_6322402 prefixEnd_6322402 3246431116947477806798809 := by
  unfold tailWord_6322402
  simp only [CollatzResearch.WordTrace]
  refine ⟨57649236310256202285252365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153731296827349872760672973 57649236310256202285252365)
  ·
    refine ⟨21618463616346075856969637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57649236310256202285252365 21618463616346075856969637)
    ·
      refine ⟨4053461928064889223181807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21618463616346075856969637 4053461928064889223181807)
      ·
        refine ⟨6080192892097333834772711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4053461928064889223181807 6080192892097333834772711)
        ·
          refine ⟨9120289338146000752159067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6080192892097333834772711 9120289338146000752159067)
          ·
            refine ⟨13680434007219001128238601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9120289338146000752159067 13680434007219001128238601)
            ·
              refine ⟨10260325505414250846178951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13680434007219001128238601 10260325505414250846178951)
              ·
                refine ⟨15390488258121376269268427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10260325505414250846178951 15390488258121376269268427)
                ·
                  refine ⟨23085732387182064403902641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15390488258121376269268427 23085732387182064403902641)
                  ·
                    refine ⟨17314299290386548302926981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23085732387182064403902641 17314299290386548302926981)
                    ·
                      refine ⟨3246431116947477806798809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17314299290386548302926981 3246431116947477806798809)
                      ·
                        rfl

theorem cell23_6322402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_6322402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322402 prefixEnd_6322402 := by exact prefixLift 6322402
  have htrace : WordTrace (prefixWord ++ tailWord_6322402) baseStart_6322402 baseEnd_6322402 := by
    simpa [prefixWord, tailWord_6322402, baseEnd_6322402] using wordTrace_append hprefix tailTrace_6322402
  have hstable : (prefixWord ++ tailWord_6322402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322402).length < 2 ^ (prefixWord ++ tailWord_6322402).sum := by decide
  have hdescent : baseEnd_6322402 < baseStart_6322402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322428 : List Nat := [2, 2, 2, 1, 4, 1, 2, 2, 1, 4, 2]
def baseStart_6322428 : Nat := 118140960795 + 6322428 * 2 ^ 59
def prefixEnd_6322428 : Nat := 4983230072969 + 3 ^ 40 * 6322428 * 2
def baseEnd_6322428 : Nat := 3246444467444494705073689

theorem tailTrace_6322428 : CollatzResearch.WordTrace tailWord_6322428 prefixEnd_6322428 3246444467444494705073689 := by
  unfold tailWord_6322428
  simp only [CollatzResearch.WordTrace]
  refine ⟨115298946769465307790727969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153731929025953743720970625 115298946769465307790727969)
  ·
    refine ⟨86474210077098980843045977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115298946769465307790727969 86474210077098980843045977)
    ·
      refine ⟨64855657557824235632284483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86474210077098980843045977 64855657557824235632284483)
      ·
        refine ⟨97283486336736353448426725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64855657557824235632284483 97283486336736353448426725)
        ·
          refine ⟨18240653688138066271580011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97283486336736353448426725 18240653688138066271580011)
          ·
            refine ⟨27360980532207099407370017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18240653688138066271580011 27360980532207099407370017)
            ·
              refine ⟨20520735399155324555527513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27360980532207099407370017 20520735399155324555527513)
              ·
                refine ⟨15390551549366493416645635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20520735399155324555527513 15390551549366493416645635)
                ·
                  refine ⟨23085827324049740124968453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15390551549366493416645635 23085827324049740124968453)
                  ·
                    refine ⟨4328592623259326273431585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23085827324049740124968453 4328592623259326273431585)
                    ·
                      refine ⟨3246444467444494705073689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4328592623259326273431585 3246444467444494705073689)
                      ·
                        rfl

theorem cell23_6322428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 1, 4, 2].length) (baseStart_6322428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322428 prefixEnd_6322428 := by exact prefixLift 6322428
  have htrace : WordTrace (prefixWord ++ tailWord_6322428) baseStart_6322428 baseEnd_6322428 := by
    simpa [prefixWord, tailWord_6322428, baseEnd_6322428] using wordTrace_append hprefix tailTrace_6322428
  have hstable : (prefixWord ++ tailWord_6322428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322428).length < 2 ^ (prefixWord ++ tailWord_6322428).sum := by decide
  have hdescent : baseEnd_6322428 < baseStart_6322428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322439 : List Nat := [1, 1, 4, 5, 2, 1, 1, 2, 2, 1, 3]
def baseStart_6322439 : Nat := 118140960795 + 6322439 * 2 ^ 59
def prefixEnd_6322439 : Nat := 4983230072969 + 3 ^ 40 * 6322439 * 2
def baseEnd_6322439 : Nat := 3246450115731694162036139

theorem tailTrace_6322439 : CollatzResearch.WordTrace tailWord_6322439 prefixEnd_6322439 3246450115731694162036139 := by
  unfold tailWord_6322439
  simp only [CollatzResearch.WordTrace]
  refine ⟨230598294741890764460106371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153732196494593842973404247 230598294741890764460106371)
  ·
    refine ⟨345897442112836146690159557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230598294741890764460106371 345897442112836146690159557)
    ·
      refine ⟨64855770396156777504404917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 345897442112836146690159557 64855770396156777504404917)
      ·
        refine ⟨6080228474639697891037961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64855770396156777504404917 6080228474639697891037961)
        ·
          refine ⟨4560171355979773418278471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6080228474639697891037961 4560171355979773418278471)
          ·
            refine ⟨6840257033969660127417707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4560171355979773418278471 6840257033969660127417707)
            ·
              refine ⟨10260385550954490191126561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6840257033969660127417707 10260385550954490191126561)
              ·
                refine ⟨7695289163215867643344921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10260385550954490191126561 7695289163215867643344921)
                ·
                  refine ⟨5771466872411900732508691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7695289163215867643344921 5771466872411900732508691)
                  ·
                    refine ⟨8657200308617851098763037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5771466872411900732508691 8657200308617851098763037)
                    ·
                      refine ⟨3246450115731694162036139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8657200308617851098763037 3246450115731694162036139)
                      ·
                        rfl

theorem cell23_6322439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_6322439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322439 prefixEnd_6322439 := by exact prefixLift 6322439
  have htrace : WordTrace (prefixWord ++ tailWord_6322439) baseStart_6322439 baseEnd_6322439 := by
    simpa [prefixWord, tailWord_6322439, baseEnd_6322439] using wordTrace_append hprefix tailTrace_6322439
  have hstable : (prefixWord ++ tailWord_6322439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322439).length < 2 ^ (prefixWord ++ tailWord_6322439).sum := by decide
  have hdescent : baseEnd_6322439 < baseStart_6322439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322462 : List Nat := [4, 3, 2, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_6322462 : Nat := 118140960795 + 6322462 * 2 ^ 59
def prefixEnd_6322462 : Nat := 4983230072969 + 3 ^ 40 * 6322462 * 2
def baseEnd_6322462 : Nat := 3246461925786747572048533

theorem tailTrace_6322462 : CollatzResearch.WordTrace tailWord_6322462 prefixEnd_6322462 3246461925786747572048533 := by
  unfold tailWord_6322462
  simp only [CollatzResearch.WordTrace]
  refine ⟨28824891702600929923524205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153732755747204959592129093 28824891702600929923524205)
  ·
    refine ⟨10809334388475348721321577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28824891702600929923524205 10809334388475348721321577)
    ·
      refine ⟨8107000791356511540991183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10809334388475348721321577 8107000791356511540991183)
      ·
        refine ⟨12160501187034767311486775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8107000791356511540991183 12160501187034767311486775)
        ·
          refine ⟨18240751780552150967230163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12160501187034767311486775 18240751780552150967230163)
          ·
            refine ⟨27361127670828226450845245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18240751780552150967230163 27361127670828226450845245)
            ·
              refine ⟨10260422876560584919066967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27361127670828226450845245 10260422876560584919066967)
              ·
                refine ⟨15390634314840877378600451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10260422876560584919066967 15390634314840877378600451)
                ·
                  refine ⟨23085951472261316067900677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15390634314840877378600451 23085951472261316067900677)
                  ·
                    refine ⟨4328615901048996762731377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23085951472261316067900677 4328615901048996762731377)
                    ·
                      refine ⟨3246461925786747572048533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4328615901048996762731377 3246461925786747572048533)
                      ·
                        rfl

theorem cell23_6322462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_6322462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322462 prefixEnd_6322462 := by exact prefixLift 6322462
  have htrace : WordTrace (prefixWord ++ tailWord_6322462) baseStart_6322462 baseEnd_6322462 := by
    simpa [prefixWord, tailWord_6322462, baseEnd_6322462] using wordTrace_append hprefix tailTrace_6322462
  have hstable : (prefixWord ++ tailWord_6322462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322462).length < 2 ^ (prefixWord ++ tailWord_6322462).sum := by decide
  have hdescent : baseEnd_6322462 < baseStart_6322462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322511 : List Nat := [1, 1, 2, 1, 1, 2, 1, 7, 3, 4]
def baseStart_6322511 : Nat := 118140960795 + 6322511 * 2 ^ 59
def prefixEnd_6322511 : Nat := 4983230072969 + 3 ^ 40 * 6322511 * 2
def baseEnd_6322511 : Nat := 1082162362112939293445269

theorem tailTrace_6322511 : CollatzResearch.WordTrace tailWord_6322511 prefixEnd_6322511 1082162362112939293445269 := by
  unfold tailWord_6322511
  simp only [CollatzResearch.WordTrace]
  refine ⟨230600920797629920756727387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153733947198419947171151591 230600920797629920756727387)
  ·
    refine ⟨345901381196444881135091081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230600920797629920756727387 345901381196444881135091081)
    ·
      refine ⟨259426035897333660851318311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345901381196444881135091081 259426035897333660851318311)
      ·
        refine ⟨389139053846000491276977467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259426035897333660851318311 389139053846000491276977467)
        ·
          refine ⟨583708580769000736915466201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389139053846000491276977467 583708580769000736915466201)
          ·
            refine ⟨437781435576750552686599651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 583708580769000736915466201 437781435576750552686599651)
            ·
              refine ⟨656672153365125829029899477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437781435576750552686599651 656672153365125829029899477)
              ·
                refine ⟨15390753594495136617888269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 656672153365125829029899477 15390753594495136617888269)
                ·
                  refine ⟨5771532597935676231708101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15390753594495136617888269 5771532597935676231708101)
                  ·
                    refine ⟨1082162362112939293445269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5771532597935676231708101 1082162362112939293445269)
                    ·
                      rfl

theorem cell23_6322511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 4].length) (baseStart_6322511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322511 prefixEnd_6322511 := by exact prefixLift 6322511
  have htrace : WordTrace (prefixWord ++ tailWord_6322511) baseStart_6322511 baseEnd_6322511 := by
    simpa [prefixWord, tailWord_6322511, baseEnd_6322511] using wordTrace_append hprefix tailTrace_6322511
  have hstable : (prefixWord ++ tailWord_6322511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322511).length < 2 ^ (prefixWord ++ tailWord_6322511).sum := by decide
  have hdescent : baseEnd_6322511 < baseStart_6322511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322521 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 6, 2, 3]
def baseStart_6322521 : Nat := 118140960795 + 6322521 * 2 ^ 59
def prefixEnd_6322521 : Nat := 4983230072969 + 3 ^ 40 * 6322521 * 2
def baseEnd_6322521 : Nat := 3246492221145362841210761

theorem tailTrace_6322521 : CollatzResearch.WordTrace tailWord_6322521 prefixEnd_6322521 3246492221145362841210761 := by
  unfold tailWord_6322521
  simp only [CollatzResearch.WordTrace]
  refine ⟨230601285527593692464591417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153734190351729128309727611 230601285527593692464591417)
  ·
    refine ⟨172950964145695269348443563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230601285527593692464591417 172950964145695269348443563)
    ·
      refine ⟨259426446218542904022665345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172950964145695269348443563 259426446218542904022665345)
      ·
        refine ⟨194569834663907178016999009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259426446218542904022665345 194569834663907178016999009)
        ·
          refine ⟨145927375997930383512749257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194569834663907178016999009 145927375997930383512749257)
          ·
            refine ⟨109445531998447787634561943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145927375997930383512749257 109445531998447787634561943)
            ·
              refine ⟨164168297997671681451842915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109445531998447787634561943 164168297997671681451842915)
              ·
                refine ⟨246252446996507522177764373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164168297997671681451842915 246252446996507522177764373)
                ·
                  refine ⟨11543083452961290102082705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 246252446996507522177764373 11543083452961290102082705)
                  ·
                    refine ⟨8657312589720967576562029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11543083452961290102082705 8657312589720967576562029)
                    ·
                      refine ⟨3246492221145362841210761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8657312589720967576562029 3246492221145362841210761)
                      ·
                        rfl

theorem cell23_6322521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 2, 3].length) (baseStart_6322521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322521 prefixEnd_6322521 := by exact prefixLift 6322521
  have htrace : WordTrace (prefixWord ++ tailWord_6322521) baseStart_6322521 baseEnd_6322521 := by
    simpa [prefixWord, tailWord_6322521, baseEnd_6322521] using wordTrace_append hprefix tailTrace_6322521
  have hstable : (prefixWord ++ tailWord_6322521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322521).length < 2 ^ (prefixWord ++ tailWord_6322521).sum := by decide
  have hdescent : baseEnd_6322521 < baseStart_6322521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322571 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 3, 5]
def baseStart_6322571 : Nat := 118140960795 + 6322571 * 2 ^ 59
def prefixEnd_6322571 : Nat := 4983230072969 + 3 ^ 40 * 6322571 * 2
def baseEnd_6322571 : Nat := 1082172631726029215195177

theorem tailTrace_6322571 : CollatzResearch.WordTrace tailWord_6322571 prefixEnd_6322571 1082172631726029215195177 := by
  unfold tailWord_6322571
  simp only [CollatzResearch.WordTrace]
  refine ⟨230603109177412551003911567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153735406118275034002607711 230603109177412551003911567)
  ·
    refine ⟨345904663766118826505867351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230603109177412551003911567 345904663766118826505867351)
    ·
      refine ⟨518856995649178239758801027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345904663766118826505867351 518856995649178239758801027)
      ·
        refine ⟨778285493473767359638201541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518856995649178239758801027 778285493473767359638201541)
        ·
          refine ⟨145928530026331379932162789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 778285493473767359638201541 145928530026331379932162789)
          ·
            refine ⟨27361599379937133737280523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145928530026331379932162789 27361599379937133737280523)
            ·
              refine ⟨41042399069905700605920785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27361599379937133737280523 41042399069905700605920785)
              ·
                refine ⟨30781799302429275454440589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41042399069905700605920785 30781799302429275454440589)
                ·
                  refine ⟨11543174738410978295415221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30781799302429275454440589 11543174738410978295415221)
                  ·
                    refine ⟨1082172631726029215195177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11543174738410978295415221 1082172631726029215195177)
                    ·
                      rfl

theorem cell23_6322571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 5].length) (baseStart_6322571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322571 prefixEnd_6322571 := by exact prefixLift 6322571
  have htrace : WordTrace (prefixWord ++ tailWord_6322571) baseStart_6322571 baseEnd_6322571 := by
    simpa [prefixWord, tailWord_6322571, baseEnd_6322571] using wordTrace_append hprefix tailTrace_6322571
  have hstable : (prefixWord ++ tailWord_6322571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322571).length < 2 ^ (prefixWord ++ tailWord_6322571).sum := by decide
  have hdescent : baseEnd_6322571 < baseStart_6322571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322595 : List Nat := [1, 1, 1, 4, 1, 4, 3, 1, 2, 3, 2]
def baseStart_6322595 : Nat := 118140960795 + 6322595 * 2 ^ 59
def prefixEnd_6322595 : Nat := 4983230072969 + 3 ^ 40 * 6322595 * 2
def baseEnd_6322595 : Nat := 3246530218713795551685421

theorem tailTrace_6322595 : CollatzResearch.WordTrace tailWord_6322595 prefixEnd_6322595 3246530218713795551685421 := by
  unfold tailWord_6322595
  simp only [CollatzResearch.WordTrace]
  refine ⟨230603984529325603102785239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153735989686217068735190159 230603984529325603102785239)
  ·
    refine ⟨345905976793988404654177859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230603984529325603102785239 345905976793988404654177859)
    ·
      refine ⟨518858965190982606981266789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345905976793988404654177859 518858965190982606981266789)
      ·
        refine ⟨97286055973309238808987523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 518858965190982606981266789 97286055973309238808987523)
        ·
          refine ⟨145929083959963858213481285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97286055973309238808987523 145929083959963858213481285)
          ·
            refine ⟨27361703242493223415027741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145929083959963858213481285 27361703242493223415027741)
            ·
              refine ⟨10260638715934958780635403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27361703242493223415027741 10260638715934958780635403)
              ·
                refine ⟨15390958073902438170953105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10260638715934958780635403 15390958073902438170953105)
                ·
                  refine ⟨11543218555426828628214829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15390958073902438170953105 11543218555426828628214829)
                  ·
                    refine ⟨4328706958285060735580561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11543218555426828628214829 4328706958285060735580561)
                    ·
                      refine ⟨3246530218713795551685421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4328706958285060735580561 3246530218713795551685421)
                      ·
                        rfl

theorem cell23_6322595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 3, 2].length) (baseStart_6322595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322595 prefixEnd_6322595 := by exact prefixLift 6322595
  have htrace : WordTrace (prefixWord ++ tailWord_6322595) baseStart_6322595 baseEnd_6322595 := by
    simpa [prefixWord, tailWord_6322595, baseEnd_6322595] using wordTrace_append hprefix tailTrace_6322595
  have hstable : (prefixWord ++ tailWord_6322595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322595).length < 2 ^ (prefixWord ++ tailWord_6322595).sum := by decide
  have hdescent : baseEnd_6322595 < baseStart_6322595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322645 : List Nat := [1, 3, 2, 3, 1, 2, 1, 4, 1, 2, 3]
def baseStart_6322645 : Nat := 118140960795 + 6322645 * 2 ^ 59
def prefixEnd_6322645 : Nat := 4983230072969 + 3 ^ 40 * 6322645 * 2
def baseEnd_6322645 : Nat := 3246555892746520356060191

theorem tailTrace_6322645 : CollatzResearch.WordTrace tailWord_6322645 prefixEnd_6322645 3246555892746520356060191 := by
  unfold tailWord_6322645
  simp only [CollatzResearch.WordTrace]
  refine ⟨230605808179144461642105389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153737205452762974428070259 230605808179144461642105389)
  ·
    refine ⟨86477178067179173115789521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230605808179144461642105389 86477178067179173115789521)
    ·
      refine ⟨64857883550384379836842141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86477178067179173115789521 64857883550384379836842141)
      ·
        refine ⟨24321706331394142438815803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64857883550384379836842141 24321706331394142438815803)
        ·
          refine ⟨36482559497091213658223705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24321706331394142438815803 36482559497091213658223705)
          ·
            refine ⟨27361919622818410243667779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36482559497091213658223705 27361919622818410243667779)
            ·
              refine ⟨41042879434227615365501669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27361919622818410243667779 41042879434227615365501669)
              ·
                refine ⟨7695539893917677881031563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41042879434227615365501669 7695539893917677881031563)
                ·
                  refine ⟨11543309840876516821547345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7695539893917677881031563 11543309840876516821547345)
                  ·
                    refine ⟨8657482380657387616160509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11543309840876516821547345 8657482380657387616160509)
                    ·
                      refine ⟨3246555892746520356060191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8657482380657387616160509 3246555892746520356060191)
                      ·
                        rfl

theorem cell23_6322645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_6322645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322645 prefixEnd_6322645 := by exact prefixLift 6322645
  have htrace : WordTrace (prefixWord ++ tailWord_6322645) baseStart_6322645 baseEnd_6322645 := by
    simpa [prefixWord, tailWord_6322645, baseEnd_6322645] using wordTrace_append hprefix tailTrace_6322645
  have hstable : (prefixWord ++ tailWord_6322645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322645).length < 2 ^ (prefixWord ++ tailWord_6322645).sum := by decide
  have hdescent : baseEnd_6322645 < baseStart_6322645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322671 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 5]
def baseStart_6322671 : Nat := 118140960795 + 6322671 * 2 ^ 59
def prefixEnd_6322671 : Nat := 4983230072969 + 3 ^ 40 * 6322671 * 2
def baseEnd_6322671 : Nat := 3246569243243537254335071

theorem tailTrace_6322671 : CollatzResearch.WordTrace tailWord_6322671 prefixEnd_6322671 3246569243243537254335071 := by
  unfold tailWord_6322671
  simp only [CollatzResearch.WordTrace]
  refine ⟨230606756477050268082551867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153737837651366845388367911 230606756477050268082551867)
  ·
    refine ⟨345910134715575402123827801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230606756477050268082551867 345910134715575402123827801)
    ·
      refine ⟨259432601036681551592870851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345910134715575402123827801 259432601036681551592870851)
      ·
        refine ⟨389148901555022327389306277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259432601036681551592870851 389148901555022327389306277)
        ·
          refine ⟨72965419041566686385494927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 389148901555022327389306277 72965419041566686385494927)
          ·
            refine ⟨109448128562350029578242391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72965419041566686385494927 109448128562350029578242391)
            ·
              refine ⟨164172192843525044367363587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109448128562350029578242391 164172192843525044367363587)
              ·
                refine ⟨246258289265287566551045381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164172192843525044367363587 246258289265287566551045381)
                ·
                  refine ⟨46173429237241418728321009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246258289265287566551045381 46173429237241418728321009)
                  ·
                    refine ⟨34630071927931064046240757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46173429237241418728321009 34630071927931064046240757)
                    ·
                      refine ⟨3246569243243537254335071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34630071927931064046240757 3246569243243537254335071)
                      ·
                        rfl

theorem cell23_6322671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_6322671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322671 prefixEnd_6322671 := by exact prefixLift 6322671
  have htrace : WordTrace (prefixWord ++ tailWord_6322671) baseStart_6322671 baseEnd_6322671 := by
    simpa [prefixWord, tailWord_6322671, baseEnd_6322671] using wordTrace_append hprefix tailTrace_6322671
  have hstable : (prefixWord ++ tailWord_6322671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322671).length < 2 ^ (prefixWord ++ tailWord_6322671).sum := by decide
  have hdescent : baseEnd_6322671 < baseStart_6322671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322675 : List Nat := [1, 1, 1, 2, 2, 2, 4, 4, 2, 1, 3]
def baseStart_6322675 : Nat := 118140960795 + 6322675 * 2 ^ 59
def prefixEnd_6322675 : Nat := 4983230072969 + 3 ^ 40 * 6322675 * 2
def baseEnd_6322675 : Nat := 3246571297166155238685053

theorem tailTrace_6322675 : CollatzResearch.WordTrace tailWord_6322675 prefixEnd_6322675 3246571297166155238685053 := by
  unfold tailWord_6322675
  simp only [CollatzResearch.WordTrace]
  refine ⟨230606902369035776765697479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153737934912690517843798319 230606902369035776765697479)
  ·
    refine ⟨345910353553553665148546219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230606902369035776765697479 345910353553553665148546219)
    ·
      refine ⟨518865530330330497722819329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345910353553553665148546219 518865530330330497722819329)
      ·
        refine ⟨389149147747747873292114497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 518865530330330497722819329 389149147747747873292114497)
        ·
          refine ⟨291861860810810904969085873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389149147747747873292114497 291861860810810904969085873)
          ·
            refine ⟨218896395608108178726814405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291861860810810904969085873 218896395608108178726814405)
            ·
              refine ⟨41043074176520283511277701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218896395608108178726814405 41043074176520283511277701)
              ·
                refine ⟨7695576408097553158364569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41043074176520283511277701 7695576408097553158364569)
                ·
                  refine ⟨5771682306073164868773427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7695576408097553158364569 5771682306073164868773427)
                  ·
                    refine ⟨8657523459109747303160141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5771682306073164868773427 8657523459109747303160141)
                    ·
                      refine ⟨3246571297166155238685053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8657523459109747303160141 3246571297166155238685053)
                      ·
                        rfl

theorem cell23_6322675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 1, 3].length) (baseStart_6322675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322675 prefixEnd_6322675 := by exact prefixLift 6322675
  have htrace : WordTrace (prefixWord ++ tailWord_6322675) baseStart_6322675 baseEnd_6322675 := by
    simpa [prefixWord, tailWord_6322675, baseEnd_6322675] using wordTrace_append hprefix tailTrace_6322675
  have hstable : (prefixWord ++ tailWord_6322675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322675).length < 2 ^ (prefixWord ++ tailWord_6322675).sum := by decide
  have hdescent : baseEnd_6322675 < baseStart_6322675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322678 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 2, 7]
def baseStart_6322678 : Nat := 118140960795 + 6322678 * 2 ^ 59
def prefixEnd_6322678 : Nat := 4983230072969 + 3 ^ 40 * 6322678 * 2
def baseEnd_6322678 : Nat := 1082190945869372908982513

theorem tailTrace_6322678 : CollatzResearch.WordTrace tailWord_6322678 prefixEnd_6322678 1082190945869372908982513 := by
  unfold tailWord_6322678
  simp only [CollatzResearch.WordTrace]
  refine ⟨14412938236751556767378543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153738007858683272185371125 14412938236751556767378543)
  ·
    refine ⟨21619407355127335151067815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14412938236751556767378543 21619407355127335151067815)
    ·
      refine ⟨32429111032691002726601723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21619407355127335151067815 32429111032691002726601723)
      ·
        refine ⟨48643666549036504089902585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32429111032691002726601723 48643666549036504089902585)
        ·
          refine ⟨36482749911777378067426939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48643666549036504089902585 36482749911777378067426939)
          ·
            refine ⟨54724124867666067101140409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36482749911777378067426939 54724124867666067101140409)
            ·
              refine ⟨41043093650749550325855307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54724124867666067101140409 41043093650749550325855307)
              ·
                refine ⟨61564640476124325488782961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41043093650749550325855307 61564640476124325488782961)
                ·
                  refine ⟨46173480357093244116587221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61564640476124325488782961 46173480357093244116587221)
                  ·
                    refine ⟨1082190945869372908982513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46173480357093244116587221 1082190945869372908982513)
                    ·
                      rfl

theorem cell23_6322678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_6322678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322678 prefixEnd_6322678 := by exact prefixLift 6322678
  have htrace : WordTrace (prefixWord ++ tailWord_6322678) baseStart_6322678 baseEnd_6322678 := by
    simpa [prefixWord, tailWord_6322678, baseEnd_6322678] using wordTrace_append hprefix tailTrace_6322678
  have hstable : (prefixWord ++ tailWord_6322678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322678).length < 2 ^ (prefixWord ++ tailWord_6322678).sum := by decide
  have hdescent : baseEnd_6322678 < baseStart_6322678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322685 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 3, 3, 2]
def baseStart_6322685 : Nat := 118140960795 + 6322685 * 2 ^ 59
def prefixEnd_6322685 : Nat := 4983230072969 + 3 ^ 40 * 6322685 * 2
def baseEnd_6322685 : Nat := 3246576431972700199560007

theorem tailTrace_6322685 : CollatzResearch.WordTrace tailWord_6322685 prefixEnd_6322685 3246576431972700199560007 := by
  unfold tailWord_6322685
  simp only [CollatzResearch.WordTrace]
  refine ⟨230607267098999548473561509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153738178065999698982374339 230607267098999548473561509)
  ·
    refine ⟨43238862581062415338792783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230607267098999548473561509 43238862581062415338792783)
    ·
      refine ⟨64858293871593623008189175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43238862581062415338792783 64858293871593623008189175)
      ·
        refine ⟨97287440807390434512283763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64858293871593623008189175 97287440807390434512283763)
        ·
          refine ⟨145931161211085651768425645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97287440807390434512283763 145931161211085651768425645)
          ·
            refine ⟨54724185454157119413159617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145931161211085651768425645 54724185454157119413159617)
            ·
              refine ⟨41043139090617839559869713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54724185454157119413159617 41043139090617839559869713)
              ·
                refine ⟨30782354317963379669902285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41043139090617839559869713 30782354317963379669902285)
                ·
                  refine ⟨11543382869236267376213357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30782354317963379669902285 11543382869236267376213357)
                  ·
                    refine ⟨4328768575963600266080009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11543382869236267376213357 4328768575963600266080009)
                    ·
                      refine ⟨3246576431972700199560007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4328768575963600266080009 3246576431972700199560007)
                      ·
                        rfl

theorem cell23_6322685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 3, 2].length) (baseStart_6322685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322685 prefixEnd_6322685 := by exact prefixLift 6322685
  have htrace : WordTrace (prefixWord ++ tailWord_6322685) baseStart_6322685 baseEnd_6322685 := by
    simpa [prefixWord, tailWord_6322685, baseEnd_6322685] using wordTrace_append hprefix tailTrace_6322685
  have hstable : (prefixWord ++ tailWord_6322685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322685).length < 2 ^ (prefixWord ++ tailWord_6322685).sum := by decide
  have hdescent : baseEnd_6322685 < baseStart_6322685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322691 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 1, 8]
def baseStart_6322691 : Nat := 118140960795 + 6322691 * 2 ^ 59
def prefixEnd_6322691 : Nat := 4983230072969 + 3 ^ 40 * 6322691 * 2
def baseEnd_6322691 : Nat := 1082193170952209058694993

theorem tailTrace_6322691 : CollatzResearch.WordTrace tailWord_6322691 prefixEnd_6322691 1082193170952209058694993 := by
  unfold tailWord_6322691
  simp only [CollatzResearch.WordTrace]
  refine ⟨230607485936977811498279927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153738323957985207665519951 230607485936977811498279927)
  ·
    refine ⟨345911228905466717247419891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230607485936977811498279927 345911228905466717247419891)
    ·
      refine ⟨518866843358200075871129837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345911228905466717247419891 518866843358200075871129837)
      ·
        refine ⟨194575066259325028451673689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 518866843358200075871129837 194575066259325028451673689)
        ·
          refine ⟨145931299694493771338755267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194575066259325028451673689 145931299694493771338755267)
          ·
            refine ⟨218896949541740657008132901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145931299694493771338755267 218896949541740657008132901)
            ·
              refine ⟨41043178039076373189024919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218896949541740657008132901 41043178039076373189024919)
              ·
                refine ⟨61564767058614559783537379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41043178039076373189024919 61564767058614559783537379)
                ·
                  refine ⟨92347150587921839675306069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61564767058614559783537379 92347150587921839675306069)
                  ·
                    refine ⟨1082193170952209058694993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92347150587921839675306069 1082193170952209058694993)
                    ·
                      rfl

theorem cell23_6322691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 8].length) (baseStart_6322691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322691 prefixEnd_6322691 := by exact prefixLift 6322691
  have htrace : WordTrace (prefixWord ++ tailWord_6322691) baseStart_6322691 baseEnd_6322691 := by
    simpa [prefixWord, tailWord_6322691, baseEnd_6322691] using wordTrace_append hprefix tailTrace_6322691
  have hstable : (prefixWord ++ tailWord_6322691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322691).length < 2 ^ (prefixWord ++ tailWord_6322691).sum := by decide
  have hdescent : baseEnd_6322691 < baseStart_6322691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322702 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2]
def baseStart_6322702 : Nat := 118140960795 + 6322702 * 2 ^ 59
def prefixEnd_6322702 : Nat := 4983230072969 + 3 ^ 40 * 6322702 * 2
def baseEnd_6322702 : Nat := 3246585161143826633047429

theorem tailTrace_6322702 : CollatzResearch.WordTrace tailWord_6322702 prefixEnd_6322702 3246585161143826633047429 := by
  unfold tailWord_6322702
  simp only [CollatzResearch.WordTrace]
  refine ⟨28825985892492245047116295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153738591426625306917953573 28825985892492245047116295)
  ·
    refine ⟨43238978838738367570674443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28825985892492245047116295 43238978838738367570674443)
    ·
      refine ⟨64858468258107551356011665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43238978838738367570674443 64858468258107551356011665)
      ·
        refine ⟨48643851193580663517008749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64858468258107551356011665 48643851193580663517008749)
        ·
          refine ⟨18241444197592748818878281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48643851193580663517008749 18241444197592748818878281)
          ·
            refine ⟨13681083148194561614158711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18241444197592748818878281 13681083148194561614158711)
            ·
              refine ⟨20521624722291842421238067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13681083148194561614158711 20521624722291842421238067)
              ·
                refine ⟨30782437083437763631857101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20521624722291842421238067 30782437083437763631857101)
                ·
                  refine ⟨11543413906289161361946413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30782437083437763631857101 11543413906289161361946413)
                  ·
                    refine ⟨4328780214858435510729905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11543413906289161361946413 4328780214858435510729905)
                    ·
                      refine ⟨3246585161143826633047429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4328780214858435510729905 3246585161143826633047429)
                      ·
                        rfl

theorem cell23_6322702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_6322702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322702 prefixEnd_6322702 := by exact prefixLift 6322702
  have htrace : WordTrace (prefixWord ++ tailWord_6322702) baseStart_6322702 baseEnd_6322702 := by
    simpa [prefixWord, tailWord_6322702, baseEnd_6322702] using wordTrace_append hprefix tailTrace_6322702
  have hstable : (prefixWord ++ tailWord_6322702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322702).length < 2 ^ (prefixWord ++ tailWord_6322702).sum := by decide
  have hdescent : baseEnd_6322702 < baseStart_6322702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322727 : List Nat := [1, 1, 7, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_6322727 : Nat := 118140960795 + 6322727 * 2 ^ 59
def prefixEnd_6322727 : Nat := 4983230072969 + 3 ^ 40 * 6322727 * 2
def baseEnd_6322727 : Nat := 3246597998160189035234815

theorem tailTrace_6322727 : CollatzResearch.WordTrace tailWord_6322727 prefixEnd_6322727 3246597998160189035234815 := by
  unfold tailWord_6322727
  simp only [CollatzResearch.WordTrace]
  refine ⟨230608798964847389646590435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153739199309898259764393623 230608798964847389646590435)
  ·
    refine ⟨345913198447271084469885653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230608798964847389646590435 345913198447271084469885653)
    ·
      refine ⟨8107340588607916042262945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 345913198447271084469885653 8107340588607916042262945)
      ·
        refine ⟨6080505441455937031697209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8107340588607916042262945 6080505441455937031697209)
        ·
          refine ⟨4560379081091952773772907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6080505441455937031697209 4560379081091952773772907)
          ·
            refine ⟨6840568621637929160659361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4560379081091952773772907 6840568621637929160659361)
            ·
              refine ⟨5130426466228446870494521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6840568621637929160659361 5130426466228446870494521)
              ·
                refine ⟨3847819849671335152870891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5130426466228446870494521 3847819849671335152870891)
                ·
                  refine ⟨5771729774507002729306337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3847819849671335152870891 5771729774507002729306337)
                  ·
                    refine ⟨4328797330880252046979753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5771729774507002729306337 4328797330880252046979753)
                    ·
                      refine ⟨3246597998160189035234815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4328797330880252046979753 3246597998160189035234815)
                      ·
                        rfl

theorem cell23_6322727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_6322727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322727 prefixEnd_6322727 := by exact prefixLift 6322727
  have htrace : WordTrace (prefixWord ++ tailWord_6322727) baseStart_6322727 baseEnd_6322727 := by
    simpa [prefixWord, tailWord_6322727, baseEnd_6322727] using wordTrace_append hprefix tailTrace_6322727
  have hstable : (prefixWord ++ tailWord_6322727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322727).length < 2 ^ (prefixWord ++ tailWord_6322727).sum := by decide
  have hdescent : baseEnd_6322727 < baseStart_6322727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322731 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 7]
def baseStart_6322731 : Nat := 118140960795 + 6322731 * 2 ^ 59
def prefixEnd_6322731 : Nat := 4983230072969 + 3 ^ 40 * 6322731 * 2
def baseEnd_6322731 : Nat := 3246600052082807019584795

theorem tailTrace_6322731 : CollatzResearch.WordTrace tailWord_6322731 prefixEnd_6322731 3246600052082807019584795 := by
  unfold tailWord_6322731
  simp only [CollatzResearch.WordTrace]
  refine ⟨230608944856832898329736047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153739296571221932219824031 230608944856832898329736047)
  ·
    refine ⟨345913417285249347494604071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230608944856832898329736047 345913417285249347494604071)
    ·
      refine ⟨518870125927874021241906107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345913417285249347494604071 518870125927874021241906107)
      ·
        refine ⟨778305188891811031862859161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518870125927874021241906107 778305188891811031862859161)
        ·
          refine ⟨583728891668858273897144371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 778305188891811031862859161 583728891668858273897144371)
          ·
            refine ⟨875593337503287410845716557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583728891668858273897144371 875593337503287410845716557)
            ·
              refine ⟨328347501563732779067143709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 875593337503287410845716557 328347501563732779067143709)
              ·
                refine ⟨123130313086399792150178891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 328347501563732779067143709 123130313086399792150178891)
                ·
                  refine ⟨184695469629599688225268337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123130313086399792150178891 184695469629599688225268337)
                  ·
                    refine ⟨138521602222199766168951253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 184695469629599688225268337 138521602222199766168951253)
                    ·
                      refine ⟨3246600052082807019584795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 138521602222199766168951253 3246600052082807019584795)
                      ·
                        rfl

theorem cell23_6322731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 7].length) (baseStart_6322731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322731 prefixEnd_6322731 := by exact prefixLift 6322731
  have htrace : WordTrace (prefixWord ++ tailWord_6322731) baseStart_6322731 baseEnd_6322731 := by
    simpa [prefixWord, tailWord_6322731, baseEnd_6322731] using wordTrace_append hprefix tailTrace_6322731
  have hstable : (prefixWord ++ tailWord_6322731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322731).length < 2 ^ (prefixWord ++ tailWord_6322731).sum := by decide
  have hdescent : baseEnd_6322731 < baseStart_6322731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322749 : List Nat := [1, 4, 1, 3, 2, 1, 2, 3, 2, 2, 2]
def baseStart_6322749 : Nat := 118140960795 + 6322749 * 2 ^ 59
def prefixEnd_6322749 : Nat := 4983230072969 + 3 ^ 40 * 6322749 * 2
def baseEnd_6322749 : Nat := 3246609294734587949159713

theorem tailTrace_6322749 : CollatzResearch.WordTrace tailWord_6322749 prefixEnd_6322749 3246609294734587949159713 := by
  unfold tailWord_6322749
  simp only [CollatzResearch.WordTrace]
  refine ⟨230609601370767687403891301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153739734247178458269260867 230609601370767687403891301)
  ·
    refine ⟨43239300257018941388229619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230609601370767687403891301 43239300257018941388229619)
    ·
      refine ⟨64858950385528412082344429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43239300257018941388229619 64858950385528412082344429)
      ·
        refine ⟨24322106394573154530879161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64858950385528412082344429 24322106394573154530879161)
        ·
          refine ⟨18241579795929865898159371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24322106394573154530879161 18241579795929865898159371)
          ·
            refine ⟨27362369693894798847239057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18241579795929865898159371 27362369693894798847239057)
            ·
              refine ⟨20521777270421099135429293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27362369693894798847239057 20521777270421099135429293)
              ·
                refine ⟨7695666476407912175785985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20521777270421099135429293 7695666476407912175785985)
                ·
                  refine ⟨5771749857305934131839489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7695666476407912175785985 5771749857305934131839489)
                  ·
                    refine ⟨4328812392979450598879617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5771749857305934131839489 4328812392979450598879617)
                    ·
                      refine ⟨3246609294734587949159713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4328812392979450598879617 3246609294734587949159713)
                      ·
                        rfl

theorem cell23_6322749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_6322749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322749 prefixEnd_6322749 := by exact prefixLift 6322749
  have htrace : WordTrace (prefixWord ++ tailWord_6322749) baseStart_6322749 baseEnd_6322749 := by
    simpa [prefixWord, tailWord_6322749, baseEnd_6322749] using wordTrace_append hprefix tailTrace_6322749
  have hstable : (prefixWord ++ tailWord_6322749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322749).length < 2 ^ (prefixWord ++ tailWord_6322749).sum := by decide
  have hdescent : baseEnd_6322749 < baseStart_6322749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322768 : List Nat := [2, 1, 1, 1, 1, 3, 2, 5, 2, 5]
def baseStart_6322768 : Nat := 118140960795 + 6322768 * 2 ^ 59
def prefixEnd_6322768 : Nat := 4983230072969 + 3 ^ 40 * 6322768 * 2
def baseEnd_6322768 : Nat := 1082206350289007791607375

theorem tailTrace_6322768 : CollatzResearch.WordTrace tailWord_6322768 prefixEnd_6322768 1082206350289007791607375 := by
  unfold tailWord_6322768
  simp only [CollatzResearch.WordTrace]
  refine ⟨115305147178849426824416479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153740196238465902432555305 115305147178849426824416479)
  ·
    refine ⟨172957720768274140236624719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115305147178849426824416479 172957720768274140236624719)
    ·
      refine ⟨259436581152411210354937079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172957720768274140236624719 259436581152411210354937079)
      ·
        refine ⟨389154871728616815532405619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259436581152411210354937079 389154871728616815532405619)
        ·
          refine ⟨583732307592925223298608429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389154871728616815532405619 583732307592925223298608429)
          ·
            refine ⟨218899615347346958736978161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 583732307592925223298608429 218899615347346958736978161)
            ·
              refine ⟨164174711510510219052733621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218899615347346958736978161 164174711510510219052733621)
              ·
                refine ⟨15391379204110333036193777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164174711510510219052733621 15391379204110333036193777)
                ·
                  refine ⟨11543534403082749777145333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15391379204110333036193777 11543534403082749777145333)
                  ·
                    refine ⟨1082206350289007791607375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11543534403082749777145333 1082206350289007791607375)
                    ·
                      rfl

theorem cell23_6322768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 2, 5].length) (baseStart_6322768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322768 prefixEnd_6322768 := by exact prefixLift 6322768
  have htrace : WordTrace (prefixWord ++ tailWord_6322768) baseStart_6322768 baseEnd_6322768 := by
    simpa [prefixWord, tailWord_6322768, baseEnd_6322768] using wordTrace_append hprefix tailTrace_6322768
  have hstable : (prefixWord ++ tailWord_6322768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322768).length < 2 ^ (prefixWord ++ tailWord_6322768).sum := by decide
  have hdescent : baseEnd_6322768 < baseStart_6322768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322772 : List Nat := [2, 4, 1, 1, 1, 4, 2, 3, 5]
def baseStart_6322772 : Nat := 118140960795 + 6322772 * 2 ^ 59
def prefixEnd_6322772 : Nat := 4983230072969 + 3 ^ 40 * 6322772 * 2
def baseEnd_6322772 : Nat := 360735678309960151019123

theorem tailTrace_6322772 : CollatzResearch.WordTrace tailWord_6322772 prefixEnd_6322772 360735678309960151019123 := by
  unfold tailWord_6322772
  simp only [CollatzResearch.WordTrace]
  refine ⟨115305220124842181165989285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153740293499789574887985713 115305220124842181165989285)
  ·
    refine ⟨21619728773407908968622991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115305220124842181165989285 21619728773407908968622991)
    ·
      refine ⟨32429593160111863452934487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21619728773407908968622991 32429593160111863452934487)
      ·
        refine ⟨48644389740167795179401731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32429593160111863452934487 48644389740167795179401731)
        ·
          refine ⟨72966584610251692769102597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48644389740167795179401731 72966584610251692769102597)
          ·
            refine ⟨13681234614422192394206737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72966584610251692769102597 13681234614422192394206737)
            ·
              refine ⟨10260925960816644295655053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13681234614422192394206737 10260925960816644295655053)
              ·
                refine ⟨3847847235306241610870645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10260925960816644295655053 3847847235306241610870645)
                ·
                  refine ⟨360735678309960151019123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3847847235306241610870645 360735678309960151019123)
                  ·
                    rfl

theorem cell23_6322772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_6322772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322772 prefixEnd_6322772 := by exact prefixLift 6322772
  have htrace : WordTrace (prefixWord ++ tailWord_6322772) baseStart_6322772 baseEnd_6322772 := by
    simpa [prefixWord, tailWord_6322772, baseEnd_6322772] using wordTrace_append hprefix tailTrace_6322772
  have hstable : (prefixWord ++ tailWord_6322772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322772).length < 2 ^ (prefixWord ++ tailWord_6322772).sum := by decide
  have hdescent : baseEnd_6322772 < baseStart_6322772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322825 : List Nat := [1, 2, 1, 1, 4, 1, 1, 5, 2, 2, 3]
def baseStart_6322825 : Nat := 118140960795 + 6322825 * 2 ^ 59
def prefixEnd_6322825 : Nat := 4983230072969 + 3 ^ 40 * 6322825 * 2
def baseEnd_6322825 : Nat := 3246648319264329651809363

theorem tailTrace_6322825 : CollatzResearch.WordTrace tailWord_6322825 prefixEnd_6322825 3246648319264329651809363 := by
  unfold tailWord_6322825
  simp only [CollatzResearch.WordTrace]
  refine ⟨230612373318492352383657929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153741582212328234922438619 230612373318492352383657929)
  ·
    refine ⟨172959279988869264287743447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230612373318492352383657929 172959279988869264287743447)
    ·
      refine ⟨259438919983303896431615171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172959279988869264287743447 259438919983303896431615171)
      ·
        refine ⟨389158379974955844647422757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259438919983303896431615171 389158379974955844647422757)
        ·
          refine ⟨72967196245304220871391767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 389158379974955844647422757 72967196245304220871391767)
          ·
            refine ⟨109450794367956331307087651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72967196245304220871391767 109450794367956331307087651)
            ·
              refine ⟨164176191551934496960631477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109450794367956331307087651 164176191551934496960631477)
              ·
                refine ⟨15391517957993859090059201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164176191551934496960631477 15391517957993859090059201)
                ·
                  refine ⟨11543638468495394317544401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15391517957993859090059201 11543638468495394317544401)
                  ·
                    refine ⟨8657728851371545738158301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11543638468495394317544401 8657728851371545738158301)
                    ·
                      refine ⟨3246648319264329651809363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8657728851371545738158301 3246648319264329651809363)
                      ·
                        rfl

theorem cell23_6322825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 2, 3].length) (baseStart_6322825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322825 prefixEnd_6322825 := by exact prefixLift 6322825
  have htrace : WordTrace (prefixWord ++ tailWord_6322825) baseStart_6322825 baseEnd_6322825 := by
    simpa [prefixWord, tailWord_6322825, baseEnd_6322825] using wordTrace_append hprefix tailTrace_6322825
  have hstable : (prefixWord ++ tailWord_6322825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322825).length < 2 ^ (prefixWord ++ tailWord_6322825).sum := by decide
  have hdescent : baseEnd_6322825 < baseStart_6322825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322849 : List Nat := [1, 2, 3, 3, 3, 2, 1, 1, 3, 4]
def baseStart_6322849 : Nat := 118140960795 + 6322849 * 2 ^ 59
def prefixEnd_6322849 : Nat := 4983230072969 + 3 ^ 40 * 6322849 * 2
def baseEnd_6322849 : Nat := 1082220214266679185969751

theorem tailTrace_6322849 : CollatzResearch.WordTrace tailWord_6322849 prefixEnd_6322849 1082220214266679185969751 := by
  unfold tailWord_6322849
  simp only [CollatzResearch.WordTrace]
  refine ⟨230613248670405404482531601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153742165780270269655021067 230613248670405404482531601)
  ·
    refine ⟨172959936502804053361898701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230613248670405404482531601 172959936502804053361898701)
    ·
      refine ⟨64859976188551520010712013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172959936502804053361898701 64859976188551520010712013)
      ·
        refine ⟨24322491070706820004017005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64859976188551520010712013 24322491070706820004017005)
        ·
          refine ⟨9120934151515057501506377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24322491070706820004017005 9120934151515057501506377)
          ·
            refine ⟨6840700613636293126129783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9120934151515057501506377 6840700613636293126129783)
            ·
              refine ⟨10261050920454439689194675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6840700613636293126129783 10261050920454439689194675)
              ·
                refine ⟨15391576380681659533792013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10261050920454439689194675 15391576380681659533792013)
                ·
                  refine ⟨5771841142755622325172005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15391576380681659533792013 5771841142755622325172005)
                  ·
                    refine ⟨1082220214266679185969751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5771841142755622325172005 1082220214266679185969751)
                    ·
                      rfl

theorem cell23_6322849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_6322849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322849 prefixEnd_6322849 := by exact prefixLift 6322849
  have htrace : WordTrace (prefixWord ++ tailWord_6322849) baseStart_6322849 baseEnd_6322849 := by
    simpa [prefixWord, tailWord_6322849, baseEnd_6322849] using wordTrace_append hprefix tailTrace_6322849
  have hstable : (prefixWord ++ tailWord_6322849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322849).length < 2 ^ (prefixWord ++ tailWord_6322849).sum := by decide
  have hdescent : baseEnd_6322849 < baseStart_6322849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322900 : List Nat := [2, 4, 1, 3, 3, 1, 2, 2, 1, 4]
def baseStart_6322900 : Nat := 118140960795 + 6322900 * 2 ^ 59
def prefixEnd_6322900 : Nat := 4983230072969 + 3 ^ 40 * 6322900 * 2
def baseEnd_6322900 : Nat := 1082228943437805619457173

theorem tailTrace_6322900 : CollatzResearch.WordTrace tailWord_6322900 prefixEnd_6322900 1082228943437805619457173 := by
  unfold tailWord_6322900
  simp only [CollatzResearch.WordTrace]
  refine ⟨115307554396610320096319077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153743405862147093461758769 115307554396610320096319077)
  ·
    refine ⟨21620166449364435018059827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115307554396610320096319077 21620166449364435018059827)
    ·
      refine ⟨32430249674046652527089741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21620166449364435018059827 32430249674046652527089741)
      ·
        refine ⟨12161343627767494697658653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32430249674046652527089741 12161343627767494697658653)
        ·
          refine ⟨4560503860412810511621995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12161343627767494697658653 4560503860412810511621995)
          ·
            refine ⟨6840755790619215767432993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4560503860412810511621995 6840755790619215767432993)
            ·
              refine ⟨5130566842964411825574745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6840755790619215767432993 5130566842964411825574745)
              ·
                refine ⟨3847925132223308869181059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5130566842964411825574745 3847925132223308869181059)
                ·
                  refine ⟨5771887698334963303771589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3847925132223308869181059 5771887698334963303771589)
                  ·
                    refine ⟨1082228943437805619457173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5771887698334963303771589 1082228943437805619457173)
                    ·
                      rfl

theorem cell23_6322900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_6322900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322900 prefixEnd_6322900 := by exact prefixLift 6322900
  have htrace : WordTrace (prefixWord ++ tailWord_6322900) baseStart_6322900 baseEnd_6322900 := by
    simpa [prefixWord, tailWord_6322900, baseEnd_6322900] using wordTrace_append hprefix tailTrace_6322900
  have hstable : (prefixWord ++ tailWord_6322900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322900).length < 2 ^ (prefixWord ++ tailWord_6322900).sum := by decide
  have hdescent : baseEnd_6322900 < baseStart_6322900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322929 : List Nat := [1, 2, 2, 2, 2, 2, 3, 2, 3, 2, 2]
def baseStart_6322929 : Nat := 118140960795 + 6322929 * 2 ^ 59
def prefixEnd_6322929 : Nat := 4983230072969 + 3 ^ 40 * 6322929 * 2
def baseEnd_6322929 : Nat := 3246701721252397244908885

theorem tailTrace_6322929 : CollatzResearch.WordTrace tailWord_6322929 prefixEnd_6322929 3246701721252397244908885 := by
  unfold tailWord_6322929
  simp only [CollatzResearch.WordTrace]
  refine ⟨230616166510115578145443841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153744111006743718763629227 230616166510115578145443841)
  ·
    refine ⟨172962124882586683609082881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230616166510115578145443841 172962124882586683609082881)
    ·
      refine ⟨129721593661940012706812161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172962124882586683609082881 129721593661940012706812161)
      ·
        refine ⟨97291195246455009530109121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129721593661940012706812161 97291195246455009530109121)
        ·
          refine ⟨72968396434841257147581841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97291195246455009530109121 72968396434841257147581841)
          ·
            refine ⟨54726297326130942860686381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72968396434841257147581841 54726297326130942860686381)
            ·
              refine ⟨20522361497299103572757393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54726297326130942860686381 20522361497299103572757393)
              ·
                refine ⟨15391771122974327679568045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20522361497299103572757393 15391771122974327679568045)
                ·
                  refine ⟨5771914171115372879838017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15391771122974327679568045 5771914171115372879838017)
                  ·
                    refine ⟨4328935628336529659878513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5771914171115372879838017 4328935628336529659878513)
                    ·
                      refine ⟨3246701721252397244908885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4328935628336529659878513 3246701721252397244908885)
                      ·
                        rfl

theorem cell23_6322929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 2, 2].length) (baseStart_6322929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322929 prefixEnd_6322929 := by exact prefixLift 6322929
  have htrace : WordTrace (prefixWord ++ tailWord_6322929) baseStart_6322929 baseEnd_6322929 := by
    simpa [prefixWord, tailWord_6322929, baseEnd_6322929] using wordTrace_append hprefix tailTrace_6322929
  have hstable : (prefixWord ++ tailWord_6322929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322929).length < 2 ^ (prefixWord ++ tailWord_6322929).sum := by decide
  have hdescent : baseEnd_6322929 < baseStart_6322929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322933 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_6322933 : Nat := 118140960795 + 6322933 * 2 ^ 59
def prefixEnd_6322933 : Nat := 4983230072969 + 3 ^ 40 * 6322933 * 2
def baseEnd_6322933 : Nat := 3246703775175015229258867

theorem tailTrace_6322933 : CollatzResearch.WordTrace tailWord_6322933 prefixEnd_6322933 3246703775175015229258867 := by
  unfold tailWord_6322933
  simp only [CollatzResearch.WordTrace]
  refine ⟨230616312402101086828589453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153744208268067391219059635 230616312402101086828589453)
  ·
    refine ⟨86481117150787907560721045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230616312402101086828589453 86481117150787907560721045)
    ·
      refine ⟨4053802366443183166908799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86481117150787907560721045 4053802366443183166908799)
      ·
        refine ⟨6080703549664774750363199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4053802366443183166908799 6080703549664774750363199)
        ·
          refine ⟨9121055324497162125544799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6080703549664774750363199 9121055324497162125544799)
          ·
            refine ⟨13681582986745743188317199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9121055324497162125544799 13681582986745743188317199)
            ·
              refine ⟨20522374480118614782475799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13681582986745743188317199 20522374480118614782475799)
              ·
                refine ⟨30783561720177922173713699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20522374480118614782475799 30783561720177922173713699)
                ·
                  refine ⟨46175342580266883260570549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30783561720177922173713699 46175342580266883260570549)
                  ·
                    refine ⟨4328938366900020305678489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46175342580266883260570549 4328938366900020305678489)
                    ·
                      refine ⟨3246703775175015229258867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4328938366900020305678489 3246703775175015229258867)
                      ·
                        rfl

theorem cell23_6322933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_6322933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322933 prefixEnd_6322933 := by exact prefixLift 6322933
  have htrace : WordTrace (prefixWord ++ tailWord_6322933) baseStart_6322933 baseEnd_6322933 := by
    simpa [prefixWord, tailWord_6322933, baseEnd_6322933] using wordTrace_append hprefix tailTrace_6322933
  have hstable : (prefixWord ++ tailWord_6322933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322933).length < 2 ^ (prefixWord ++ tailWord_6322933).sum := by decide
  have hdescent : baseEnd_6322933 < baseStart_6322933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322946 : List Nat := [3, 4, 1, 1, 1, 2, 4, 1, 1, 1, 4]
def baseStart_6322946 : Nat := 118140960795 + 6322946 * 2 ^ 59
def prefixEnd_6322946 : Nat := 4983230072969 + 3 ^ 40 * 6322946 * 2
def baseEnd_6322946 : Nat := 3246710450423523678396307

theorem tailTrace_6322946 : CollatzResearch.WordTrace tailWord_6322946 prefixEnd_6322946 3246710450423523678396307 := by
  unfold tailWord_6322946
  simp only [CollatzResearch.WordTrace]
  refine ⟨57654196637763497512203173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153744524367369326699208461 57654196637763497512203173)
  ·
    refine ⟨10810161869580655783538095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57654196637763497512203173 10810161869580655783538095)
    ·
      refine ⟨16215242804370983675307143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10810161869580655783538095 16215242804370983675307143)
      ·
        refine ⟨24322864206556475512960715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16215242804370983675307143 24322864206556475512960715)
        ·
          refine ⟨36484296309834713269441073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24322864206556475512960715 36484296309834713269441073)
          ·
            refine ⟨27363222232376034952080805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36484296309834713269441073 27363222232376034952080805)
            ·
              refine ⟨5130604168570506553515151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27363222232376034952080805 5130604168570506553515151)
              ·
                refine ⟨7695906252855759830272727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5130604168570506553515151 7695906252855759830272727)
                ·
                  refine ⟨11543859379283639745409091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7695906252855759830272727 11543859379283639745409091)
                  ·
                    refine ⟨17315789068925459618113637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11543859379283639745409091 17315789068925459618113637)
                    ·
                      refine ⟨3246710450423523678396307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17315789068925459618113637 3246710450423523678396307)
                      ·
                        rfl

theorem cell23_6322946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_6322946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322946 prefixEnd_6322946 := by exact prefixLift 6322946
  have htrace : WordTrace (prefixWord ++ tailWord_6322946) baseStart_6322946 baseEnd_6322946 := by
    simpa [prefixWord, tailWord_6322946, baseEnd_6322946] using wordTrace_append hprefix tailTrace_6322946
  have hstable : (prefixWord ++ tailWord_6322946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322946).length < 2 ^ (prefixWord ++ tailWord_6322946).sum := by decide
  have hdescent : baseEnd_6322946 < baseStart_6322946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322973 : List Nat := [1, 4, 2, 4, 1, 1, 3, 1, 2, 4]
def baseStart_6322973 : Nat := 118140960795 + 6322973 * 2 ^ 59
def prefixEnd_6322973 : Nat := 4983230072969 + 3 ^ 40 * 6322973 * 2
def baseEnd_6322973 : Nat := 1082241438133731690919561

theorem tailTrace_6322973 : CollatzResearch.WordTrace tailWord_6322973 prefixEnd_6322973 1082241438133731690919561 := by
  unfold tailWord_6322973
  simp only [CollatzResearch.WordTrace]
  refine ⟨230617771321956173660045573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153745180881304115773363715 230617771321956173660045573)
  ·
    refine ⟨43240832122866782561258545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230617771321956173660045573 43240832122866782561258545)
    ·
      refine ⟨32430624092150086920943909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43240832122866782561258545 32430624092150086920943909)
      ·
        refine ⟨6080742017278141297676983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32430624092150086920943909 6080742017278141297676983)
        ·
          refine ⟨9121113025917211946515475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6080742017278141297676983 9121113025917211946515475)
          ·
            refine ⟨13681669538875817919773213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9121113025917211946515475 13681669538875817919773213)
            ·
              refine ⟨5130626077078431719914955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13681669538875817919773213 5130626077078431719914955)
              ·
                refine ⟨7695939115617647579872433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5130626077078431719914955 7695939115617647579872433)
                ·
                  refine ⟨5771954336713235684904325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7695939115617647579872433 5771954336713235684904325)
                  ·
                    refine ⟨1082241438133731690919561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5771954336713235684904325 1082241438133731690919561)
                    ·
                      rfl

theorem cell23_6322973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_6322973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322973 prefixEnd_6322973 := by exact prefixLift 6322973
  have htrace : WordTrace (prefixWord ++ tailWord_6322973) baseStart_6322973 baseEnd_6322973 := by
    simpa [prefixWord, tailWord_6322973, baseEnd_6322973] using wordTrace_append hprefix tailTrace_6322973
  have hstable : (prefixWord ++ tailWord_6322973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322973).length < 2 ^ (prefixWord ++ tailWord_6322973).sum := by decide
  have hdescent : baseEnd_6322973 < baseStart_6322973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6322986 : List Nat := [3, 1, 4, 3, 1, 2, 2, 7]
def baseStart_6322986 : Nat := 118140960795 + 6322986 * 2 ^ 59
def prefixEnd_6322986 : Nat := 4983230072969 + 3 ^ 40 * 6322986 * 2
def baseEnd_6322986 : Nat := 120249295912951982292449

theorem tailTrace_6322986 : CollatzResearch.WordTrace tailWord_6322986 prefixEnd_6322986 120249295912951982292449 := by
  unfold tailWord_6322986
  simp only [CollatzResearch.WordTrace]
  refine ⟨57654561367727269220067203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153745496980606051253512541 57654561367727269220067203)
  ·
    refine ⟨86481842051590903830100805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57654561367727269220067203 86481842051590903830100805)
    ·
      refine ⟨16215345384673294468143901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86481842051590903830100805 16215345384673294468143901)
      ·
        refine ⟨6080754519252485425553963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16215345384673294468143901 6080754519252485425553963)
        ·
          refine ⟨9121131778878728138330945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6080754519252485425553963 9121131778878728138330945)
          ·
            refine ⟨6840848834159046103748209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9121131778878728138330945 6840848834159046103748209)
            ·
              refine ⟨5130636625619284577811157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6840848834159046103748209 5130636625619284577811157)
              ·
                refine ⟨120249295912951982292449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5130636625619284577811157 120249295912951982292449)
                ·
                  rfl

theorem cell23_6322986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 7].length) (baseStart_6322986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6322986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6322986 prefixEnd_6322986 := by exact prefixLift 6322986
  have htrace : WordTrace (prefixWord ++ tailWord_6322986) baseStart_6322986 baseEnd_6322986 := by
    simpa [prefixWord, tailWord_6322986, baseEnd_6322986] using wordTrace_append hprefix tailTrace_6322986
  have hstable : (prefixWord ++ tailWord_6322986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6322986).length < 2 ^ (prefixWord ++ tailWord_6322986).sum := by decide
  have hdescent : baseEnd_6322986 < baseStart_6322986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6322986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323014 : List Nat := [6, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2]
def baseStart_6323014 : Nat := 118140960795 + 6323014 * 2 ^ 59
def prefixEnd_6323014 : Nat := 4983230072969 + 3 ^ 40 * 6323014 * 2
def baseEnd_6323014 : Nat := 3246745367108029412345995

theorem tailTrace_6323014 : CollatzResearch.WordTrace tailWord_6323014 prefixEnd_6323014 3246745367108029412345995 := by
  unfold tailWord_6323014
  simp only [CollatzResearch.WordTrace]
  refine ⟨7206852084837738676946503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 153746177809871758441525397 7206852084837738676946503)
  ·
    refine ⟨10810278127256608015419755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7206852084837738676946503 10810278127256608015419755)
    ·
      refine ⟨16215417190884912023129633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10810278127256608015419755 16215417190884912023129633)
      ·
        refine ⟨12161562893163684017347225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16215417190884912023129633 12161562893163684017347225)
        ·
          refine ⟨9121172169872763013010419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12161562893163684017347225 9121172169872763013010419)
          ·
            refine ⟨13681758254809144519515629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9121172169872763013010419 13681758254809144519515629)
            ·
              refine ⟨5130659345553429194818361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13681758254809144519515629 5130659345553429194818361)
              ·
                refine ⟨3847994509165071896113771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5130659345553429194818361 3847994509165071896113771)
                ·
                  refine ⟨5771991763747607844170657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3847994509165071896113771 5771991763747607844170657)
                  ·
                    refine ⟨4328993822810705883127993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5771991763747607844170657 4328993822810705883127993)
                    ·
                      refine ⟨3246745367108029412345995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4328993822810705883127993 3246745367108029412345995)
                      ·
                        rfl

theorem cell23_6323014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_6323014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323014 prefixEnd_6323014 := by exact prefixLift 6323014
  have htrace : WordTrace (prefixWord ++ tailWord_6323014) baseStart_6323014 baseEnd_6323014 := by
    simpa [prefixWord, tailWord_6323014, baseEnd_6323014] using wordTrace_append hprefix tailTrace_6323014
  have hstable : (prefixWord ++ tailWord_6323014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323014).length < 2 ^ (prefixWord ++ tailWord_6323014).sum := by decide
  have hdescent : baseEnd_6323014 < baseStart_6323014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323055 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 1, 7]
def baseStart_6323055 : Nat := 118140960795 + 6323055 * 2 ^ 59
def prefixEnd_6323055 : Nat := 4983230072969 + 3 ^ 40 * 6323055 * 2
def baseEnd_6323055 : Nat := 1082255473271621250644435

theorem tailTrace_6323055 : CollatzResearch.WordTrace tailWord_6323055 prefixEnd_6323055 1082255473271621250644435 := by
  unfold tailWord_6323055
  simp only [CollatzResearch.WordTrace]
  refine ⟨230620762107659101664530619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153747174738439401109687079 230620762107659101664530619)
  ·
    refine ⟨345931143161488652496795929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230620762107659101664530619 345931143161488652496795929)
    ·
      refine ⟨259448357371116489372596947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345931143161488652496795929 259448357371116489372596947)
      ·
        refine ⟨389172536056674734058895421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259448357371116489372596947 389172536056674734058895421)
        ·
          refine ⟨145939701021253025272085783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389172536056674734058895421 145939701021253025272085783)
          ·
            refine ⟨218909551531879537908128675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145939701021253025272085783 218909551531879537908128675)
            ·
              refine ⟨328364327297819306862193013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218909551531879537908128675 328364327297819306862193013)
              ·
                refine ⟨30784155684170560018330595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 328364327297819306862193013 30784155684170560018330595)
                ·
                  refine ⟨46176233526255840027495893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30784155684170560018330595 46176233526255840027495893)
                  ·
                    refine ⟨1082255473271621250644435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46176233526255840027495893 1082255473271621250644435)
                    ·
                      rfl

theorem cell23_6323055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 7].length) (baseStart_6323055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323055 prefixEnd_6323055 := by exact prefixLift 6323055
  have htrace : WordTrace (prefixWord ++ tailWord_6323055) baseStart_6323055 baseEnd_6323055 := by
    simpa [prefixWord, tailWord_6323055, baseEnd_6323055] using wordTrace_append hprefix tailTrace_6323055
  have hstable : (prefixWord ++ tailWord_6323055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323055).length < 2 ^ (prefixWord ++ tailWord_6323055).sum := by decide
  have hdescent : baseEnd_6323055 < baseStart_6323055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323079 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 2, 5, 2]
def baseStart_6323079 : Nat := 118140960795 + 6323079 * 2 ^ 59
def prefixEnd_6323079 : Nat := 4983230072969 + 3 ^ 40 * 6323079 * 2
def baseEnd_6323079 : Nat := 3246778743350571658033195

theorem tailTrace_6323079 : CollatzResearch.WordTrace tailWord_6323079 prefixEnd_6323079 3246778743350571658033195 := by
  unfold tailWord_6323079
  simp only [CollatzResearch.WordTrace]
  refine ⟨230621637459572153763404291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153747758306381435842269527 230621637459572153763404291)
  ·
    refine ⟨345932456189358230645106437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230621637459572153763404291 345932456189358230645106437)
    ·
      refine ⟨64862335535504668245957457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 345932456189358230645106437 64862335535504668245957457)
      ·
        refine ⟨48646751651628501184468093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64862335535504668245957457 48646751651628501184468093)
        ·
          refine ⟨18242531869360687944175535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48646751651628501184468093 18242531869360687944175535)
          ·
            refine ⟨27363797804041031916263303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18242531869360687944175535 27363797804041031916263303)
            ·
              refine ⟨41045696706061547874394955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27363797804041031916263303 41045696706061547874394955)
              ·
                refine ⟨61568545059092321811592433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41045696706061547874394955 61568545059092321811592433)
                ·
                  refine ⟨46176408794319241358694325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61568545059092321811592433 46176408794319241358694325)
                  ·
                    refine ⟨4329038324467428877377593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46176408794319241358694325 4329038324467428877377593)
                    ·
                      refine ⟨3246778743350571658033195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4329038324467428877377593 3246778743350571658033195)
                      ·
                        rfl

theorem cell23_6323079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_6323079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323079 prefixEnd_6323079 := by exact prefixLift 6323079
  have htrace : WordTrace (prefixWord ++ tailWord_6323079) baseStart_6323079 baseEnd_6323079 := by
    simpa [prefixWord, tailWord_6323079, baseEnd_6323079] using wordTrace_append hprefix tailTrace_6323079
  have hstable : (prefixWord ++ tailWord_6323079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323079).length < 2 ^ (prefixWord ++ tailWord_6323079).sum := by decide
  have hdescent : baseEnd_6323079 < baseStart_6323079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323106 : List Nat := [3, 3, 1, 2, 2, 3, 1, 1, 2, 5]
def baseStart_6323106 : Nat := 118140960795 + 6323106 * 2 ^ 59
def prefixEnd_6323106 : Nat := 4983230072969 + 3 ^ 40 * 6323106 * 2
def baseEnd_6323106 : Nat := 1082264202442747684131857

theorem tailTrace_6323106 : CollatzResearch.WordTrace tailWord_6323106 prefixEnd_6323106 1082264202442747684131857 := by
  unfold tailWord_6323106
  simp only [CollatzResearch.WordTrace]
  refine ⟨57655655557618584343659293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153748414820316224916424781 57655655557618584343659293)
  ·
    refine ⟨21620870834106969128872235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57655655557618584343659293 21620870834106969128872235)
    ·
      refine ⟨32431306251160453693308353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21620870834106969128872235 32431306251160453693308353)
      ·
        refine ⟨24323479688370340269981265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32431306251160453693308353 24323479688370340269981265)
        ·
          refine ⟨18242609766277755202485949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24323479688370340269981265 18242609766277755202485949)
          ·
            refine ⟨6840978662354158200932231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18242609766277755202485949 6840978662354158200932231)
            ·
              refine ⟨10261467993531237301398347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6840978662354158200932231 10261467993531237301398347)
              ·
                refine ⟨15392201990296855952097521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10261467993531237301398347 15392201990296855952097521)
                ·
                  refine ⟨11544151492722641964073141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15392201990296855952097521 11544151492722641964073141)
                  ·
                    refine ⟨1082264202442747684131857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11544151492722641964073141 1082264202442747684131857)
                    ·
                      rfl

theorem cell23_6323106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_6323106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323106 prefixEnd_6323106 := by exact prefixLift 6323106
  have htrace : WordTrace (prefixWord ++ tailWord_6323106) baseStart_6323106 baseEnd_6323106 := by
    simpa [prefixWord, tailWord_6323106, baseEnd_6323106] using wordTrace_append hprefix tailTrace_6323106
  have hstable : (prefixWord ++ tailWord_6323106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323106).length < 2 ^ (prefixWord ++ tailWord_6323106).sum := by decide
  have hdescent : baseEnd_6323106 < baseStart_6323106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323115 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 10]
def baseStart_6323115 : Nat := 118140960795 + 6323115 * 2 ^ 59
def prefixEnd_6323115 : Nat := 4983230072969 + 3 ^ 40 * 6323115 * 2
def baseEnd_6323115 : Nat := 360755247628237057464781

theorem tailTrace_6323115 : CollatzResearch.WordTrace tailWord_6323115 prefixEnd_6323115 360755247628237057464781 := by
  unfold tailWord_6323115
  simp only [CollatzResearch.WordTrace]
  refine ⟨230622950487441731911714799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153748633658294487941143199 230622950487441731911714799)
  ·
    refine ⟨345934425731162597867572199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230622950487441731911714799 345934425731162597867572199)
    ·
      refine ⟨518901638596743896801358299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345934425731162597867572199 518901638596743896801358299)
      ·
        refine ⟨778352457895115845202037449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518901638596743896801358299 778352457895115845202037449)
        ·
          refine ⟨583764343421336883901528087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 778352457895115845202037449 583764343421336883901528087)
          ·
            refine ⟨875646515132005325852292131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583764343421336883901528087 875646515132005325852292131)
            ·
              refine ⟨1313469772698007988778438197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 875646515132005325852292131 1313469772698007988778438197)
              ·
                refine ⟨123137791190438248947978581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1313469772698007988778438197 123137791190438248947978581)
                ·
                  refine ⟨360755247628237057464781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 123137791190438248947978581 360755247628237057464781)
                  ·
                    rfl

theorem cell23_6323115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 10].length) (baseStart_6323115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323115 prefixEnd_6323115 := by exact prefixLift 6323115
  have htrace : WordTrace (prefixWord ++ tailWord_6323115) baseStart_6323115 baseEnd_6323115 := by
    simpa [prefixWord, tailWord_6323115, baseEnd_6323115] using wordTrace_append hprefix tailTrace_6323115
  have hstable : (prefixWord ++ tailWord_6323115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323115).length < 2 ^ (prefixWord ++ tailWord_6323115).sum := by decide
  have hdescent : baseEnd_6323115 < baseStart_6323115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323136 : List Nat := [2, 1, 1, 2, 3, 3, 2, 4, 1, 4]
def baseStart_6323136 : Nat := 118140960795 + 6323136 * 2 ^ 59
def prefixEnd_6323136 : Nat := 4983230072969 + 3 ^ 40 * 6323136 * 2
def baseEnd_6323136 : Nat := 1082269337249292645006811

theorem tailTrace_6323136 : CollatzResearch.WordTrace tailWord_6323136 prefixEnd_6323136 1082269337249292645006811 := by
  unfold tailWord_6323136
  simp only [CollatzResearch.WordTrace]
  refine ⟨115311858210182826249114631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153749144280243768332152841 115311858210182826249114631)
  ·
    refine ⟨172967787315274239373671947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115311858210182826249114631 172967787315274239373671947)
    ·
      refine ⟨259451680972911359060507921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172967787315274239373671947 259451680972911359060507921)
      ·
        refine ⟨194588760729683519295380941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259451680972911359060507921 194588760729683519295380941)
        ·
          refine ⟨72970785273631319735767853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194588760729683519295380941 72970785273631319735767853)
          ·
            refine ⟨27364044477611744900912945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72970785273631319735767853 27364044477611744900912945)
            ·
              refine ⟨20523033358208808675684709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27364044477611744900912945 20523033358208808675684709)
              ·
                refine ⟨3848068754664151626690883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20523033358208808675684709 3848068754664151626690883)
                ·
                  refine ⟨5772103131996227440036325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3848068754664151626690883 5772103131996227440036325)
                  ·
                    refine ⟨1082269337249292645006811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5772103131996227440036325 1082269337249292645006811)
                    ·
                      rfl

theorem cell23_6323136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 1, 4].length) (baseStart_6323136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323136 prefixEnd_6323136 := by exact prefixLift 6323136
  have htrace : WordTrace (prefixWord ++ tailWord_6323136) baseStart_6323136 baseEnd_6323136 := by
    simpa [prefixWord, tailWord_6323136, baseEnd_6323136] using wordTrace_append hprefix tailTrace_6323136
  have hstable : (prefixWord ++ tailWord_6323136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323136).length < 2 ^ (prefixWord ++ tailWord_6323136).sum := by decide
  have hdescent : baseEnd_6323136 < baseStart_6323136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323159 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 5, 1, 3]
def baseStart_6323159 : Nat := 118140960795 + 6323159 * 2 ^ 59
def prefixEnd_6323159 : Nat := 4983230072969 + 3 ^ 40 * 6323159 * 2
def baseEnd_6323159 : Nat := 3246819821802931345032827

theorem tailTrace_6323159 : CollatzResearch.WordTrace tailWord_6323159 prefixEnd_6323159 3246819821802931345032827 := by
  unfold tailWord_6323159
  simp only [CollatzResearch.WordTrace]
  refine ⟨230624555299282327426316531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153749703532854884950877687 230624555299282327426316531)
  ·
    refine ⟨345936832948923491139474797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230624555299282327426316531 345936832948923491139474797)
    ·
      refine ⟨129726312355846309177303049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345936832948923491139474797 129726312355846309177303049)
      ·
        refine ⟨97294734266884731882977287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129726312355846309177303049 97294734266884731882977287)
        ·
          refine ⟨145942101400327097824465931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97294734266884731882977287 145942101400327097824465931)
          ·
            refine ⟨218913152100490646736698897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145942101400327097824465931 218913152100490646736698897)
            ·
              refine ⟨164184864075367985052524173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218913152100490646736698897 164184864075367985052524173)
              ·
                refine ⟨61569324028262994394696565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164184864075367985052524173 61569324028262994394696565)
                ·
                  refine ⟨5772124127649655724502803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61569324028262994394696565 5772124127649655724502803)
                  ·
                    refine ⟨8658186191474483586754205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5772124127649655724502803 8658186191474483586754205)
                    ·
                      refine ⟨3246819821802931345032827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8658186191474483586754205 3246819821802931345032827)
                      ·
                        rfl

theorem cell23_6323159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_6323159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323159 prefixEnd_6323159 := by exact prefixLift 6323159
  have htrace : WordTrace (prefixWord ++ tailWord_6323159) baseStart_6323159 baseEnd_6323159 := by
    simpa [prefixWord, tailWord_6323159, baseEnd_6323159] using wordTrace_append hprefix tailTrace_6323159
  have hstable : (prefixWord ++ tailWord_6323159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323159).length < 2 ^ (prefixWord ++ tailWord_6323159).sum := by decide
  have hdescent : baseEnd_6323159 < baseStart_6323159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323170 : List Nat := [3, 3, 3, 1, 1, 1, 3, 3, 1, 4]
def baseStart_6323170 : Nat := 118140960795 + 6323170 * 2 ^ 59
def prefixEnd_6323170 : Nat := 4983230072969 + 3 ^ 40 * 6323170 * 2
def baseEnd_6323170 : Nat := 1082275156696710267331759

theorem tailTrace_6323170 : CollatzResearch.WordTrace tailWord_6323170 prefixEnd_6323170 1082275156696710267331759 := by
  unfold tailWord_6323170
  simp only [CollatzResearch.WordTrace]
  refine ⟨57656239125560619076241741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153749971001494984203311309 57656239125560619076241741)
  ·
    refine ⟨21621089672085232153590653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57656239125560619076241741 21621089672085232153590653)
    ·
      refine ⟨8107908627031962057596495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21621089672085232153590653 8107908627031962057596495)
      ·
        refine ⟨12161862940547943086394743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8107908627031962057596495 12161862940547943086394743)
        ·
          refine ⟨18242794410821914629592115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12161862940547943086394743 18242794410821914629592115)
          ·
            refine ⟨27364191616232871944388173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18242794410821914629592115 27364191616232871944388173)
            ·
              refine ⟨10261571856087326979145565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27364191616232871944388173 10261571856087326979145565)
              ·
                refine ⟨3848089446032747617179587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10261571856087326979145565 3848089446032747617179587)
                ·
                  refine ⟨5772134169049121425769381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3848089446032747617179587 5772134169049121425769381)
                  ·
                    refine ⟨1082275156696710267331759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5772134169049121425769381 1082275156696710267331759)
                    ·
                      rfl

theorem cell23_6323170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_6323170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323170 prefixEnd_6323170 := by exact prefixLift 6323170
  have htrace : WordTrace (prefixWord ++ tailWord_6323170) baseStart_6323170 baseEnd_6323170 := by
    simpa [prefixWord, tailWord_6323170, baseEnd_6323170] using wordTrace_append hprefix tailTrace_6323170
  have hstable : (prefixWord ++ tailWord_6323170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323170).length < 2 ^ (prefixWord ++ tailWord_6323170).sum := by decide
  have hdescent : baseEnd_6323170 < baseStart_6323170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323233 : List Nat := [1, 2, 3, 2, 3, 2, 3, 1, 1, 1, 4]
def baseStart_6323233 : Nat := 118140960795 + 6323233 * 2 ^ 59
def prefixEnd_6323233 : Nat := 4983230072969 + 3 ^ 40 * 6323233 * 2
def baseEnd_6323233 : Nat := 3246857819371364055507487

theorem tailTrace_6323233 : CollatzResearch.WordTrace tailWord_6323233 prefixEnd_6323233 3246857819371364055507487 := by
  unfold tailWord_6323233
  simp only [CollatzResearch.WordTrace]
  refine ⟨230627254301014238064510353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153751502867342825376340235 230627254301014238064510353)
  ·
    refine ⟨172970440725760678548382765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230627254301014238064510353 172970440725760678548382765)
    ·
      refine ⟨64863915272160254455643537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172970440725760678548382765 64863915272160254455643537)
      ·
        refine ⟨48647936454120190841732653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64863915272160254455643537 48647936454120190841732653)
        ·
          refine ⟨18242976170295071565649745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48647936454120190841732653 18242976170295071565649745)
          ·
            refine ⟨13682232127721303674237309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18242976170295071565649745 13682232127721303674237309)
            ·
              refine ⟨5130837047895488877838991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13682232127721303674237309 5130837047895488877838991)
              ·
                refine ⟨7696255571843233316758487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5130837047895488877838991 7696255571843233316758487)
                ·
                  refine ⟨11544383357764849975137731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7696255571843233316758487 11544383357764849975137731)
                  ·
                    refine ⟨17316575036647274962706597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11544383357764849975137731 17316575036647274962706597)
                    ·
                      refine ⟨3246857819371364055507487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17316575036647274962706597 3246857819371364055507487)
                      ·
                        rfl

theorem cell23_6323233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_6323233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323233 prefixEnd_6323233 := by exact prefixLift 6323233
  have htrace : WordTrace (prefixWord ++ tailWord_6323233) baseStart_6323233 baseEnd_6323233 := by
    simpa [prefixWord, tailWord_6323233, baseEnd_6323233] using wordTrace_append hprefix tailTrace_6323233
  have hstable : (prefixWord ++ tailWord_6323233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323233).length < 2 ^ (prefixWord ++ tailWord_6323233).sum := by decide
  have hdescent : baseEnd_6323233 < baseStart_6323233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323236 : List Nat := [2, 3, 1, 4, 1, 1, 3, 1, 1, 1, 5]
def baseStart_6323236 : Nat := 118140960795 + 6323236 * 2 ^ 59
def prefixEnd_6323236 : Nat := 4983230072969 + 3 ^ 40 * 6323236 * 2
def baseEnd_6323236 : Nat := 3246859359813327543769973

theorem tailTrace_6323236 : CollatzResearch.WordTrace tailWord_6323236 prefixEnd_6323236 3246859359813327543769973 := by
  unfold tailWord_6323236
  simp only [CollatzResearch.WordTrace]
  refine ⟨115313681860001684788434781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153751575813335579717913041 115313681860001684788434781)
  ·
    refine ⟨43242630697500631795663043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115313681860001684788434781 43242630697500631795663043)
    ·
      refine ⟨64863946046250947693494565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43242630697500631795663043 64863946046250947693494565)
      ·
        refine ⟨12161989883672052692530231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64863946046250947693494565 12161989883672052692530231)
        ·
          refine ⟨18242984825508079038795347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12161989883672052692530231 18242984825508079038795347)
          ·
            refine ⟨27364477238262118558193021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18242984825508079038795347 27364477238262118558193021)
            ·
              refine ⟨10261678964348294459322383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27364477238262118558193021 10261678964348294459322383)
              ·
                refine ⟨15392518446522441688983575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10261678964348294459322383 15392518446522441688983575)
                ·
                  refine ⟨23088777669783662533475363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15392518446522441688983575 23088777669783662533475363)
                  ·
                    refine ⟨34633166504675493800213045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23088777669783662533475363 34633166504675493800213045)
                    ·
                      refine ⟨3246859359813327543769973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34633166504675493800213045 3246859359813327543769973)
                      ·
                        rfl

theorem cell23_6323236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_6323236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323236 prefixEnd_6323236 := by exact prefixLift 6323236
  have htrace : WordTrace (prefixWord ++ tailWord_6323236) baseStart_6323236 baseEnd_6323236 := by
    simpa [prefixWord, tailWord_6323236, baseEnd_6323236] using wordTrace_append hprefix tailTrace_6323236
  have hstable : (prefixWord ++ tailWord_6323236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323236).length < 2 ^ (prefixWord ++ tailWord_6323236).sum := by decide
  have hdescent : baseEnd_6323236 < baseStart_6323236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323239 : List Nat := [1, 1, 7, 1, 1, 12]
def baseStart_6323239 : Nat := 118140960795 + 6323239 * 2 ^ 59
def prefixEnd_6323239 : Nat := 4983230072969 + 3 ^ 40 * 6323239 * 2
def baseEnd_6323239 : Nat := 13361567490762514535113

theorem tailTrace_6323239 : CollatzResearch.WordTrace tailWord_6323239 prefixEnd_6323239 13361567490762514535113 := by
  unfold tailWord_6323239
  simp only [CollatzResearch.WordTrace]
  refine ⟨230627473138992501089228771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153751648759328334059485847 230627473138992501089228771)
  ·
    refine ⟨345941209708488751633843157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230627473138992501089228771 345941209708488751633843157)
    ·
      refine ⟨8107997102542705116418199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 345941209708488751633843157 8107997102542705116418199)
      ·
        refine ⟨12161995653814057674627299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8107997102542705116418199 12161995653814057674627299)
        ·
          refine ⟨18242993480721086511940949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12161995653814057674627299 18242993480721086511940949)
          ·
            refine ⟨13361567490762514535113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 18242993480721086511940949 13361567490762514535113)
            ·
              rfl

theorem cell23_6323239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 12].length) (baseStart_6323239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323239 prefixEnd_6323239 := by exact prefixLift 6323239
  have htrace : WordTrace (prefixWord ++ tailWord_6323239) baseStart_6323239 baseEnd_6323239 := by
    simpa [prefixWord, tailWord_6323239, baseEnd_6323239] using wordTrace_append hprefix tailTrace_6323239
  have hstable : (prefixWord ++ tailWord_6323239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323239).length < 2 ^ (prefixWord ++ tailWord_6323239).sum := by decide
  have hdescent : baseEnd_6323239 < baseStart_6323239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323249 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 3, 3, 3]
def baseStart_6323249 : Nat := 118140960795 + 6323249 * 2 ^ 59
def prefixEnd_6323249 : Nat := 4983230072969 + 3 ^ 40 * 6323249 * 2
def baseEnd_6323249 : Nat := 3246866035061835992907413

theorem tailTrace_6323249 : CollatzResearch.WordTrace tailWord_6323249 prefixEnd_6323249 3246866035061835992907413 := by
  unfold tailWord_6323249
  simp only [CollatzResearch.WordTrace]
  refine ⟨230627837868956272797092801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153751891912637515198061867 230627837868956272797092801)
  ·
    refine ⟨172970878401717204597819601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230627837868956272797092801 172970878401717204597819601)
    ·
      refine ⟨129728158801287903448364701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172970878401717204597819601 129728158801287903448364701)
      ·
        refine ⟨48648059550482963793136763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129728158801287903448364701 48648059550482963793136763)
        ·
          refine ⟨72972089325724445689705145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48648059550482963793136763 72972089325724445689705145)
          ·
            refine ⟨54729066994293334267278859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72972089325724445689705145 54729066994293334267278859)
            ·
              refine ⟨82093600491440001400918289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54729066994293334267278859 82093600491440001400918289)
              ·
                refine ⟨61570200368580001050688717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82093600491440001400918289 61570200368580001050688717)
                ·
                  refine ⟨23088825138217500394008269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61570200368580001050688717 23088825138217500394008269)
                  ·
                    refine ⟨8658309426831562647753101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23088825138217500394008269 8658309426831562647753101)
                    ·
                      refine ⟨3246866035061835992907413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8658309426831562647753101 3246866035061835992907413)
                      ·
                        rfl

theorem cell23_6323249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_6323249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323249 prefixEnd_6323249 := by exact prefixLift 6323249
  have htrace : WordTrace (prefixWord ++ tailWord_6323249) baseStart_6323249 baseEnd_6323249 := by
    simpa [prefixWord, tailWord_6323249, baseEnd_6323249] using wordTrace_append hprefix tailTrace_6323249
  have hstable : (prefixWord ++ tailWord_6323249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323249).length < 2 ^ (prefixWord ++ tailWord_6323249).sum := by decide
  have hdescent : baseEnd_6323249 < baseStart_6323249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323250 : List Nat := [3, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2]
def baseStart_6323250 : Nat := 118140960795 + 6323250 * 2 ^ 59
def prefixEnd_6323250 : Nat := 4983230072969 + 3 ^ 40 * 6323250 * 2
def baseEnd_6323250 : Nat := 3246866548542490488994909

theorem tailTrace_6323250 : CollatzResearch.WordTrace tailWord_6323250 prefixEnd_6323250 3246866548542490488994909 := by
  unfold tailWord_6323250
  simp only [CollatzResearch.WordTrace]
  refine ⟨57656968585488162491969801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153751916227968433311919469 57656968585488162491969801)
  ·
    refine ⟨43242726439116121868977351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57656968585488162491969801 43242726439116121868977351)
    ·
      refine ⟨64864089658674182803466027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43242726439116121868977351 64864089658674182803466027)
      ·
        refine ⟨97296134488011274205199041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64864089658674182803466027 97296134488011274205199041)
        ·
          refine ⟨72972100866008455653899281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97296134488011274205199041 72972100866008455653899281)
          ·
            refine ⟨54729075649506341740424461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72972100866008455653899281 54729075649506341740424461)
            ·
              refine ⟨20523403368564878152659173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54729075649506341740424461 20523403368564878152659173)
              ·
                refine ⟨3848138131605914653623595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20523403368564878152659173 3848138131605914653623595)
                ·
                  refine ⟨5772207197408871980435393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3848138131605914653623595 5772207197408871980435393)
                  ·
                    refine ⟨4329155398056653985326545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5772207197408871980435393 4329155398056653985326545)
                    ·
                      refine ⟨3246866548542490488994909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4329155398056653985326545 3246866548542490488994909)
                      ·
                        rfl

theorem cell23_6323250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2].length) (baseStart_6323250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323250 prefixEnd_6323250 := by exact prefixLift 6323250
  have htrace : WordTrace (prefixWord ++ tailWord_6323250) baseStart_6323250 baseEnd_6323250 := by
    simpa [prefixWord, tailWord_6323250, baseEnd_6323250] using wordTrace_append hprefix tailTrace_6323250
  have hstable : (prefixWord ++ tailWord_6323250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323250).length < 2 ^ (prefixWord ++ tailWord_6323250).sum := by decide
  have hdescent : baseEnd_6323250 < baseStart_6323250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323259 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 1, 9, 2]
def baseStart_6323259 : Nat := 118140960795 + 6323259 * 2 ^ 59
def prefixEnd_6323259 : Nat := 4983230072969 + 3 ^ 40 * 6323259 * 2
def baseEnd_6323259 : Nat := 3246871169868380953782367

theorem tailTrace_6323259 : CollatzResearch.WordTrace tailWord_6323259 prefixEnd_6323259 3246871169868380953782367 := by
  unfold tailWord_6323259
  simp only [CollatzResearch.WordTrace]
  refine ⟨230628202598920044504956831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153752135065946696336637887 230628202598920044504956831)
  ·
    refine ⟨345942303898380066757435247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230628202598920044504956831 345942303898380066757435247)
    ·
      refine ⟨518913455847570100136152871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345942303898380066757435247 518913455847570100136152871)
      ·
        refine ⟨778370183771355150204229307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518913455847570100136152871 778370183771355150204229307)
        ·
          refine ⟨1167555275657032725306343961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778370183771355150204229307 1167555275657032725306343961)
          ·
            refine ⟨875666456742774543979757971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1167555275657032725306343961 875666456742774543979757971)
            ·
              refine ⟨1313499685114161815969636957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 875666456742774543979757971 1313499685114161815969636957)
              ·
                refine ⟨492562381917810680988613859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1313499685114161815969636957 492562381917810680988613859)
                ·
                  refine ⟨738843572876716021482920789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 492562381917810680988613859 738843572876716021482920789)
                  ·
                    refine ⟨4329161559824507938376489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 738843572876716021482920789 4329161559824507938376489)
                    ·
                      refine ⟨3246871169868380953782367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4329161559824507938376489 3246871169868380953782367)
                      ·
                        rfl

theorem cell23_6323259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 9, 2].length) (baseStart_6323259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323259 prefixEnd_6323259 := by exact prefixLift 6323259
  have htrace : WordTrace (prefixWord ++ tailWord_6323259) baseStart_6323259 baseEnd_6323259 := by
    simpa [prefixWord, tailWord_6323259, baseEnd_6323259] using wordTrace_append hprefix tailTrace_6323259
  have hstable : (prefixWord ++ tailWord_6323259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323259).length < 2 ^ (prefixWord ++ tailWord_6323259).sum := by decide
  have hdescent : baseEnd_6323259 < baseStart_6323259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323317 : List Nat := [1, 3, 4, 3, 2, 1, 1, 1, 1, 3, 3]
def baseStart_6323317 : Nat := 118140960795 + 6323317 * 2 ^ 59
def prefixEnd_6323317 : Nat := 4983230072969 + 3 ^ 40 * 6323317 * 2
def baseEnd_6323317 : Nat := 3246900951746341726857101

theorem tailTrace_6323317 : CollatzResearch.WordTrace tailWord_6323317 prefixEnd_6323317 3246900951746341726857101 := by
  unfold tailWord_6323317
  simp only [CollatzResearch.WordTrace]
  refine ⟨230630318032709920410568205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153753545355139946940378803 230630318032709920410568205)
  ·
    refine ⟨86486369262266220153963077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230630318032709920410568205 86486369262266220153963077)
    ·
      refine ⟨16216194236674916278868077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86486369262266220153963077 16216194236674916278868077)
      ·
        refine ⟨6081072838753093604575529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16216194236674916278868077 6081072838753093604575529)
        ·
          refine ⟨4560804629064820203431647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6081072838753093604575529 4560804629064820203431647)
          ·
            refine ⟨6841206943597230305147471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4560804629064820203431647 6841206943597230305147471)
            ·
              refine ⟨10261810415395845457721207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6841206943597230305147471 10261810415395845457721207)
              ·
                refine ⟨15392715623093768186581811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10261810415395845457721207 15392715623093768186581811)
                ·
                  refine ⟨23089073434640652279872717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15392715623093768186581811 23089073434640652279872717)
                  ·
                    refine ⟨8658402537990244604952269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23089073434640652279872717 8658402537990244604952269)
                    ·
                      refine ⟨3246900951746341726857101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8658402537990244604952269 3246900951746341726857101)
                      ·
                        rfl

theorem cell23_6323317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_6323317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323317 prefixEnd_6323317 := by exact prefixLift 6323317
  have htrace : WordTrace (prefixWord ++ tailWord_6323317) baseStart_6323317 baseEnd_6323317 := by
    simpa [prefixWord, tailWord_6323317, baseEnd_6323317] using wordTrace_append hprefix tailTrace_6323317
  have hstable : (prefixWord ++ tailWord_6323317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323317).length < 2 ^ (prefixWord ++ tailWord_6323317).sum := by decide
  have hdescent : baseEnd_6323317 < baseStart_6323317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323319 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 4]
def baseStart_6323319 : Nat := 118140960795 + 6323319 * 2 ^ 59
def prefixEnd_6323319 : Nat := 4983230072969 + 3 ^ 40 * 6323319 * 2
def baseEnd_6323319 : Nat := 3246901978707650719032091

theorem tailTrace_6323319 : CollatzResearch.WordTrace tailWord_6323319 prefixEnd_6323319 3246901978707650719032091 := by
  unfold tailWord_6323319
  simp only [CollatzResearch.WordTrace]
  refine ⟨230630390978702674752141011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153753593985801783168094007 230630390978702674752141011)
  ·
    refine ⟨345945586468054012128211517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230630390978702674752141011 345945586468054012128211517)
    ·
      refine ⟨129729594925520254548079319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345945586468054012128211517 129729594925520254548079319)
      ·
        refine ⟨194594392388280381822118979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129729594925520254548079319 194594392388280381822118979)
        ·
          refine ⟨291891588582420572733178469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194594392388280381822118979 291891588582420572733178469)
          ·
            refine ⟨54729672859203857387470963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 291891588582420572733178469 54729672859203857387470963)
            ·
              refine ⟨82094509288805786081206445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54729672859203857387470963 82094509288805786081206445)
              ·
                refine ⟨30785440983302169780452417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82094509288805786081206445 30785440983302169780452417)
                ·
                  refine ⟨23089080737476627335339313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30785440983302169780452417 23089080737476627335339313)
                  ·
                    refine ⟨17316810553107470501504485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23089080737476627335339313 17316810553107470501504485)
                    ·
                      refine ⟨3246901978707650719032091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17316810553107470501504485 3246901978707650719032091)
                      ·
                        rfl

theorem cell23_6323319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_6323319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323319 prefixEnd_6323319 := by exact prefixLift 6323319
  have htrace : WordTrace (prefixWord ++ tailWord_6323319) baseStart_6323319 baseEnd_6323319 := by
    simpa [prefixWord, tailWord_6323319, baseEnd_6323319] using wordTrace_append hprefix tailTrace_6323319
  have hstable : (prefixWord ++ tailWord_6323319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323319).length < 2 ^ (prefixWord ++ tailWord_6323319).sum := by decide
  have hdescent : baseEnd_6323319 < baseStart_6323319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323323 : List Nat := [1, 1, 1, 1, 1, 4, 1, 7, 2, 2, 2]
def baseStart_6323323 : Nat := 118140960795 + 6323323 * 2 ^ 59
def prefixEnd_6323323 : Nat := 4983230072969 + 3 ^ 40 * 6323323 * 2
def baseEnd_6323323 : Nat := 3246904032630268703382073

theorem tailTrace_6323323 : CollatzResearch.WordTrace tailWord_6323323 prefixEnd_6323323 3246904032630268703382073 := by
  unfold tailWord_6323323
  simp only [CollatzResearch.WordTrace]
  refine ⟨230630536870688183435286623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153753691247125455623524415 230630536870688183435286623)
  ·
    refine ⟨345945805306032275152929935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230630536870688183435286623 345945805306032275152929935)
    ·
      refine ⟨518918707959048412729394903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345945805306032275152929935 518918707959048412729394903)
      ·
        refine ⟨778378061938572619094092355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518918707959048412729394903 778378061938572619094092355)
        ·
          refine ⟨1167567092907858928641138533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778378061938572619094092355 1167567092907858928641138533)
          ·
            refine ⟨218918829920223549120213475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1167567092907858928641138533 218918829920223549120213475)
            ·
              refine ⟨328378244880335323680320213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218918829920223549120213475 328378244880335323680320213)
              ·
                refine ⟨7696365114382859148757505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 328378244880335323680320213 7696365114382859148757505)
                ·
                  refine ⟨5772273835787144361568129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7696365114382859148757505 5772273835787144361568129)
                  ·
                    refine ⟨4329205376840358271176097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5772273835787144361568129 4329205376840358271176097)
                    ·
                      refine ⟨3246904032630268703382073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4329205376840358271176097 3246904032630268703382073)
                      ·
                        rfl

theorem cell23_6323323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 2, 2].length) (baseStart_6323323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323323 prefixEnd_6323323 := by exact prefixLift 6323323
  have htrace : WordTrace (prefixWord ++ tailWord_6323323) baseStart_6323323 baseEnd_6323323 := by
    simpa [prefixWord, tailWord_6323323, baseEnd_6323323] using wordTrace_append hprefix tailTrace_6323323
  have hstable : (prefixWord ++ tailWord_6323323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323323).length < 2 ^ (prefixWord ++ tailWord_6323323).sum := by decide
  have hdescent : baseEnd_6323323 < baseStart_6323323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323339 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 3]
def baseStart_6323339 : Nat := 118140960795 + 6323339 * 2 ^ 59
def prefixEnd_6323339 : Nat := 4983230072969 + 3 ^ 40 * 6323339 * 2
def baseEnd_6323339 : Nat := 3246912248320740640781999

theorem tailTrace_6323339 : CollatzResearch.WordTrace tailWord_6323339 prefixEnd_6323339 3246912248320740640781999 := by
  unfold tailWord_6323339
  simp only [CollatzResearch.WordTrace]
  refine ⟨230631120438630218167869071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153754080292420145445246047 230631120438630218167869071)
  ·
    refine ⟨345946680657945327251803607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230631120438630218167869071 345946680657945327251803607)
    ·
      refine ⟨518920020986917990877705411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345946680657945327251803607 518920020986917990877705411)
      ·
        refine ⟨778380031480376986316558117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518920020986917990877705411 778380031480376986316558117)
        ·
          refine ⟨145946255902570684934354647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 778380031480376986316558117 145946255902570684934354647)
          ·
            refine ⟨218919383853856027401531971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145946255902570684934354647 218919383853856027401531971)
            ·
              refine ⟨328379075780784041102297957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218919383853856027401531971 328379075780784041102297957)
              ·
                refine ⟨61571076708897007706680867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 328379075780784041102297957 61571076708897007706680867)
                ·
                  refine ⟨92356615063345511560021301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61571076708897007706680867 92356615063345511560021301)
                  ·
                    refine ⟨8658432662188641708751997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92356615063345511560021301 8658432662188641708751997)
                    ·
                      refine ⟨3246912248320740640781999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8658432662188641708751997 3246912248320740640781999)
                      ·
                        rfl

theorem cell23_6323339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 3].length) (baseStart_6323339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323339 prefixEnd_6323339 := by exact prefixLift 6323339
  have htrace : WordTrace (prefixWord ++ tailWord_6323339) baseStart_6323339 baseEnd_6323339 := by
    simpa [prefixWord, tailWord_6323339, baseEnd_6323339] using wordTrace_append hprefix tailTrace_6323339
  have hstable : (prefixWord ++ tailWord_6323339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323339).length < 2 ^ (prefixWord ++ tailWord_6323339).sum := by decide
  have hdescent : baseEnd_6323339 < baseStart_6323339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323379 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 4]
def baseStart_6323379 : Nat := 118140960795 + 6323379 * 2 ^ 59
def prefixEnd_6323379 : Nat := 4983230072969 + 3 ^ 40 * 6323379 * 2
def baseEnd_6323379 : Nat := 3246932787546920484281815

theorem tailTrace_6323379 : CollatzResearch.WordTrace tailWord_6323379 prefixEnd_6323379 3246932787546920484281815 := by
  unfold tailWord_6323379
  simp only [CollatzResearch.WordTrace]
  refine ⟨230632579358485304999325191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153755052905656869999550127 230632579358485304999325191)
  ·
    refine ⟨345948869037727957498987787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230632579358485304999325191 345948869037727957498987787)
    ·
      refine ⟨518923303556591936248481681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345948869037727957498987787 518923303556591936248481681)
      ·
        refine ⟨389192477667443952186361261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 518923303556591936248481681 389192477667443952186361261)
        ·
          refine ⟨145947179125291482069885473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389192477667443952186361261 145947179125291482069885473)
          ·
            refine ⟨109460384343968611552414105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145947179125291482069885473 109460384343968611552414105)
            ·
              refine ⟨82095288257976458664310579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109460384343968611552414105 82095288257976458664310579)
              ·
                refine ⟨123142932386964687996465869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82095288257976458664310579 123142932386964687996465869)
                ·
                  refine ⟨46178599645111757998674701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123142932386964687996465869 46178599645111757998674701)
                  ·
                    refine ⟨17316974866916909249503013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46178599645111757998674701 17316974866916909249503013)
                    ·
                      refine ⟨3246932787546920484281815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17316974866916909249503013 3246932787546920484281815)
                      ·
                        rfl

theorem cell23_6323379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 4].length) (baseStart_6323379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323379 prefixEnd_6323379 := by exact prefixLift 6323379
  have htrace : WordTrace (prefixWord ++ tailWord_6323379) baseStart_6323379 baseEnd_6323379 := by
    simpa [prefixWord, tailWord_6323379, baseEnd_6323379] using wordTrace_append hprefix tailTrace_6323379
  have hstable : (prefixWord ++ tailWord_6323379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323379).length < 2 ^ (prefixWord ++ tailWord_6323379).sum := by decide
  have hdescent : baseEnd_6323379 < baseStart_6323379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323389 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 2, 8]
def baseStart_6323389 : Nat := 118140960795 + 6323389 * 2 ^ 59
def prefixEnd_6323389 : Nat := 4983230072969 + 3 ^ 40 * 6323389 * 2
def baseEnd_6323389 : Nat := 1082312640784488481718923

theorem tailTrace_6323389 : CollatzResearch.WordTrace tailWord_6323389 prefixEnd_6323389 1082312640784488481718923 := by
  unfold tailWord_6323389
  simp only [CollatzResearch.WordTrace]
  refine ⟨230632944088449076707189221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153755296058966051138126147 230632944088449076707189221)
  ·
    refine ⟨43243677016584201882597979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230632944088449076707189221 43243677016584201882597979)
    ·
      refine ⟨64865515524876302823896969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43243677016584201882597979 64865515524876302823896969)
      ·
        refine ⟨48649136643657227117922727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64865515524876302823896969 48649136643657227117922727)
        ·
          refine ⟨72973704965485840676884091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48649136643657227117922727 72973704965485840676884091)
          ·
            refine ⟨109460557448228761015326137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72973704965485840676884091 109460557448228761015326137)
            ·
              refine ⟨82095418086171570761494603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109460557448228761015326137 82095418086171570761494603)
              ·
                refine ⟨123143127129257356142241905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82095418086171570761494603 123143127129257356142241905)
                ·
                  refine ⟨92357345346943017106681429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123143127129257356142241905 92357345346943017106681429)
                  ·
                    refine ⟨1082312640784488481718923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92357345346943017106681429 1082312640784488481718923)
                    ·
                      rfl

theorem cell23_6323389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_6323389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323389 prefixEnd_6323389 := by exact prefixLift 6323389
  have htrace : WordTrace (prefixWord ++ tailWord_6323389) baseStart_6323389 baseEnd_6323389 := by
    simpa [prefixWord, tailWord_6323389, baseEnd_6323389] using wordTrace_append hprefix tailTrace_6323389
  have hstable : (prefixWord ++ tailWord_6323389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323389).length < 2 ^ (prefixWord ++ tailWord_6323389).sum := by decide
  have hdescent : baseEnd_6323389 < baseStart_6323389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323393 : List Nat := [1, 2, 6, 1, 1, 1, 1, 3, 2, 5]
def baseStart_6323393 : Nat := 118140960795 + 6323393 * 2 ^ 59
def prefixEnd_6323393 : Nat := 4983230072969 + 3 ^ 40 * 6323393 * 2
def baseEnd_6323393 : Nat := 1082313325425361143168917

theorem tailTrace_6323393 : CollatzResearch.WordTrace tailWord_6323393 prefixEnd_6323393 1082313325425361143168917 := by
  unfold tailWord_6323393
  simp only [CollatzResearch.WordTrace]
  refine ⟨230633089980434585390334833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153755393320289723593556555 230633089980434585390334833)
  ·
    refine ⟨172974817485325939042751125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230633089980434585390334833 172974817485325939042751125)
    ·
      refine ⟨8108194569624653392628959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 172974817485325939042751125 8108194569624653392628959)
      ·
        refine ⟨12162291854436980088943439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8108194569624653392628959 12162291854436980088943439)
        ·
          refine ⟨18243437781655470133415159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12162291854436980088943439 18243437781655470133415159)
          ·
            refine ⟨27365156672483205200122739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18243437781655470133415159 27365156672483205200122739)
            ·
              refine ⟨41047735008724807800184109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27365156672483205200122739 41047735008724807800184109)
              ·
                refine ⟨15392900628271802925069041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41047735008724807800184109 15392900628271802925069041)
                ·
                  refine ⟨11544675471203852193801781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15392900628271802925069041 11544675471203852193801781)
                  ·
                    refine ⟨1082313325425361143168917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11544675471203852193801781 1082313325425361143168917)
                    ·
                      rfl

theorem cell23_6323393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_6323393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323393 prefixEnd_6323393 := by exact prefixLift 6323393
  have htrace : WordTrace (prefixWord ++ tailWord_6323393) baseStart_6323393 baseEnd_6323393 := by
    simpa [prefixWord, tailWord_6323393, baseEnd_6323393] using wordTrace_append hprefix tailTrace_6323393
  have hstable : (prefixWord ++ tailWord_6323393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323393).length < 2 ^ (prefixWord ++ tailWord_6323393).sum := by decide
  have hdescent : baseEnd_6323393 < baseStart_6323393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323409 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 2, 1, 6]
def baseStart_6323409 : Nat := 118140960795 + 6323409 * 2 ^ 59
def prefixEnd_6323409 : Nat := 4983230072969 + 3 ^ 40 * 6323409 * 2
def baseEnd_6323409 : Nat := 3246948191966555366906677

theorem tailTrace_6323409 : CollatzResearch.WordTrace tailWord_6323409 prefixEnd_6323409 3246948191966555366906677 := by
  unfold tailWord_6323409
  simp only [CollatzResearch.WordTrace]
  refine ⟨230633673548376620122917281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153755782365584413415278187 230633673548376620122917281)
  ·
    refine ⟨172975255161282465092187961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230633673548376620122917281 172975255161282465092187961)
    ·
      refine ⟨129731441370961848819140971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172975255161282465092187961 129731441370961848819140971)
      ·
        refine ⟨194597162056442773228711457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129731441370961848819140971 194597162056442773228711457)
        ·
          refine ⟨145947871542332079921533593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194597162056442773228711457 145947871542332079921533593)
          ·
            refine ⟨109460903656749059941150195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145947871542332079921533593 109460903656749059941150195)
            ·
              refine ⟨164191355485123589911725293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109460903656749059941150195 164191355485123589911725293)
              ·
                refine ⟨61571758306921346216896985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164191355485123589911725293 61571758306921346216896985)
                ·
                  refine ⟨46178818730191009662672739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61571758306921346216896985 46178818730191009662672739)
                  ·
                    refine ⟨69268228095286514494009109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46178818730191009662672739 69268228095286514494009109)
                    ·
                      refine ⟨3246948191966555366906677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69268228095286514494009109 3246948191966555366906677)
                      ·
                        rfl

theorem cell23_6323409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_6323409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323409 prefixEnd_6323409 := by exact prefixLift 6323409
  have htrace : WordTrace (prefixWord ++ tailWord_6323409) baseStart_6323409 baseEnd_6323409 := by
    simpa [prefixWord, tailWord_6323409, baseEnd_6323409] using wordTrace_append hprefix tailTrace_6323409
  have hstable : (prefixWord ++ tailWord_6323409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323409).length < 2 ^ (prefixWord ++ tailWord_6323409).sum := by decide
  have hdescent : baseEnd_6323409 < baseStart_6323409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323413 : List Nat := [1, 3, 2, 4, 1, 1, 2, 2, 2, 1, 4]
def baseStart_6323413 : Nat := 118140960795 + 6323413 * 2 ^ 59
def prefixEnd_6323413 : Nat := 4983230072969 + 3 ^ 40 * 6323413 * 2
def baseEnd_6323413 : Nat := 3246950245889173351256659

theorem tailTrace_6323413 : CollatzResearch.WordTrace tailWord_6323413 prefixEnd_6323413 3246950245889173351256659 := by
  unfold tailWord_6323413
  simp only [CollatzResearch.WordTrace]
  refine ⟨230633819440362128806062893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153755879626908085870708595 230633819440362128806062893)
  ·
    refine ⟨86487682290135798302273585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230633819440362128806062893 86487682290135798302273585)
    ·
      refine ⟨64865761717601848726705189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86487682290135798302273585 64865761717601848726705189)
      ·
        refine ⟨12162330322050346636257223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64865761717601848726705189 12162330322050346636257223)
        ·
          refine ⟨18243495483075519954385835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12162330322050346636257223 18243495483075519954385835)
          ·
            refine ⟨27365243224613279931578753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18243495483075519954385835 27365243224613279931578753)
            ·
              refine ⟨20523932418459959948684065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27365243224613279931578753 20523932418459959948684065)
              ·
                refine ⟨15392949313844969961513049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20523932418459959948684065 15392949313844969961513049)
                ·
                  refine ⟨11544711985383727471134787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15392949313844969961513049 11544711985383727471134787)
                  ·
                    refine ⟨17317067978075591206702181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11544711985383727471134787 17317067978075591206702181)
                    ·
                      refine ⟨3246950245889173351256659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17317067978075591206702181 3246950245889173351256659)
                      ·
                        rfl

theorem cell23_6323413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_6323413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323413 prefixEnd_6323413 := by exact prefixLift 6323413
  have htrace : WordTrace (prefixWord ++ tailWord_6323413) baseStart_6323413 baseEnd_6323413 := by
    simpa [prefixWord, tailWord_6323413, baseEnd_6323413] using wordTrace_append hprefix tailTrace_6323413
  have hstable : (prefixWord ++ tailWord_6323413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323413).length < 2 ^ (prefixWord ++ tailWord_6323413).sum := by decide
  have hdescent : baseEnd_6323413 < baseStart_6323413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323414 : List Nat := [5, 2, 1, 2, 2, 2, 2, 2, 5]
def baseStart_6323414 : Nat := 118140960795 + 6323414 * 2 ^ 59
def prefixEnd_6323414 : Nat := 4983230072969 + 3 ^ 40 * 6323414 * 2
def baseEnd_6323414 : Nat := 360772306596647538593795

theorem tailTrace_6323414 : CollatzResearch.WordTrace tailWord_6323414 prefixEnd_6323414 360772306596647538593795 := by
  unfold tailWord_6323414
  simp only [CollatzResearch.WordTrace]
  refine ⟨14414615994584906623553081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153755903942239003984566197 14414615994584906623553081)
  ·
    refine ⟨10810961995938679967664811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14414615994584906623553081 10810961995938679967664811)
    ·
      refine ⟨16216442993908019951497217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10810961995938679967664811 16216442993908019951497217)
      ·
        refine ⟨12162332245431014963622913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16216442993908019951497217 12162332245431014963622913)
        ·
          refine ⟨9121749184073261222717185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12162332245431014963622913 9121749184073261222717185)
          ·
            refine ⟨6841311888054945917037889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9121749184073261222717185 6841311888054945917037889)
            ·
              refine ⟨5130983916041209437778417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6841311888054945917037889 5130983916041209437778417)
              ·
                refine ⟨3848237937030907078333813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5130983916041209437778417 3848237937030907078333813)
                ·
                  refine ⟨360772306596647538593795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3848237937030907078333813 360772306596647538593795)
                  ·
                    rfl

theorem cell23_6323414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_6323414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323414 prefixEnd_6323414 := by exact prefixLift 6323414
  have htrace : WordTrace (prefixWord ++ tailWord_6323414) baseStart_6323414 baseEnd_6323414 := by
    simpa [prefixWord, tailWord_6323414, baseEnd_6323414] using wordTrace_append hprefix tailTrace_6323414
  have hstable : (prefixWord ++ tailWord_6323414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323414).length < 2 ^ (prefixWord ++ tailWord_6323414).sum := by decide
  have hdescent : baseEnd_6323414 < baseStart_6323414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323436 : List Nat := [2, 2, 1, 1, 2, 4, 2, 3, 6]
def baseStart_6323436 : Nat := 118140960795 + 6323436 * 2 ^ 59
def prefixEnd_6323436 : Nat := 4983230072969 + 3 ^ 40 * 6323436 * 2
def baseEnd_6323436 : Nat := 360773561771580751252117

theorem tailTrace_6323436 : CollatzResearch.WordTrace tailWord_6323436 prefixEnd_6323436 360773561771580751252117 := by
  unfold tailWord_6323436
  simp only [CollatzResearch.WordTrace]
  refine ⟨115317329159639401867075081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153756438879519202489433441 115317329159639401867075081)
  ·
    refine ⟨86487996869729551400306311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115317329159639401867075081 86487996869729551400306311)
    ·
      refine ⟨129731995304594327100459467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86487996869729551400306311 129731995304594327100459467)
      ·
        refine ⟨194597992956891490650689201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129731995304594327100459467 194597992956891490650689201)
        ·
          refine ⟨145948494717668617988016901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194597992956891490650689201 145948494717668617988016901)
          ·
            refine ⟨27365342759562865872753169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145948494717668617988016901 27365342759562865872753169)
            ·
              refine ⟨20524007069672149404564877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27365342759562865872753169 20524007069672149404564877)
              ·
                refine ⟨7696502651127056026711829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20524007069672149404564877 7696502651127056026711829)
                ·
                  refine ⟨360773561771580751252117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7696502651127056026711829 360773561771580751252117)
                  ·
                    rfl

theorem cell23_6323436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 6].length) (baseStart_6323436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323436 prefixEnd_6323436 := by exact prefixLift 6323436
  have htrace : WordTrace (prefixWord ++ tailWord_6323436) baseStart_6323436 baseEnd_6323436 := by
    simpa [prefixWord, tailWord_6323436, baseEnd_6323436] using wordTrace_append hprefix tailTrace_6323436
  have hstable : (prefixWord ++ tailWord_6323436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323436).length < 2 ^ (prefixWord ++ tailWord_6323436).sum := by decide
  have hdescent : baseEnd_6323436 < baseStart_6323436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323444 : List Nat := [2, 6, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_6323444 : Nat := 118140960795 + 6323444 * 2 ^ 59
def prefixEnd_6323444 : Nat := 4983230072969 + 3 ^ 40 * 6323444 * 2
def baseEnd_6323444 : Nat := 1082322054596487576656339

theorem tailTrace_6323444 : CollatzResearch.WordTrace tailWord_6323444 prefixEnd_6323444 1082322054596487576656339 := by
  unfold tailWord_6323444
  simp only [CollatzResearch.WordTrace]
  refine ⟨115317475051624910550220693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153756633402166547400294257 115317475051624910550220693)
  ·
    refine ⟨5405506643044917682041595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 115317475051624910550220693 5405506643044917682041595)
    ·
      refine ⟨8108259964567376523062393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5405506643044917682041595 8108259964567376523062393)
      ·
        refine ⟨6081194973425532392296795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8108259964567376523062393 6081194973425532392296795)
        ·
          refine ⟨9121792460138298588445193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6081194973425532392296795 9121792460138298588445193)
          ·
            refine ⟨6841344345103723941333895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9121792460138298588445193 6841344345103723941333895)
            ·
              refine ⟨10262016517655585912000843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6841344345103723941333895 10262016517655585912000843)
              ·
                refine ⟨15393024776483378868001265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10262016517655585912000843 15393024776483378868001265)
                ·
                  refine ⟨11544768582362534151000949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15393024776483378868001265 11544768582362534151000949)
                  ·
                    refine ⟨1082322054596487576656339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11544768582362534151000949 1082322054596487576656339)
                    ·
                      rfl

theorem cell23_6323444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_6323444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323444 prefixEnd_6323444 := by exact prefixLift 6323444
  have htrace : WordTrace (prefixWord ++ tailWord_6323444) baseStart_6323444 baseEnd_6323444 := by
    simpa [prefixWord, tailWord_6323444, baseEnd_6323444] using wordTrace_append hprefix tailTrace_6323444
  have hstable : (prefixWord ++ tailWord_6323444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323444).length < 2 ^ (prefixWord ++ tailWord_6323444).sum := by decide
  have hdescent : baseEnd_6323444 < baseStart_6323444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323473 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 4, 3, 2]
def baseStart_6323473 : Nat := 118140960795 + 6323473 * 2 ^ 59
def prefixEnd_6323473 : Nat := 4983230072969 + 3 ^ 40 * 6323473 * 2
def baseEnd_6323473 : Nat := 3246981054728443116506383

theorem tailTrace_6323473 : CollatzResearch.WordTrace tailWord_6323473 prefixEnd_6323473 3246981054728443116506383 := by
  unfold tailWord_6323473
  simp only [CollatzResearch.WordTrace]
  refine ⟨230636007820144759053247073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153757338546763172702164715 230636007820144759053247073)
  ·
    refine ⟨172977005865108569289935305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230636007820144759053247073 172977005865108569289935305)
    ·
      refine ⟨129732754398831426967451479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172977005865108569289935305 129732754398831426967451479)
      ·
        refine ⟨194599131598247140451177219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129732754398831426967451479 194599131598247140451177219)
        ·
          refine ⟨291898697397370710676765829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194599131598247140451177219 291898697397370710676765829)
          ·
            refine ⟨54731005762007008251893593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 291898697397370710676765829 54731005762007008251893593)
            ·
              refine ⟨41048254321505256188920195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54731005762007008251893593 41048254321505256188920195)
              ·
                refine ⟨61572381482257884283380293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41048254321505256188920195 61572381482257884283380293)
                ·
                  refine ⟨11544821527923353303133805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61572381482257884283380293 11544821527923353303133805)
                  ·
                    refine ⟨4329308072971257488675177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11544821527923353303133805 4329308072971257488675177)
                    ·
                      refine ⟨3246981054728443116506383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4329308072971257488675177 3246981054728443116506383)
                      ·
                        rfl

theorem cell23_6323473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 3, 2].length) (baseStart_6323473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323473 prefixEnd_6323473 := by exact prefixLift 6323473
  have htrace : WordTrace (prefixWord ++ tailWord_6323473) baseStart_6323473 baseEnd_6323473 := by
    simpa [prefixWord, tailWord_6323473, baseEnd_6323473] using wordTrace_append hprefix tailTrace_6323473
  have hstable : (prefixWord ++ tailWord_6323473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323473).length < 2 ^ (prefixWord ++ tailWord_6323473).sum := by decide
  have hdescent : baseEnd_6323473 < baseStart_6323473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323480 : List Nat := [2, 1, 2, 3, 1, 4, 2, 1, 3, 1, 3]
def baseStart_6323480 : Nat := 118140960795 + 6323480 * 2 ^ 59
def prefixEnd_6323480 : Nat := 4983230072969 + 3 ^ 40 * 6323480 * 2
def baseEnd_6323480 : Nat := 3246984649093024589118851

theorem tailTrace_6323480 : CollatzResearch.WordTrace tailWord_6323480 prefixEnd_6323480 3246984649093024589118851 := by
  unfold tailWord_6323480
  simp only [CollatzResearch.WordTrace]
  refine ⟨115318131565559699624375947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153757508754079599499167929 115318131565559699624375947)
  ·
    refine ⟨172977197348339549436563921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115318131565559699624375947 172977197348339549436563921)
    ·
      refine ⟨129732898011254662077422941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172977197348339549436563921 129732898011254662077422941)
      ·
        refine ⟨48649836754220498279033603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129732898011254662077422941 48649836754220498279033603)
        ·
          refine ⟨72974755131330747418550405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48649836754220498279033603 72974755131330747418550405)
          ·
            refine ⟨13682766587124515140978201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72974755131330747418550405 13682766587124515140978201)
            ·
              refine ⟨10262074940343386355733651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13682766587124515140978201 10262074940343386355733651)
              ·
                refine ⟨15393112410515079533600477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10262074940343386355733651 15393112410515079533600477)
                ·
                  refine ⟨5772417153943154825100179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15393112410515079533600477 5772417153943154825100179)
                  ·
                    refine ⟨8658625730914732237650269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5772417153943154825100179 8658625730914732237650269)
                    ·
                      refine ⟨3246984649093024589118851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8658625730914732237650269 3246984649093024589118851)
                      ·
                        rfl

theorem cell23_6323480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_6323480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323480 prefixEnd_6323480 := by exact prefixLift 6323480
  have htrace : WordTrace (prefixWord ++ tailWord_6323480) baseStart_6323480 baseEnd_6323480 := by
    simpa [prefixWord, tailWord_6323480, baseEnd_6323480] using wordTrace_append hprefix tailTrace_6323480
  have hstable : (prefixWord ++ tailWord_6323480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323480).length < 2 ^ (prefixWord ++ tailWord_6323480).sum := by decide
  have hdescent : baseEnd_6323480 < baseStart_6323480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323576 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 6, 3, 4]
def baseStart_6323576 : Nat := 118140960795 + 6323576 * 2 ^ 59
def prefixEnd_6323576 : Nat := 4983230072969 + 3 ^ 40 * 6323576 * 2
def baseEnd_6323576 : Nat := 3247033943235856213518409

theorem tailTrace_6323576 : CollatzResearch.WordTrace tailWord_6323576 prefixEnd_6323576 3247033943235856213518409 := by
  unfold tailWord_6323576
  simp only [CollatzResearch.WordTrace]
  refine ⟨115319882269385803822123291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153759843025847738429497721 115319882269385803822123291)
  ·
    refine ⟨172979823404078705733184937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115319882269385803822123291 172979823404078705733184937)
    ·
      refine ⟨129734867553059029299888703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172979823404078705733184937 129734867553059029299888703)
      ·
        refine ⟨194602301329588543949833055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129734867553059029299888703 194602301329588543949833055)
        ·
          refine ⟨291903451994382815924749583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194602301329588543949833055 291903451994382815924749583)
          ·
            refine ⟨437855177991574223887124375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291903451994382815924749583 437855177991574223887124375)
            ·
              refine ⟨656782766987361335830686563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437855177991574223887124375 656782766987361335830686563)
              ·
                refine ⟨985174150481042003746029845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 656782766987361335830686563 985174150481042003746029845)
                ·
                  refine ⟨46180038303798843925595149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 985174150481042003746029845 46180038303798843925595149)
                  ·
                    refine ⟨17317514363924566472098181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46180038303798843925595149 17317514363924566472098181)
                    ·
                      refine ⟨3247033943235856213518409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17317514363924566472098181 3247033943235856213518409)
                      ·
                        rfl

theorem cell23_6323576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_6323576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323576 prefixEnd_6323576 := by exact prefixLift 6323576
  have htrace : WordTrace (prefixWord ++ tailWord_6323576) baseStart_6323576 baseEnd_6323576 := by
    simpa [prefixWord, tailWord_6323576, baseEnd_6323576] using wordTrace_append hprefix tailTrace_6323576
  have hstable : (prefixWord ++ tailWord_6323576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323576).length < 2 ^ (prefixWord ++ tailWord_6323576).sum := by decide
  have hdescent : baseEnd_6323576 < baseStart_6323576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323587 : List Nat := [1, 1, 1, 3, 5, 2, 2, 2, 2, 1, 3]
def baseStart_6323587 : Nat := 118140960795 + 6323587 * 2 ^ 59
def prefixEnd_6323587 : Nat := 4983230072969 + 3 ^ 40 * 6323587 * 2
def baseEnd_6323587 : Nat := 3247039591523055670480859

theorem tailTrace_6323587 : CollatzResearch.WordTrace tailWord_6323587 prefixEnd_6323587 3247039591523055670480859 := by
  unfold tailWord_6323587
  simp only [CollatzResearch.WordTrace]
  refine ⟨230640165741731756522897015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153760110494487837681931343 230640165741731756522897015)
  ·
    refine ⟨345960248612597634784345523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230640165741731756522897015 345960248612597634784345523)
    ·
      refine ⟨518940372918896452176518285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345960248612597634784345523 518940372918896452176518285)
      ·
        refine ⟨194602639844586169566194357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 518940372918896452176518285 194602639844586169566194357)
        ·
          refine ⟨18243997485429953396830721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 194602639844586169566194357 18243997485429953396830721)
          ·
            refine ⟨13682998114072465047623041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18243997485429953396830721 13682998114072465047623041)
            ·
              refine ⟨10262248585554348785717281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13682998114072465047623041 10262248585554348785717281)
              ·
                refine ⟨7696686439165761589287961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10262248585554348785717281 7696686439165761589287961)
                ·
                  refine ⟨5772514829374321191965971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7696686439165761589287961 5772514829374321191965971)
                  ·
                    refine ⟨8658772244061481787948957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5772514829374321191965971 8658772244061481787948957)
                    ·
                      refine ⟨3247039591523055670480859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8658772244061481787948957 3247039591523055670480859)
                      ·
                        rfl

theorem cell23_6323587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 1, 3].length) (baseStart_6323587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323587 prefixEnd_6323587 := by exact prefixLift 6323587
  have htrace : WordTrace (prefixWord ++ tailWord_6323587) baseStart_6323587 baseEnd_6323587 := by
    simpa [prefixWord, tailWord_6323587, baseEnd_6323587] using wordTrace_append hprefix tailTrace_6323587
  have hstable : (prefixWord ++ tailWord_6323587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323587).length < 2 ^ (prefixWord ++ tailWord_6323587).sum := by decide
  have hdescent : baseEnd_6323587 < baseStart_6323587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323623 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_6323623 : Nat := 118140960795 + 6323623 * 2 ^ 59
def prefixEnd_6323623 : Nat := 4983230072969 + 3 ^ 40 * 6323623 * 2
def baseEnd_6323623 : Nat := 3247058076826617529630693

theorem tailTrace_6323623 : CollatzResearch.WordTrace tailWord_6323623 prefixEnd_6323623 3247058076826617529630693 := by
  unfold tailWord_6323623
  simp only [CollatzResearch.WordTrace]
  refine ⟨230641478769601334671207523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153760985846400889780805015 230641478769601334671207523)
  ·
    refine ⟨345962218154402002006811285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230641478769601334671207523 345962218154402002006811285)
    ·
      refine ⟨16216978975987593844069279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 345962218154402002006811285 16216978975987593844069279)
      ·
        refine ⟨24325468463981390766103919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16216978975987593844069279 24325468463981390766103919)
        ·
          refine ⟨36488202695972086149155879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24325468463981390766103919 36488202695972086149155879)
          ·
            refine ⟨54732304043958129223733819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36488202695972086149155879 54732304043958129223733819)
            ·
              refine ⟨82098456065937193835600729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54732304043958129223733819 82098456065937193835600729)
              ·
                refine ⟨61573842049452895376700547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82098456065937193835600729 61573842049452895376700547)
                ·
                  refine ⟨92360763074179343065050821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61573842049452895376700547 92360763074179343065050821)
                  ·
                    refine ⟨17317643076408626824697029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92360763074179343065050821 17317643076408626824697029)
                    ·
                      refine ⟨3247058076826617529630693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17317643076408626824697029 3247058076826617529630693)
                      ·
                        rfl

theorem cell23_6323623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_6323623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323623 prefixEnd_6323623 := by exact prefixLift 6323623
  have htrace : WordTrace (prefixWord ++ tailWord_6323623) baseStart_6323623 baseEnd_6323623 := by
    simpa [prefixWord, tailWord_6323623, baseEnd_6323623] using wordTrace_append hprefix tailTrace_6323623
  have hstable : (prefixWord ++ tailWord_6323623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323623).length < 2 ^ (prefixWord ++ tailWord_6323623).sum := by decide
  have hdescent : baseEnd_6323623 < baseStart_6323623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323644 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 4, 2, 2]
def baseStart_6323644 : Nat := 118140960795 + 6323644 * 2 ^ 59
def prefixEnd_6323644 : Nat := 4983230072969 + 3 ^ 40 * 6323644 * 2
def baseEnd_6323644 : Nat := 3247068859920361947468097

theorem tailTrace_6323644 : CollatzResearch.WordTrace tailWord_6323644 prefixEnd_6323644 3247068859920361947468097 := by
  unfold tailWord_6323644
  simp only [CollatzResearch.WordTrace]
  refine ⟨115321122351262627628860993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153761496468350170171814657 115321122351262627628860993)
  ·
    refine ⟨86490841763446970721645745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115321122351262627628860993 86490841763446970721645745)
    ·
      refine ⟨64868131322585228041234309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86490841763446970721645745 64868131322585228041234309)
      ·
        refine ⟨12162774622984730257731433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64868131322585228041234309 12162774622984730257731433)
        ·
          refine ⟨9122080967238547693298575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12162774622984730257731433 9122080967238547693298575)
          ·
            refine ⟨13683121450857821539947863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9122080967238547693298575 13683121450857821539947863)
            ·
              refine ⟨20524682176286732309921795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13683121450857821539947863 20524682176286732309921795)
              ·
                refine ⟨30787023264430098464882693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20524682176286732309921795 30787023264430098464882693)
                ·
                  refine ⟨5772566862080643462165505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30787023264430098464882693 5772566862080643462165505)
                  ·
                    refine ⟨4329425146560482596624129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5772566862080643462165505 4329425146560482596624129)
                    ·
                      refine ⟨3247068859920361947468097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4329425146560482596624129 3247068859920361947468097)
                      ·
                        rfl

theorem cell23_6323644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_6323644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323644 prefixEnd_6323644 := by exact prefixLift 6323644
  have htrace : WordTrace (prefixWord ++ tailWord_6323644) baseStart_6323644 baseEnd_6323644 := by
    simpa [prefixWord, tailWord_6323644, baseEnd_6323644] using wordTrace_append hprefix tailTrace_6323644
  have hstable : (prefixWord ++ tailWord_6323644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323644).length < 2 ^ (prefixWord ++ tailWord_6323644).sum := by decide
  have hdescent : baseEnd_6323644 < baseStart_6323644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323660 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 2, 3, 3]
def baseStart_6323660 : Nat := 118140960795 + 6323660 * 2 ^ 59
def prefixEnd_6323660 : Nat := 4983230072969 + 3 ^ 40 * 6323660 * 2
def baseEnd_6323660 : Nat := 3247077075610833884868023

theorem tailTrace_6323660 : CollatzResearch.WordTrace tailWord_6323660 prefixEnd_6323660 3247077075610833884868023 := by
  unfold tailWord_6323660
  simp only [CollatzResearch.WordTrace]
  refine ⟨115321414135233644995152217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153761885513644859993536289 115321414135233644995152217)
  ·
    refine ⟨86491060601425233746364163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115321414135233644995152217 86491060601425233746364163)
    ·
      refine ⟨129736590902137850619546245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86491060601425233746364163 129736590902137850619546245)
      ·
        refine ⟨24325610794150846991164921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129736590902137850619546245 24325610794150846991164921)
        ·
          refine ⟨18244208095613135243373691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24325610794150846991164921 18244208095613135243373691)
          ·
            refine ⟨27366312143419702865060537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18244208095613135243373691 27366312143419702865060537)
            ·
              refine ⟨20524734107564777148795403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27366312143419702865060537 20524734107564777148795403)
              ·
                refine ⟨30787101161347165723193105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20524734107564777148795403 30787101161347165723193105)
                ·
                  refine ⟨23090325871010374292394829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30787101161347165723193105 23090325871010374292394829)
                  ·
                    refine ⟨8658872201628890359648061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23090325871010374292394829 8658872201628890359648061)
                    ·
                      refine ⟨3247077075610833884868023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8658872201628890359648061 3247077075610833884868023)
                      ·
                        rfl

theorem cell23_6323660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_6323660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323660 prefixEnd_6323660 := by exact prefixLift 6323660
  have htrace : WordTrace (prefixWord ++ tailWord_6323660) baseStart_6323660 baseEnd_6323660 := by
    simpa [prefixWord, tailWord_6323660, baseEnd_6323660] using wordTrace_append hprefix tailTrace_6323660
  have hstable : (prefixWord ++ tailWord_6323660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323660).length < 2 ^ (prefixWord ++ tailWord_6323660).sum := by decide
  have hdescent : baseEnd_6323660 < baseStart_6323660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323703 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 3]
def baseStart_6323703 : Nat := 118140960795 + 6323703 * 2 ^ 59
def prefixEnd_6323703 : Nat := 4983230072969 + 3 ^ 40 * 6323703 * 2
def baseEnd_6323703 : Nat := 3247099155278977216630325

theorem tailTrace_6323703 : CollatzResearch.WordTrace tailWord_6323703 prefixEnd_6323703 3247099155278977216630325 := by
  unfold tailWord_6323703
  simp only [CollatzResearch.WordTrace]
  refine ⟨230644396609311508334119763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153762931072874338889413175 230644396609311508334119763)
  ·
    refine ⟨345966594913967262501179645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230644396609311508334119763 345966594913967262501179645)
    ·
      refine ⟨129737473092737723437942367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345966594913967262501179645 129737473092737723437942367)
      ·
        refine ⟨194606209639106585156913551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129737473092737723437942367 194606209639106585156913551)
        ·
          refine ⟨291909314458659877735370327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194606209639106585156913551 291909314458659877735370327)
          ·
            refine ⟨437863971687989816603055491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291909314458659877735370327 437863971687989816603055491)
            ·
              refine ⟨656795957531984724904583237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437863971687989816603055491 656795957531984724904583237)
              ·
                refine ⟨123149242037247135919609357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 656795957531984724904583237 123149242037247135919609357)
                ·
                  refine ⟨46180965763967675969853509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123149242037247135919609357 46180965763967675969853509)
                  ·
                    refine ⟨8658931080743939244347533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46180965763967675969853509 8658931080743939244347533)
                    ·
                      refine ⟨3247099155278977216630325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8658931080743939244347533 3247099155278977216630325)
                      ·
                        rfl

theorem cell23_6323703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 3].length) (baseStart_6323703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323703 prefixEnd_6323703 := by exact prefixLift 6323703
  have htrace : WordTrace (prefixWord ++ tailWord_6323703) baseStart_6323703 baseEnd_6323703 := by
    simpa [prefixWord, tailWord_6323703, baseEnd_6323703] using wordTrace_append hprefix tailTrace_6323703
  have hstable : (prefixWord ++ tailWord_6323703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323703).length < 2 ^ (prefixWord ++ tailWord_6323703).sum := by decide
  have hdescent : baseEnd_6323703 < baseStart_6323703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323760 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 3, 5, 2]
def baseStart_6323760 : Nat := 118140960795 + 6323760 * 2 ^ 59
def prefixEnd_6323760 : Nat := 4983230072969 + 3 ^ 40 * 6323760 * 2
def baseEnd_6323760 : Nat := 3247128423676283493617563

theorem tailTrace_6323760 : CollatzResearch.WordTrace tailWord_6323760 prefixEnd_6323760 3247128423676283493617563 := by
  unfold tailWord_6323760
  simp only [CollatzResearch.WordTrace]
  refine ⟨115323237785052503534472367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153764317046736671379296489 115323237785052503534472367)
  ·
    refine ⟨172984856677578755301708551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115323237785052503534472367 172984856677578755301708551)
    ·
      refine ⟨259477285016368132952562827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172984856677578755301708551 259477285016368132952562827)
      ·
        refine ⟨389215927524552199428844241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259477285016368132952562827 389215927524552199428844241)
        ·
          refine ⟨291911945643414149571633181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389215927524552199428844241 291911945643414149571633181)
          ·
            refine ⟨109466979616280306089362443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291911945643414149571633181 109466979616280306089362443)
            ·
              refine ⟨164200469424420459134043665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109466979616280306089362443 164200469424420459134043665)
              ·
                refine ⟨123150352068315344350532749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164200469424420459134043665 123150352068315344350532749)
                ·
                  refine ⟨46181382025618254131449781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123150352068315344350532749 46181382025618254131449781)
                  ·
                    refine ⟨4329504564901711324823417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46181382025618254131449781 4329504564901711324823417)
                    ·
                      refine ⟨3247128423676283493617563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4329504564901711324823417 3247128423676283493617563)
                      ·
                        rfl

theorem cell23_6323760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 3, 5, 2].length) (baseStart_6323760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323760 prefixEnd_6323760 := by exact prefixLift 6323760
  have htrace : WordTrace (prefixWord ++ tailWord_6323760) baseStart_6323760 baseEnd_6323760 := by
    simpa [prefixWord, tailWord_6323760, baseEnd_6323760] using wordTrace_append hprefix tailTrace_6323760
  have hstable : (prefixWord ++ tailWord_6323760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323760).length < 2 ^ (prefixWord ++ tailWord_6323760).sum := by decide
  have hdescent : baseEnd_6323760 < baseStart_6323760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323777 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 1, 5, 2]
def baseStart_6323777 : Nat := 118140960795 + 6323777 * 2 ^ 59
def prefixEnd_6323777 : Nat := 4983230072969 + 3 ^ 40 * 6323777 * 2
def baseEnd_6323777 : Nat := 3247137152847409927104985

theorem tailTrace_6323777 : CollatzResearch.WordTrace tailWord_6323777 prefixEnd_6323777 3247137152847409927104985 := by
  unfold tailWord_6323777
  simp only [CollatzResearch.WordTrace]
  refine ⟨230647095611043418972313585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153764730407362279314875723 230647095611043418972313585)
  ·
    refine ⟨172985321708282564229235189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230647095611043418972313585 172985321708282564229235189)
    ·
      refine ⟨16217373910151490396490799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172985321708282564229235189 16217373910151490396490799)
      ·
        refine ⟨24326060865227235594736199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16217373910151490396490799 24326060865227235594736199)
        ·
          refine ⟨36489091297840853392104299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24326060865227235594736199 36489091297840853392104299)
          ·
            refine ⟨54733636946761280088156449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36489091297840853392104299 54733636946761280088156449)
            ·
              refine ⟨41050227710070960066117337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54733636946761280088156449 41050227710070960066117337)
              ·
                refine ⟨30787670782553220049588003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41050227710070960066117337 30787670782553220049588003)
                ·
                  refine ⟨46181506173829830074382005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30787670782553220049588003 46181506173829830074382005)
                  ·
                    refine ⟨4329516203796546569473313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46181506173829830074382005 4329516203796546569473313)
                    ·
                      refine ⟨3247137152847409927104985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4329516203796546569473313 3247137152847409927104985)
                      ·
                        rfl

theorem cell23_6323777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_6323777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323777 prefixEnd_6323777 := by exact prefixLift 6323777
  have htrace : WordTrace (prefixWord ++ tailWord_6323777) baseStart_6323777 baseEnd_6323777 := by
    simpa [prefixWord, tailWord_6323777, baseEnd_6323777] using wordTrace_append hprefix tailTrace_6323777
  have hstable : (prefixWord ++ tailWord_6323777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323777).length < 2 ^ (prefixWord ++ tailWord_6323777).sum := by decide
  have hdescent : baseEnd_6323777 < baseStart_6323777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323794 : List Nat := [3, 2, 2, 1, 2, 2, 3, 1, 2, 3, 2]
def baseStart_6323794 : Nat := 118140960795 + 6323794 * 2 ^ 59
def prefixEnd_6323794 : Nat := 4983230072969 + 3 ^ 40 * 6323794 * 2
def baseEnd_6323794 : Nat := 3247145882018536360592407

theorem tailTrace_6323794 : CollatzResearch.WordTrace tailWord_6323794 prefixEnd_6323794 3247145882018536360592407 := by
  unfold tailWord_6323794
  simp only [CollatzResearch.WordTrace]
  refine ⟨57661928912995457718920609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153765143767987887250454957 57661928912995457718920609)
  ·
    refine ⟨43246446684746593289190457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57661928912995457718920609 43246446684746593289190457)
    ·
      refine ⟨32434835013559944966892843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43246446684746593289190457 32434835013559944966892843)
      ·
        refine ⟨48652252520339917450339265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32434835013559944966892843 48652252520339917450339265)
        ·
          refine ⟨36489189390254938087754449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48652252520339917450339265 36489189390254938087754449)
          ·
            refine ⟨27366892042691203565815837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36489189390254938087754449 27366892042691203565815837)
            ·
              refine ⟨10262584516009201337180939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27366892042691203565815837 10262584516009201337180939)
              ·
                refine ⟨15393876774013802005771409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10262584516009201337180939 15393876774013802005771409)
                ·
                  refine ⟨11545407580510351504328557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15393876774013802005771409 11545407580510351504328557)
                  ·
                    refine ⟨4329527842691381814123209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11545407580510351504328557 4329527842691381814123209)
                    ·
                      refine ⟨3247145882018536360592407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4329527842691381814123209 3247145882018536360592407)
                      ·
                        rfl

theorem cell23_6323794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_6323794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323794 prefixEnd_6323794 := by exact prefixLift 6323794
  have htrace : WordTrace (prefixWord ++ tailWord_6323794) baseStart_6323794 baseEnd_6323794 := by
    simpa [prefixWord, tailWord_6323794, baseEnd_6323794] using wordTrace_append hprefix tailTrace_6323794
  have hstable : (prefixWord ++ tailWord_6323794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323794).length < 2 ^ (prefixWord ++ tailWord_6323794).sum := by decide
  have hdescent : baseEnd_6323794 < baseStart_6323794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323800 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 4, 4]
def baseStart_6323800 : Nat := 118140960795 + 6323800 * 2 ^ 59
def prefixEnd_6323800 : Nat := 4983230072969 + 3 ^ 40 * 6323800 * 2
def baseEnd_6323800 : Nat := 1082382987634154445705793

theorem tailTrace_6323800 : CollatzResearch.WordTrace tailWord_6323800 prefixEnd_6323800 1082382987634154445705793 := by
  unfold tailWord_6323800
  simp only [CollatzResearch.WordTrace]
  refine ⟨115323967244980046950200427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153765289659973395933600569 115323967244980046950200427)
  ·
    refine ⟨172985950867470070425300641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115323967244980046950200427 172985950867470070425300641)
    ·
      refine ⟨129739463150602552818975481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172985950867470070425300641 129739463150602552818975481)
      ·
        refine ⟨97304597362951914614231611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129739463150602552818975481 97304597362951914614231611)
        ·
          refine ⟨145956896044427871921347417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97304597362951914614231611 145956896044427871921347417)
          ·
            refine ⟨109467672033320903941010563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145956896044427871921347417 109467672033320903941010563)
            ·
              refine ⟨164201508049981355911515845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109467672033320903941010563 164201508049981355911515845)
              ·
                refine ⟨30787782759371504233409221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164201508049981355911515845 30787782759371504233409221)
                ·
                  refine ⟨5772709267382157043764229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30787782759371504233409221 5772709267382157043764229)
                  ·
                    refine ⟨1082382987634154445705793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5772709267382157043764229 1082382987634154445705793)
                    ·
                      rfl

theorem cell23_6323800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 4, 4].length) (baseStart_6323800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323800 prefixEnd_6323800 := by exact prefixLift 6323800
  have htrace : WordTrace (prefixWord ++ tailWord_6323800) baseStart_6323800 baseEnd_6323800 := by
    simpa [prefixWord, tailWord_6323800, baseEnd_6323800] using wordTrace_append hprefix tailTrace_6323800
  have hstable : (prefixWord ++ tailWord_6323800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323800).length < 2 ^ (prefixWord ++ tailWord_6323800).sum := by decide
  have hdescent : baseEnd_6323800 < baseStart_6323800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323804 : List Nat := [2, 2, 4, 1, 2, 1, 4, 1, 1, 5]
def baseStart_6323804 : Nat := 118140960795 + 6323804 * 2 ^ 59
def prefixEnd_6323804 : Nat := 4983230072969 + 3 ^ 40 * 6323804 * 2
def baseEnd_6323804 : Nat := 1082383672275027107155787

theorem tailTrace_6323804 : CollatzResearch.WordTrace tailWord_6323804 prefixEnd_6323804 1082383672275027107155787 := by
  unfold tailWord_6323804
  simp only [CollatzResearch.WordTrace]
  refine ⟨115324040190972801291773233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153765386921297068389030977 115324040190972801291773233)
  ·
    refine ⟨86493030143229600968829925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115324040190972801291773233 86493030143229600968829925)
    ·
      refine ⟨16217443151855550181655611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86493030143229600968829925 16217443151855550181655611)
      ·
        refine ⟨24326164727783325272483417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16217443151855550181655611 24326164727783325272483417)
        ·
          refine ⟨18244623545837493954362563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24326164727783325272483417 18244623545837493954362563)
          ·
            refine ⟨27366935318756240931543845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18244623545837493954362563 27366935318756240931543845)
            ·
              refine ⟨5131300372266795174664471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27366935318756240931543845 5131300372266795174664471)
              ·
                refine ⟨7696950558400192761996707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5131300372266795174664471 7696950558400192761996707)
                ·
                  refine ⟨11545425837600289142995061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7696950558400192761996707 11545425837600289142995061)
                  ·
                    refine ⟨1082383672275027107155787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11545425837600289142995061 1082383672275027107155787)
                    ·
                      rfl

theorem cell23_6323804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_6323804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323804 prefixEnd_6323804 := by exact prefixLift 6323804
  have htrace : WordTrace (prefixWord ++ tailWord_6323804) baseStart_6323804 baseEnd_6323804 := by
    simpa [prefixWord, tailWord_6323804, baseEnd_6323804] using wordTrace_append hprefix tailTrace_6323804
  have hstable : (prefixWord ++ tailWord_6323804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323804).length < 2 ^ (prefixWord ++ tailWord_6323804).sum := by decide
  have hdescent : baseEnd_6323804 < baseStart_6323804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323817 : List Nat := [1, 2, 1, 1, 1, 4, 5, 2, 2, 4]
def baseStart_6323817 : Nat := 118140960795 + 6323817 * 2 ^ 59
def prefixEnd_6323817 : Nat := 4983230072969 + 3 ^ 40 * 6323817 * 2
def baseEnd_6323817 : Nat := 1082385897357863256868267

theorem tailTrace_6323817 : CollatzResearch.WordTrace tailWord_6323817 prefixEnd_6323817 1082385897357863256868267 := by
  unfold tailWord_6323817
  simp only [CollatzResearch.WordTrace]
  refine ⟨230648554530898505803769705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153765703020599003869179803 230648554530898505803769705)
  ·
    refine ⟨172986415898173879352827279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230648554530898505803769705 172986415898173879352827279)
    ·
      refine ⟨259479623847260819029240919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172986415898173879352827279 259479623847260819029240919)
      ·
        refine ⟨389219435770891228543861379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259479623847260819029240919 389219435770891228543861379)
        ·
          refine ⟨583829153656336842815792069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389219435770891228543861379 583829153656336842815792069)
          ·
            refine ⟨109467966310563158027961013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 583829153656336842815792069 109467966310563158027961013)
            ·
              refine ⟨10262621841615296065121345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109467966310563158027961013 10262621841615296065121345)
              ·
                refine ⟨7696966381211472048841009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10262621841615296065121345 7696966381211472048841009)
                ·
                  refine ⟨5772724785908604036630757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7696966381211472048841009 5772724785908604036630757)
                  ·
                    refine ⟨1082385897357863256868267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5772724785908604036630757 1082385897357863256868267)
                    ·
                      rfl

theorem cell23_6323817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 4].length) (baseStart_6323817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323817 prefixEnd_6323817 := by exact prefixLift 6323817
  have htrace : WordTrace (prefixWord ++ tailWord_6323817) baseStart_6323817 baseEnd_6323817 := by
    simpa [prefixWord, tailWord_6323817, baseEnd_6323817] using wordTrace_append hprefix tailTrace_6323817
  have hstable : (prefixWord ++ tailWord_6323817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323817).length < 2 ^ (prefixWord ++ tailWord_6323817).sum := by decide
  have hdescent : baseEnd_6323817 < baseStart_6323817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323823 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 7]
def baseStart_6323823 : Nat := 118140960795 + 6323823 * 2 ^ 59
def prefixEnd_6323823 : Nat := 4983230072969 + 3 ^ 40 * 6323823 * 2
def baseEnd_6323823 : Nat := 3247160772957516747129773

theorem tailTrace_6323823 : CollatzResearch.WordTrace tailWord_6323823 prefixEnd_6323823 3247160772957516747129773 := by
  unfold tailWord_6323823
  simp only [CollatzResearch.WordTrace]
  refine ⟨230648773368876768828488123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153765848912584512552325415 230648773368876768828488123)
  ·
    refine ⟨345973160053315153242732185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230648773368876768828488123 345973160053315153242732185)
    ·
      refine ⟨259479870039986364932049139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345973160053315153242732185 259479870039986364932049139)
      ·
        refine ⟨389219805059979547398073709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259479870039986364932049139 389219805059979547398073709)
        ·
          refine ⟨145957426897492330274277641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389219805059979547398073709 145957426897492330274277641)
          ·
            refine ⟨109468070173119247705708231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145957426897492330274277641 109468070173119247705708231)
            ·
              refine ⟨164202105259678871558562347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109468070173119247705708231 164202105259678871558562347)
              ·
                refine ⟨246303157889518307337843521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164202105259678871558562347 246303157889518307337843521)
                ·
                  refine ⟨184727368417138730503382641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246303157889518307337843521 184727368417138730503382641)
                  ·
                    refine ⟨138545526312854047877536981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 184727368417138730503382641 138545526312854047877536981)
                    ·
                      refine ⟨3247160772957516747129773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 138545526312854047877536981 3247160772957516747129773)
                      ·
                        rfl

theorem cell23_6323823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_6323823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323823 prefixEnd_6323823 := by exact prefixLift 6323823
  have htrace : WordTrace (prefixWord ++ tailWord_6323823) baseStart_6323823 baseEnd_6323823 := by
    simpa [prefixWord, tailWord_6323823, baseEnd_6323823] using wordTrace_append hprefix tailTrace_6323823
  have hstable : (prefixWord ++ tailWord_6323823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323823).length < 2 ^ (prefixWord ++ tailWord_6323823).sum := by decide
  have hdescent : baseEnd_6323823 < baseStart_6323823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323824 : List Nat := [2, 1, 1, 1, 6, 1, 1, 3, 3, 2, 2]
def baseStart_6323824 : Nat := 118140960795 + 6323824 * 2 ^ 59
def prefixEnd_6323824 : Nat := 4983230072969 + 3 ^ 40 * 6323824 * 2
def baseEnd_6323824 : Nat := 3247161286438171243217269

theorem tailTrace_6323824 : CollatzResearch.WordTrace tailWord_6323824 prefixEnd_6323824 3247161286438171243217269 := by
  unfold tailWord_6323824
  simp only [CollatzResearch.WordTrace]
  refine ⟨115324404920936572999637263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153765873227915430666183017 115324404920936572999637263)
  ·
    refine ⟨172986607381404859499455895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115324404920936572999637263 172986607381404859499455895)
    ·
      refine ⟨259479911072107289249183843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172986607381404859499455895 259479911072107289249183843)
      ·
        refine ⟨389219866608160933873775765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259479911072107289249183843 389219866608160933873775765)
        ·
          refine ⟨18244681247257543775333239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 389219866608160933873775765 18244681247257543775333239)
          ·
            refine ⟨27367021870886315662999859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18244681247257543775333239 27367021870886315662999859)
            ·
              refine ⟨41050532806329473494499789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27367021870886315662999859 41050532806329473494499789)
              ·
                refine ⟨15393949802373552560437421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41050532806329473494499789 15393949802373552560437421)
                ·
                  refine ⟨5772731175890082210164033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15393949802373552560437421 5772731175890082210164033)
                  ·
                    refine ⟨4329548381917561657623025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5772731175890082210164033 4329548381917561657623025)
                    ·
                      refine ⟨3247161286438171243217269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4329548381917561657623025 3247161286438171243217269)
                      ·
                        rfl

theorem cell23_6323824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 3, 2, 2].length) (baseStart_6323824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323824 prefixEnd_6323824 := by exact prefixLift 6323824
  have htrace : WordTrace (prefixWord ++ tailWord_6323824) baseStart_6323824 baseEnd_6323824 := by
    simpa [prefixWord, tailWord_6323824, baseEnd_6323824] using wordTrace_append hprefix tailTrace_6323824
  have hstable : (prefixWord ++ tailWord_6323824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323824).length < 2 ^ (prefixWord ++ tailWord_6323824).sum := by decide
  have hdescent : baseEnd_6323824 < baseStart_6323824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323837 : List Nat := [1, 4, 1, 1, 4, 1, 3, 1, 1, 2, 4]
def baseStart_6323837 : Nat := 118140960795 + 6323837 * 2 ^ 59
def prefixEnd_6323837 : Nat := 4983230072969 + 3 ^ 40 * 6323837 * 2
def baseEnd_6323837 : Nat := 3247167961686679692354709

theorem tailTrace_6323837 : CollatzResearch.WordTrace tailWord_6323837 prefixEnd_6323837 3247167961686679692354709 := by
  unfold tailWord_6323837
  simp only [CollatzResearch.WordTrace]
  refine ⟨230649283990826049219497765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153766189327217366146331843 230649283990826049219497765)
  ·
    refine ⟨43246740748279884228655831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230649283990826049219497765 43246740748279884228655831)
    ·
      refine ⟨64870111122419826342983747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43246740748279884228655831 64870111122419826342983747)
      ·
        refine ⟨97305166683629739514475621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64870111122419826342983747 97305166683629739514475621)
        ·
          refine ⟨18244718753180576158964179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97305166683629739514475621 18244718753180576158964179)
          ·
            refine ⟨27367078129770864238446269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18244718753180576158964179 27367078129770864238446269)
            ·
              refine ⟨10262654298664074089417351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27367078129770864238446269 10262654298664074089417351)
              ·
                refine ⟨15393981447996111134126027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10262654298664074089417351 15393981447996111134126027)
                ·
                  refine ⟨23090972171994166701189041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15393981447996111134126027 23090972171994166701189041)
                  ·
                    refine ⟨17318229128995625025891781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23090972171994166701189041 17318229128995625025891781)
                    ·
                      refine ⟨3247167961686679692354709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17318229128995625025891781 3247167961686679692354709)
                      ·
                        rfl

theorem cell23_6323837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_6323837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323837 prefixEnd_6323837 := by exact prefixLift 6323837
  have htrace : WordTrace (prefixWord ++ tailWord_6323837) baseStart_6323837 baseEnd_6323837 := by
    simpa [prefixWord, tailWord_6323837, baseEnd_6323837] using wordTrace_append hprefix tailTrace_6323837
  have hstable : (prefixWord ++ tailWord_6323837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323837).length < 2 ^ (prefixWord ++ tailWord_6323837).sum := by decide
  have hdescent : baseEnd_6323837 < baseStart_6323837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323847 : List Nat := [1, 1, 4, 2, 1, 5, 2, 7]
def baseStart_6323847 : Nat := 118140960795 + 6323847 * 2 ^ 59
def prefixEnd_6323847 : Nat := 4983230072969 + 3 ^ 40 * 6323847 * 2
def baseEnd_6323847 : Nat := 120265670240489801971469

theorem tailTrace_6323847 : CollatzResearch.WordTrace tailWord_6323847 prefixEnd_6323847 120265670240489801971469 := by
  unfold tailWord_6323847
  simp only [CollatzResearch.WordTrace]
  refine ⟨230649648720789820927361795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153766432480526547284907863 230649648720789820927361795)
  ·
    refine ⟨345974473081184731391042693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230649648720789820927361795 345974473081184731391042693)
    ·
      refine ⟨64870213702722137135820505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 345974473081184731391042693 64870213702722137135820505)
      ·
        refine ⟨48652660277041602851865379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64870213702722137135820505 48652660277041602851865379)
        ·
          refine ⟨72978990415562404277798069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48652660277041602851865379 72978990415562404277798069)
          ·
            refine ⟨6841780351458975401043569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72978990415562404277798069 6841780351458975401043569)
            ·
              refine ⟨5131335263594231550782677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6841780351458975401043569 5131335263594231550782677)
              ·
                refine ⟨120265670240489801971469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5131335263594231550782677 120265670240489801971469)
                ·
                  rfl

theorem cell23_6323847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 7].length) (baseStart_6323847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323847 prefixEnd_6323847 := by exact prefixLift 6323847
  have htrace : WordTrace (prefixWord ++ tailWord_6323847) baseStart_6323847 baseEnd_6323847 := by
    simpa [prefixWord, tailWord_6323847, baseEnd_6323847] using wordTrace_append hprefix tailTrace_6323847
  have hstable : (prefixWord ++ tailWord_6323847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323847).length < 2 ^ (prefixWord ++ tailWord_6323847).sum := by decide
  have hdescent : baseEnd_6323847 < baseStart_6323847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323890 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 2, 6]
def baseStart_6323890 : Nat := 118140960795 + 6323890 * 2 ^ 59
def prefixEnd_6323890 : Nat := 4983230072969 + 3 ^ 40 * 6323890 * 2
def baseEnd_6323890 : Nat := 1082398392053789328330655

theorem tailTrace_6323890 : CollatzResearch.WordTrace tailWord_6323890 prefixEnd_6323890 1082398392053789328330655 := by
  unfold tailWord_6323890
  simp only [CollatzResearch.WordTrace]
  refine ⟨57662804264908509817794281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153767478039756026180784749 57662804264908509817794281)
  ·
    refine ⟨43247103198681382363345711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57662804264908509817794281 43247103198681382363345711)
    ·
      refine ⟨64870654798022073545018567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43247103198681382363345711 64870654798022073545018567)
      ·
        refine ⟨97305982197033110317527851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64870654798022073545018567 97305982197033110317527851)
        ·
          refine ⟨145958973295549665476291777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97305982197033110317527851 145958973295549665476291777)
          ·
            refine ⟨109469229971662249107218833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145958973295549665476291777 109469229971662249107218833)
            ·
              refine ⟨82101922478746686830414125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109469229971662249107218833 82101922478746686830414125)
              ·
                refine ⟨30788220929530007561405297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82101922478746686830414125 30788220929530007561405297)
                ·
                  refine ⟨23091165697147505671053973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30788220929530007561405297 23091165697147505671053973)
                  ·
                    refine ⟨1082398392053789328330655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23091165697147505671053973 1082398392053789328330655)
                    ·
                      rfl

theorem cell23_6323890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_6323890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323890 prefixEnd_6323890 := by exact prefixLift 6323890
  have htrace : WordTrace (prefixWord ++ tailWord_6323890) baseStart_6323890 baseEnd_6323890 := by
    simpa [prefixWord, tailWord_6323890, baseEnd_6323890] using wordTrace_append hprefix tailTrace_6323890
  have hstable : (prefixWord ++ tailWord_6323890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323890).length < 2 ^ (prefixWord ++ tailWord_6323890).sum := by decide
  have hdescent : baseEnd_6323890 < baseStart_6323890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323926 : List Nat := [5, 2, 1, 3, 2, 1, 2, 2, 1, 2, 2]
def baseStart_6323926 : Nat := 118140960795 + 6323926 * 2 ^ 59
def prefixEnd_6323926 : Nat := 4983230072969 + 3 ^ 40 * 6323926 * 2
def baseEnd_6323926 : Nat := 3247213661464929844141801

theorem tailTrace_6323926 : CollatzResearch.WordTrace tailWord_6323926 prefixEnd_6323926 3247213661464929844141801 := by
  unfold tailWord_6323926
  simp only [CollatzResearch.WordTrace]
  refine ⟨14415783130468976088717977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153768353391669078279658421 14415783130468976088717977)
  ·
    refine ⟨10811837347851732066538483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14415783130468976088717977 10811837347851732066538483)
    ·
      refine ⟨16217756021777598099807725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10811837347851732066538483 16217756021777598099807725)
      ·
        refine ⟨6081658508166599287427897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16217756021777598099807725 6081658508166599287427897)
        ·
          refine ⟨4561243881124949465570923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6081658508166599287427897 4561243881124949465570923)
          ·
            refine ⟨6841865821687424198356385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4561243881124949465570923 6841865821687424198356385)
            ·
              refine ⟨5131399366265568148767289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6841865821687424198356385 5131399366265568148767289)
              ·
                refine ⟨3848549524699176111575467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5131399366265568148767289 3848549524699176111575467)
                ·
                  refine ⟨5772824287048764167363201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3848549524699176111575467 5772824287048764167363201)
                  ·
                    refine ⟨4329618215286573125522401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5772824287048764167363201 4329618215286573125522401)
                    ·
                      refine ⟨3247213661464929844141801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4329618215286573125522401 3247213661464929844141801)
                      ·
                        rfl

theorem cell23_6323926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_6323926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323926 prefixEnd_6323926 := by exact prefixLift 6323926
  have htrace : WordTrace (prefixWord ++ tailWord_6323926) baseStart_6323926 baseEnd_6323926 := by
    simpa [prefixWord, tailWord_6323926, baseEnd_6323926] using wordTrace_append hprefix tailTrace_6323926
  have hstable : (prefixWord ++ tailWord_6323926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323926).length < 2 ^ (prefixWord ++ tailWord_6323926).sum := by decide
  have hdescent : baseEnd_6323926 < baseStart_6323926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323960 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 3, 2, 5]
def baseStart_6323960 : Nat := 118140960795 + 6323960 * 2 ^ 59
def prefixEnd_6323960 : Nat := 4983230072969 + 3 ^ 40 * 6323960 * 2
def baseEnd_6323960 : Nat := 3247231119807182711116643

theorem tailTrace_6323960 : CollatzResearch.WordTrace tailWord_6323960 prefixEnd_6323960 3247231119807182711116643 := by
  unfold tailWord_6323960
  simp only [CollatzResearch.WordTrace]
  refine ⟨115326885084690220613112667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153769180112920294150816889 115326885084690220613112667)
  ·
    refine ⟨172990327627035330919669001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115326885084690220613112667 172990327627035330919669001)
    ·
      refine ⟨129742745720276498189751751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172990327627035330919669001 129742745720276498189751751)
      ·
        refine ⟨194614118580414747284627627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129742745720276498189751751 194614118580414747284627627)
        ·
          refine ⟨291921177870622120926941441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194614118580414747284627627 291921177870622120926941441)
          ·
            refine ⟨218940883402966590695206081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291921177870622120926941441 218940883402966590695206081)
            ·
              refine ⟨164205662552224943021404561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218940883402966590695206081 164205662552224943021404561)
              ·
                refine ⟨123154246914168707266053421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164205662552224943021404561 123154246914168707266053421)
                ·
                  refine ⟨46182842592813265224770033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123154246914168707266053421 46182842592813265224770033)
                  ·
                    refine ⟨34637131944609948918577525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46182842592813265224770033 34637131944609948918577525)
                    ·
                      refine ⟨3247231119807182711116643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34637131944609948918577525 3247231119807182711116643)
                      ·
                        rfl

theorem cell23_6323960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_6323960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323960 prefixEnd_6323960 := by exact prefixLift 6323960
  have htrace : WordTrace (prefixWord ++ tailWord_6323960) baseStart_6323960 baseEnd_6323960 := by
    simpa [prefixWord, tailWord_6323960, baseEnd_6323960] using wordTrace_append hprefix tailTrace_6323960
  have hstable : (prefixWord ++ tailWord_6323960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323960).length < 2 ^ (prefixWord ++ tailWord_6323960).sum := by decide
  have hdescent : baseEnd_6323960 < baseStart_6323960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323967 : List Nat := [1, 1, 2, 2, 1, 3, 5, 1, 2, 5]
def baseStart_6323967 : Nat := 118140960795 + 6323967 * 2 ^ 59
def prefixEnd_6323967 : Nat := 4983230072969 + 3 ^ 40 * 6323967 * 2
def baseEnd_6323967 : Nat := 1082411571390588061243037

theorem tailTrace_6323967 : CollatzResearch.WordTrace tailWord_6323967 prefixEnd_6323967 1082411571390588061243037 := by
  unfold tailWord_6323967
  simp only [CollatzResearch.WordTrace]
  refine ⟨230654025480355081421730155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153769350320236720947820103 230654025480355081421730155)
  ·
    refine ⟨345981038220532622132595233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230654025480355081421730155 345981038220532622132595233)
    ·
      refine ⟨259485778665399466599446425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345981038220532622132595233 259485778665399466599446425)
      ·
        refine ⟨194614333999049599949584819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259485778665399466599446425 194614333999049599949584819)
        ·
          refine ⟨291921500998574399924377229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194614333999049599949584819 291921500998574399924377229)
          ·
            refine ⟨109470562874465399971641461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291921500998574399924377229 109470562874465399971641461)
            ·
              refine ⟨10262865269481131247341387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109470562874465399971641461 10262865269481131247341387)
              ·
                refine ⟨15394297904221696871012081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10262865269481131247341387 15394297904221696871012081)
                ·
                  refine ⟨11545723428166272653259061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15394297904221696871012081 11545723428166272653259061)
                  ·
                    refine ⟨1082411571390588061243037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11545723428166272653259061 1082411571390588061243037)
                    ·
                      rfl

theorem cell23_6323967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 5].length) (baseStart_6323967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323967 prefixEnd_6323967 := by exact prefixLift 6323967
  have htrace : WordTrace (prefixWord ++ tailWord_6323967) baseStart_6323967 baseEnd_6323967 := by
    simpa [prefixWord, tailWord_6323967, baseEnd_6323967] using wordTrace_append hprefix tailTrace_6323967
  have hstable : (prefixWord ++ tailWord_6323967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323967).length < 2 ^ (prefixWord ++ tailWord_6323967).sum := by decide
  have hdescent : baseEnd_6323967 < baseStart_6323967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6323988 : List Nat := [2, 4, 4, 1, 1, 1, 2, 1, 7]
def baseStart_6323988 : Nat := 118140960795 + 6323988 * 2 ^ 59
def prefixEnd_6323988 : Nat := 4983230072969 + 3 ^ 40 * 6323988 * 2
def baseEnd_6323988 : Nat := 360805055251723177951835

theorem tailTrace_6323988 : CollatzResearch.WordTrace tailWord_6323988 prefixEnd_6323988 360805055251723177951835 := by
  unfold tailWord_6323988
  simp only [CollatzResearch.WordTrace]
  refine ⟨115327395706639501004122309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153769860942186001338829745 115327395706639501004122309)
  ·
    refine ⟨21623886694994906438272933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115327395706639501004122309 21623886694994906438272933)
    ·
      refine ⟨4054478755311544957176175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21623886694994906438272933 4054478755311544957176175)
      ·
        refine ⟨6081718132967317435764263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4054478755311544957176175 6081718132967317435764263)
        ·
          refine ⟨9122577199450976153646395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6081718132967317435764263 9122577199450976153646395)
          ·
            refine ⟨13683865799176464230469593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9122577199450976153646395 13683865799176464230469593)
            ·
              refine ⟨10262899349382348172852195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13683865799176464230469593 10262899349382348172852195)
              ·
                refine ⟨15394349024073522259278293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10262899349382348172852195 15394349024073522259278293)
                ·
                  refine ⟨360805055251723177951835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15394349024073522259278293 360805055251723177951835)
                  ·
                    rfl

theorem cell23_6323988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_6323988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6323988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6323988 prefixEnd_6323988 := by exact prefixLift 6323988
  have htrace : WordTrace (prefixWord ++ tailWord_6323988) baseStart_6323988 baseEnd_6323988 := by
    simpa [prefixWord, tailWord_6323988, baseEnd_6323988] using wordTrace_append hprefix tailTrace_6323988
  have hstable : (prefixWord ++ tailWord_6323988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6323988).length < 2 ^ (prefixWord ++ tailWord_6323988).sum := by decide
  have hdescent : baseEnd_6323988 < baseStart_6323988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6323988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324038 : List Nat := [6, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_6324038 : Nat := 118140960795 + 6324038 * 2 ^ 59
def prefixEnd_6324038 : Nat := 4983230072969 + 3 ^ 40 * 6324038 * 2
def baseEnd_6324038 : Nat := 3247271171298233405941285

theorem tailTrace_6324038 : CollatzResearch.WordTrace tailWord_6324038 prefixEnd_6324038 3247271171298233405941285 := by
  unfold tailWord_6324038
  simp only [CollatzResearch.WordTrace]
  refine ⟨7208019220721808142111399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 153771076708731907031709845 7208019220721808142111399)
  ·
    refine ⟨10812028831082712213167099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7208019220721808142111399 10812028831082712213167099)
    ·
      refine ⟨16218043246624068319750649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10812028831082712213167099 16218043246624068319750649)
      ·
        refine ⟨12163532434968051239812987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16218043246624068319750649 12163532434968051239812987)
        ·
          refine ⟨18245298652452076859719481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12163532434968051239812987 18245298652452076859719481)
          ·
            refine ⟨13683973989339057644789611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18245298652452076859719481 13683973989339057644789611)
            ·
              refine ⟨20525960984008586467184417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13683973989339057644789611 20525960984008586467184417)
              ·
                refine ⟨15394470738006439850388313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20525960984008586467184417 15394470738006439850388313)
                ·
                  refine ⟨11545853053504829887791235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15394470738006439850388313 11545853053504829887791235)
                  ·
                    refine ⟨17318779580257244831686853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11545853053504829887791235 17318779580257244831686853)
                    ·
                      refine ⟨3247271171298233405941285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17318779580257244831686853 3247271171298233405941285)
                      ·
                        rfl

theorem cell23_6324038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_6324038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324038 prefixEnd_6324038 := by exact prefixLift 6324038
  have htrace : WordTrace (prefixWord ++ tailWord_6324038) baseStart_6324038 baseEnd_6324038 := by
    simpa [prefixWord, tailWord_6324038, baseEnd_6324038] using wordTrace_append hprefix tailTrace_6324038
  have hstable : (prefixWord ++ tailWord_6324038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324038).length < 2 ^ (prefixWord ++ tailWord_6324038).sum := by decide
  have hdescent : baseEnd_6324038 < baseStart_6324038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324057 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 3, 5]
def baseStart_6324057 : Nat := 118140960795 + 6324057 * 2 ^ 59
def prefixEnd_6324057 : Nat := 4983230072969 + 3 ^ 40 * 6324057 * 2
def baseEnd_6324057 : Nat := 1082426975810222943867899

theorem tailTrace_6324057 : CollatzResearch.WordTrace tailWord_6324057 prefixEnd_6324057 1082426975810222943867899 := by
  unfold tailWord_6324057
  simp only [CollatzResearch.WordTrace]
  refine ⟨230657308050029026792506425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153771538700019351195004283 230657308050029026792506425)
  ·
    refine ⟨172992981037521770094379819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230657308050029026792506425 172992981037521770094379819)
    ·
      refine ⟨259489471556282655141569729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172992981037521770094379819 259489471556282655141569729)
      ·
        refine ⟨194617103667211991356177297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259489471556282655141569729 194617103667211991356177297)
        ·
          refine ⟨145962827750408993517132973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194617103667211991356177297 145962827750408993517132973)
          ·
            refine ⟨54736060406403372568924865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145962827750408993517132973 54736060406403372568924865)
            ·
              refine ⟨41052045304802529426693649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54736060406403372568924865 41052045304802529426693649)
              ·
                refine ⟨30789033978601897070020237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41052045304802529426693649 30789033978601897070020237)
                ·
                  refine ⟨11545887741975711401257589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30789033978601897070020237 11545887741975711401257589)
                  ·
                    refine ⟨1082426975810222943867899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11545887741975711401257589 1082426975810222943867899)
                    ·
                      rfl

theorem cell23_6324057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 5].length) (baseStart_6324057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324057 prefixEnd_6324057 := by exact prefixLift 6324057
  have htrace : WordTrace (prefixWord ++ tailWord_6324057) baseStart_6324057 baseEnd_6324057 := by
    simpa [prefixWord, tailWord_6324057, baseEnd_6324057] using wordTrace_append hprefix tailTrace_6324057
  have hstable : (prefixWord ++ tailWord_6324057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324057).length < 2 ^ (prefixWord ++ tailWord_6324057).sum := by decide
  have hdescent : baseEnd_6324057 < baseStart_6324057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324081 : List Nat := [1, 2, 2, 2, 1, 3, 4, 1, 2, 3, 2]
def baseStart_6324081 : Nat := 118140960795 + 6324081 * 2 ^ 59
def prefixEnd_6324081 : Nat := 4983230072969 + 3 ^ 40 * 6324081 * 2
def baseEnd_6324081 : Nat := 3247293250966376737703587

theorem tailTrace_6324081 : CollatzResearch.WordTrace tailWord_6324081 prefixEnd_6324081 3247293250966376737703587 := by
  unfold tailWord_6324081
  simp only [CollatzResearch.WordTrace]
  refine ⟨230658183401942078891380097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153772122267961385927586731 230658183401942078891380097)
  ·
    refine ⟨172993637551456559168535073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230658183401942078891380097 172993637551456559168535073)
    ·
      refine ⟨129745228163592419376401305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172993637551456559168535073 129745228163592419376401305)
      ·
        refine ⟨97308921122694314532300979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129745228163592419376401305 97308921122694314532300979)
        ·
          refine ⟨145963381684041471798451469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97308921122694314532300979 145963381684041471798451469)
          ·
            refine ⟨54736268131515551924419301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145963381684041471798451469 54736268131515551924419301)
            ·
              refine ⟨10263050274659165985828619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54736268131515551924419301 10263050274659165985828619)
              ·
                refine ⟨15394575411988748978742929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10263050274659165985828619 15394575411988748978742929)
                ·
                  refine ⟨11545931558991561734057197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15394575411988748978742929 11545931558991561734057197)
                  ·
                    refine ⟨4329724334621835650271449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11545931558991561734057197 4329724334621835650271449)
                    ·
                      refine ⟨3247293250966376737703587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4329724334621835650271449 3247293250966376737703587)
                      ·
                        rfl

theorem cell23_6324081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 3, 2].length) (baseStart_6324081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324081 prefixEnd_6324081 := by exact prefixLift 6324081
  have htrace : WordTrace (prefixWord ++ tailWord_6324081) baseStart_6324081 baseEnd_6324081 := by
    simpa [prefixWord, tailWord_6324081, baseEnd_6324081] using wordTrace_append hprefix tailTrace_6324081
  have hstable : (prefixWord ++ tailWord_6324081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324081).length < 2 ^ (prefixWord ++ tailWord_6324081).sum := by decide
  have hdescent : baseEnd_6324081 < baseStart_6324081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324107 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 4]
def baseStart_6324107 : Nat := 118140960795 + 6324107 * 2 ^ 59
def prefixEnd_6324107 : Nat := 4983230072969 + 3 ^ 40 * 6324107 * 2
def baseEnd_6324107 : Nat := 3247306601463393635978467

theorem tailTrace_6324107 : CollatzResearch.WordTrace tailWord_6324107 prefixEnd_6324107 3247306601463393635978467 := by
  unfold tailWord_6324107
  simp only [CollatzResearch.WordTrace]
  refine ⟨230659131699847885331826575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153772754466565256887884383 230659131699847885331826575)
  ·
    refine ⟨345988697549771827997739863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230659131699847885331826575 345988697549771827997739863)
    ·
      refine ⟨518983046324657741996609795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345988697549771827997739863 518983046324657741996609795)
      ·
        refine ⟨778474569486986612994914693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518983046324657741996609795 778474569486986612994914693)
        ·
          refine ⟨145963981778809989936546505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 778474569486986612994914693 145963981778809989936546505)
          ·
            refine ⟨109472986334107492452409879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145963981778809989936546505 109472986334107492452409879)
            ·
              refine ⟨164209479501161238678614819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109472986334107492452409879 164209479501161238678614819)
              ·
                refine ⟨246314219251741858017922229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164209479501161238678614819 246314219251741858017922229)
                ·
                  refine ⟨23091958054850799189180209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 246314219251741858017922229 23091958054850799189180209)
                  ·
                    refine ⟨17318968541138099391885157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23091958054850799189180209 17318968541138099391885157)
                    ·
                      refine ⟨3247306601463393635978467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17318968541138099391885157 3247306601463393635978467)
                      ·
                        rfl

theorem cell23_6324107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 4].length) (baseStart_6324107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324107 prefixEnd_6324107 := by exact prefixLift 6324107
  have htrace : WordTrace (prefixWord ++ tailWord_6324107) baseStart_6324107 baseEnd_6324107 := by
    simpa [prefixWord, tailWord_6324107, baseEnd_6324107] using wordTrace_append hprefix tailTrace_6324107
  have hstable : (prefixWord ++ tailWord_6324107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324107).length < 2 ^ (prefixWord ++ tailWord_6324107).sum := by decide
  have hdescent : baseEnd_6324107 < baseStart_6324107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324145 : List Nat := [1, 2, 2, 4, 2, 1, 1, 5, 1, 2, 2]
def baseStart_6324145 : Nat := 118140960795 + 6324145 * 2 ^ 59
def prefixEnd_6324145 : Nat := 4983230072969 + 3 ^ 40 * 6324145 * 2
def baseEnd_6324145 : Nat := 3247326113728264487303293

theorem tailTrace_6324145 : CollatzResearch.WordTrace tailWord_6324145 prefixEnd_6324145 3247326113728264487303293 := by
  unfold tailWord_6324145
  simp only [CollatzResearch.WordTrace]
  refine ⟨230660517673710217821709889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153773678449140145214473259 230660517673710217821709889)
  ·
    refine ⟨172995388255282663366282417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230660517673710217821709889 172995388255282663366282417)
    ·
      refine ⟨129746541191461997524711813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172995388255282663366282417 129746541191461997524711813)
      ·
        refine ⟨24327476473399124535883465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129746541191461997524711813 24327476473399124535883465)
        ·
          refine ⟨18245607355049343401912599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24327476473399124535883465 18245607355049343401912599)
          ·
            refine ⟨27368411032574015102868899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18245607355049343401912599 27368411032574015102868899)
            ·
              refine ⟨41052616548861022654303349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27368411032574015102868899 41052616548861022654303349)
              ·
                refine ⟨3848682801455720873840939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41052616548861022654303349 3848682801455720873840939)
                ·
                  refine ⟨5773024202183581310761409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3848682801455720873840939 5773024202183581310761409)
                  ·
                    refine ⟨4329768151637685983071057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5773024202183581310761409 4329768151637685983071057)
                    ·
                      refine ⟨3247326113728264487303293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4329768151637685983071057 3247326113728264487303293)
                      ·
                        rfl

theorem cell23_6324145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_6324145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324145 prefixEnd_6324145 := by exact prefixLift 6324145
  have htrace : WordTrace (prefixWord ++ tailWord_6324145) baseStart_6324145 baseEnd_6324145 := by
    simpa [prefixWord, tailWord_6324145, baseEnd_6324145] using wordTrace_append hprefix tailTrace_6324145
  have hstable : (prefixWord ++ tailWord_6324145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324145).length < 2 ^ (prefixWord ++ tailWord_6324145).sum := by decide
  have hdescent : baseEnd_6324145 < baseStart_6324145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324177 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 1, 8]
def baseStart_6324177 : Nat := 118140960795 + 6324177 * 2 ^ 59
def prefixEnd_6324177 : Nat := 4983230072969 + 3 ^ 40 * 6324177 * 2
def baseEnd_6324177 : Nat := 1082447515036402787367715

theorem tailTrace_6324177 : CollatzResearch.WordTrace tailWord_6324177 prefixEnd_6324177 1082447515036402787367715 := by
  unfold tailWord_6324177
  simp only [CollatzResearch.WordTrace]
  refine ⟨230661684809594287286874785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153774456539729524857916523 230661684809594287286874785)
  ·
    refine ⟨172996263607195715465156089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230661684809594287286874785 172996263607195715465156089)
    ·
      refine ⟨129747197705396786598867067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172996263607195715465156089 129747197705396786598867067)
      ·
        refine ⟨194620796558095179898300601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129747197705396786598867067 194620796558095179898300601)
        ·
          refine ⟨145965597418571384923725451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194620796558095179898300601 145965597418571384923725451)
          ·
            refine ⟨218948396127857077385588177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145965597418571384923725451 218948396127857077385588177)
            ·
              refine ⟨164211297095892808039191133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218948396127857077385588177 164211297095892808039191133)
              ·
                refine ⟨61579236410959803014696675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164211297095892808039191133 61579236410959803014696675)
                ·
                  refine ⟨92368854616439704522045013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61579236410959803014696675 92368854616439704522045013)
                  ·
                    refine ⟨1082447515036402787367715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92368854616439704522045013 1082447515036402787367715)
                    ·
                      rfl

theorem cell23_6324177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_6324177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324177 prefixEnd_6324177 := by exact prefixLift 6324177
  have htrace : WordTrace (prefixWord ++ tailWord_6324177) baseStart_6324177 baseEnd_6324177 := by
    simpa [prefixWord, tailWord_6324177, baseEnd_6324177] using wordTrace_append hprefix tailTrace_6324177
  have hstable : (prefixWord ++ tailWord_6324177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324177).length < 2 ^ (prefixWord ++ tailWord_6324177).sum := by decide
  have hdescent : baseEnd_6324177 < baseStart_6324177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324278 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 1, 7, 2]
def baseStart_6324278 : Nat := 118140960795 + 6324278 * 2 ^ 59
def prefixEnd_6324278 : Nat := 4983230072969 + 3 ^ 40 * 6324278 * 2
def baseEnd_6324278 : Nat := 3247394406655312466940181

theorem tailTrace_6324278 : CollatzResearch.WordTrace tailWord_6324278 prefixEnd_6324278 3247394406655312466940181 := by
  unfold tailWord_6324278
  simp only [CollatzResearch.WordTrace]
  refine ⟨14416585536389273846018843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153776912388152254357534325 14416585536389273846018843)
  ·
    refine ⟨21624878304583910769028265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14416585536389273846018843 21624878304583910769028265)
    ·
      refine ⟨16218658728437933076771199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21624878304583910769028265 16218658728437933076771199)
      ·
        refine ⟨24327988092656899615156799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16218658728437933076771199 24327988092656899615156799)
        ·
          refine ⟨36491982138985349422735199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24327988092656899615156799 36491982138985349422735199)
          ·
            refine ⟨54737973208478024134102799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36491982138985349422735199 54737973208478024134102799)
            ·
              refine ⟨82106959812717036201154199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54737973208478024134102799 82106959812717036201154199)
              ·
                refine ⟨123160439719075554301731299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82106959812717036201154199 123160439719075554301731299)
                ·
                  refine ⟨184740659578613331452596949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123160439719075554301731299 184740659578613331452596949)
                  ·
                    refine ⟨4329859208873749955920241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 184740659578613331452596949 4329859208873749955920241)
                    ·
                      refine ⟨3247394406655312466940181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4329859208873749955920241 3247394406655312466940181)
                      ·
                        rfl

theorem cell23_6324278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_6324278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324278 prefixEnd_6324278 := by exact prefixLift 6324278
  have htrace : WordTrace (prefixWord ++ tailWord_6324278) baseStart_6324278 baseEnd_6324278 := by
    simpa [prefixWord, tailWord_6324278, baseEnd_6324278] using wordTrace_append hprefix tailTrace_6324278
  have hstable : (prefixWord ++ tailWord_6324278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324278).length < 2 ^ (prefixWord ++ tailWord_6324278).sum := by decide
  have hdescent : baseEnd_6324278 < baseStart_6324278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324314 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 8]
def baseStart_6324314 : Nat := 118140960795 + 6324314 * 2 ^ 59
def prefixEnd_6324314 : Nat := 4983230072969 + 3 ^ 40 * 6324314 * 2
def baseEnd_6324314 : Nat := 360823654662097147343335

theorem tailTrace_6324314 : CollatzResearch.WordTrace tailWord_6324314 prefixEnd_6324314 360823654662097147343335 := by
  unfold tailWord_6324314
  simp only [CollatzResearch.WordTrace]
  refine ⟨57666670402524489921152999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153777787740065306456407997 57666670402524489921152999)
  ·
    refine ⟨86500005603786734881729499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57666670402524489921152999 86500005603786734881729499)
    ·
      refine ⟨129750008405680102322594249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86500005603786734881729499 129750008405680102322594249)
      ·
        refine ⟨97312506304260076741945687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129750008405680102322594249 97312506304260076741945687)
        ·
          refine ⟨145968759456390115112918531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97312506304260076741945687 145968759456390115112918531)
          ·
            refine ⟨218953139184585172669377797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145968759456390115112918531 218953139184585172669377797)
            ·
              refine ⟨41053713597109719875508337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218953139184585172669377797 41053713597109719875508337)
              ·
                refine ⟨30790285197832289906631253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41053713597109719875508337 30790285197832289906631253)
                ·
                  refine ⟨360823654662097147343335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30790285197832289906631253 360823654662097147343335)
                  ·
                    rfl

theorem cell23_6324314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 8].length) (baseStart_6324314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324314 prefixEnd_6324314 := by exact prefixLift 6324314
  have htrace : WordTrace (prefixWord ++ tailWord_6324314) baseStart_6324314 baseEnd_6324314 := by
    simpa [prefixWord, tailWord_6324314, baseEnd_6324314] using wordTrace_append hprefix tailTrace_6324314
  have hstable : (prefixWord ++ tailWord_6324314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324314).length < 2 ^ (prefixWord ++ tailWord_6324314).sum := by decide
  have hdescent : baseEnd_6324314 < baseStart_6324314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324348 : List Nat := [2, 2, 2, 1, 1, 5, 3, 1, 6]
def baseStart_6324348 : Nat := 118140960795 + 6324348 * 2 ^ 59
def prefixEnd_6324348 : Nat := 4983230072969 + 3 ^ 40 * 6324348 * 2
def baseEnd_6324348 : Nat := 360825594477903021451651

theorem tailTrace_6324348 : CollatzResearch.WordTrace tailWord_6324348 prefixEnd_6324348 360825594477903021451651 := by
  unfold tailWord_6324348
  simp only [CollatzResearch.WordTrace]
  refine ⟨115333960845987391745674849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153778614461316522327566465 115333960845987391745674849)
  ·
    refine ⟨86500470634490543809256137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115333960845987391745674849 86500470634490543809256137)
    ·
      refine ⟨64875352975867907856942103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86500470634490543809256137 64875352975867907856942103)
      ·
        refine ⟨97313029463801861785413155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64875352975867907856942103 97313029463801861785413155)
        ·
          refine ⟨145969544195702792678119733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97313029463801861785413155 145969544195702792678119733)
          ·
            refine ⟨13684644768347136813573725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 145969544195702792678119733 13684644768347136813573725)
            ·
              refine ⟨5131741788130176305090147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13684644768347136813573725 5131741788130176305090147)
              ·
                refine ⟨7697612682195264457635221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5131741788130176305090147 7697612682195264457635221)
                ·
                  refine ⟨360825594477903021451651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7697612682195264457635221 360825594477903021451651)
                  ·
                    rfl

theorem cell23_6324348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 6].length) (baseStart_6324348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324348 prefixEnd_6324348 := by exact prefixLift 6324348
  have htrace : WordTrace (prefixWord ++ tailWord_6324348) baseStart_6324348 baseEnd_6324348 := by
    simpa [prefixWord, tailWord_6324348, baseEnd_6324348] using wordTrace_append hprefix tailTrace_6324348
  have hstable : (prefixWord ++ tailWord_6324348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324348).length < 2 ^ (prefixWord ++ tailWord_6324348).sum := by decide
  have hdescent : baseEnd_6324348 < baseStart_6324348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324368 : List Nat := [2, 1, 1, 1, 1, 1, 6, 3, 2, 3, 2]
def baseStart_6324368 : Nat := 118140960795 + 6324368 * 2 ^ 59
def prefixEnd_6324368 : Nat := 4983230072969 + 3 ^ 40 * 6324368 * 2
def baseEnd_6324368 : Nat := 3247440619914217114814767

theorem tailTrace_6324368 : CollatzResearch.WordTrace tailWord_6324368 prefixEnd_6324368 3247440619914217114814767 := by
  unfold tailWord_6324368
  simp only [CollatzResearch.WordTrace]
  refine ⟨115334325575951163453538879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153779100767934884604718505 115334325575951163453538879)
  ·
    refine ⟨173001488363926745180308319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115334325575951163453538879 173001488363926745180308319)
    ·
      refine ⟨259502232545890117770462479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173001488363926745180308319 259502232545890117770462479)
      ·
        refine ⟨389253348818835176655693719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259502232545890117770462479 389253348818835176655693719)
        ·
          refine ⟨583880023228252764983540579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389253348818835176655693719 583880023228252764983540579)
          ·
            refine ⟨875820034842379147475310869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583880023228252764983540579 875820034842379147475310869)
            ·
              refine ⟨41054064133236522537905197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 875820034842379147475310869 41054064133236522537905197)
              ·
                refine ⟨15395274049963695951714449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41054064133236522537905197 15395274049963695951714449)
                ·
                  refine ⟨11546455537472771963785837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15395274049963695951714449 11546455537472771963785837)
                  ·
                    refine ⟨4329920826552289486419689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11546455537472771963785837 4329920826552289486419689)
                    ·
                      refine ⟨3247440619914217114814767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4329920826552289486419689 3247440619914217114814767)
                      ·
                        rfl

theorem cell23_6324368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 2, 3, 2].length) (baseStart_6324368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324368 prefixEnd_6324368 := by exact prefixLift 6324368
  have htrace : WordTrace (prefixWord ++ tailWord_6324368) baseStart_6324368 baseEnd_6324368 := by
    simpa [prefixWord, tailWord_6324368, baseEnd_6324368] using wordTrace_append hprefix tailTrace_6324368
  have hstable : (prefixWord ++ tailWord_6324368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324368).length < 2 ^ (prefixWord ++ tailWord_6324368).sum := by decide
  have hdescent : baseEnd_6324368 < baseStart_6324368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324385 : List Nat := [1, 2, 3, 3, 1, 3, 1, 2, 2, 3, 2]
def baseStart_6324385 : Nat := 118140960795 + 6324385 * 2 ^ 59
def prefixEnd_6324385 : Nat := 4983230072969 + 3 ^ 40 * 6324385 * 2
def baseEnd_6324385 : Nat := 3247449349085343548302189

theorem tailTrace_6324385 : CollatzResearch.WordTrace tailWord_6324385 prefixEnd_6324385 3247449349085343548302189 := by
  unfold tailWord_6324385
  simp only [CollatzResearch.WordTrace]
  refine ⟨230669271192840738810446609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153779514128560492540297739 230669271192840738810446609)
  ·
    refine ⟨173001953394630554107834957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230669271192840738810446609 173001953394630554107834957)
    ·
      refine ⟨64875732522986457790438109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173001953394630554107834957 64875732522986457790438109)
      ·
        refine ⟨24328399696119921671414291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64875732522986457790438109 24328399696119921671414291)
        ·
          refine ⟨36492599544179882507121437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24328399696119921671414291 36492599544179882507121437)
          ·
            refine ⟨13684724829067455940170539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36492599544179882507121437 13684724829067455940170539)
            ·
              refine ⟨20527087243601183910255809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13684724829067455940170539 20527087243601183910255809)
              ·
                refine ⟨15395315432700887932691857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20527087243601183910255809 15395315432700887932691857)
                ·
                  refine ⟨11546486574525665949518893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15395315432700887932691857 11546486574525665949518893)
                  ·
                    refine ⟨4329932465447124731069585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11546486574525665949518893 4329932465447124731069585)
                    ·
                      refine ⟨3247449349085343548302189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4329932465447124731069585 3247449349085343548302189)
                      ·
                        rfl

theorem cell23_6324385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_6324385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324385 prefixEnd_6324385 := by exact prefixLift 6324385
  have htrace : WordTrace (prefixWord ++ tailWord_6324385) baseStart_6324385 baseEnd_6324385 := by
    simpa [prefixWord, tailWord_6324385, baseEnd_6324385] using wordTrace_append hprefix tailTrace_6324385
  have hstable : (prefixWord ++ tailWord_6324385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324385).length < 2 ^ (prefixWord ++ tailWord_6324385).sum := by decide
  have hdescent : baseEnd_6324385 < baseStart_6324385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324408 : List Nat := [2, 1, 2, 1, 2, 1, 5, 3, 2, 4]
def baseStart_6324408 : Nat := 118140960795 + 6324408 * 2 ^ 59
def prefixEnd_6324408 : Nat := 4983230072969 + 3 ^ 40 * 6324408 * 2
def baseEnd_6324408 : Nat := 1082487053046798986104861

theorem tailTrace_6324408 : CollatzResearch.WordTrace tailWord_6324408 prefixEnd_6324408 1082487053046798986104861 := by
  unfold tailWord_6324408
  simp only [CollatzResearch.WordTrace]
  refine ⟨115335055035878706869266939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153780073381171609159022585 115335055035878706869266939)
  ·
    refine ⟨173002582553818060303900409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115335055035878706869266939 173002582553818060303900409)
    ·
      refine ⟨129751936915363545227925307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173002582553818060303900409 129751936915363545227925307)
      ·
        refine ⟨194627905373045317841887961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129751936915363545227925307 194627905373045317841887961)
        ·
          refine ⟨145970929029783988381415971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194627905373045317841887961 145970929029783988381415971)
          ·
            refine ⟨218956393544675982572123957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145970929029783988381415971 218956393544675982572123957)
            ·
              refine ⟨20527161894813373366136621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 218956393544675982572123957 20527161894813373366136621)
              ·
                refine ⟨7697685710555015012301233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20527161894813373366136621 7697685710555015012301233)
                ·
                  refine ⟨5773264282916261259225925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7697685710555015012301233 5773264282916261259225925)
                  ·
                    refine ⟨1082487053046798986104861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5773264282916261259225925 1082487053046798986104861)
                    ·
                      rfl

theorem cell23_6324408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 2, 4].length) (baseStart_6324408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324408 prefixEnd_6324408 := by exact prefixLift 6324408
  have htrace : WordTrace (prefixWord ++ tailWord_6324408) baseStart_6324408 baseEnd_6324408 := by
    simpa [prefixWord, tailWord_6324408, baseEnd_6324408] using wordTrace_append hprefix tailTrace_6324408
  have hstable : (prefixWord ++ tailWord_6324408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324408).length < 2 ^ (prefixWord ++ tailWord_6324408).sum := by decide
  have hdescent : baseEnd_6324408 < baseStart_6324408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324411 : List Nat := [1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 4]
def baseStart_6324411 : Nat := 118140960795 + 6324411 * 2 ^ 59
def prefixEnd_6324411 : Nat := 4983230072969 + 3 ^ 40 * 6324411 * 2
def baseEnd_6324411 : Nat := 3247462699582360446577069

theorem tailTrace_6324411 : CollatzResearch.WordTrace tailWord_6324411 prefixEnd_6324411 3247462699582360446577069 := by
  unfold tailWord_6324411
  simp only [CollatzResearch.WordTrace]
  refine ⟨230670219490746545250893087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153780146327164363500595391 230670219490746545250893087)
  ·
    refine ⟨346005329236119817876339631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230670219490746545250893087 346005329236119817876339631)
    ·
      refine ⟨519007993854179726814509447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346005329236119817876339631 519007993854179726814509447)
      ·
        refine ⟨778511990781269590221764171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519007993854179726814509447 778511990781269590221764171)
        ·
          refine ⟨1167767986171904385332646257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778511990781269590221764171 1167767986171904385332646257)
          ·
            refine ⟨875825989628928288999484693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1167767986171904385332646257 875825989628928288999484693)
            ·
              refine ⟨41054343263856013546850845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 875825989628928288999484693 41054343263856013546850845)
              ·
                refine ⟨15395378723946005080069067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41054343263856013546850845 15395378723946005080069067)
                ·
                  refine ⟨23093068085919007620103601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15395378723946005080069067 23093068085919007620103601)
                  ·
                    refine ⟨17319801064439255715077701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23093068085919007620103601 17319801064439255715077701)
                    ·
                      refine ⟨3247462699582360446577069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17319801064439255715077701 3247462699582360446577069)
                      ·
                        rfl

theorem cell23_6324411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 4].length) (baseStart_6324411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324411 prefixEnd_6324411 := by exact prefixLift 6324411
  have htrace : WordTrace (prefixWord ++ tailWord_6324411) baseStart_6324411 baseEnd_6324411 := by
    simpa [prefixWord, tailWord_6324411, baseEnd_6324411] using wordTrace_append hprefix tailTrace_6324411
  have hstable : (prefixWord ++ tailWord_6324411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324411).length < 2 ^ (prefixWord ++ tailWord_6324411).sum := by decide
  have hdescent : baseEnd_6324411 < baseStart_6324411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324412 : List Nat := [2, 2, 2, 3, 4, 1, 1, 2, 1, 5]
def baseStart_6324412 : Nat := 118140960795 + 6324412 * 2 ^ 59
def prefixEnd_6324412 : Nat := 4983230072969 + 3 ^ 40 * 6324412 * 2
def baseEnd_6324412 : Nat := 1082487737687671647554855

theorem tailTrace_6324412 : CollatzResearch.WordTrace tailWord_6324412 prefixEnd_6324412 1082487737687671647554855 := by
  unfold tailWord_6324412
  simp only [CollatzResearch.WordTrace]
  refine ⟨115335127981871461210839745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153780170642495281614452993 115335127981871461210839745)
  ·
    refine ⟨86501345986403595908129809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115335127981871461210839745 86501345986403595908129809)
    ·
      refine ⟨64876009489802696931097357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86501345986403595908129809 64876009489802696931097357)
      ·
        refine ⟨24328503558676011349161509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64876009489802696931097357 24328503558676011349161509)
        ·
          refine ⟨4561594417251752127967783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24328503558676011349161509 4561594417251752127967783)
          ·
            refine ⟨6842391625877628191951675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4561594417251752127967783 6842391625877628191951675)
            ·
              refine ⟨10263587438816442287927513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6842391625877628191951675 10263587438816442287927513)
              ·
                refine ⟨7697690579112331715945635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10263587438816442287927513 7697690579112331715945635)
                ·
                  refine ⟨11546535868668497573918453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7697690579112331715945635 11546535868668497573918453)
                  ·
                    refine ⟨1082487737687671647554855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11546535868668497573918453 1082487737687671647554855)
                    ·
                      rfl

theorem cell23_6324412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_6324412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324412 prefixEnd_6324412 := by exact prefixLift 6324412
  have htrace : WordTrace (prefixWord ++ tailWord_6324412) baseStart_6324412 baseEnd_6324412 := by
    simpa [prefixWord, tailWord_6324412, baseEnd_6324412] using wordTrace_append hprefix tailTrace_6324412
  have hstable : (prefixWord ++ tailWord_6324412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324412).length < 2 ^ (prefixWord ++ tailWord_6324412).sum := by decide
  have hdescent : baseEnd_6324412 < baseStart_6324412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324438 : List Nat := [5, 2, 1, 2, 1, 12]
def baseStart_6324438 : Nat := 118140960795 + 6324438 * 2 ^ 59
def prefixEnd_6324438 : Nat := 4983230072969 + 3 ^ 40 * 6324438 * 2
def baseEnd_6324438 : Nat := 13364101084609184530615

theorem tailTrace_6324438 : CollatzResearch.WordTrace tailWord_6324438 prefixEnd_6324438 13364101084609184530615 := by
  unfold tailWord_6324438
  simp only [CollatzResearch.WordTrace]
  refine ⟨14416950266353045553882873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153780802841099152574750645 14416950266353045553882873)
  ·
    refine ⟨10812712699764784165412155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14416950266353045553882873 10812712699764784165412155)
    ·
      refine ⟨16219069049647176248118233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10812712699764784165412155 16219069049647176248118233)
      ·
        refine ⟨12164301787235382186088675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16219069049647176248118233 12164301787235382186088675)
        ·
          refine ⟨18246452680853073279133013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12164301787235382186088675 18246452680853073279133013)
          ·
            refine ⟨13364101084609184530615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 18246452680853073279133013 13364101084609184530615)
            ·
              rfl

theorem cell23_6324438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 12].length) (baseStart_6324438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324438 prefixEnd_6324438 := by exact prefixLift 6324438
  have htrace : WordTrace (prefixWord ++ tailWord_6324438) baseStart_6324438 baseEnd_6324438 := by
    simpa [prefixWord, tailWord_6324438, baseEnd_6324438] using wordTrace_append hprefix tailTrace_6324438
  have hstable : (prefixWord ++ tailWord_6324438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324438).length < 2 ^ (prefixWord ++ tailWord_6324438).sum := by decide
  have hdescent : baseEnd_6324438 < baseStart_6324438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324465 : List Nat := [1, 2, 2, 2, 2, 1, 4, 3, 2, 1, 3]
def baseStart_6324465 : Nat := 118140960795 + 6324465 * 2 ^ 59
def prefixEnd_6324465 : Nat := 4983230072969 + 3 ^ 40 * 6324465 * 2
def baseEnd_6324465 : Nat := 3247490427537703235301821

theorem tailTrace_6324465 : CollatzResearch.WordTrace tailWord_6324465 prefixEnd_6324465 3247490427537703235301821 := by
  unfold tailWord_6324465
  simp only [CollatzResearch.WordTrace]
  refine ⟨230672189032550912473358849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153781459355033941648905899 230672189032550912473358849)
  ·
    refine ⟨173004141774413184355019137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230672189032550912473358849 173004141774413184355019137)
    ·
      refine ⟨129753106330809888266264353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173004141774413184355019137 129753106330809888266264353)
      ·
        refine ⟨97314829748107416199698265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129753106330809888266264353 97314829748107416199698265)
        ·
          refine ⟨72986122311080562149773699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97314829748107416199698265 72986122311080562149773699)
          ·
            refine ⟨109479183466620843224660549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72986122311080562149773699 109479183466620843224660549)
            ·
              refine ⟨20527346899991408104623853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109479183466620843224660549 20527346899991408104623853)
              ·
                refine ⟨7697755087496778039233945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20527346899991408104623853 7697755087496778039233945)
                ·
                  refine ⟨5773316315622583529425459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7697755087496778039233945 5773316315622583529425459)
                  ·
                    refine ⟨8659974473433875294138189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5773316315622583529425459 8659974473433875294138189)
                    ·
                      refine ⟨3247490427537703235301821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8659974473433875294138189 3247490427537703235301821)
                      ·
                        rfl

theorem cell23_6324465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_6324465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324465 prefixEnd_6324465 := by exact prefixLift 6324465
  have htrace : WordTrace (prefixWord ++ tailWord_6324465) baseStart_6324465 baseEnd_6324465 := by
    simpa [prefixWord, tailWord_6324465, baseEnd_6324465] using wordTrace_append hprefix tailTrace_6324465
  have hstable : (prefixWord ++ tailWord_6324465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324465).length < 2 ^ (prefixWord ++ tailWord_6324465).sum := by decide
  have hdescent : baseEnd_6324465 < baseStart_6324465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324478 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_6324478 : Nat := 118140960795 + 6324478 * 2 ^ 59
def prefixEnd_6324478 : Nat := 4983230072969 + 3 ^ 40 * 6324478 * 2
def baseEnd_6324478 : Nat := 3247497102786211684439261

theorem tailTrace_6324478 : CollatzResearch.WordTrace tailWord_6324478 prefixEnd_6324478 3247497102786211684439261 := by
  unfold tailWord_6324478
  simp only [CollatzResearch.WordTrace]
  refine ⟨28834082897687976961697761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153781775454335877129054725 28834082897687976961697761)
  ·
    refine ⟨21625562173265982721273321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28834082897687976961697761 21625562173265982721273321)
    ·
      refine ⟨16219171629949487040954991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21625562173265982721273321 16219171629949487040954991)
      ·
        refine ⟨24328757444924230561432487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16219171629949487040954991 24328757444924230561432487)
        ·
          refine ⟨36493136167386345842148731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24328757444924230561432487 36493136167386345842148731)
          ·
            refine ⟨54739704251079518763223097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36493136167386345842148731 54739704251079518763223097)
            ·
              refine ⟨41054778188309639072417323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54739704251079518763223097 41054778188309639072417323)
              ·
                refine ⟨61582167282464458608625985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41054778188309639072417323 61582167282464458608625985)
                ·
                  refine ⟨46186625461848343956469489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61582167282464458608625985 46186625461848343956469489)
                  ·
                    refine ⟨34639969096386257967352117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46186625461848343956469489 34639969096386257967352117)
                    ·
                      refine ⟨3247497102786211684439261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34639969096386257967352117 3247497102786211684439261)
                      ·
                        rfl

theorem cell23_6324478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_6324478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324478 prefixEnd_6324478 := by exact prefixLift 6324478
  have htrace : WordTrace (prefixWord ++ tailWord_6324478) baseStart_6324478 baseEnd_6324478 := by
    simpa [prefixWord, tailWord_6324478, baseEnd_6324478] using wordTrace_append hprefix tailTrace_6324478
  have hstable : (prefixWord ++ tailWord_6324478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324478).length < 2 ^ (prefixWord ++ tailWord_6324478).sum := by decide
  have hdescent : baseEnd_6324478 < baseStart_6324478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324481 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 1, 8]
def baseStart_6324481 : Nat := 118140960795 + 6324481 * 2 ^ 59
def prefixEnd_6324481 : Nat := 4983230072969 + 3 ^ 40 * 6324481 * 2
def baseEnd_6324481 : Nat := 1082499547742725057567249

theorem tailTrace_6324481 : CollatzResearch.WordTrace tailWord_6324481 prefixEnd_6324481 1082499547742725057567249 := by
  unfold tailWord_6324481
  simp only [CollatzResearch.WordTrace]
  refine ⟨230672772600492947205941297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153781848400328631470627531 230672772600492947205941297)
  ·
    refine ⟨173004579450369710404455973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230672772600492947205941297 173004579450369710404455973)
    ·
      refine ⟨32438358646944320700835495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173004579450369710404455973 32438358646944320700835495)
      ·
        refine ⟨48657537970416481051253243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32438358646944320700835495 48657537970416481051253243)
        ·
          refine ⟨72986306955624721576879865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48657537970416481051253243 72986306955624721576879865)
          ·
            refine ⟨54739730216718541182659899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72986306955624721576879865 54739730216718541182659899)
            ·
              refine ⟨82109595325077811773989849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54739730216718541182659899 82109595325077811773989849)
              ·
                refine ⟨61582196493808358830492387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82109595325077811773989849 61582196493808358830492387)
                ·
                  refine ⟨92373294740712538245738581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61582196493808358830492387 92373294740712538245738581)
                  ·
                    refine ⟨1082499547742725057567249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92373294740712538245738581 1082499547742725057567249)
                    ·
                      rfl

theorem cell23_6324481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_6324481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324481 prefixEnd_6324481 := by exact prefixLift 6324481
  have htrace : WordTrace (prefixWord ++ tailWord_6324481) baseStart_6324481 baseEnd_6324481 := by
    simpa [prefixWord, tailWord_6324481, baseEnd_6324481] using wordTrace_append hprefix tailTrace_6324481
  have hstable : (prefixWord ++ tailWord_6324481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324481).length < 2 ^ (prefixWord ++ tailWord_6324481).sum := by decide
  have hdescent : baseEnd_6324481 < baseStart_6324481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324491 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 5]
def baseStart_6324491 : Nat := 118140960795 + 6324491 * 2 ^ 59
def prefixEnd_6324491 : Nat := 4983230072969 + 3 ^ 40 * 6324491 * 2
def baseEnd_6324491 : Nat := 3247503778034720133576701

theorem tailTrace_6324491 : CollatzResearch.WordTrace tailWord_6324491 prefixEnd_6324491 3247503778034720133576701 := by
  unfold tailWord_6324491
  simp only [CollatzResearch.WordTrace]
  refine ⟨230673137330456718913805327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153782091553637812609203551 230673137330456718913805327)
  ·
    refine ⟨346009705995685078370707991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230673137330456718913805327 346009705995685078370707991)
    ·
      refine ⟨519014558993527617556061987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346009705995685078370707991 519014558993527617556061987)
      ·
        refine ⟨778521838490291426334092981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519014558993527617556061987 778521838490291426334092981)
        ·
          refine ⟨72986422358464821218821217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 778521838490291426334092981 72986422358464821218821217)
          ·
            refine ⟨54739816768848615914115913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72986422358464821218821217 54739816768848615914115913)
            ·
              refine ⟨41054862576636461935586935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54739816768848615914115913 41054862576636461935586935)
              ·
                refine ⟨61582293864954692903380403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41054862576636461935586935 61582293864954692903380403)
                ·
                  refine ⟨92373440797432039355070605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61582293864954692903380403 92373440797432039355070605)
                  ·
                    refine ⟨34640040299037014758151477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92373440797432039355070605 34640040299037014758151477)
                    ·
                      refine ⟨3247503778034720133576701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34640040299037014758151477 3247503778034720133576701)
                      ·
                        rfl

theorem cell23_6324491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 5].length) (baseStart_6324491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324491 prefixEnd_6324491 := by exact prefixLift 6324491
  have htrace : WordTrace (prefixWord ++ tailWord_6324491) baseStart_6324491 baseEnd_6324491 := by
    simpa [prefixWord, tailWord_6324491, baseEnd_6324491] using wordTrace_append hprefix tailTrace_6324491
  have hstable : (prefixWord ++ tailWord_6324491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324491).length < 2 ^ (prefixWord ++ tailWord_6324491).sum := by decide
  have hdescent : baseEnd_6324491 < baseStart_6324491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324526 : List Nat := [4, 1, 3, 3, 1, 1, 2, 2, 1, 3, 2]
def baseStart_6324526 : Nat := 118140960795 + 6324526 * 2 ^ 59
def prefixEnd_6324526 : Nat := 4983230072969 + 3 ^ 40 * 6324526 * 2
def baseEnd_6324526 : Nat := 3247521749857627496639041

theorem tailTrace_6324526 : CollatzResearch.WordTrace tailWord_6324526 prefixEnd_6324526 3247521749857627496639041 := by
  unfold tailWord_6324526
  simp only [CollatzResearch.WordTrace]
  refine ⟨28834301735666239986416179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153782942590219946594219621 28834301735666239986416179)
  ·
    refine ⟨43251452603499359979624269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28834301735666239986416179 43251452603499359979624269)
    ·
      refine ⟨16219294726312259992359101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43251452603499359979624269 16219294726312259992359101)
      ·
        refine ⟨6082235522367097497134663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16219294726312259992359101 6082235522367097497134663)
        ·
          refine ⟨9123353283550646245701995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6082235522367097497134663 9123353283550646245701995)
          ·
            refine ⟨13685029925325969368552993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9123353283550646245701995 13685029925325969368552993)
            ·
              refine ⟨10263772443994477026414745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13685029925325969368552993 10263772443994477026414745)
              ·
                refine ⟨7697829332995857769811059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10263772443994477026414745 7697829332995857769811059)
                ·
                  refine ⟨11546743999493786654716589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7697829332995857769811059 11546743999493786654716589)
                  ·
                    refine ⟨4330028999810169995518721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11546743999493786654716589 4330028999810169995518721)
                    ·
                      refine ⟨3247521749857627496639041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4330028999810169995518721 3247521749857627496639041)
                      ·
                        rfl

theorem cell23_6324526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_6324526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324526 prefixEnd_6324526 := by exact prefixLift 6324526
  have htrace : WordTrace (prefixWord ++ tailWord_6324526) baseStart_6324526 baseEnd_6324526 := by
    simpa [prefixWord, tailWord_6324526, baseEnd_6324526] using wordTrace_append hprefix tailTrace_6324526
  have hstable : (prefixWord ++ tailWord_6324526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324526).length < 2 ^ (prefixWord ++ tailWord_6324526).sum := by decide
  have hdescent : baseEnd_6324526 < baseStart_6324526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324615 : List Nat := [1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 3]
def baseStart_6324615 : Nat := 118140960795 + 6324615 * 2 ^ 59
def prefixEnd_6324615 : Nat := 4983230072969 + 3 ^ 40 * 6324615 * 2
def baseEnd_6324615 : Nat := 3247567449635877648426131

theorem tailTrace_6324615 : CollatzResearch.WordTrace tailWord_6324615 prefixEnd_6324615 3247567449635877648426131 := by
  unfold tailWord_6324615
  simp only [CollatzResearch.WordTrace]
  refine ⟨230677659982007488091319299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153785106654671658727546199 230677659982007488091319299)
  ·
    refine ⟨346016489973011232136978949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230677659982007488091319299 346016489973011232136978949)
    ·
      refine ⟨64878091869939606025683553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346016489973011232136978949 64878091869939606025683553)
      ·
        refine ⟨48658568902454704519262665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64878091869939606025683553 48658568902454704519262665)
        ·
          refine ⟨36493926676841028389446999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48658568902454704519262665 36493926676841028389446999)
          ·
            refine ⟨54740890015261542584170499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36493926676841028389446999 54740890015261542584170499)
            ·
              refine ⟨82111335022892313876255749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54740890015261542584170499 82111335022892313876255749)
              ·
                refine ⟨15395875316792308851797953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82111335022892313876255749 15395875316792308851797953)
                ·
                  refine ⟨11546906487594231638848465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15395875316792308851797953 11546906487594231638848465)
                  ·
                    refine ⟨8660179865695673729136349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11546906487594231638848465 8660179865695673729136349)
                    ·
                      refine ⟨3247567449635877648426131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8660179865695673729136349 3247567449635877648426131)
                      ·
                        rfl

theorem cell23_6324615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_6324615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324615 prefixEnd_6324615 := by exact prefixLift 6324615
  have htrace : WordTrace (prefixWord ++ tailWord_6324615) baseStart_6324615 baseEnd_6324615 := by
    simpa [prefixWord, tailWord_6324615, baseEnd_6324615] using wordTrace_append hprefix tailTrace_6324615
  have hstable : (prefixWord ++ tailWord_6324615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324615).length < 2 ^ (prefixWord ++ tailWord_6324615).sum := by decide
  have hdescent : baseEnd_6324615 < baseStart_6324615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324679 : List Nat := [1, 1, 4, 1, 1, 4, 2, 4, 1, 1, 3]
def baseStart_6324679 : Nat := 118140960795 + 6324679 * 2 ^ 59
def prefixEnd_6324679 : Nat := 4983230072969 + 3 ^ 40 * 6324679 * 2
def baseEnd_6324679 : Nat := 3247600312397765398025837

theorem tailTrace_6324679 : CollatzResearch.WordTrace tailWord_6324679 prefixEnd_6324679 3247600312397765398025837 := by
  unfold tailWord_6324679
  simp only [CollatzResearch.WordTrace]
  refine ⟨230679994253775627021649091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153786662835850418014432727 230679994253775627021649091)
  ·
    refine ⟨346019991380663440532473637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230679994253775627021649091 346019991380663440532473637)
    ·
      refine ⟨64878748383874395099838807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346019991380663440532473637 64878748383874395099838807)
      ·
        refine ⟨97318122575811592649758211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64878748383874395099838807 97318122575811592649758211)
        ·
          refine ⟨145977183863717388974637317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97318122575811592649758211 145977183863717388974637317)
          ·
            refine ⟨27370721974447010432744497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145977183863717388974637317 27370721974447010432744497)
            ·
              refine ⟨20528041480835257824558373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27370721974447010432744497 20528041480835257824558373)
              ·
                refine ⟨3849007777656610842104695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20528041480835257824558373 3849007777656610842104695)
                ·
                  refine ⟨5773511666484916263157043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3849007777656610842104695 5773511666484916263157043)
                  ·
                    refine ⟨8660267499727374394735565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5773511666484916263157043 8660267499727374394735565)
                    ·
                      refine ⟨3247600312397765398025837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8660267499727374394735565 3247600312397765398025837)
                      ·
                        rfl

theorem cell23_6324679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 1, 1, 3].length) (baseStart_6324679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324679 prefixEnd_6324679 := by exact prefixLift 6324679
  have htrace : WordTrace (prefixWord ++ tailWord_6324679) baseStart_6324679 baseEnd_6324679 := by
    simpa [prefixWord, tailWord_6324679, baseEnd_6324679] using wordTrace_append hprefix tailTrace_6324679
  have hstable : (prefixWord ++ tailWord_6324679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324679).length < 2 ^ (prefixWord ++ tailWord_6324679).sum := by decide
  have hdescent : baseEnd_6324679 < baseStart_6324679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324749 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_6324749 : Nat := 118140960795 + 6324749 * 2 ^ 59
def prefixEnd_6324749 : Nat := 4983230072969 + 3 ^ 40 * 6324749 * 2
def baseEnd_6324749 : Nat := 3247636256043580124150515

theorem tailTrace_6324749 : CollatzResearch.WordTrace tailWord_6324749 prefixEnd_6324749 3247636256043580124150515 := by
  unfold tailWord_6324749
  simp only [CollatzResearch.WordTrace]
  refine ⟨230682547363522028976697301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153788364909014685984464867 230682547363522028976697301)
  ·
    refine ⟨5406622203832547554141343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 230682547363522028976697301 5406622203832547554141343)
    ·
      refine ⟨8109933305748821331212015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5406622203832547554141343 8109933305748821331212015)
      ·
        refine ⟨12164899958623231996818023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8109933305748821331212015 12164899958623231996818023)
        ·
          refine ⟨18247349937934847995227035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12164899958623231996818023 18247349937934847995227035)
          ·
            refine ⟨27371024906902271992840553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18247349937934847995227035 27371024906902271992840553)
            ·
              refine ⟨20528268680176703994630415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27371024906902271992840553 20528268680176703994630415)
              ·
                refine ⟨30792403020265055991945623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20528268680176703994630415 30792403020265055991945623)
                ·
                  refine ⟨46188604530397583987918435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30792403020265055991945623 46188604530397583987918435)
                  ·
                    refine ⟨69282906795596375981877653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46188604530397583987918435 69282906795596375981877653)
                    ·
                      refine ⟨3247636256043580124150515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69282906795596375981877653 3247636256043580124150515)
                      ·
                        rfl

theorem cell23_6324749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_6324749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324749 prefixEnd_6324749 := by exact prefixLift 6324749
  have htrace : WordTrace (prefixWord ++ tailWord_6324749) baseStart_6324749 baseEnd_6324749 := by
    simpa [prefixWord, tailWord_6324749, baseEnd_6324749] using wordTrace_append hprefix tailTrace_6324749
  have hstable : (prefixWord ++ tailWord_6324749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324749).length < 2 ^ (prefixWord ++ tailWord_6324749).sum := by decide
  have hdescent : baseEnd_6324749 < baseStart_6324749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324756 : List Nat := [2, 4, 3, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_6324756 : Nat := 118140960795 + 6324756 * 2 ^ 59
def prefixEnd_6324756 : Nat := 4983230072969 + 3 ^ 40 * 6324756 * 2
def baseEnd_6324756 : Nat := 3247639850408161596762983

theorem tailTrace_6324756 : CollatzResearch.WordTrace tailWord_6324756 prefixEnd_6324756 3247639850408161596762983 := by
  unfold tailWord_6324756
  simp only [CollatzResearch.WordTrace]
  refine ⟨115341401337248334586101061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153788535116331112781468081 115341401337248334586101061)
  ·
    refine ⟨21626512750734062734893949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115341401337248334586101061 21626512750734062734893949)
    ·
      refine ⟨8109942281525273525585231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21626512750734062734893949 8109942281525273525585231)
      ·
        refine ⟨12164913422287910288377847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8109942281525273525585231 12164913422287910288377847)
        ·
          refine ⟨18247370133431865432566771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12164913422287910288377847 18247370133431865432566771)
          ·
            refine ⟨27371055200147798148850157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18247370133431865432566771 27371055200147798148850157)
            ·
              refine ⟨10264145700055424305818809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27371055200147798148850157 10264145700055424305818809)
              ·
                refine ⟨7698109275041568229364107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10264145700055424305818809 7698109275041568229364107)
                ·
                  refine ⟨11547163912562352344046161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7698109275041568229364107 11547163912562352344046161)
                  ·
                    refine ⟨8660372934421764258034621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11547163912562352344046161 8660372934421764258034621)
                    ·
                      refine ⟨3247639850408161596762983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8660372934421764258034621 3247639850408161596762983)
                      ·
                        rfl

theorem cell23_6324756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_6324756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324756 prefixEnd_6324756 := by exact prefixLift 6324756
  have htrace : WordTrace (prefixWord ++ tailWord_6324756) baseStart_6324756 baseEnd_6324756 := by
    simpa [prefixWord, tailWord_6324756, baseEnd_6324756] using wordTrace_append hprefix tailTrace_6324756
  have hstable : (prefixWord ++ tailWord_6324756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324756).length < 2 ^ (prefixWord ++ tailWord_6324756).sum := by decide
  have hdescent : baseEnd_6324756 < baseStart_6324756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324792 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 3, 4, 2]
def baseStart_6324792 : Nat := 118140960795 + 6324792 * 2 ^ 59
def prefixEnd_6324792 : Nat := 4983230072969 + 3 ^ 40 * 6324792 * 2
def baseEnd_6324792 : Nat := 3247658335711723455912817

theorem tailTrace_6324792 : CollatzResearch.WordTrace tailWord_6324792 prefixEnd_6324792 3247658335711723455912817 := by
  unfold tailWord_6324792
  simp only [CollatzResearch.WordTrace]
  refine ⟨115342057851183123660256315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153789410468244164880341753 115342057851183123660256315)
  ·
    refine ⟨173013086776774685490384473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115342057851183123660256315 173013086776774685490384473)
    ·
      refine ⟨129759815082581014117788355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173013086776774685490384473 129759815082581014117788355)
      ·
        refine ⟨194639722623871521176682533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129759815082581014117788355 194639722623871521176682533)
        ·
          refine ⟨36494947991975910220627975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194639722623871521176682533 36494947991975910220627975)
          ·
            refine ⟨54742421987963865330941963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36494947991975910220627975 54742421987963865330941963)
            ·
              refine ⟨82113632981945797996412945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54742421987963865330941963 82113632981945797996412945)
              ·
                refine ⟨61585224736459348497309709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82113632981945797996412945 61585224736459348497309709)
                ·
                  refine ⟨23094459276172255686491141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61585224736459348497309709 23094459276172255686491141)
                  ·
                    refine ⟨4330211114282297941217089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23094459276172255686491141 4330211114282297941217089)
                    ·
                      refine ⟨3247658335711723455912817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4330211114282297941217089 3247658335711723455912817)
                      ·
                        rfl

theorem cell23_6324792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 3, 4, 2].length) (baseStart_6324792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324792 prefixEnd_6324792 := by exact prefixLift 6324792
  have htrace : WordTrace (prefixWord ++ tailWord_6324792) baseStart_6324792 baseEnd_6324792 := by
    simpa [prefixWord, tailWord_6324792, baseEnd_6324792] using wordTrace_append hprefix tailTrace_6324792
  have hstable : (prefixWord ++ tailWord_6324792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324792).length < 2 ^ (prefixWord ++ tailWord_6324792).sum := by decide
  have hdescent : baseEnd_6324792 < baseStart_6324792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324805 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 1, 4, 4]
def baseStart_6324805 : Nat := 118140960795 + 6324805 * 2 ^ 59
def prefixEnd_6324805 : Nat := 4983230072969 + 3 ^ 40 * 6324805 * 2
def baseEnd_6324805 : Nat := 3247665010960231905050257

theorem tailTrace_6324805 : CollatzResearch.WordTrace tailWord_6324805 prefixEnd_6324805 3247665010960231905050257 := by
  unfold tailWord_6324805
  simp only [CollatzResearch.WordTrace]
  refine ⟨230684589851319150540735869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153789726567546100360490579 230684589851319150540735869)
  ·
    refine ⟨86506721194244681452775951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230684589851319150540735869 86506721194244681452775951)
    ·
      refine ⟨129760081791367022179163927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86506721194244681452775951 129760081791367022179163927)
      ·
        refine ⟨194640122687050533268745891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129760081791367022179163927 194640122687050533268745891)
        ·
          refine ⟨291960184030575799903118837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194640122687050533268745891 291960184030575799903118837)
          ·
            refine ⟨27371267252866481240917391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 291960184030575799903118837 27371267252866481240917391)
            ·
              refine ⟨41056900879299721861376087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27371267252866481240917391 41056900879299721861376087)
              ·
                refine ⟨61585351318949582792064131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41056900879299721861376087 61585351318949582792064131)
                ·
                  refine ⟨92378026978424374188096197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61585351318949582792064131 92378026978424374188096197)
                  ·
                    refine ⟨17320880058454570160268037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92378026978424374188096197 17320880058454570160268037)
                    ·
                      refine ⟨3247665010960231905050257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17320880058454570160268037 3247665010960231905050257)
                      ·
                        rfl

theorem cell23_6324805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_6324805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324805 prefixEnd_6324805 := by exact prefixLift 6324805
  have htrace : WordTrace (prefixWord ++ tailWord_6324805) baseStart_6324805 baseEnd_6324805 := by
    simpa [prefixWord, tailWord_6324805, baseEnd_6324805] using wordTrace_append hprefix tailTrace_6324805
  have hstable : (prefixWord ++ tailWord_6324805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324805).length < 2 ^ (prefixWord ++ tailWord_6324805).sum := by decide
  have hdescent : baseEnd_6324805 < baseStart_6324805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324832 : List Nat := [2, 1, 1, 3, 2, 1, 3, 5, 5]
def baseStart_6324832 : Nat := 118140960795 + 6324832 * 2 ^ 59
def prefixEnd_6324832 : Nat := 4983230072969 + 3 ^ 40 * 6324832 * 2
def baseEnd_6324832 : Nat := 360853208326433699934737

theorem tailTrace_6324832 : CollatzResearch.WordTrace tailWord_6324832 prefixEnd_6324832 360853208326433699934737 := by
  unfold tailWord_6324832
  simp only [CollatzResearch.WordTrace]
  refine ⟨115342787311110667075984375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153790383081480889434645833 115342787311110667075984375)
  ·
    refine ⟨173014180966666000613976563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115342787311110667075984375 173014180966666000613976563)
    ·
      refine ⟨259521271449999000920964845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173014180966666000613976563 259521271449999000920964845)
      ·
        refine ⟨97320476793749625345361817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259521271449999000920964845 97320476793749625345361817)
        ·
          refine ⟨72990357595312219009021363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97320476793749625345361817 72990357595312219009021363)
          ·
            refine ⟨109485536392968328513532045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72990357595312219009021363 109485536392968328513532045)
            ·
              refine ⟨41057076147363123192574517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109485536392968328513532045 41057076147363123192574517)
              ·
                refine ⟨3849100888815292799303861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41057076147363123192574517 3849100888815292799303861)
                ·
                  refine ⟨360853208326433699934737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3849100888815292799303861 360853208326433699934737)
                  ·
                    rfl

theorem cell23_6324832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 5].length) (baseStart_6324832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324832 prefixEnd_6324832 := by exact prefixLift 6324832
  have htrace : WordTrace (prefixWord ++ tailWord_6324832) baseStart_6324832 baseEnd_6324832 := by
    simpa [prefixWord, tailWord_6324832, baseEnd_6324832] using wordTrace_append hprefix tailTrace_6324832
  have hstable : (prefixWord ++ tailWord_6324832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324832).length < 2 ^ (prefixWord ++ tailWord_6324832).sum := by decide
  have hdescent : baseEnd_6324832 < baseStart_6324832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324842 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 4, 3, 3]
def baseStart_6324842 : Nat := 118140960795 + 6324842 * 2 ^ 59
def prefixEnd_6324842 : Nat := 4983230072969 + 3 ^ 40 * 6324842 * 2
def baseEnd_6324842 : Nat := 3247684009744448260287587

theorem tailTrace_6324842 : CollatzResearch.WordTrace tailWord_6324842 prefixEnd_6324842 3247684009744448260287587 := by
  unfold tailWord_6324842
  simp only [CollatzResearch.WordTrace]
  refine ⟨57671484838046276464958195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153790626234790070573221853 57671484838046276464958195)
  ·
    refine ⟨86507227257069414697437293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57671484838046276464958195 86507227257069414697437293)
    ·
      refine ⟨32440210221401030511538985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86507227257069414697437293 32440210221401030511538985)
      ·
        refine ⟨24330157666050772883654239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32440210221401030511538985 24330157666050772883654239)
        ·
          refine ⟨36495236499076159325481359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24330157666050772883654239 36495236499076159325481359)
          ·
            refine ⟨54742854748614238988222039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36495236499076159325481359 54742854748614238988222039)
            ·
              refine ⟨82114282122921358482333059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54742854748614238988222039 82114282122921358482333059)
              ·
                refine ⟨123171423184382037723499589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82114282122921358482333059 123171423184382037723499589)
                ·
                  refine ⟨23094641847071632073156173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123171423184382037723499589 23094641847071632073156173)
                  ·
                    refine ⟨8660490692651862027433565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23094641847071632073156173 8660490692651862027433565)
                    ·
                      refine ⟨3247684009744448260287587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8660490692651862027433565 3247684009744448260287587)
                      ·
                        rfl

theorem cell23_6324842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_6324842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324842 prefixEnd_6324842 := by exact prefixLift 6324842
  have htrace : WordTrace (prefixWord ++ tailWord_6324842) baseStart_6324842 baseEnd_6324842 := by
    simpa [prefixWord, tailWord_6324842, baseEnd_6324842] using wordTrace_append hprefix tailTrace_6324842
  have hstable : (prefixWord ++ tailWord_6324842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324842).length < 2 ^ (prefixWord ++ tailWord_6324842).sum := by decide
  have hdescent : baseEnd_6324842 < baseStart_6324842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324855 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 5]
def baseStart_6324855 : Nat := 118140960795 + 6324855 * 2 ^ 59
def prefixEnd_6324855 : Nat := 4983230072969 + 3 ^ 40 * 6324855 * 2
def baseEnd_6324855 : Nat := 3247690684992956709425027

theorem tailTrace_6324855 : CollatzResearch.WordTrace tailWord_6324855 prefixEnd_6324855 3247690684992956709425027 := by
  unfold tailWord_6324855
  simp only [CollatzResearch.WordTrace]
  refine ⟨230686413501138009080056019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153790942334092006053370679 230686413501138009080056019)
  ·
    refine ⟨346029620251707013620084029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230686413501138009080056019 346029620251707013620084029)
    ·
      refine ⟨129761107594390130107531511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346029620251707013620084029 129761107594390130107531511)
      ·
        refine ⟨194641661391585195161297267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129761107594390130107531511 194641661391585195161297267)
        ·
          refine ⟨291962492087377792741945901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194641661391585195161297267 291962492087377792741945901)
          ·
            refine ⟨109485934532766672278229713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291962492087377792741945901 109485934532766672278229713)
            ·
              refine ⟨82114450899575004208672285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109485934532766672278229713 82114450899575004208672285)
              ·
                refine ⟨30792919087340626578252107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82114450899575004208672285 30792919087340626578252107)
                ·
                  refine ⟨46189378631010939867378161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30792919087340626578252107 46189378631010939867378161)
                  ·
                    refine ⟨34642033973258204900533621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46189378631010939867378161 34642033973258204900533621)
                    ·
                      refine ⟨3247690684992956709425027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34642033973258204900533621 3247690684992956709425027)
                      ·
                        rfl

theorem cell23_6324855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_6324855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324855 prefixEnd_6324855 := by exact prefixLift 6324855
  have htrace : WordTrace (prefixWord ++ tailWord_6324855) baseStart_6324855 baseEnd_6324855 := by
    simpa [prefixWord, tailWord_6324855, baseEnd_6324855] using wordTrace_append hprefix tailTrace_6324855
  have hstable : (prefixWord ++ tailWord_6324855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324855).length < 2 ^ (prefixWord ++ tailWord_6324855).sum := by decide
  have hdescent : baseEnd_6324855 < baseStart_6324855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324885 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 4, 3, 5]
def baseStart_6324885 : Nat := 118140960795 + 6324885 * 2 ^ 59
def prefixEnd_6324885 : Nat := 4983230072969 + 3 ^ 40 * 6324885 * 2
def baseEnd_6324885 : Nat := 3247706089412591592049889

theorem tailTrace_6324885 : CollatzResearch.WordTrace tailWord_6324885 prefixEnd_6324885 3247706089412591592049889 := by
  unfold tailWord_6324885
  simp only [CollatzResearch.WordTrace]
  refine ⟨230687507691029324203648109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153791671794019549469098739 230687507691029324203648109)
  ·
    refine ⟨86507815384135996576368041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230687507691029324203648109 86507815384135996576368041)
    ·
      refine ⟨64880861538101997432276031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86507815384135996576368041 64880861538101997432276031)
      ·
        refine ⟨97321292307152996148414047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64880861538101997432276031 97321292307152996148414047)
        ·
          refine ⟨145981938460729494222621071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97321292307152996148414047 145981938460729494222621071)
          ·
            refine ⟨218972907691094241333931607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145981938460729494222621071 218972907691094241333931607)
            ·
              refine ⟨328459361536641362000897411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218972907691094241333931607 328459361536641362000897411)
              ·
                refine ⟨492689042304962043001346117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328459361536641362000897411 492689042304962043001346117)
                ·
                  refine ⟨92379195432180383062752397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 492689042304962043001346117 92379195432180383062752397)
                  ·
                    refine ⟨34642198287067643648532149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92379195432180383062752397 34642198287067643648532149)
                    ·
                      refine ⟨3247706089412591592049889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34642198287067643648532149 3247706089412591592049889)
                      ·
                        rfl

theorem cell23_6324885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_6324885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324885 prefixEnd_6324885 := by exact prefixLift 6324885
  have htrace : WordTrace (prefixWord ++ tailWord_6324885) baseStart_6324885 baseEnd_6324885 := by
    simpa [prefixWord, tailWord_6324885, baseEnd_6324885] using wordTrace_append hprefix tailTrace_6324885
  have hstable : (prefixWord ++ tailWord_6324885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324885).length < 2 ^ (prefixWord ++ tailWord_6324885).sum := by decide
  have hdescent : baseEnd_6324885 < baseStart_6324885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324906 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_6324906 : Nat := 118140960795 + 6324906 * 2 ^ 59
def prefixEnd_6324906 : Nat := 4983230072969 + 3 ^ 40 * 6324906 * 2
def baseEnd_6324906 : Nat := 3247716872506336009887293

theorem tailTrace_6324906 : CollatzResearch.WordTrace tailWord_6324906 prefixEnd_6324906 3247716872506336009887293 := by
  unfold tailWord_6324906
  simp only [CollatzResearch.WordTrace]
  refine ⟨57672068405988311197540643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153792182415968829860108381 57672068405988311197540643)
  ·
    refine ⟨86508102608982466796310965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57672068405988311197540643 86508102608982466796310965)
    ·
      refine ⟨8110134619592106262154153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86508102608982466796310965 8110134619592106262154153)
      ·
        refine ⟨6082600964694079696615615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8110134619592106262154153 6082600964694079696615615)
        ·
          refine ⟨9123901447041119544923423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6082600964694079696615615 9123901447041119544923423)
          ·
            refine ⟨13685852170561679317385135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9123901447041119544923423 13685852170561679317385135)
            ·
              refine ⟨20528778255842518976077703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13685852170561679317385135 20528778255842518976077703)
              ·
                refine ⟨30793167383763778464116555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20528778255842518976077703 30793167383763778464116555)
                ·
                  refine ⟨46189751075645667696174833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30793167383763778464116555 46189751075645667696174833)
                  ·
                    refine ⟨34642313306734250772131125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46189751075645667696174833 34642313306734250772131125)
                    ·
                      refine ⟨3247716872506336009887293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34642313306734250772131125 3247716872506336009887293)
                      ·
                        rfl

theorem cell23_6324906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_6324906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324906 prefixEnd_6324906 := by exact prefixLift 6324906
  have htrace : WordTrace (prefixWord ++ tailWord_6324906) baseStart_6324906 baseEnd_6324906 := by
    simpa [prefixWord, tailWord_6324906, baseEnd_6324906] using wordTrace_append hprefix tailTrace_6324906
  have hstable : (prefixWord ++ tailWord_6324906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324906).length < 2 ^ (prefixWord ++ tailWord_6324906).sum := by decide
  have hdescent : baseEnd_6324906 < baseStart_6324906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324922 : List Nat := [3, 1, 1, 1, 2, 3, 3, 3, 6]
def baseStart_6324922 : Nat := 118140960795 + 6324922 * 2 ^ 59
def prefixEnd_6324922 : Nat := 4983230072969 + 3 ^ 40 * 6324922 * 2
def baseEnd_6324922 : Nat := 360858343132978660809691

theorem tailTrace_6324922 : CollatzResearch.WordTrace tailWord_6324922 prefixEnd_6324922 360858343132978660809691 := by
  unfold tailWord_6324922
  simp only [CollatzResearch.WordTrace]
  refine ⟨57672214297973819880686255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153792571461263519681830013 57672214297973819880686255)
  ·
    refine ⟨86508321446960729821029383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57672214297973819880686255 86508321446960729821029383)
    ·
      refine ⟨129762482170441094731544075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86508321446960729821029383 129762482170441094731544075)
      ·
        refine ⟨194643723255661642097316113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129762482170441094731544075 194643723255661642097316113)
        ·
          refine ⟨145982792441746231572987085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194643723255661642097316113 145982792441746231572987085)
          ·
            refine ⟨54743547165654836839870157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145982792441746231572987085 54743547165654836839870157)
            ·
              refine ⟨20528830187120563814951309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54743547165654836839870157 20528830187120563814951309)
              ·
                refine ⟨7698311320170211430606741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20528830187120563814951309 7698311320170211430606741)
                ·
                  refine ⟨360858343132978660809691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7698311320170211430606741 360858343132978660809691)
                  ·
                    rfl

theorem cell23_6324922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 6].length) (baseStart_6324922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324922 prefixEnd_6324922 := by exact prefixLift 6324922
  have htrace : WordTrace (prefixWord ++ tailWord_6324922) baseStart_6324922 baseEnd_6324922 := by
    simpa [prefixWord, tailWord_6324922, baseEnd_6324922] using wordTrace_append hprefix tailTrace_6324922
  have hstable : (prefixWord ++ tailWord_6324922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324922).length < 2 ^ (prefixWord ++ tailWord_6324922).sum := by decide
  have hdescent : baseEnd_6324922 < baseStart_6324922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324956 : List Nat := [2, 2, 5, 1, 1, 2, 2, 2, 6]
def baseStart_6324956 : Nat := 118140960795 + 6324956 * 2 ^ 59
def prefixEnd_6324956 : Nat := 4983230072969 + 3 ^ 40 * 6324956 * 2
def baseEnd_6324956 : Nat := 360860282948784534918007

theorem tailTrace_6324956 : CollatzResearch.WordTrace tailWord_6324956 prefixEnd_6324956 360860282948784534918007 := by
  unfold tailWord_6324956
  simp only [CollatzResearch.WordTrace]
  refine ⟨115345048636886051664741361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153793398182514735552988481 115345048636886051664741361)
  ·
    refine ⟨86508786477664538748556021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115345048636886051664741361 86508786477664538748556021)
    ·
      refine ⟨8110198732281050507677127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86508786477664538748556021 8110198732281050507677127)
      ·
        refine ⟨12165298098421575761515691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8110198732281050507677127 12165298098421575761515691)
        ·
          refine ⟨18247947147632363642273537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12165298098421575761515691 18247947147632363642273537)
          ·
            refine ⟨13685960360724272731705153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18247947147632363642273537 13685960360724272731705153)
            ·
              refine ⟨10264470270543204548778865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13685960360724272731705153 10264470270543204548778865)
              ·
                refine ⟨7698352702907403411584149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10264470270543204548778865 7698352702907403411584149)
                ·
                  refine ⟨360860282948784534918007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7698352702907403411584149 360860282948784534918007)
                  ·
                    rfl

theorem cell23_6324956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 6].length) (baseStart_6324956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324956 prefixEnd_6324956 := by exact prefixLift 6324956
  have htrace : WordTrace (prefixWord ++ tailWord_6324956) baseStart_6324956 baseEnd_6324956 := by
    simpa [prefixWord, tailWord_6324956, baseEnd_6324956] using wordTrace_append hprefix tailTrace_6324956
  have hstable : (prefixWord ++ tailWord_6324956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324956).length < 2 ^ (prefixWord ++ tailWord_6324956).sum := by decide
  have hdescent : baseEnd_6324956 < baseStart_6324956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324989 : List Nat := [1, 4, 1, 1, 1, 1, 4, 4, 1, 1, 4]
def baseStart_6324989 : Nat := 118140960795 + 6324989 * 2 ^ 59
def prefixEnd_6324989 : Nat := 4983230072969 + 3 ^ 40 * 6324989 * 2
def baseEnd_6324989 : Nat := 3247759491400659185149411

theorem tailTrace_6324989 : CollatzResearch.WordTrace tailWord_6324989 prefixEnd_6324989 3247759491400659185149411 := by
  unfold tailWord_6324989
  simp only [CollatzResearch.WordTrace]
  refine ⟨230691300882652549965434021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153794200588435033310289347 230691300882652549965434021)
  ·
    refine ⟨43254618915497353118518879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230691300882652549965434021 43254618915497353118518879)
    ·
      refine ⟨64881928373246029677778319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43254618915497353118518879 64881928373246029677778319)
      ·
        refine ⟨97322892559869044516667479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64881928373246029677778319 97322892559869044516667479)
        ·
          refine ⟨145984338839803566775001219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97322892559869044516667479 145984338839803566775001219)
          ·
            refine ⟨218976508259705350162501829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145984338839803566775001219 218976508259705350162501829)
            ·
              refine ⟨41058095298694753155469093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218976508259705350162501829 41058095298694753155469093)
              ·
                refine ⟨7698392868505266216650455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41058095298694753155469093 7698392868505266216650455)
                ·
                  refine ⟨11547589302757899324975683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7698392868505266216650455 11547589302757899324975683)
                  ·
                    refine ⟨17321383954136848987463525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11547589302757899324975683 17321383954136848987463525)
                    ·
                      refine ⟨3247759491400659185149411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17321383954136848987463525 3247759491400659185149411)
                      ·
                        rfl

theorem cell23_6324989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_6324989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324989 prefixEnd_6324989 := by exact prefixLift 6324989
  have htrace : WordTrace (prefixWord ++ tailWord_6324989) baseStart_6324989 baseEnd_6324989 := by
    simpa [prefixWord, tailWord_6324989, baseEnd_6324989] using wordTrace_append hprefix tailTrace_6324989
  have hstable : (prefixWord ++ tailWord_6324989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324989).length < 2 ^ (prefixWord ++ tailWord_6324989).sum := by decide
  have hdescent : baseEnd_6324989 < baseStart_6324989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324999 : List Nat := [1, 1, 4, 4, 1, 1, 2, 2, 1, 6]
def baseStart_6324999 : Nat := 118140960795 + 6324999 * 2 ^ 59
def prefixEnd_6324999 : Nat := 4983230072969 + 3 ^ 40 * 6324999 * 2
def baseEnd_6324999 : Nat := 1082588208735734715341455

theorem tailTrace_6324999 : CollatzResearch.WordTrace tailWord_6324999 prefixEnd_6324999 1082588208735734715341455 := by
  unfold tailWord_6324999
  simp only [CollatzResearch.WordTrace]
  refine ⟨230691665612616321673298051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153794443741744214448865367 230691665612616321673298051)
  ·
    refine ⟨346037498418924482509947077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230691665612616321673298051 346037498418924482509947077)
    ·
      refine ⟨64882030953548340470615077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346037498418924482509947077 64882030953548340470615077)
      ·
        refine ⟨12165380803790313838240327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64882030953548340470615077 12165380803790313838240327)
        ·
          refine ⟨18248071205685470757360491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12165380803790313838240327 18248071205685470757360491)
          ·
            refine ⟨27372106808528206136040737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18248071205685470757360491 27372106808528206136040737)
            ·
              refine ⟨20529080106396154602030553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27372106808528206136040737 20529080106396154602030553)
              ·
                refine ⟨15396810079797115951522915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20529080106396154602030553 15396810079797115951522915)
                ·
                  refine ⟨23095215119695673927284373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15396810079797115951522915 23095215119695673927284373)
                  ·
                    refine ⟨1082588208735734715341455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23095215119695673927284373 1082588208735734715341455)
                    ·
                      rfl

theorem cell23_6324999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_6324999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6324999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6324999 prefixEnd_6324999 := by exact prefixLift 6324999
  have htrace : WordTrace (prefixWord ++ tailWord_6324999) baseStart_6324999 baseEnd_6324999 := by
    simpa [prefixWord, tailWord_6324999, baseEnd_6324999] using wordTrace_append hprefix tailTrace_6324999
  have hstable : (prefixWord ++ tailWord_6324999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324999).length < 2 ^ (prefixWord ++ tailWord_6324999).sum := by decide
  have hdescent : baseEnd_6324999 < baseStart_6324999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325006 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2]
def baseStart_6325006 : Nat := 118140960795 + 6325006 * 2 ^ 59
def prefixEnd_6325006 : Nat := 4983230072969 + 3 ^ 40 * 6325006 * 2
def baseEnd_6325006 : Nat := 3247768220571785618636833

theorem tailTrace_6325006 : CollatzResearch.WordTrace tailWord_6325006 prefixEnd_6325006 3247768220571785618636833 := by
  unfold tailWord_6325006
  simp only [CollatzResearch.WordTrace]
  refine ⟨28836490115448870233600359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153794613949060641245868581 28836490115448870233600359)
  ·
    refine ⟨43254735173173305350400539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28836490115448870233600359 43254735173173305350400539)
    ·
      refine ⟨64882102759759958025600809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43254735173173305350400539 64882102759759958025600809)
      ·
        refine ⟨48661577069819968519200607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64882102759759958025600809 48661577069819968519200607)
        ·
          refine ⟨72992365604729952778800911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48661577069819968519200607 72992365604729952778800911)
          ·
            refine ⟨109488548407094929168201367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72992365604729952778800911 109488548407094929168201367)
            ·
              refine ⟨164232822610642393752302051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109488548407094929168201367 164232822610642393752302051)
              ·
                refine ⟨246349233915963590628453077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164232822610642393752302051 246349233915963590628453077)
                ·
                  refine ⟨5773810169905396655354369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 246349233915963590628453077 5773810169905396655354369)
                  ·
                    refine ⟨4330357627429047491515777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5773810169905396655354369 4330357627429047491515777)
                    ·
                      refine ⟨3247768220571785618636833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4330357627429047491515777 3247768220571785618636833)
                      ·
                        rfl

theorem cell23_6325006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_6325006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325006 prefixEnd_6325006 := by exact prefixLift 6325006
  have htrace : WordTrace (prefixWord ++ tailWord_6325006) baseStart_6325006 baseEnd_6325006 := by
    simpa [prefixWord, tailWord_6325006, baseEnd_6325006] using wordTrace_append hprefix tailTrace_6325006
  have hstable : (prefixWord ++ tailWord_6325006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325006).length < 2 ^ (prefixWord ++ tailWord_6325006).sum := by decide
  have hdescent : baseEnd_6325006 < baseStart_6325006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325023 : List Nat := [1, 1, 2, 4, 2, 3, 2, 1, 3, 2, 2]
def baseStart_6325023 : Nat := 118140960795 + 6325023 * 2 ^ 59
def prefixEnd_6325023 : Nat := 4983230072969 + 3 ^ 40 * 6325023 * 2
def baseEnd_6325023 : Nat := 3247776949742912052124255

theorem tailTrace_6325023 : CollatzResearch.WordTrace tailWord_6325023 prefixEnd_6325023 3247776949742912052124255 := by
  unfold tailWord_6325023
  simp only [CollatzResearch.WordTrace]
  refine ⟨230692540964529373772171723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153795027309686249181447815 230692540964529373772171723)
  ·
    refine ⟨346038811446794060658257585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230692540964529373772171723 346038811446794060658257585)
    ·
      refine ⟨259529108585095545493693189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346038811446794060658257585 259529108585095545493693189)
      ·
        refine ⟨48661707859705414780067473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259529108585095545493693189 48661707859705414780067473)
        ·
          refine ⟨36496280894779061085050605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48661707859705414780067473 36496280894779061085050605)
          ·
            refine ⟨13686105335542147906893977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36496280894779061085050605 13686105335542147906893977)
            ·
              refine ⟨10264579001656610930170483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13686105335542147906893977 10264579001656610930170483)
              ·
                refine ⟨15396868502484916395255725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10264579001656610930170483 15396868502484916395255725)
                ·
                  refine ⟨5773825688431843648220897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15396868502484916395255725 5773825688431843648220897)
                  ·
                    refine ⟨4330369266323882736165673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5773825688431843648220897 4330369266323882736165673)
                    ·
                      refine ⟨3247776949742912052124255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4330369266323882736165673 3247776949742912052124255)
                      ·
                        rfl

theorem cell23_6325023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_6325023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325023 prefixEnd_6325023 := by exact prefixLift 6325023
  have htrace : WordTrace (prefixWord ++ tailWord_6325023) baseStart_6325023 baseEnd_6325023 := by
    simpa [prefixWord, tailWord_6325023, baseEnd_6325023] using wordTrace_append hprefix tailTrace_6325023
  have hstable : (prefixWord ++ tailWord_6325023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325023).length < 2 ^ (prefixWord ++ tailWord_6325023).sum := by decide
  have hdescent : baseEnd_6325023 < baseStart_6325023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325039 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 8, 1, 3]
def baseStart_6325039 : Nat := 118140960795 + 6325039 * 2 ^ 59
def prefixEnd_6325039 : Nat := 4983230072969 + 3 ^ 40 * 6325039 * 2
def baseEnd_6325039 : Nat := 3247785165433383989524181

theorem tailTrace_6325039 : CollatzResearch.WordTrace tailWord_6325039 prefixEnd_6325039 3247785165433383989524181 := by
  unfold tailWord_6325039
  simp only [CollatzResearch.WordTrace]
  refine ⟨230693124532471408504754171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153795416354980939003169447 230693124532471408504754171)
  ·
    refine ⟨346039686798707112757131257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230693124532471408504754171 346039686798707112757131257)
    ·
      refine ⟨259529765099030334567848443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346039686798707112757131257 259529765099030334567848443)
      ·
        refine ⟨389294647648545501851772665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259529765099030334567848443 389294647648545501851772665)
        ·
          refine ⟨291970985736409126388829499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389294647648545501851772665 291970985736409126388829499)
          ·
            refine ⟨437956478604613689583244249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291970985736409126388829499 437956478604613689583244249)
            ·
              refine ⟨328467358953460267187433187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 437956478604613689583244249 328467358953460267187433187)
              ·
                refine ⟨492701038430190400781149781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328467358953460267187433187 492701038430190400781149781)
                ·
                  refine ⟨5773840294103793759154099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 492701038430190400781149781 5773840294103793759154099)
                  ·
                    refine ⟨8660760441155690638731149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5773840294103793759154099 8660760441155690638731149)
                    ·
                      refine ⟨3247785165433383989524181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8660760441155690638731149 3247785165433383989524181)
                      ·
                        rfl

theorem cell23_6325039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 1, 3].length) (baseStart_6325039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325039 prefixEnd_6325039 := by exact prefixLift 6325039
  have htrace : WordTrace (prefixWord ++ tailWord_6325039) baseStart_6325039 baseEnd_6325039 := by
    simpa [prefixWord, tailWord_6325039, baseEnd_6325039] using wordTrace_append hprefix tailTrace_6325039
  have hstable : (prefixWord ++ tailWord_6325039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325039).length < 2 ^ (prefixWord ++ tailWord_6325039).sum := by decide
  have hdescent : baseEnd_6325039 < baseStart_6325039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325046 : List Nat := [5, 1, 2, 2, 2, 1, 1, 9]
def baseStart_6325046 : Nat := 118140960795 + 6325046 * 2 ^ 59
def prefixEnd_6325046 : Nat := 4983230072969 + 3 ^ 40 * 6325046 * 2
def baseEnd_6325046 : Nat := 120288472585109831930987

theorem tailTrace_6325046 : CollatzResearch.WordTrace tailWord_6325046 prefixEnd_6325046 120288472585109831930987 := by
  unfold tailWord_6325046
  simp only [CollatzResearch.WordTrace]
  refine ⟨14418336240215378043766187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153795586562297365800172661 14418336240215378043766187)
  ·
    refine ⟨21627504360323067065649281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14418336240215378043766187 21627504360323067065649281)
    ·
      refine ⟨16220628270242300299236961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21627504360323067065649281 16220628270242300299236961)
      ·
        refine ⟨12165471202681725224427721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16220628270242300299236961 12165471202681725224427721)
        ·
          refine ⟨9124103402011293918320791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12165471202681725224427721 9124103402011293918320791)
          ·
            refine ⟨13686155103016940877481187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9124103402011293918320791 13686155103016940877481187)
            ·
              refine ⟨20529232654525411316221781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13686155103016940877481187 20529232654525411316221781)
              ·
                refine ⟨120288472585109831930987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20529232654525411316221781 120288472585109831930987)
                ·
                  rfl

theorem cell23_6325046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_6325046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325046 prefixEnd_6325046 := by exact prefixLift 6325046
  have htrace : WordTrace (prefixWord ++ tailWord_6325046) baseStart_6325046 baseEnd_6325046 := by
    simpa [prefixWord, tailWord_6325046, baseEnd_6325046] using wordTrace_append hprefix tailTrace_6325046
  have hstable : (prefixWord ++ tailWord_6325046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325046).length < 2 ^ (prefixWord ++ tailWord_6325046).sum := by decide
  have hdescent : baseEnd_6325046 < baseStart_6325046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325072 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 4, 6]
def baseStart_6325072 : Nat := 118140960795 + 6325072 * 2 ^ 59
def prefixEnd_6325072 : Nat := 4983230072969 + 3 ^ 40 * 6325072 * 2
def baseEnd_6325072 : Nat := 1082600703431660786803843

theorem tailTrace_6325072 : CollatzResearch.WordTrace tailWord_6325072 prefixEnd_6325072 1082600703431660786803843 := by
  unfold tailWord_6325072
  simp only [CollatzResearch.WordTrace]
  refine ⟨115347164070675927570352735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153796218760901236760470313 115347164070675927570352735)
  ·
    refine ⟨173020746106013891355529103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115347164070675927570352735 173020746106013891355529103)
    ·
      refine ⟨259531119159020837033293655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173020746106013891355529103 259531119159020837033293655)
      ·
        refine ⟨389296678738531255549940483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259531119159020837033293655 389296678738531255549940483)
        ·
          refine ⟨583945018107796883324910725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389296678738531255549940483 583945018107796883324910725)
          ·
            refine ⟨109489690895211915623420761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 583945018107796883324910725 109489690895211915623420761)
            ·
              refine ⟨82117268171408936717565571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109489690895211915623420761 82117268171408936717565571)
              ·
                refine ⟨123175902257113405076348357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82117268171408936717565571 123175902257113405076348357)
                ·
                  refine ⟨23095481673208763451815317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123175902257113405076348357 23095481673208763451815317)
                  ·
                    refine ⟨1082600703431660786803843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23095481673208763451815317 1082600703431660786803843)
                    ·
                      rfl

theorem cell23_6325072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 4, 6].length) (baseStart_6325072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325072 prefixEnd_6325072 := by exact prefixLift 6325072
  have htrace : WordTrace (prefixWord ++ tailWord_6325072) baseStart_6325072 baseEnd_6325072 := by
    simpa [prefixWord, tailWord_6325072, baseEnd_6325072] using wordTrace_append hprefix tailTrace_6325072
  have hstable : (prefixWord ++ tailWord_6325072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325072).length < 2 ^ (prefixWord ++ tailWord_6325072).sum := by decide
  have hdescent : baseEnd_6325072 < baseStart_6325072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325090 : List Nat := [3, 3, 2, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_6325090 : Nat := 118140960795 + 6325090 * 2 ^ 59
def prefixEnd_6325090 : Nat := 4983230072969 + 3 ^ 40 * 6325090 * 2
def baseEnd_6325090 : Nat := 3247811352946763289986447

theorem tailTrace_6325090 : CollatzResearch.WordTrace tailWord_6325090 prefixEnd_6325090 3247811352946763289986447 := by
  unfold tailWord_6325090
  simp only [CollatzResearch.WordTrace]
  refine ⟨57673746163821661053715181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153796656436857762809907149 57673746163821661053715181)
  ·
    refine ⟨21627654811433122895143193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57673746163821661053715181 21627654811433122895143193)
    ·
      refine ⟨16220741108574842171357395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21627654811433122895143193 16220741108574842171357395)
      ·
        refine ⟨24331111662862263257036093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16220741108574842171357395 24331111662862263257036093)
        ·
          refine ⟨9124166873573348721388535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24331111662862263257036093 9124166873573348721388535)
          ·
            refine ⟨13686250310360023082082803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9124166873573348721388535 13686250310360023082082803)
            ·
              refine ⟨20529375465540034623124205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13686250310360023082082803 20529375465540034623124205)
              ·
                refine ⟨7698515799577512983671577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20529375465540034623124205 7698515799577512983671577)
                ·
                  refine ⟨5773886849683134737753683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7698515799577512983671577 5773886849683134737753683)
                  ·
                    refine ⟨8660830274524702106630525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5773886849683134737753683 8660830274524702106630525)
                    ·
                      refine ⟨3247811352946763289986447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8660830274524702106630525 3247811352946763289986447)
                      ·
                        rfl

theorem cell23_6325090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_6325090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325090 prefixEnd_6325090 := by exact prefixLift 6325090
  have htrace : WordTrace (prefixWord ++ tailWord_6325090) baseStart_6325090 baseEnd_6325090 := by
    simpa [prefixWord, tailWord_6325090, baseEnd_6325090] using wordTrace_append hprefix tailTrace_6325090
  have hstable : (prefixWord ++ tailWord_6325090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325090).length < 2 ^ (prefixWord ++ tailWord_6325090).sum := by decide
  have hdescent : baseEnd_6325090 < baseStart_6325090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325112 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 1, 2, 7]
def baseStart_6325112 : Nat := 118140960795 + 6325112 * 2 ^ 59
def prefixEnd_6325112 : Nat := 4983230072969 + 3 ^ 40 * 6325112 * 2
def baseEnd_6325112 : Nat := 3247822649521162203911345

theorem tailTrace_6325112 : CollatzResearch.WordTrace tailWord_6325112 prefixEnd_6325112 3247822649521162203911345 := by
  unfold tailWord_6325112
  simp only [CollatzResearch.WordTrace]
  refine ⟨115347893530603470986080795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153797191374137961314774393 115347893530603470986080795)
  ·
    refine ⟨173021840295905206479121193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115347893530603470986080795 173021840295905206479121193)
    ·
      refine ⟨129766380221928904859340895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173021840295905206479121193 129766380221928904859340895)
      ·
        refine ⟨194649570332893357289011343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129766380221928904859340895 194649570332893357289011343)
        ·
          refine ⟨291974355499340035933517015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194649570332893357289011343 291974355499340035933517015)
          ·
            refine ⟨437961533249010053900275523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291974355499340035933517015 437961533249010053900275523)
            ·
              refine ⟨656942299873515080850413285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437961533249010053900275523 656942299873515080850413285)
              ·
                refine ⟨123176681226284077659452491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 656942299873515080850413285 123176681226284077659452491)
                ·
                  refine ⟨184765021839426116489178737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123176681226284077659452491 184765021839426116489178737)
                  ·
                    refine ⟨138573766379569587366884053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 184765021839426116489178737 138573766379569587366884053)
                    ·
                      refine ⟨3247822649521162203911345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 138573766379569587366884053 3247822649521162203911345)
                      ·
                        rfl

theorem cell23_6325112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_6325112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325112 prefixEnd_6325112 := by exact prefixLift 6325112
  have htrace : WordTrace (prefixWord ++ tailWord_6325112) baseStart_6325112 baseEnd_6325112 := by
    simpa [prefixWord, tailWord_6325112, baseEnd_6325112] using wordTrace_append hprefix tailTrace_6325112
  have hstable : (prefixWord ++ tailWord_6325112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325112).length < 2 ^ (prefixWord ++ tailWord_6325112).sum := by decide
  have hdescent : baseEnd_6325112 < baseStart_6325112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325130 : List Nat := [3, 1, 2, 4, 1, 1, 1, 4, 2, 2, 2]
def baseStart_6325130 : Nat := 118140960795 + 6325130 * 2 ^ 59
def prefixEnd_6325130 : Nat := 4983230072969 + 3 ^ 40 * 6325130 * 2
def baseEnd_6325130 : Nat := 3247831892172943133486263

theorem tailTrace_6325130 : CollatzResearch.WordTrace tailWord_6325130 prefixEnd_6325130 3247831892172943133486263 := by
  unfold tailWord_6325130
  simp only [CollatzResearch.WordTrace]
  refine ⟨57674110893785432761579211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153797629050094487364211229 57674110893785432761579211)
  ·
    refine ⟨86511166340678149142368817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57674110893785432761579211 86511166340678149142368817)
    ·
      refine ⟨64883374755508611856776613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86511166340678149142368817 64883374755508611856776613)
      ·
        refine ⟨12165632766657864723145615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64883374755508611856776613 12165632766657864723145615)
        ·
          refine ⟨18248449149986797084718423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12165632766657864723145615 18248449149986797084718423)
          ·
            refine ⟨27372673724980195627077635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18248449149986797084718423 27372673724980195627077635)
            ·
              refine ⟨41059010587470293440616453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27372673724980195627077635 41059010587470293440616453)
              ·
                refine ⟨7698564485150680020115585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41059010587470293440616453 7698564485150680020115585)
                ·
                  refine ⟨5773923363863010015086689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7698564485150680020115585 5773923363863010015086689)
                  ·
                    refine ⟨4330442522897257511315017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5773923363863010015086689 4330442522897257511315017)
                    ·
                      refine ⟨3247831892172943133486263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4330442522897257511315017 3247831892172943133486263)
                      ·
                        rfl

theorem cell23_6325130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_6325130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325130 prefixEnd_6325130 := by exact prefixLift 6325130
  have htrace : WordTrace (prefixWord ++ tailWord_6325130) baseStart_6325130 baseEnd_6325130 := by
    simpa [prefixWord, tailWord_6325130, baseEnd_6325130] using wordTrace_append hprefix tailTrace_6325130
  have hstable : (prefixWord ++ tailWord_6325130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325130).length < 2 ^ (prefixWord ++ tailWord_6325130).sum := by decide
  have hdescent : baseEnd_6325130 < baseStart_6325130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325149 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 1, 7]
def baseStart_6325149 : Nat := 118140960795 + 6325149 * 2 ^ 59
def prefixEnd_6325149 : Nat := 4983230072969 + 3 ^ 40 * 6325149 * 2
def baseEnd_6325149 : Nat := 1082613882768459519716225

theorem tailTrace_6325149 : CollatzResearch.WordTrace tailWord_6325149 prefixEnd_6325149 1082613882768459519716225 := by
  unfold tailWord_6325149
  simp only [CollatzResearch.WordTrace]
  refine ⟨230697136562072897291258501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153798091041381931527505667 230697136562072897291258501)
  ·
    refine ⟨43255713105388668242110969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230697136562072897291258501 43255713105388668242110969)
    ·
      refine ⟨32441784829041501181583227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43255713105388668242110969 32441784829041501181583227)
      ·
        refine ⟨48662677243562251772374841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32441784829041501181583227 48662677243562251772374841)
        ·
          refine ⟨36497007932671688829281131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48662677243562251772374841 36497007932671688829281131)
          ·
            refine ⟨54745511899007533243921697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36497007932671688829281131 54745511899007533243921697)
            ·
              refine ⟨41059133924255649932941273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54745511899007533243921697 41059133924255649932941273)
              ·
                refine ⟨30794350443191737449705955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41059133924255649932941273 30794350443191737449705955)
                ·
                  refine ⟨46191525664787606174558933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30794350443191737449705955 46191525664787606174558933)
                  ·
                    refine ⟨1082613882768459519716225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46191525664787606174558933 1082613882768459519716225)
                    ·
                      rfl

theorem cell23_6325149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_6325149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325149 prefixEnd_6325149 := by exact prefixLift 6325149
  have htrace : WordTrace (prefixWord ++ tailWord_6325149) baseStart_6325149 baseEnd_6325149 := by
    simpa [prefixWord, tailWord_6325149, baseEnd_6325149] using wordTrace_append hprefix tailTrace_6325149
  have hstable : (prefixWord ++ tailWord_6325149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325149).length < 2 ^ (prefixWord ++ tailWord_6325149).sum := by decide
  have hdescent : baseEnd_6325149 < baseStart_6325149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325156 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 2, 5, 2]
def baseStart_6325156 : Nat := 118140960795 + 6325156 * 2 ^ 59
def prefixEnd_6325156 : Nat := 4983230072969 + 3 ^ 40 * 6325156 * 2
def baseEnd_6325156 : Nat := 3247845242669960031761143

theorem tailTrace_6325156 : CollatzResearch.WordTrace tailWord_6325156 prefixEnd_6325156 3247845242669960031761143 := by
  unfold tailWord_6325156
  simp only [CollatzResearch.WordTrace]
  refine ⟨115348695936523768743381661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153798261248698358324508881 115348695936523768743381661)
  ·
    refine ⟨43255760976196413278768123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115348695936523768743381661 43255760976196413278768123)
    ·
      refine ⟨64883641464294619918152185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43255760976196413278768123 64883641464294619918152185)
      ·
        refine ⟨48662731098220964938614139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64883641464294619918152185 48662731098220964938614139)
        ·
          refine ⟨72994096647331447407921209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48662731098220964938614139 72994096647331447407921209)
          ·
            refine ⟨54745572485498585555940907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72994096647331447407921209 54745572485498585555940907)
            ·
              refine ⟨82118358728247878333911361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54745572485498585555940907 82118358728247878333911361)
              ·
                refine ⟨61588769046185908750433521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82118358728247878333911361 61588769046185908750433521)
                ·
                  refine ⟨46191576784639431562825141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61588769046185908750433521 46191576784639431562825141)
                  ·
                    refine ⟨4330460323559946709014857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46191576784639431562825141 4330460323559946709014857)
                    ·
                      refine ⟨3247845242669960031761143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4330460323559946709014857 3247845242669960031761143)
                      ·
                        rfl

theorem cell23_6325156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_6325156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325156 prefixEnd_6325156 := by exact prefixLift 6325156
  have htrace : WordTrace (prefixWord ++ tailWord_6325156) baseStart_6325156 baseEnd_6325156 := by
    simpa [prefixWord, tailWord_6325156, baseEnd_6325156] using wordTrace_append hprefix tailTrace_6325156
  have hstable : (prefixWord ++ tailWord_6325156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325156).length < 2 ^ (prefixWord ++ tailWord_6325156).sum := by decide
  have hdescent : baseEnd_6325156 < baseStart_6325156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325213 : List Nat := [1, 4, 3, 1, 2, 1, 2, 2, 3, 4]
def baseStart_6325213 : Nat := 118140960795 + 6325213 * 2 ^ 59
def prefixEnd_6325213 : Nat := 4983230072969 + 3 ^ 40 * 6325213 * 2
def baseEnd_6325213 : Nat := 1082624837022422102916127

theorem tailTrace_6325213 : CollatzResearch.WordTrace tailWord_6325213 prefixEnd_6325213 1082624837022422102916127 := by
  unfold tailWord_6325213
  simp only [CollatzResearch.WordTrace]
  refine ⟨230699470833841036221588293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153799647222560690814392195 230699470833841036221588293)
  ·
    refine ⟨43256150781345194291547805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230699470833841036221588293 43256150781345194291547805)
    ·
      refine ⟨16221056543004447859330427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43256150781345194291547805 16221056543004447859330427)
      ·
        refine ⟨24331584814506671788995641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16221056543004447859330427 24331584814506671788995641)
        ·
          refine ⟨18248688610880003841746731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24331584814506671788995641 18248688610880003841746731)
          ·
            refine ⟨27373032916320005762620097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18248688610880003841746731 27373032916320005762620097)
            ·
              refine ⟨20529774687240004321965073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27373032916320005762620097 20529774687240004321965073)
              ·
                refine ⟨15397331015430003241473805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20529774687240004321965073 15397331015430003241473805)
                ·
                  refine ⟨5773999130786251215552677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15397331015430003241473805 5773999130786251215552677)
                  ·
                    refine ⟨1082624837022422102916127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5773999130786251215552677 1082624837022422102916127)
                    ·
                      rfl

theorem cell23_6325213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_6325213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325213 prefixEnd_6325213 := by exact prefixLift 6325213
  have htrace : WordTrace (prefixWord ++ tailWord_6325213) baseStart_6325213 baseEnd_6325213 := by
    simpa [prefixWord, tailWord_6325213, baseEnd_6325213] using wordTrace_append hprefix tailTrace_6325213
  have hstable : (prefixWord ++ tailWord_6325213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325213).length < 2 ^ (prefixWord ++ tailWord_6325213).sum := by decide
  have hdescent : baseEnd_6325213 < baseStart_6325213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325304 : List Nat := [2, 1, 2, 1, 5, 3, 2, 2, 1, 1, 3]
def baseStart_6325304 : Nat := 118140960795 + 6325304 * 2 ^ 59
def prefixEnd_6325304 : Nat := 4983230072969 + 3 ^ 40 * 6325304 * 2
def baseEnd_6325304 : Nat := 3247921237806825452710463

theorem tailTrace_6325304 : CollatzResearch.WordTrace tailWord_6325304 prefixEnd_6325304 3247921237806825452710463 := by
  unfold tailWord_6325304
  simp only [CollatzResearch.WordTrace]
  refine ⟨115351394938255679381575483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153801859917674239175433977 115351394938255679381575483)
  ·
    refine ⟨173027092407383519072363225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115351394938255679381575483 173027092407383519072363225)
    ·
      refine ⟨129770319305537639304272419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173027092407383519072363225 129770319305537639304272419)
      ·
        refine ⟨194655478958306458956408629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129770319305537639304272419 194655478958306458956408629)
        ·
          refine ⟨18248951152341230527163309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 194655478958306458956408629 18248951152341230527163309)
          ·
            refine ⟨6843356682127961447686241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18248951152341230527163309 6843356682127961447686241)
            ·
              refine ⟨5132517511595971085764681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6843356682127961447686241 5132517511595971085764681)
              ·
                refine ⟨3849388133696978314323511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5132517511595971085764681 3849388133696978314323511)
                ·
                  refine ⟨5774082200545467471485267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3849388133696978314323511 5774082200545467471485267)
                  ·
                    refine ⟨8661123300818201207227901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5774082200545467471485267 8661123300818201207227901)
                    ·
                      refine ⟨3247921237806825452710463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8661123300818201207227901 3247921237806825452710463)
                      ·
                        rfl

theorem cell23_6325304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 1, 1, 3].length) (baseStart_6325304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325304 prefixEnd_6325304 := by exact prefixLift 6325304
  have htrace : WordTrace (prefixWord ++ tailWord_6325304) baseStart_6325304 baseEnd_6325304 := by
    simpa [prefixWord, tailWord_6325304, baseEnd_6325304] using wordTrace_append hprefix tailTrace_6325304
  have hstable : (prefixWord ++ tailWord_6325304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325304).length < 2 ^ (prefixWord ++ tailWord_6325304).sum := by decide
  have hdescent : baseEnd_6325304 < baseStart_6325304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325339 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 13]
def baseStart_6325339 : Nat := 118140960795 + 6325339 * 2 ^ 59
def prefixEnd_6325339 : Nat := 4983230072969 + 3 ^ 40 * 6325339 * 2
def baseEnd_6325339 : Nat := 3247939209629732815772801

theorem tailTrace_6325339 : CollatzResearch.WordTrace tailWord_6325339 prefixEnd_6325339 3247939209629732815772801 := by
  unfold tailWord_6325339
  simp only [CollatzResearch.WordTrace]
  refine ⟨230704066431384559740675071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153802710954256373160450047 230704066431384559740675071)
  ·
    refine ⟨346056099647076839611012607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230704066431384559740675071 346056099647076839611012607)
    ·
      refine ⟨519084149470615259416518911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346056099647076839611012607 519084149470615259416518911)
      ·
        refine ⟨778626224205922889124778367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519084149470615259416518911 778626224205922889124778367)
        ·
          refine ⟨1167939336308884333687167551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778626224205922889124778367 1167939336308884333687167551)
          ·
            refine ⟨1751909004463326500530751327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1167939336308884333687167551 1751909004463326500530751327)
            ·
              refine ⟨2627863506694989750796126991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1751909004463326500530751327 2627863506694989750796126991)
              ·
                refine ⟨3941795260042484626194190487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2627863506694989750796126991 3941795260042484626194190487)
                ·
                  refine ⟨5912692890063726939291285731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3941795260042484626194190487 5912692890063726939291285731)
                  ·
                    refine ⟨8869039335095590408936928597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5912692890063726939291285731 8869039335095590408936928597)
                    ·
                      refine ⟨3247939209629732815772801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 13 8869039335095590408936928597 3247939209629732815772801)
                      ·
                        rfl

theorem cell23_6325339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 13].length) (baseStart_6325339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325339 prefixEnd_6325339 := by exact prefixLift 6325339
  have htrace : WordTrace (prefixWord ++ tailWord_6325339) baseStart_6325339 baseEnd_6325339 := by
    simpa [prefixWord, tailWord_6325339, baseEnd_6325339] using wordTrace_append hprefix tailTrace_6325339
  have hstable : (prefixWord ++ tailWord_6325339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325339).length < 2 ^ (prefixWord ++ tailWord_6325339).sum := by decide
  have hdescent : baseEnd_6325339 < baseStart_6325339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325343 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 4, 1, 3]
def baseStart_6325343 : Nat := 118140960795 + 6325343 * 2 ^ 59
def prefixEnd_6325343 : Nat := 4983230072969 + 3 ^ 40 * 6325343 * 2
def baseEnd_6325343 : Nat := 3247941263552350800122783

theorem tailTrace_6325343 : CollatzResearch.WordTrace tailWord_6325343 prefixEnd_6325343 3247941263552350800122783 := by
  unfold tailWord_6325343
  simp only [CollatzResearch.WordTrace]
  refine ⟨230704212323370068423820683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153802808215580045615880455 230704212323370068423820683)
  ·
    refine ⟨346056318485055102635731025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230704212323370068423820683 346056318485055102635731025)
    ·
      refine ⟨259542238863791326976798269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346056318485055102635731025 259542238863791326976798269)
      ·
        refine ⟨97328339573921747616299351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259542238863791326976798269 97328339573921747616299351)
        ·
          refine ⟨145992509360882621424449027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97328339573921747616299351 145992509360882621424449027)
          ·
            refine ⟨218988764041323932136673541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145992509360882621424449027 218988764041323932136673541)
            ·
              refine ⟨41060393257748237275626289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218988764041323932136673541 41060393257748237275626289)
              ·
                refine ⟨30795294943311177956719717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41060393257748237275626289 30795294943311177956719717)
                ·
                  refine ⟨5774117801870845866884947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30795294943311177956719717 5774117801870845866884947)
                  ·
                    refine ⟨8661176702806268800327421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5774117801870845866884947 8661176702806268800327421)
                    ·
                      refine ⟨3247941263552350800122783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8661176702806268800327421 3247941263552350800122783)
                      ·
                        rfl

theorem cell23_6325343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_6325343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325343 prefixEnd_6325343 := by exact prefixLift 6325343
  have htrace : WordTrace (prefixWord ++ tailWord_6325343) baseStart_6325343 baseEnd_6325343 := by
    simpa [prefixWord, tailWord_6325343, baseEnd_6325343] using wordTrace_append hprefix tailTrace_6325343
  have hstable : (prefixWord ++ tailWord_6325343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325343).length < 2 ^ (prefixWord ++ tailWord_6325343).sum := by decide
  have hdescent : baseEnd_6325343 < baseStart_6325343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325376 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 2, 6]
def baseStart_6325376 : Nat := 118140960795 + 6325376 * 2 ^ 59
def prefixEnd_6325376 : Nat := 4983230072969 + 3 ^ 40 * 6325376 * 2
def baseEnd_6325376 : Nat := 1082652736137983057003377

theorem tailTrace_6325376 : CollatzResearch.WordTrace tailWord_6325376 prefixEnd_6325376 1082652736137983057003377 := by
  unfold tailWord_6325376
  simp only [CollatzResearch.WordTrace]
  refine ⟨115352707966125257529885991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153803610621500343373181321 115352707966125257529885991)
  ·
    refine ⟨173029061949187886294828987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115352707966125257529885991 173029061949187886294828987)
    ·
      refine ⟨259543592923781829442243481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173029061949187886294828987 259543592923781829442243481)
      ·
        refine ⟨194657694692836372081682611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259543592923781829442243481 194657694692836372081682611)
        ·
          refine ⟨291986542039254558122523917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194657694692836372081682611 291986542039254558122523917)
          ·
            refine ⟨109494953264720459295946469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291986542039254558122523917 109494953264720459295946469)
            ·
              refine ⟨20530303737135086117989963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109494953264720459295946469 20530303737135086117989963)
              ·
                refine ⟨30795455605702629176984945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20530303737135086117989963 30795455605702629176984945)
                ·
                  refine ⟨23096591704276971882738709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30795455605702629176984945 23096591704276971882738709)
                  ·
                    refine ⟨1082652736137983057003377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23096591704276971882738709 1082652736137983057003377)
                    ·
                      rfl

theorem cell23_6325376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 2, 6].length) (baseStart_6325376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325376 prefixEnd_6325376 := by exact prefixLift 6325376
  have htrace : WordTrace (prefixWord ++ tailWord_6325376) baseStart_6325376 baseEnd_6325376 := by
    simpa [prefixWord, tailWord_6325376, baseEnd_6325376] using wordTrace_append hprefix tailTrace_6325376
  have hstable : (prefixWord ++ tailWord_6325376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325376).length < 2 ^ (prefixWord ++ tailWord_6325376).sum := by decide
  have hdescent : baseEnd_6325376 < baseStart_6325376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325423 : List Nat := [1, 1, 2, 1, 2, 3, 2, 6, 5]
def baseStart_6325423 : Nat := 118140960795 + 6325423 * 2 ^ 59
def prefixEnd_6325423 : Nat := 4983230072969 + 3 ^ 40 * 6325423 * 2
def baseEnd_6325423 : Nat := 360886926889412276346935

theorem tailTrace_6325423 : CollatzResearch.WordTrace tailWord_6325423 prefixEnd_6325423 360886926889412276346935 := by
  unfold tailWord_6325423
  simp only [CollatzResearch.WordTrace]
  refine ⟨230707130163080242086732923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153804753442053494724488615 230707130163080242086732923)
  ·
    refine ⟨346060695244620363130099385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230707130163080242086732923 346060695244620363130099385)
    ·
      refine ⟨259545521433465272347574539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346060695244620363130099385 259545521433465272347574539)
      ·
        refine ⟨389318282150197908521361809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259545521433465272347574539 389318282150197908521361809)
        ·
          refine ⟨291988711612648431391021357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389318282150197908521361809 291988711612648431391021357)
          ·
            refine ⟨109495766854743161771633009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291988711612648431391021357 109495766854743161771633009)
            ·
              refine ⟨82121825141057371328724757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109495766854743161771633009 82121825141057371328724757)
              ·
                refine ⟨3849460553487064281033973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82121825141057371328724757 3849460553487064281033973)
                ·
                  refine ⟨360886926889412276346935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3849460553487064281033973 360886926889412276346935)
                  ·
                    rfl

theorem cell23_6325423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 5].length) (baseStart_6325423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325423 prefixEnd_6325423 := by exact prefixLift 6325423
  have htrace : WordTrace (prefixWord ++ tailWord_6325423) baseStart_6325423 baseEnd_6325423 := by
    simpa [prefixWord, tailWord_6325423, baseEnd_6325423] using wordTrace_append hprefix tailTrace_6325423
  have hstable : (prefixWord ++ tailWord_6325423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325423).length < 2 ^ (prefixWord ++ tailWord_6325423).sum := by decide
  have hdescent : baseEnd_6325423 < baseStart_6325423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325443 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 4, 5, 2]
def baseStart_6325443 : Nat := 118140960795 + 6325443 * 2 ^ 59
def prefixEnd_6325443 : Nat := 4983230072969 + 3 ^ 40 * 6325443 * 2
def baseEnd_6325443 : Nat := 3247992611617800408872323

theorem tailTrace_6325443 : CollatzResearch.WordTrace tailWord_6325443 prefixEnd_6325443 3247992611617800408872323 := by
  unfold tailWord_6325443
  simp only [CollatzResearch.WordTrace]
  refine ⟨230707859623007785502460983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153805239748671857001640655 230707859623007785502460983)
  ·
    refine ⟨346061789434511678253691475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230707859623007785502460983 346061789434511678253691475)
    ·
      refine ⟨519092684151767517380537213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346061789434511678253691475 519092684151767517380537213)
      ·
        refine ⟨194659756556912819017701455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 519092684151767517380537213 194659756556912819017701455)
        ·
          refine ⟨291989634835369228526552183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194659756556912819017701455 291989634835369228526552183)
          ·
            refine ⟨437984452253053842789828275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291989634835369228526552183 437984452253053842789828275)
            ·
              refine ⟨656976678379580764184742413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437984452253053842789828275 656976678379580764184742413)
              ·
                refine ⟨246366254392342786569278405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 656976678379580764184742413 246366254392342786569278405)
                ·
                  refine ⟨46193672698564272481739701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246366254392342786569278405 46193672698564272481739701)
                  ·
                    refine ⟨4330656815490400545163097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46193672698564272481739701 4330656815490400545163097)
                    ·
                      refine ⟨3247992611617800408872323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4330656815490400545163097 3247992611617800408872323)
                      ·
                        rfl

theorem cell23_6325443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 5, 2].length) (baseStart_6325443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325443 prefixEnd_6325443 := by exact prefixLift 6325443
  have htrace : WordTrace (prefixWord ++ tailWord_6325443) baseStart_6325443 baseEnd_6325443 := by
    simpa [prefixWord, tailWord_6325443, baseEnd_6325443] using wordTrace_append hprefix tailTrace_6325443
  have hstable : (prefixWord ++ tailWord_6325443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325443).length < 2 ^ (prefixWord ++ tailWord_6325443).sum := by decide
  have hdescent : baseEnd_6325443 < baseStart_6325443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325496 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 12]
def baseStart_6325496 : Nat := 118140960795 + 6325496 * 2 ^ 59
def prefixEnd_6325496 : Nat := 4983230072969 + 3 ^ 40 * 6325496 * 2
def baseEnd_6325496 : Nat := 360891091788054300167731

theorem tailTrace_6325496 : CollatzResearch.WordTrace tailWord_6325496 prefixEnd_6325496 360891091788054300167731 := by
  unfold tailWord_6325496
  simp only [CollatzResearch.WordTrace]
  refine ⟨115354896345907887777070171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153806528461210517036093561 115354896345907887777070171)
  ·
    refine ⟨173032344518861831665605257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115354896345907887777070171 173032344518861831665605257)
    ·
      refine ⟨129774258389146373749203943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173032344518861831665605257 129774258389146373749203943)
      ·
        refine ⟨194661387583719560623805915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129774258389146373749203943 194661387583719560623805915)
        ·
          refine ⟨291992081375579340935708873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194661387583719560623805915 291992081375579340935708873)
          ·
            refine ⟨218994061031684505701781655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291992081375579340935708873 218994061031684505701781655)
            ·
              refine ⟨328491091547526758552672483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218994061031684505701781655 328491091547526758552672483)
              ·
                refine ⟨492736637321290137829008725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328491091547526758552672483 492736637321290137829008725)
                ·
                  refine ⟨360891091788054300167731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 492736637321290137829008725 360891091788054300167731)
                  ·
                    rfl

theorem cell23_6325496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 12].length) (baseStart_6325496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325496 prefixEnd_6325496 := by exact prefixLift 6325496
  have htrace : WordTrace (prefixWord ++ tailWord_6325496) baseStart_6325496 baseEnd_6325496 := by
    simpa [prefixWord, tailWord_6325496, baseEnd_6325496] using wordTrace_append hprefix tailTrace_6325496
  have hstable : (prefixWord ++ tailWord_6325496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325496).length < 2 ^ (prefixWord ++ tailWord_6325496).sum := by decide
  have hdescent : baseEnd_6325496 < baseStart_6325496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325530 : List Nat := [3, 1, 1, 3, 3, 1, 3, 2, 6]
def baseStart_6325530 : Nat := 118140960795 + 6325530 * 2 ^ 59
def prefixEnd_6325530 : Nat := 4983230072969 + 3 ^ 40 * 6325530 * 2
def baseEnd_6325530 : Nat := 360893031603860174276047

theorem tailTrace_6325530 : CollatzResearch.WordTrace tailWord_6325530 prefixEnd_6325530 360893031603860174276047 := by
  unfold tailWord_6325530
  simp only [CollatzResearch.WordTrace]
  refine ⟨57677758193423149840219511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153807355182461732907252029 57677758193423149840219511)
  ·
    refine ⟨86516637290134724760329267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57677758193423149840219511 86516637290134724760329267)
    ·
      refine ⟨129774955935202087140493901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86516637290134724760329267 129774955935202087140493901)
      ·
        refine ⟨48665608475700782677685213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129774955935202087140493901 48665608475700782677685213)
        ·
          refine ⟨18249603178387793504131955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48665608475700782677685213 18249603178387793504131955)
          ·
            refine ⟨27374404767581690256197933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18249603178387793504131955 27374404767581690256197933)
            ·
              refine ⟨10265401787843133846074225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27374404767581690256197933 10265401787843133846074225)
              ·
                refine ⟨7699051340882350384555669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10265401787843133846074225 7699051340882350384555669)
                ·
                  refine ⟨360893031603860174276047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7699051340882350384555669 360893031603860174276047)
                  ·
                    rfl

theorem cell23_6325530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 6].length) (baseStart_6325530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325530 prefixEnd_6325530 := by exact prefixLift 6325530
  have htrace : WordTrace (prefixWord ++ tailWord_6325530) baseStart_6325530 baseEnd_6325530 := by
    simpa [prefixWord, tailWord_6325530, baseEnd_6325530] using wordTrace_append hprefix tailTrace_6325530
  have hstable : (prefixWord ++ tailWord_6325530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325530).length < 2 ^ (prefixWord ++ tailWord_6325530).sum := by decide
  have hdescent : baseEnd_6325530 < baseStart_6325530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325557 : List Nat := [1, 3, 3, 1, 2, 2, 2, 2, 3, 1, 3]
def baseStart_6325557 : Nat := 118140960795 + 6325557 * 2 ^ 59
def prefixEnd_6325557 : Nat := 4983230072969 + 3 ^ 40 * 6325557 * 2
def baseEnd_6325557 : Nat := 3248051148412412962846799

theorem tailTrace_6325557 : CollatzResearch.WordTrace tailWord_6325557 prefixEnd_6325557 3248051148412412962846799 := by
  unfold tailWord_6325557
  simp only [CollatzResearch.WordTrace]
  refine ⟨230712017544594782972110925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153808011696396521981407283 230712017544594782972110925)
  ·
    refine ⟨86517006579223043614541597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230712017544594782972110925 86517006579223043614541597)
    ·
      refine ⟨32443877467208641355453099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86517006579223043614541597 32443877467208641355453099)
      ·
        refine ⟨48665816200812962033179649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32443877467208641355453099 48665816200812962033179649)
        ·
          refine ⟨36499362150609721524884737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48665816200812962033179649 36499362150609721524884737)
          ·
            refine ⟨27374521612957291143663553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36499362150609721524884737 27374521612957291143663553)
            ·
              refine ⟨20530891209717968357747665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27374521612957291143663553 20530891209717968357747665)
              ·
                refine ⟨15398168407288476268310749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20530891209717968357747665 15398168407288476268310749)
                ·
                  refine ⟨5774313152733178600616531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15398168407288476268310749 5774313152733178600616531)
                  ·
                    refine ⟨8661469729099767900924797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5774313152733178600616531 8661469729099767900924797)
                    ·
                      refine ⟨3248051148412412962846799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8661469729099767900924797 3248051148412412962846799)
                      ·
                        rfl

theorem cell23_6325557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_6325557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325557 prefixEnd_6325557 := by exact prefixLift 6325557
  have htrace : WordTrace (prefixWord ++ tailWord_6325557) baseStart_6325557 baseEnd_6325557 := by
    simpa [prefixWord, tailWord_6325557, baseEnd_6325557] using wordTrace_append hprefix tailTrace_6325557
  have hstable : (prefixWord ++ tailWord_6325557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325557).length < 2 ^ (prefixWord ++ tailWord_6325557).sum := by decide
  have hdescent : baseEnd_6325557 < baseStart_6325557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325563 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 4]
def baseStart_6325563 : Nat := 118140960795 + 6325563 * 2 ^ 59
def prefixEnd_6325563 : Nat := 4983230072969 + 3 ^ 40 * 6325563 * 2
def baseEnd_6325563 : Nat := 3248054229296339939371771

theorem tailTrace_6325563 : CollatzResearch.WordTrace tailWord_6325563 prefixEnd_6325563 3248054229296339939371771 := by
  unfold tailWord_6325563
  simp only [CollatzResearch.WordTrace]
  refine ⟨230712236382573045996829343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153808157588382030664552895 230712236382573045996829343)
  ·
    refine ⟨346068354573859568995244015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230712236382573045996829343 346068354573859568995244015)
    ·
      refine ⟨519102531860789353492866023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346068354573859568995244015 519102531860789353492866023)
      ·
        refine ⟨778653797791184030239299035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519102531860789353492866023 778653797791184030239299035)
        ·
          refine ⟨1167980696686776045358948553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778653797791184030239299035 1167980696686776045358948553)
          ·
            refine ⟨875985522515082034019211415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1167980696686776045358948553 875985522515082034019211415)
            ·
              refine ⟨1313978283772623051028817123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 875985522515082034019211415 1313978283772623051028817123)
              ·
                refine ⟨1970967425658934576543225685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1313978283772623051028817123 1970967425658934576543225685)
                ·
                  refine ⟨11548637259720319784432963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1970967425658934576543225685 11548637259720319784432963)
                  ·
                    refine ⟨17322955889580479676649445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11548637259720319784432963 17322955889580479676649445)
                    ·
                      refine ⟨3248054229296339939371771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17322955889580479676649445 3248054229296339939371771)
                      ·
                        rfl

theorem cell23_6325563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 4].length) (baseStart_6325563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325563 prefixEnd_6325563 := by exact prefixLift 6325563
  have htrace : WordTrace (prefixWord ++ tailWord_6325563) baseStart_6325563 baseEnd_6325563 := by
    simpa [prefixWord, tailWord_6325563, baseEnd_6325563] using wordTrace_append hprefix tailTrace_6325563
  have hstable : (prefixWord ++ tailWord_6325563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325563).length < 2 ^ (prefixWord ++ tailWord_6325563).sum := by decide
  have hdescent : baseEnd_6325563 < baseStart_6325563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325573 : List Nat := [1, 3, 1, 1, 1, 2, 1, 6, 1, 6]
def baseStart_6325573 : Nat := 118140960795 + 6325573 * 2 ^ 59
def prefixEnd_6325573 : Nat := 4983230072969 + 3 ^ 40 * 6325573 * 2
def baseEnd_6325573 : Nat := 1082686454700961633415575

theorem tailTrace_6325573 : CollatzResearch.WordTrace tailWord_6325573 prefixEnd_6325573 1082686454700961633415575 := by
  unfold tailWord_6325573
  simp only [CollatzResearch.WordTrace]
  refine ⟨230712601112536817704693373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153808400741691211803128915 230712601112536817704693373)
  ·
    refine ⟨86517225417201306639260015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230712601112536817704693373 86517225417201306639260015)
    ·
      refine ⟨129775838125801959958890023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86517225417201306639260015 129775838125801959958890023)
      ·
        refine ⟨194663757188702939938335035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129775838125801959958890023 194663757188702939938335035)
        ·
          refine ⟨291995635783054409907502553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194663757188702939938335035 291995635783054409907502553)
          ·
            refine ⟨218996726837290807430626915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291995635783054409907502553 218996726837290807430626915)
            ·
              refine ⟨328495090255936211145940373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218996726837290807430626915 328495090255936211145940373)
              ·
                refine ⟨15398207355747009897465955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 328495090255936211145940373 15398207355747009897465955)
                ·
                  refine ⟨23097311033620514846198933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15398207355747009897465955 23097311033620514846198933)
                  ·
                    refine ⟨1082686454700961633415575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23097311033620514846198933 1082686454700961633415575)
                    ·
                      rfl

theorem cell23_6325573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_6325573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325573 prefixEnd_6325573 := by exact prefixLift 6325573
  have htrace : WordTrace (prefixWord ++ tailWord_6325573) baseStart_6325573 baseEnd_6325573 := by
    simpa [prefixWord, tailWord_6325573, baseEnd_6325573] using wordTrace_append hprefix tailTrace_6325573
  have hstable : (prefixWord ++ tailWord_6325573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325573).length < 2 ^ (prefixWord ++ tailWord_6325573).sum := by decide
  have hdescent : baseEnd_6325573 < baseStart_6325573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325583 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 3]
def baseStart_6325583 : Nat := 118140960795 + 6325583 * 2 ^ 59
def prefixEnd_6325583 : Nat := 4983230072969 + 3 ^ 40 * 6325583 * 2
def baseEnd_6325583 : Nat := 3248064498909429861121679

theorem tailTrace_6325583 : CollatzResearch.WordTrace tailWord_6325583 prefixEnd_6325583 3248064498909429861121679 := by
  unfold tailWord_6325583
  simp only [CollatzResearch.WordTrace]
  refine ⟨230712965842500589412557403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153808643895000392941704935 230712965842500589412557403)
  ·
    refine ⟨346069448763750884118836105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230712965842500589412557403 346069448763750884118836105)
    ·
      refine ⟨259552086572813163089127079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346069448763750884118836105 259552086572813163089127079)
      ·
        refine ⟨389328129859219744633690619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259552086572813163089127079 389328129859219744633690619)
        ·
          refine ⟨583992194788829616950535929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389328129859219744633690619 583992194788829616950535929)
          ·
            refine ⟨437994146091622212712901947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 583992194788829616950535929 437994146091622212712901947)
            ·
              refine ⟨656991219137433319069352921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437994146091622212712901947 656991219137433319069352921)
              ·
                refine ⟨492743414353074989302014691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 656991219137433319069352921 492743414353074989302014691)
                ·
                  refine ⟨739115121529612483953022037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 492743414353074989302014691 739115121529612483953022037)
                  ·
                    refine ⟨8661505330425146296324477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 739115121529612483953022037 8661505330425146296324477)
                    ·
                      refine ⟨3248064498909429861121679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8661505330425146296324477 3248064498909429861121679)
                      ·
                        rfl

theorem cell23_6325583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 3].length) (baseStart_6325583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325583 prefixEnd_6325583 := by exact prefixLift 6325583
  have htrace : WordTrace (prefixWord ++ tailWord_6325583) baseStart_6325583 baseEnd_6325583 := by
    simpa [prefixWord, tailWord_6325583, baseEnd_6325583] using wordTrace_append hprefix tailTrace_6325583
  have hstable : (prefixWord ++ tailWord_6325583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325583).length < 2 ^ (prefixWord ++ tailWord_6325583).sum := by decide
  have hdescent : baseEnd_6325583 < baseStart_6325583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325591 : List Nat := [1, 1, 3, 2, 3, 3, 3, 2, 1, 1, 3]
def baseStart_6325591 : Nat := 118140960795 + 6325591 * 2 ^ 59
def prefixEnd_6325591 : Nat := 4983230072969 + 3 ^ 40 * 6325591 * 2
def baseEnd_6325591 : Nat := 3248068606754665829821643

theorem tailTrace_6325591 : CollatzResearch.WordTrace tailWord_6325591 prefixEnd_6325591 3248068606754665829821643 := by
  unfold tailWord_6325591
  simp only [CollatzResearch.WordTrace]
  refine ⟨230713257626471606778848627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153808838417647737852565751 230713257626471606778848627)
  ·
    refine ⟨346069886439707410168272941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230713257626471606778848627 346069886439707410168272941)
    ·
      refine ⟨129776207414890278813102353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346069886439707410168272941 129776207414890278813102353)
      ·
        refine ⟨97332155561167709109826765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129776207414890278813102353 97332155561167709109826765)
        ·
          refine ⟨36499558335437890916185037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97332155561167709109826765 36499558335437890916185037)
          ·
            refine ⟨13687334375789209093569389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36499558335437890916185037 13687334375789209093569389)
            ·
              refine ⟨5132750390920953410088521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13687334375789209093569389 5132750390920953410088521)
              ·
                refine ⟨3849562793190715057566391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5132750390920953410088521 3849562793190715057566391)
                ·
                  refine ⟨5774344189786072586349587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3849562793190715057566391 5774344189786072586349587)
                  ·
                    refine ⟨8661516284679108879524381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5774344189786072586349587 8661516284679108879524381)
                    ·
                      refine ⟨3248068606754665829821643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8661516284679108879524381 3248068606754665829821643)
                      ·
                        rfl

theorem cell23_6325591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 1, 1, 3].length) (baseStart_6325591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325591 prefixEnd_6325591 := by exact prefixLift 6325591
  have htrace : WordTrace (prefixWord ++ tailWord_6325591) baseStart_6325591 baseEnd_6325591 := by
    simpa [prefixWord, tailWord_6325591, baseEnd_6325591] using wordTrace_append hprefix tailTrace_6325591
  have hstable : (prefixWord ++ tailWord_6325591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325591).length < 2 ^ (prefixWord ++ tailWord_6325591).sum := by decide
  have hdescent : baseEnd_6325591 < baseStart_6325591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325593 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 1, 1, 6]
def baseStart_6325593 : Nat := 118140960795 + 6325593 * 2 ^ 59
def prefixEnd_6325593 : Nat := 4983230072969 + 3 ^ 40 * 6325593 * 2
def baseEnd_6325593 : Nat := 3248069633715974821996633

theorem tailTrace_6325593 : CollatzResearch.WordTrace tailWord_6325593 prefixEnd_6325593 3248069633715974821996633 := by
  unfold tailWord_6325593
  simp only [CollatzResearch.WordTrace]
  refine ⟨230713330572464361120421433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153808887048309574080280955 230713330572464361120421433)
  ·
    refine ⟨173034997929348270840316075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230713330572464361120421433 173034997929348270840316075)
    ·
      refine ⟨259552496894022406260474113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173034997929348270840316075 259552496894022406260474113)
      ·
        refine ⟨194664372670516804695355585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259552496894022406260474113 194664372670516804695355585)
        ·
          refine ⟨145998279502887603521516689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194664372670516804695355585 145998279502887603521516689)
          ·
            refine ⟨109498709627165702641137517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145998279502887603521516689 109498709627165702641137517)
            ·
              refine ⟨41062016110187138490426569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109498709627165702641137517 41062016110187138490426569)
              ·
                refine ⟨30796512082640353867819927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41062016110187138490426569 30796512082640353867819927)
                ·
                  refine ⟨46194768123960530801729891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30796512082640353867819927 46194768123960530801729891)
                  ·
                    refine ⟨69292152185940796202594837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46194768123960530801729891 69292152185940796202594837)
                    ·
                      refine ⟨3248069633715974821996633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69292152185940796202594837 3248069633715974821996633)
                      ·
                        rfl

theorem cell23_6325593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_6325593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325593 prefixEnd_6325593 := by exact prefixLift 6325593
  have htrace : WordTrace (prefixWord ++ tailWord_6325593) baseStart_6325593 baseEnd_6325593 := by
    simpa [prefixWord, tailWord_6325593, baseEnd_6325593] using wordTrace_append hprefix tailTrace_6325593
  have hstable : (prefixWord ++ tailWord_6325593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325593).length < 2 ^ (prefixWord ++ tailWord_6325593).sum := by decide
  have hdescent : baseEnd_6325593 < baseStart_6325593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325600 : List Nat := [2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 5]
def baseStart_6325600 : Nat := 118140960795 + 6325600 * 2 ^ 59
def prefixEnd_6325600 : Nat := 4983230072969 + 3 ^ 40 * 6325600 * 2
def baseEnd_6325600 : Nat := 3248073228080556294609101

theorem tailTrace_6325600 : CollatzResearch.WordTrace tailWord_6325600 prefixEnd_6325600 3248073228080556294609101 := by
  unfold tailWord_6325600
  simp only [CollatzResearch.WordTrace]
  refine ⟨115356792941719500657963127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153809057255626000877284169 115356792941719500657963127)
  ·
    refine ⟨173035189412579250986944691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115356792941719500657963127 173035189412579250986944691)
    ·
      refine ⟨259552784118868876480417037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173035189412579250986944691 259552784118868876480417037)
      ·
        refine ⟨97332294044575828680156389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259552784118868876480417037 97332294044575828680156389)
        ·
          refine ⟨18249805133357967877529323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97332294044575828680156389 18249805133357967877529323)
          ·
            refine ⟨27374707700036951816293985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18249805133357967877529323 27374707700036951816293985)
            ·
              refine ⟨20531030775027713862220489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27374707700036951816293985 20531030775027713862220489)
              ·
                refine ⟨15398273081270785396665367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20531030775027713862220489 15398273081270785396665367)
                ·
                  refine ⟨23097409621906178094998051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15398273081270785396665367 23097409621906178094998051)
                  ·
                    refine ⟨34646114432859267142497077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23097409621906178094998051 34646114432859267142497077)
                    ·
                      refine ⟨3248073228080556294609101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34646114432859267142497077 3248073228080556294609101)
                      ·
                        rfl

theorem cell23_6325600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_6325600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325600 prefixEnd_6325600 := by exact prefixLift 6325600
  have htrace : WordTrace (prefixWord ++ tailWord_6325600) baseStart_6325600 baseEnd_6325600 := by
    simpa [prefixWord, tailWord_6325600, baseEnd_6325600] using wordTrace_append hprefix tailTrace_6325600
  have hstable : (prefixWord ++ tailWord_6325600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325600).length < 2 ^ (prefixWord ++ tailWord_6325600).sum := by decide
  have hdescent : baseEnd_6325600 < baseStart_6325600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325603 : List Nat := [1, 1, 1, 5, 2, 2, 1, 10]
def baseStart_6325603 : Nat := 118140960795 + 6325603 * 2 ^ 59
def prefixEnd_6325603 : Nat := 4983230072969 + 3 ^ 40 * 6325603 * 2
def baseEnd_6325603 : Nat := 120299065500834066032281

theorem tailTrace_6325603 : CollatzResearch.WordTrace tailWord_6325603 prefixEnd_6325603 120299065500834066032281 := by
  unfold tailWord_6325603
  simp only [CollatzResearch.WordTrace]
  refine ⟨230713695302428132828285463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153809130201618755218856975 230713695302428132828285463)
  ·
    refine ⟨346070542953642199242428195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230713695302428132828285463 346070542953642199242428195)
    ·
      refine ⟨519105814430463298863642293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346070542953642199242428195 519105814430463298863642293)
      ·
        refine ⟨48666170102855934268466465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 519105814430463298863642293 48666170102855934268466465)
        ·
          refine ⟨36499627577141950701349849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48666170102855934268466465 36499627577141950701349849)
          ·
            refine ⟨27374720682856463026012387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36499627577141950701349849 27374720682856463026012387)
            ·
              refine ⟨41062081024284694539018581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27374720682856463026012387 41062081024284694539018581)
              ·
                refine ⟨120299065500834066032281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41062081024284694539018581 120299065500834066032281)
                ·
                  rfl

theorem cell23_6325603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 10].length) (baseStart_6325603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325603 prefixEnd_6325603 := by exact prefixLift 6325603
  have htrace : WordTrace (prefixWord ++ tailWord_6325603) baseStart_6325603 baseEnd_6325603 := by
    simpa [prefixWord, tailWord_6325603, baseEnd_6325603] using wordTrace_append hprefix tailTrace_6325603
  have hstable : (prefixWord ++ tailWord_6325603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325603).length < 2 ^ (prefixWord ++ tailWord_6325603).sum := by decide
  have hdescent : baseEnd_6325603 < baseStart_6325603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325614 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 3, 1, 4]
def baseStart_6325614 : Nat := 118140960795 + 6325614 * 2 ^ 59
def prefixEnd_6325614 : Nat := 4983230072969 + 3 ^ 40 * 6325614 * 2
def baseEnd_6325614 : Nat := 3248080416809719239834037

theorem tailTrace_6325614 : CollatzResearch.WordTrace tailWord_6325614 prefixEnd_6325614 3248080416809719239834037 := by
  unfold tailWord_6325614
  simp only [CollatzResearch.WordTrace]
  refine ⟨28839262063173535213366987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153809397670258854471290597 28839262063173535213366987)
  ·
    refine ⟨43258893094760302820050481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28839262063173535213366987 43258893094760302820050481)
    ·
      refine ⟨32444169821070227115037861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43258893094760302820050481 32444169821070227115037861)
      ·
        refine ⟨6083281841450667584069599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32444169821070227115037861 6083281841450667584069599)
        ·
          refine ⟨9124922762176001376104399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6083281841450667584069599 9124922762176001376104399)
          ·
            refine ⟨13687384143264002064156599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9124922762176001376104399 13687384143264002064156599)
            ·
              refine ⟨20531076214896003096234899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13687384143264002064156599 20531076214896003096234899)
              ·
                refine ⟨30796614322344004644352349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20531076214896003096234899 30796614322344004644352349)
                ·
                  refine ⟨11548730370879001741632131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30796614322344004644352349 11548730370879001741632131)
                  ·
                    refine ⟨17323095556318502612448197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11548730370879001741632131 17323095556318502612448197)
                    ·
                      refine ⟨3248080416809719239834037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17323095556318502612448197 3248080416809719239834037)
                      ·
                        rfl

theorem cell23_6325614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_6325614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325614 prefixEnd_6325614 := by exact prefixLift 6325614
  have htrace : WordTrace (prefixWord ++ tailWord_6325614) baseStart_6325614 baseEnd_6325614 := by
    simpa [prefixWord, tailWord_6325614, baseEnd_6325614] using wordTrace_append hprefix tailTrace_6325614
  have hstable : (prefixWord ++ tailWord_6325614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325614).length < 2 ^ (prefixWord ++ tailWord_6325614).sum := by decide
  have hdescent : baseEnd_6325614 < baseStart_6325614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325617 : List Nat := [1, 2, 2, 2, 1, 2, 5, 2, 1, 2, 3]
def baseStart_6325617 : Nat := 118140960795 + 6325617 * 2 ^ 59
def prefixEnd_6325617 : Nat := 4983230072969 + 3 ^ 40 * 6325617 * 2
def baseEnd_6325617 : Nat := 3248081957251682728096523

theorem tailTrace_6325617 : CollatzResearch.WordTrace tailWord_6325617 prefixEnd_6325617 3248081957251682728096523 := by
  unfold tailWord_6325617
  simp only [CollatzResearch.WordTrace]
  refine ⟨230714205924377413219295105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153809470616251608812863403 230714205924377413219295105)
  ·
    refine ⟨173035654443283059914471329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230714205924377413219295105 173035654443283059914471329)
    ·
      refine ⟨129776740832462294935853497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173035654443283059914471329 129776740832462294935853497)
      ·
        refine ⟨97332555624346721201890123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129776740832462294935853497 97332555624346721201890123)
        ·
          refine ⟨145998833436520081802835185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97332555624346721201890123 145998833436520081802835185)
          ·
            refine ⟨109499125077390061352126389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145998833436520081802835185 109499125077390061352126389)
            ·
              refine ⟨10265542976005318251761849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109499125077390061352126389 10265542976005318251761849)
              ·
                refine ⟨7699157232003988688821387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10265542976005318251761849 7699157232003988688821387)
                ·
                  refine ⟨11548735848005983033232081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7699157232003988688821387 11548735848005983033232081)
                  ·
                    refine ⟨8661551886004487274924061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11548735848005983033232081 8661551886004487274924061)
                    ·
                      refine ⟨3248081957251682728096523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8661551886004487274924061 3248081957251682728096523)
                      ·
                        rfl

theorem cell23_6325617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_6325617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325617 prefixEnd_6325617 := by exact prefixLift 6325617
  have htrace : WordTrace (prefixWord ++ tailWord_6325617) baseStart_6325617 baseEnd_6325617 := by
    simpa [prefixWord, tailWord_6325617, baseEnd_6325617] using wordTrace_append hprefix tailTrace_6325617
  have hstable : (prefixWord ++ tailWord_6325617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325617).length < 2 ^ (prefixWord ++ tailWord_6325617).sum := by decide
  have hdescent : baseEnd_6325617 < baseStart_6325617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325634 : List Nat := [3, 4, 2, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_6325634 : Nat := 118140960795 + 6325634 * 2 ^ 59
def prefixEnd_6325634 : Nat := 4983230072969 + 3 ^ 40 * 6325634 * 2
def baseEnd_6325634 : Nat := 3248090686422809161583945

theorem tailTrace_6325634 : CollatzResearch.WordTrace tailWord_6325634 prefixEnd_6325634 3248090686422809161583945 := by
  unfold tailWord_6325634
  simp only [CollatzResearch.WordTrace]
  refine ⟨57678706491328956280665989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153809883976877216748442637 57678706491328956280665989)
  ·
    refine ⟨10814757467124179302624873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57678706491328956280665989 10814757467124179302624873)
    ·
      refine ⟨8111068100343134476968655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10814757467124179302624873 8111068100343134476968655)
      ·
        refine ⟨12166602150514701715452983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8111068100343134476968655 12166602150514701715452983)
        ·
          refine ⟨18249903225772052573179475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12166602150514701715452983 18249903225772052573179475)
          ·
            refine ⟨27374854838658078859769213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18249903225772052573179475 27374854838658078859769213)
            ·
              refine ⟨10265570564496779572413455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27374854838658078859769213 10265570564496779572413455)
              ·
                refine ⟨15398355846745169358620183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10265570564496779572413455 15398355846745169358620183)
                ·
                  refine ⟨23097533770117754037930275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15398355846745169358620183 23097533770117754037930275)
                  ·
                    refine ⟨34646300655176631056895413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23097533770117754037930275 34646300655176631056895413)
                    ·
                      refine ⟨3248090686422809161583945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34646300655176631056895413 3248090686422809161583945)
                      ·
                        rfl

theorem cell23_6325634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_6325634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325634 prefixEnd_6325634 := by exact prefixLift 6325634
  have htrace : WordTrace (prefixWord ++ tailWord_6325634) baseStart_6325634 baseEnd_6325634 := by
    simpa [prefixWord, tailWord_6325634, baseEnd_6325634] using wordTrace_append hprefix tailTrace_6325634
  have hstable : (prefixWord ++ tailWord_6325634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325634).length < 2 ^ (prefixWord ++ tailWord_6325634).sum := by decide
  have hdescent : baseEnd_6325634 < baseStart_6325634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325657 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 3, 3, 2]
def baseStart_6325657 : Nat := 118140960795 + 6325657 * 2 ^ 59
def prefixEnd_6325657 : Nat := 4983230072969 + 3 ^ 40 * 6325657 * 2
def baseEnd_6325657 : Nat := 3248102496477862571596339

theorem tailTrace_6325657 : CollatzResearch.WordTrace tailWord_6325657 prefixEnd_6325657 3248102496477862571596339 := by
  unfold tailWord_6325657
  simp only [CollatzResearch.WordTrace]
  refine ⟨230715664844232500050751225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153810443229488333367167483 230715664844232500050751225)
  ·
    refine ⟨173036748633174375038063419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230715664844232500050751225 173036748633174375038063419)
    ·
      refine ⟨259555122949761562557095129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173036748633174375038063419 259555122949761562557095129)
      ·
        refine ⟨194666342212321171917821347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259555122949761562557095129 194666342212321171917821347)
        ·
          refine ⟨291999513318481757876732021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194666342212321171917821347 291999513318481757876732021)
          ·
            refine ⟨27374954373607664800943627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 291999513318481757876732021 27374954373607664800943627)
            ·
              refine ⟨41062431560411497201415441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27374954373607664800943627 41062431560411497201415441)
              ·
                refine ⟨30796823670308622901061581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41062431560411497201415441 30796823670308622901061581)
                ·
                  refine ⟨11548808876365733587898093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30796823670308622901061581 11548808876365733587898093)
                  ·
                    refine ⟨4330803328637150095461785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11548808876365733587898093 4330803328637150095461785)
                    ·
                      refine ⟨3248102496477862571596339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4330803328637150095461785 3248102496477862571596339)
                      ·
                        rfl

theorem cell23_6325657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 3, 2].length) (baseStart_6325657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325657 prefixEnd_6325657 := by exact prefixLift 6325657
  have htrace : WordTrace (prefixWord ++ tailWord_6325657) baseStart_6325657 baseEnd_6325657 := by
    simpa [prefixWord, tailWord_6325657, baseEnd_6325657] using wordTrace_append hprefix tailTrace_6325657
  have hstable : (prefixWord ++ tailWord_6325657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325657).length < 2 ^ (prefixWord ++ tailWord_6325657).sum := by decide
  have hdescent : baseEnd_6325657 < baseStart_6325657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325687 : List Nat := [1, 1, 3, 1, 3, 2, 1, 4, 1, 4, 2]
def baseStart_6325687 : Nat := 118140960795 + 6325687 * 2 ^ 59
def prefixEnd_6325687 : Nat := 4983230072969 + 3 ^ 40 * 6325687 * 2
def baseEnd_6325687 : Nat := 3248117900897497454221201

theorem tailTrace_6325687 : CollatzResearch.WordTrace tailWord_6325687 prefixEnd_6325687 3248117900897497454221201 := by
  unfold tailWord_6325687
  simp only [CollatzResearch.WordTrace]
  refine ⟨230716759034123815174343315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153811172689415876782895543 230716759034123815174343315)
  ·
    refine ⟨346075138551185722761514973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230716759034123815174343315 346075138551185722761514973)
    ·
      refine ⟨129778176956694646035568115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346075138551185722761514973 129778176956694646035568115)
      ·
        refine ⟨194667265435041969053352173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129778176956694646035568115 194667265435041969053352173)
        ·
          refine ⟨73000224538140738395007065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194667265435041969053352173 73000224538140738395007065)
          ·
            refine ⟨54750168403605553796255299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73000224538140738395007065 54750168403605553796255299)
            ·
              refine ⟨82125252605408330694382949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54750168403605553796255299 82125252605408330694382949)
              ·
                refine ⟨15398484863514062005196803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82125252605408330694382949 15398484863514062005196803)
                ·
                  refine ⟨23097727295271093007795205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15398484863514062005196803 23097727295271093007795205)
                  ·
                    refine ⟨4330823867863329938961601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23097727295271093007795205 4330823867863329938961601)
                    ·
                      refine ⟨3248117900897497454221201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4330823867863329938961601 3248117900897497454221201)
                      ·
                        rfl

theorem cell23_6325687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 4, 2].length) (baseStart_6325687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325687 prefixEnd_6325687 := by exact prefixLift 6325687
  have htrace : WordTrace (prefixWord ++ tailWord_6325687) baseStart_6325687 baseEnd_6325687 := by
    simpa [prefixWord, tailWord_6325687, baseEnd_6325687] using wordTrace_append hprefix tailTrace_6325687
  have hstable : (prefixWord ++ tailWord_6325687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325687).length < 2 ^ (prefixWord ++ tailWord_6325687).sum := by decide
  have hdescent : baseEnd_6325687 < baseStart_6325687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325704 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 4, 2, 2]
def baseStart_6325704 : Nat := 118140960795 + 6325704 * 2 ^ 59
def prefixEnd_6325704 : Nat := 4983230072969 + 3 ^ 40 * 6325704 * 2
def baseEnd_6325704 : Nat := 3248126630068623887708623

theorem tailTrace_6325704 : CollatzResearch.WordTrace tailWord_6325704 prefixEnd_6325704 3248126630068623887708623 := by
  unfold tailWord_6325704
  simp only [CollatzResearch.WordTrace]
  refine ⟨115358689537531113538856083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153811586050041484718474777 115358689537531113538856083)
  ·
    refine ⟨173038034306296670308284125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115358689537531113538856083 173038034306296670308284125)
    ·
      refine ⟨64889262864861251365606547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173038034306296670308284125 64889262864861251365606547)
      ·
        refine ⟨97333894297291877048409821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64889262864861251365606547 97333894297291877048409821)
        ·
          refine ⟨36500210361484453893153683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97333894297291877048409821 36500210361484453893153683)
          ·
            refine ⟨54750315542226680839730525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36500210361484453893153683 54750315542226680839730525)
            ·
              refine ⟨20531368328335005314898947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54750315542226680839730525 20531368328335005314898947)
              ·
                refine ⟨30797052492502507972348421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20531368328335005314898947 30797052492502507972348421)
                ·
                  refine ⟨5774447342344220244815329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30797052492502507972348421 5774447342344220244815329)
                  ·
                    refine ⟨4330835506758165183611497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5774447342344220244815329 4330835506758165183611497)
                    ·
                      refine ⟨3248126630068623887708623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4330835506758165183611497 3248126630068623887708623)
                      ·
                        rfl

theorem cell23_6325704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 4, 2, 2].length) (baseStart_6325704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325704 prefixEnd_6325704 := by exact prefixLift 6325704
  have htrace : WordTrace (prefixWord ++ tailWord_6325704) baseStart_6325704 baseEnd_6325704 := by
    simpa [prefixWord, tailWord_6325704, baseEnd_6325704] using wordTrace_append hprefix tailTrace_6325704
  have hstable : (prefixWord ++ tailWord_6325704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325704).length < 2 ^ (prefixWord ++ tailWord_6325704).sum := by decide
  have hdescent : baseEnd_6325704 < baseStart_6325704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325710 : List Nat := [4, 1, 1, 1, 2, 1, 3, 3, 7]
def baseStart_6325710 : Nat := 118140960795 + 6325710 * 2 ^ 59
def prefixEnd_6325710 : Nat := 4983230072969 + 3 ^ 40 * 6325710 * 2
def baseEnd_6325710 : Nat := 360903301216950096025955

theorem tailTrace_6325710 : CollatzResearch.WordTrace tailWord_6325710 prefixEnd_6325710 360903301216950096025955 := by
  unfold tailWord_6325710
  simp only [CollatzResearch.WordTrace]
  refine ⟨28839699739130061262803823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153811731942026993401620389 28839699739130061262803823)
  ·
    refine ⟨43259549608695091894205735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28839699739130061262803823 43259549608695091894205735)
    ·
      refine ⟨64889324413042637841308603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43259549608695091894205735 64889324413042637841308603)
      ·
        refine ⟨97333986619563956761962905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64889324413042637841308603 97333986619563956761962905)
        ·
          refine ⟨73000489964672967571472179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97333986619563956761962905 73000489964672967571472179)
          ·
            refine ⟨109500734947009451357208269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73000489964672967571472179 109500734947009451357208269)
            ·
              refine ⟨41062775605128544258953101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109500734947009451357208269 41062775605128544258953101)
              ·
                refine ⟨15398540851923204097107413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41062775605128544258953101 15398540851923204097107413)
                ·
                  refine ⟨360903301216950096025955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15398540851923204097107413 360903301216950096025955)
                  ·
                    rfl

theorem cell23_6325710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_6325710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325710 prefixEnd_6325710 := by exact prefixLift 6325710
  have htrace : WordTrace (prefixWord ++ tailWord_6325710) baseStart_6325710 baseEnd_6325710 := by
    simpa [prefixWord, tailWord_6325710, baseEnd_6325710] using wordTrace_append hprefix tailTrace_6325710
  have hstable : (prefixWord ++ tailWord_6325710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325710).length < 2 ^ (prefixWord ++ tailWord_6325710).sum := by decide
  have hdescent : baseEnd_6325710 < baseStart_6325710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325744 : List Nat := [2, 1, 1, 1, 3, 6, 1, 3, 5]
def baseStart_6325744 : Nat := 118140960795 + 6325744 * 2 ^ 59
def prefixEnd_6325744 : Nat := 4983230072969 + 3 ^ 40 * 6325744 * 2
def baseEnd_6325744 : Nat := 360905241032755970134271

theorem tailTrace_6325744 : CollatzResearch.WordTrace tailWord_6325744 prefixEnd_6325744 360905241032755970134271 := by
  unfold tailWord_6325744
  simp only [CollatzResearch.WordTrace]
  refine ⟨115359418997458656954584143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153812558663278209272778857 115359418997458656954584143)
  ·
    refine ⟨173039128496187985431876215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115359418997458656954584143 173039128496187985431876215)
    ·
      refine ⟨259558692744281978147814323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173039128496187985431876215 259558692744281978147814323)
      ·
        refine ⟨389338039116422967221721485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259558692744281978147814323 389338039116422967221721485)
        ·
          refine ⟨146001764668658612708145557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389338039116422967221721485 146001764668658612708145557)
          ·
            refine ⟨6843832718843372470694323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 146001764668658612708145557 6843832718843372470694323)
            ·
              refine ⟨10265749078265058706041485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6843832718843372470694323 10265749078265058706041485)
              ·
                refine ⟨3849655904349397014765557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10265749078265058706041485 3849655904349397014765557)
                ·
                  refine ⟨360905241032755970134271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3849655904349397014765557 360905241032755970134271)
                  ·
                    rfl

theorem cell23_6325744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 5].length) (baseStart_6325744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325744 prefixEnd_6325744 := by exact prefixLift 6325744
  have htrace : WordTrace (prefixWord ++ tailWord_6325744) baseStart_6325744 baseEnd_6325744 := by
    simpa [prefixWord, tailWord_6325744, baseEnd_6325744] using wordTrace_append hprefix tailTrace_6325744
  have hstable : (prefixWord ++ tailWord_6325744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325744).length < 2 ^ (prefixWord ++ tailWord_6325744).sum := by decide
  have hdescent : baseEnd_6325744 < baseStart_6325744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325757 : List Nat := [1, 4, 1, 1, 1, 5, 1, 2, 2, 5]
def baseStart_6325757 : Nat := 118140960795 + 6325757 * 2 ^ 59
def prefixEnd_6325757 : Nat := 4983230072969 + 3 ^ 40 * 6325757 * 2
def baseEnd_6325757 : Nat := 1082717948181104060115293

theorem tailTrace_6325757 : CollatzResearch.WordTrace tailWord_6325757 prefixEnd_6325757 1082717948181104060115293 := by
  unfold tailWord_6325757
  simp only [CollatzResearch.WordTrace]
  refine ⟨230719312143870217129391525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153812874762580144752927683 230719312143870217129391525)
  ·
    refine ⟨43259871026975665711760911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230719312143870217129391525 43259871026975665711760911)
    ·
      refine ⟨64889806540463498567641367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43259871026975665711760911 64889806540463498567641367)
      ·
        refine ⟨97334709810695247851462051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64889806540463498567641367 97334709810695247851462051)
        ·
          refine ⟨146002064716042871777193077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97334709810695247851462051 146002064716042871777193077)
          ·
            refine ⟨13687693567129019229111851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146002064716042871777193077 13687693567129019229111851)
            ·
              refine ⟨20531540350693528843667777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13687693567129019229111851 20531540350693528843667777)
              ·
                refine ⟨15398655263020146632750833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20531540350693528843667777 15398655263020146632750833)
                ·
                  refine ⟨11548991447265109974563125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15398655263020146632750833 11548991447265109974563125)
                  ·
                    refine ⟨1082717948181104060115293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11548991447265109974563125 1082717948181104060115293)
                    ·
                      rfl

theorem cell23_6325757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_6325757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325757 prefixEnd_6325757 := by exact prefixLift 6325757
  have htrace : WordTrace (prefixWord ++ tailWord_6325757) baseStart_6325757 baseEnd_6325757 := by
    simpa [prefixWord, tailWord_6325757, baseEnd_6325757] using wordTrace_append hprefix tailTrace_6325757
  have hstable : (prefixWord ++ tailWord_6325757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325757).length < 2 ^ (prefixWord ++ tailWord_6325757).sum := by decide
  have hdescent : baseEnd_6325757 < baseStart_6325757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325761 : List Nat := [1, 2, 4, 1, 4, 1, 3, 2, 5]
def baseStart_6325761 : Nat := 118140960795 + 6325761 * 2 ^ 59
def prefixEnd_6325761 : Nat := 4983230072969 + 3 ^ 40 * 6325761 * 2
def baseEnd_6325761 : Nat := 360906210940658907188429

theorem tailTrace_6325761 : CollatzResearch.WordTrace tailWord_6325761 prefixEnd_6325761 360906210940658907188429 := by
  unfold tailWord_6325761
  simp only [CollatzResearch.WordTrace]
  refine ⟨230719458035855725812537137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153812972023903817208358091 230719458035855725812537137)
  ·
    refine ⟨173039593526891794359402853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230719458035855725812537137 173039593526891794359402853)
    ·
      refine ⟨32444923786292211442388035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173039593526891794359402853 32444923786292211442388035)
      ·
        refine ⟨48667385679438317163582053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32444923786292211442388035 48667385679438317163582053)
        ·
          refine ⟨9125134814894684468171635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48667385679438317163582053 9125134814894684468171635)
          ·
            refine ⟨13687702222342026702257453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9125134814894684468171635 13687702222342026702257453)
            ·
              refine ⟨5132888333378260013346545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13687702222342026702257453 5132888333378260013346545)
              ·
                refine ⟨3849666250033695010009909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5132888333378260013346545 3849666250033695010009909)
                ·
                  refine ⟨360906210940658907188429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3849666250033695010009909 360906210940658907188429)
                  ·
                    rfl

theorem cell23_6325761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 5].length) (baseStart_6325761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325761 prefixEnd_6325761 := by exact prefixLift 6325761
  have htrace : WordTrace (prefixWord ++ tailWord_6325761) baseStart_6325761 baseEnd_6325761 := by
    simpa [prefixWord, tailWord_6325761, baseEnd_6325761] using wordTrace_append hprefix tailTrace_6325761
  have hstable : (prefixWord ++ tailWord_6325761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325761).length < 2 ^ (prefixWord ++ tailWord_6325761).sum := by decide
  have hdescent : baseEnd_6325761 < baseStart_6325761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325767 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 5]
def baseStart_6325767 : Nat := 118140960795 + 6325767 * 2 ^ 59
def prefixEnd_6325767 : Nat := 4983230072969 + 3 ^ 40 * 6325767 * 2
def baseEnd_6325767 : Nat := 3248158979349857141220833

theorem tailTrace_6325767 : CollatzResearch.WordTrace tailWord_6325767 prefixEnd_6325767 3248158979349857141220833 := by
  unfold tailWord_6325767
  simp only [CollatzResearch.WordTrace]
  refine ⟨230719676873833988837255555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153813117915889325891503703 230719676873833988837255555)
  ·
    refine ⟨346079515310750983255883333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230719676873833988837255555 346079515310750983255883333)
    ·
      refine ⟨64889909120765809360478125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346079515310750983255883333 64889909120765809360478125)
      ·
        refine ⟨24333715920287178510179297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64889909120765809360478125 24333715920287178510179297)
        ·
          refine ⟨18250286940215383882634473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24333715920287178510179297 18250286940215383882634473)
          ·
            refine ⟨13687715205161537911975855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18250286940215383882634473 13687715205161537911975855)
            ·
              refine ⟨20531572807742306867963783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13687715205161537911975855 20531572807742306867963783)
              ·
                refine ⟨30797359211613460301945675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20531572807742306867963783 30797359211613460301945675)
                ·
                  refine ⟨46196038817420190452918513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30797359211613460301945675 46196038817420190452918513)
                  ·
                    refine ⟨34647029113065142839688885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46196038817420190452918513 34647029113065142839688885)
                    ·
                      refine ⟨3248158979349857141220833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34647029113065142839688885 3248158979349857141220833)
                      ·
                        rfl

theorem cell23_6325767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_6325767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325767 prefixEnd_6325767 := by exact prefixLift 6325767
  have htrace : WordTrace (prefixWord ++ tailWord_6325767) baseStart_6325767 baseEnd_6325767 := by
    simpa [prefixWord, tailWord_6325767, baseEnd_6325767] using wordTrace_append hprefix tailTrace_6325767
  have hstable : (prefixWord ++ tailWord_6325767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325767).length < 2 ^ (prefixWord ++ tailWord_6325767).sum := by decide
  have hdescent : baseEnd_6325767 < baseStart_6325767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325777 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 1, 6, 2]
def baseStart_6325777 : Nat := 118140960795 + 6325777 * 2 ^ 59
def prefixEnd_6325777 : Nat := 4983230072969 + 3 ^ 40 * 6325777 * 2
def baseEnd_6325777 : Nat := 3248164114156402102095787

theorem tailTrace_6325777 : CollatzResearch.WordTrace tailWord_6325777 prefixEnd_6325777 3248164114156402102095787 := by
  unfold tailWord_6325777
  simp only [CollatzResearch.WordTrace]
  refine ⟨230720041603797760545119585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153813361069198507030079723 230720041603797760545119585)
  ·
    refine ⟨173040031202848320408839689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230720041603797760545119585 173040031202848320408839689)
    ·
      refine ⟨129780023402136240306629767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173040031202848320408839689 129780023402136240306629767)
      ·
        refine ⟨194670035103204360459944651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129780023402136240306629767 194670035103204360459944651)
        ·
          refine ⟨292005052654806540689916977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194670035103204360459944651 292005052654806540689916977)
          ·
            refine ⟨219003789491104905517437733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292005052654806540689916977 219003789491104905517437733)
            ·
              refine ⟨41063210529582169784519575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 219003789491104905517437733 41063210529582169784519575)
              ·
                refine ⟨61594815794373254676779363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41063210529582169784519575 61594815794373254676779363)
                ·
                  refine ⟨92392223691559882015169045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61594815794373254676779363 92392223691559882015169045)
                  ·
                    refine ⟨4330885485541869469461049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92392223691559882015169045 4330885485541869469461049)
                    ·
                      refine ⟨3248164114156402102095787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4330885485541869469461049 3248164114156402102095787)
                      ·
                        rfl

theorem cell23_6325777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 6, 2].length) (baseStart_6325777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325777 prefixEnd_6325777 := by exact prefixLift 6325777
  have htrace : WordTrace (prefixWord ++ tailWord_6325777) baseStart_6325777 baseEnd_6325777 := by
    simpa [prefixWord, tailWord_6325777, baseEnd_6325777] using wordTrace_append hprefix tailTrace_6325777
  have hstable : (prefixWord ++ tailWord_6325777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325777).length < 2 ^ (prefixWord ++ tailWord_6325777).sum := by decide
  have hdescent : baseEnd_6325777 < baseStart_6325777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325817 : List Nat := [1, 2, 1, 5, 1, 2, 1, 4, 6]
def baseStart_6325817 : Nat := 118140960795 + 6325817 * 2 ^ 59
def prefixEnd_6325817 : Nat := 4983230072969 + 3 ^ 40 * 6325817 * 2
def baseEnd_6325817 : Nat := 360909405931397993955067

theorem tailTrace_6325817 : CollatzResearch.WordTrace tailWord_6325817 prefixEnd_6325817 360909405931397993955067 := by
  unfold tailWord_6325817
  simp only [CollatzResearch.WordTrace]
  refine ⟨230721500523652847376575705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153814333682435231584383803 230721500523652847376575705)
  ·
    refine ⟨173041125392739635532431779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230721500523652847376575705 173041125392739635532431779)
    ·
      refine ⟨259561688089109453298647669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173041125392739635532431779 259561688089109453298647669)
      ·
        refine ⟨24333908258354011246748219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 259561688089109453298647669 24333908258354011246748219)
        ·
          refine ⟨36500862387531016870122329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24333908258354011246748219 36500862387531016870122329)
          ·
            refine ⟨27375646790648262652591747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36500862387531016870122329 27375646790648262652591747)
            ·
              refine ⟨41063470185972393978887621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27375646790648262652591747 41063470185972393978887621)
              ·
                refine ⟨7699400659869823871041429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41063470185972393978887621 7699400659869823871041429)
                ·
                  refine ⟨360909405931397993955067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7699400659869823871041429 360909405931397993955067)
                  ·
                    rfl

theorem cell23_6325817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 6].length) (baseStart_6325817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325817 prefixEnd_6325817 := by exact prefixLift 6325817
  have htrace : WordTrace (prefixWord ++ tailWord_6325817) baseStart_6325817 baseEnd_6325817 := by
    simpa [prefixWord, tailWord_6325817, baseEnd_6325817] using wordTrace_append hprefix tailTrace_6325817
  have hstable : (prefixWord ++ tailWord_6325817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325817).length < 2 ^ (prefixWord ++ tailWord_6325817).sum := by decide
  have hdescent : baseEnd_6325817 < baseStart_6325817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325840 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 7]
def baseStart_6325840 : Nat := 118140960795 + 6325840 * 2 ^ 59
def prefixEnd_6325840 : Nat := 4983230072969 + 3 ^ 40 * 6325840 * 2
def baseEnd_6325840 : Nat := 3248196463437635355607997

theorem tailTrace_6325840 : CollatzResearch.WordTrace tailWord_6325840 prefixEnd_6325840 3248196463437635355607997 := by
  unfold tailWord_6325840
  simp only [CollatzResearch.WordTrace]
  refine ⟨115361169701284761152331487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153814892935046348203108649 115361169701284761152331487)
  ·
    refine ⟨173041754551927141728497231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115361169701284761152331487 173041754551927141728497231)
    ·
      refine ⟨259562631827890712592745847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173041754551927141728497231 259562631827890712592745847)
      ·
        refine ⟨389343947741836068889118771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259562631827890712592745847 389343947741836068889118771)
        ·
          refine ⟨584015921612754103333678157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389343947741836068889118771 584015921612754103333678157)
          ·
            refine ⟨219005970604782788750129309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 584015921612754103333678157 219005970604782788750129309)
            ·
              refine ⟨82127238976793545781298491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219005970604782788750129309 82127238976793545781298491)
              ·
                refine ⟨123190858465190318671947737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82127238976793545781298491 123190858465190318671947737)
                ·
                  refine ⟨92393143848892739003960803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123190858465190318671947737 92393143848892739003960803)
                  ·
                    refine ⟨138589715773339108505941205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92393143848892739003960803 138589715773339108505941205)
                    ·
                      refine ⟨3248196463437635355607997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 138589715773339108505941205 3248196463437635355607997)
                      ·
                        rfl

theorem cell23_6325840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_6325840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325840 prefixEnd_6325840 := by exact prefixLift 6325840
  have htrace : WordTrace (prefixWord ++ tailWord_6325840) baseStart_6325840 baseEnd_6325840 := by
    simpa [prefixWord, tailWord_6325840, baseEnd_6325840] using wordTrace_append hprefix tailTrace_6325840
  have hstable : (prefixWord ++ tailWord_6325840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325840).length < 2 ^ (prefixWord ++ tailWord_6325840).sum := by decide
  have hdescent : baseEnd_6325840 < baseStart_6325840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325847 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 3, 5]
def baseStart_6325847 : Nat := 118140960795 + 6325847 * 2 ^ 59
def prefixEnd_6325847 : Nat := 4983230072969 + 3 ^ 40 * 6325847 * 2
def baseEnd_6325847 : Nat := 1082733352600738942740155

theorem tailTrace_6325847 : CollatzResearch.WordTrace tailWord_6325847 prefixEnd_6325847 1082733352600738942740155 := by
  unfold tailWord_6325847
  simp only [CollatzResearch.WordTrace]
  refine ⟨230722594713544162500167795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153815063142362775000111863 230722594713544162500167795)
  ·
    refine ⟨346083892070316243750251693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230722594713544162500167795 346083892070316243750251693)
    ·
      refine ⟨129781459526368591406344385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346083892070316243750251693 129781459526368591406344385)
      ·
        refine ⟨97336094644776443554758289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129781459526368591406344385 97336094644776443554758289)
        ·
          refine ⟨73002070983582332666068717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97336094644776443554758289 73002070983582332666068717)
          ·
            refine ⟨27375776618843374749775769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73002070983582332666068717 27375776618843374749775769)
            ·
              refine ⟨20531832464132531062331827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27375776618843374749775769 20531832464132531062331827)
              ·
                refine ⟨30797748696198796593497741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20531832464132531062331827 30797748696198796593497741)
                ·
                  refine ⟨11549155761074548722561653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30797748696198796593497741 11549155761074548722561653)
                  ·
                    refine ⟨1082733352600738942740155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11549155761074548722561653 1082733352600738942740155)
                    ·
                      rfl

theorem cell23_6325847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_6325847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325847 prefixEnd_6325847 := by exact prefixLift 6325847
  have htrace : WordTrace (prefixWord ++ tailWord_6325847) baseStart_6325847 baseEnd_6325847 := by
    simpa [prefixWord, tailWord_6325847, baseEnd_6325847] using wordTrace_append hprefix tailTrace_6325847
  have hstable : (prefixWord ++ tailWord_6325847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325847).length < 2 ^ (prefixWord ++ tailWord_6325847).sum := by decide
  have hdescent : baseEnd_6325847 < baseStart_6325847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325878 : List Nat := [5, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3]
def baseStart_6325878 : Nat := 118140960795 + 6325878 * 2 ^ 59
def prefixEnd_6325878 : Nat := 4983230072969 + 3 ^ 40 * 6325878 * 2
def baseEnd_6325878 : Nat := 3248215975702506206932823

theorem tailTrace_6325878 : CollatzResearch.WordTrace tailWord_6325878 prefixEnd_6325878 3248215975702506206932823 := by
  unfold tailWord_6325878
  simp only [CollatzResearch.WordTrace]
  refine ⟨14420232836026990924659143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153815816917621236529697525 14420232836026990924659143)
  ·
    refine ⟨21630349254040486386988715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14420232836026990924659143 21630349254040486386988715)
    ·
      refine ⟨32445523881060729580483073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21630349254040486386988715 32445523881060729580483073)
      ·
        refine ⟨24334142910795547185362305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32445523881060729580483073 24334142910795547185362305)
        ·
          refine ⟨18250607183096660389021729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24334142910795547185362305 18250607183096660389021729)
          ·
            refine ⟨13687955387322495291766297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18250607183096660389021729 13687955387322495291766297)
            ·
              refine ⟨10265966540491871468824723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13687955387322495291766297 10265966540491871468824723)
              ·
                refine ⟨15398949810737807203237085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10265966540491871468824723 15398949810737807203237085)
                ·
                  refine ⟨5774606179026677701213907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15398949810737807203237085 5774606179026677701213907)
                  ·
                    refine ⟨8661909268540016551820861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5774606179026677701213907 8661909268540016551820861)
                    ·
                      refine ⟨3248215975702506206932823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8661909268540016551820861 3248215975702506206932823)
                      ·
                        rfl

theorem cell23_6325878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_6325878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325878 prefixEnd_6325878 := by exact prefixLift 6325878
  have htrace : WordTrace (prefixWord ++ tailWord_6325878) baseStart_6325878 baseEnd_6325878 := by
    simpa [prefixWord, tailWord_6325878, baseEnd_6325878] using wordTrace_append hprefix tailTrace_6325878
  have hstable : (prefixWord ++ tailWord_6325878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325878).length < 2 ^ (prefixWord ++ tailWord_6325878).sum := by decide
  have hdescent : baseEnd_6325878 < baseStart_6325878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325921 : List Nat := [1, 2, 3, 3, 2, 1, 2, 3, 1, 2, 3]
def baseStart_6325921 : Nat := 118140960795 + 6325921 * 2 ^ 59
def prefixEnd_6325921 : Nat := 4983230072969 + 3 ^ 40 * 6325921 * 2
def baseEnd_6325921 : Nat := 3248238055370649538695125

theorem tailTrace_6325921 : CollatzResearch.WordTrace tailWord_6325921 prefixEnd_6325921 3248238055370649538695125 := by
  unfold tailWord_6325921
  simp only [CollatzResearch.WordTrace]
  refine ⟨230725293715276073138361617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153816862476850715425574411 230725293715276073138361617)
  ·
    refine ⟨173043970286457054853771213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230725293715276073138361617 173043970286457054853771213)
    ·
      refine ⟨64891488857421395570164205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173043970286457054853771213 64891488857421395570164205)
      ·
        refine ⟨24334308321533023338811577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64891488857421395570164205 24334308321533023338811577)
        ·
          refine ⟨18250731241149767504108683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24334308321533023338811577 18250731241149767504108683)
          ·
            refine ⟨27376096861724651256163025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18250731241149767504108683 27376096861724651256163025)
            ·
              refine ⟨20532072646293488442122269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27376096861724651256163025 20532072646293488442122269)
              ·
                refine ⟨7699527242360058165795851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20532072646293488442122269 7699527242360058165795851)
                ·
                  refine ⟨11549290863540087248693777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7699527242360058165795851 11549290863540087248693777)
                  ·
                    refine ⟨8661968147655065436520333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11549290863540087248693777 8661968147655065436520333)
                    ·
                      refine ⟨3248238055370649538695125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8661968147655065436520333 3248238055370649538695125)
                      ·
                        rfl

theorem cell23_6325921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_6325921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325921 prefixEnd_6325921 := by exact prefixLift 6325921
  have htrace : WordTrace (prefixWord ++ tailWord_6325921) baseStart_6325921 baseEnd_6325921 := by
    simpa [prefixWord, tailWord_6325921, baseEnd_6325921] using wordTrace_append hprefix tailTrace_6325921
  have hstable : (prefixWord ++ tailWord_6325921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325921).length < 2 ^ (prefixWord ++ tailWord_6325921).sum := by decide
  have hdescent : baseEnd_6325921 < baseStart_6325921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325935 : List Nat := [1, 1, 2, 1, 2, 4, 5, 2, 1, 2, 2]
def baseStart_6325935 : Nat := 118140960795 + 6325935 * 2 ^ 59
def prefixEnd_6325935 : Nat := 4983230072969 + 3 ^ 40 * 6325935 * 2
def baseEnd_6325935 : Nat := 3248245244099812483920061

theorem tailTrace_6325935 : CollatzResearch.WordTrace tailWord_6325935 prefixEnd_6325935 3248245244099812483920061 := by
  unfold tailWord_6325935
  simp only [CollatzResearch.WordTrace]
  refine ⟨230725804337225353529371259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153817202891483569019580839 230725804337225353529371259)
  ·
    refine ⟨346088706505838030294056889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230725804337225353529371259 346088706505838030294056889)
    ·
      refine ⟨259566529879378522720542667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346088706505838030294056889 259566529879378522720542667)
      ·
        refine ⟨389349794819067784080814001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259566529879378522720542667 389349794819067784080814001)
        ·
          refine ⟨292012346114300838060610501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389349794819067784080814001 292012346114300838060610501)
          ·
            refine ⟨54752314896431407136364469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 292012346114300838060610501 54752314896431407136364469)
            ·
              refine ⟨5133029521540444419034169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54752314896431407136364469 5133029521540444419034169)
              ·
                refine ⟨3849772141155333314275627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5133029521540444419034169 3849772141155333314275627)
                ·
                  refine ⟨5774658211732999971413441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3849772141155333314275627 5774658211732999971413441)
                  ·
                    refine ⟨4330993658799749978560081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5774658211732999971413441 4330993658799749978560081)
                    ·
                      refine ⟨3248245244099812483920061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4330993658799749978560081 3248245244099812483920061)
                      ·
                        rfl

theorem cell23_6325935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 1, 2, 2].length) (baseStart_6325935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325935 prefixEnd_6325935 := by exact prefixLift 6325935
  have htrace : WordTrace (prefixWord ++ tailWord_6325935) baseStart_6325935 baseEnd_6325935 := by
    simpa [prefixWord, tailWord_6325935, baseEnd_6325935] using wordTrace_append hprefix tailTrace_6325935
  have hstable : (prefixWord ++ tailWord_6325935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325935).length < 2 ^ (prefixWord ++ tailWord_6325935).sum := by decide
  have hdescent : baseEnd_6325935 < baseStart_6325935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325951 : List Nat := [1, 1, 2, 2, 2, 3, 3, 3, 2, 1, 3]
def baseStart_6325951 : Nat := 118140960795 + 6325951 * 2 ^ 59
def prefixEnd_6325951 : Nat := 4983230072969 + 3 ^ 40 * 6325951 * 2
def baseEnd_6325951 : Nat := 3248253459790284421319987

theorem tailTrace_6325951 : CollatzResearch.WordTrace tailWord_6325951 prefixEnd_6325951 3248253459790284421319987 := by
  unfold tailWord_6325951
  simp only [CollatzResearch.WordTrace]
  refine ⟨230726387905167388261953707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153817591936778258841302471 230726387905167388261953707)
  ·
    refine ⟨346089581857751082392930561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230726387905167388261953707 346089581857751082392930561)
    ·
      refine ⟨259567186393313311794697921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346089581857751082392930561 259567186393313311794697921)
      ·
        refine ⟨194675389794984983846023441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259567186393313311794697921 194675389794984983846023441)
        ·
          refine ⟨146006542346238737884517581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194675389794984983846023441 146006542346238737884517581)
          ·
            refine ⟨54752453379839526706694093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146006542346238737884517581 54752453379839526706694093)
            ·
              refine ⟨20532170017439822515010285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54752453379839526706694093 20532170017439822515010285)
              ·
                refine ⟨7699563756539933443128857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20532170017439822515010285 7699563756539933443128857)
                ·
                  refine ⟨5774672817404950082346643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7699563756539933443128857 5774672817404950082346643)
                  ·
                    refine ⟨8662009226107425123519965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5774672817404950082346643 8662009226107425123519965)
                    ·
                      refine ⟨3248253459790284421319987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8662009226107425123519965 3248253459790284421319987)
                      ·
                        rfl

theorem cell23_6325951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 1, 3].length) (baseStart_6325951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325951 prefixEnd_6325951 := by exact prefixLift 6325951
  have htrace : WordTrace (prefixWord ++ tailWord_6325951) baseStart_6325951 baseEnd_6325951 := by
    simpa [prefixWord, tailWord_6325951, baseEnd_6325951] using wordTrace_append hprefix tailTrace_6325951
  have hstable : (prefixWord ++ tailWord_6325951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325951).length < 2 ^ (prefixWord ++ tailWord_6325951).sum := by decide
  have hdescent : baseEnd_6325951 < baseStart_6325951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325957 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 2, 3, 4]
def baseStart_6325957 : Nat := 118140960795 + 6325957 * 2 ^ 59
def prefixEnd_6325957 : Nat := 4983230072969 + 3 ^ 40 * 6325957 * 2
def baseEnd_6325957 : Nat := 3248256540674211397844959

theorem tailTrace_6325957 : CollatzResearch.WordTrace tailWord_6325957 prefixEnd_6325957 3248256540674211397844959 := by
  unfold tailWord_6325957
  simp only [CollatzResearch.WordTrace]
  refine ⟨230726606743145651286672125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153817737828763767524448083 230726606743145651286672125)
  ·
    refine ⟨86522477528679619232502047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230726606743145651286672125 86522477528679619232502047)
    ·
      refine ⟨129783716293019428848753071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86522477528679619232502047 129783716293019428848753071)
      ·
        refine ⟨194675574439529143273129607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129783716293019428848753071 194675574439529143273129607)
        ·
          refine ⟨292013361659293714909694411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194675574439529143273129607 292013361659293714909694411)
          ·
            refine ⟨438020042488940572364541617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292013361659293714909694411 438020042488940572364541617)
            ·
              refine ⟨328515031866705429273406213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438020042488940572364541617 328515031866705429273406213)
              ·
                refine ⟨61596568475007267988763665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 328515031866705429273406213 61596568475007267988763665)
                ·
                  refine ⟨46197426356255450991572749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61596568475007267988763665 46197426356255450991572749)
                  ·
                    refine ⟨17324034883595794121839781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46197426356255450991572749 17324034883595794121839781)
                    ·
                      refine ⟨3248256540674211397844959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17324034883595794121839781 3248256540674211397844959)
                      ·
                        rfl

theorem cell23_6325957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_6325957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325957 prefixEnd_6325957 := by exact prefixLift 6325957
  have htrace : WordTrace (prefixWord ++ tailWord_6325957) baseStart_6325957 baseEnd_6325957 := by
    simpa [prefixWord, tailWord_6325957, baseEnd_6325957] using wordTrace_append hprefix tailTrace_6325957
  have hstable : (prefixWord ++ tailWord_6325957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325957).length < 2 ^ (prefixWord ++ tailWord_6325957).sum := by decide
  have hdescent : baseEnd_6325957 < baseStart_6325957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6325994 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 2, 4, 3]
def baseStart_6325994 : Nat := 118140960795 + 6325994 * 2 ^ 59
def prefixEnd_6325994 : Nat := 4983230072969 + 3 ^ 40 * 6325994 * 2
def baseEnd_6325994 : Nat := 3248275539458427753082289

theorem tailTrace_6325994 : CollatzResearch.WordTrace tailWord_6325994 prefixEnd_6325994 3248275539458427753082289 := by
  unfold tailWord_6325994
  simp only [CollatzResearch.WordTrace]
  refine ⟨57681989061002901651442259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153818637496007737737179357 57681989061002901651442259)
  ·
    refine ⟨86522983591504352477163389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57681989061002901651442259 86522983591504352477163389)
    ·
      refine ⟨32446118846814132178936271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86522983591504352477163389 32446118846814132178936271)
      ·
        refine ⟨48669178270221198268404407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32446118846814132178936271 48669178270221198268404407)
        ·
          refine ⟨73003767405331797402606611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48669178270221198268404407 73003767405331797402606611)
          ·
            refine ⟨109505651107997696103909917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73003767405331797402606611 109505651107997696103909917)
            ·
              refine ⟨41064619165499136038966219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109505651107997696103909917 41064619165499136038966219)
              ·
                refine ⟨61596928748248704058449329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41064619165499136038966219 61596928748248704058449329)
                ·
                  refine ⟨46197696561186528043836997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61596928748248704058449329 46197696561186528043836997)
                  ·
                    refine ⟨8662068105222474008219437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46197696561186528043836997 8662068105222474008219437)
                    ·
                      refine ⟨3248275539458427753082289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8662068105222474008219437 3248275539458427753082289)
                      ·
                        rfl

theorem cell23_6325994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_6325994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6325994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6325994 prefixEnd_6325994 := by exact prefixLift 6325994
  have htrace : WordTrace (prefixWord ++ tailWord_6325994) baseStart_6325994 baseEnd_6325994 := by
    simpa [prefixWord, tailWord_6325994, baseEnd_6325994] using wordTrace_append hprefix tailTrace_6325994
  have hstable : (prefixWord ++ tailWord_6325994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6325994).length < 2 ^ (prefixWord ++ tailWord_6325994).sum := by decide
  have hdescent : baseEnd_6325994 < baseStart_6325994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6325994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326024 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 1, 5, 3]
def baseStart_6326024 : Nat := 118140960795 + 6326024 * 2 ^ 59
def prefixEnd_6326024 : Nat := 4983230072969 + 3 ^ 40 * 6326024 * 2
def baseEnd_6326024 : Nat := 3248290943878062635707151

theorem tailTrace_6326024 : CollatzResearch.WordTrace tailWord_6326024 prefixEnd_6326024 3248290943878062635707151 := by
  unfold tailWord_6326024
  simp only [CollatzResearch.WordTrace]
  refine ⟨115364525216951460864680563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153819366955935281152907417 115364525216951460864680563)
  ·
    refine ⟨173046787825427191297020845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115364525216951460864680563 173046787825427191297020845)
    ·
      refine ⟨64892545434535196736382817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173046787825427191297020845 64892545434535196736382817)
      ·
        refine ⟨48669409075901397552287113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64892545434535196736382817 48669409075901397552287113)
        ·
          refine ⟨36502056806926048164215335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48669409075901397552287113 36502056806926048164215335)
          ·
            refine ⟨54753085210389072246323003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36502056806926048164215335 54753085210389072246323003)
            ·
              refine ⟨82129627815583608369484505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54753085210389072246323003 82129627815583608369484505)
              ·
                refine ⟨61597220861687706277113379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82129627815583608369484505 61597220861687706277113379)
                ·
                  refine ⟨92395831292531559415670069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61597220861687706277113379 92395831292531559415670069)
                  ·
                    refine ⟨8662109183674833695219069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92395831292531559415670069 8662109183674833695219069)
                    ·
                      refine ⟨3248290943878062635707151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8662109183674833695219069 3248290943878062635707151)
                      ·
                        rfl

theorem cell23_6326024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_6326024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326024 prefixEnd_6326024 := by exact prefixLift 6326024
  have htrace : WordTrace (prefixWord ++ tailWord_6326024) baseStart_6326024 baseEnd_6326024 := by
    simpa [prefixWord, tailWord_6326024, baseEnd_6326024] using wordTrace_append hprefix tailTrace_6326024
  have hstable : (prefixWord ++ tailWord_6326024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326024).length < 2 ^ (prefixWord ++ tailWord_6326024).sum := by decide
  have hdescent : baseEnd_6326024 < baseStart_6326024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326036 : List Nat := [2, 4, 4, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_6326036 : Nat := 118140960795 + 6326036 * 2 ^ 59
def prefixEnd_6326036 : Nat := 4983230072969 + 3 ^ 40 * 6326036 * 2
def baseEnd_6326036 : Nat := 3248297105645916588757097

theorem tailTrace_6326036 : CollatzResearch.WordTrace tailWord_6326036 prefixEnd_6326036 3248297105645916588757097 := by
  unfold tailWord_6326036
  simp only [CollatzResearch.WordTrace]
  refine ⟨115364744054929723889398981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153819658739906298519198641 115364744054929723889398981)
  ·
    refine ⟨21630889510299323229262309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115364744054929723889398981 21630889510299323229262309)
    ·
      refine ⟨4055791783181123105486683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21630889510299323229262309 4055791783181123105486683)
      ·
        refine ⟨6083687674771684658230025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4055791783181123105486683 6083687674771684658230025)
        ·
          refine ⟨4562765756078763493672519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6083687674771684658230025 4562765756078763493672519)
          ·
            refine ⟨6844148634118145240508779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4562765756078763493672519 6844148634118145240508779)
            ·
              refine ⟨10266222951177217860763169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6844148634118145240508779 10266222951177217860763169)
              ·
                refine ⟨7699667213382913395572377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10266222951177217860763169 7699667213382913395572377)
                ·
                  refine ⟨5774750410037185046679283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7699667213382913395572377 5774750410037185046679283)
                  ·
                    refine ⟨8662125615055777570018925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5774750410037185046679283 8662125615055777570018925)
                    ·
                      refine ⟨3248297105645916588757097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8662125615055777570018925 3248297105645916588757097)
                      ·
                        rfl

theorem cell23_6326036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_6326036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326036 prefixEnd_6326036 := by exact prefixLift 6326036
  have htrace : WordTrace (prefixWord ++ tailWord_6326036) baseStart_6326036 baseEnd_6326036 := by
    simpa [prefixWord, tailWord_6326036, baseEnd_6326036] using wordTrace_append hprefix tailTrace_6326036
  have hstable : (prefixWord ++ tailWord_6326036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326036).length < 2 ^ (prefixWord ++ tailWord_6326036).sum := by decide
  have hdescent : baseEnd_6326036 < baseStart_6326036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326044 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 4, 5]
def baseStart_6326044 : Nat := 118140960795 + 6326044 * 2 ^ 59
def prefixEnd_6326044 : Nat := 4983230072969 + 3 ^ 40 * 6326044 * 2
def baseEnd_6326044 : Nat := 1082767071163717519152353

theorem tailTrace_6326044 : CollatzResearch.WordTrace tailWord_6326044 prefixEnd_6326044 1082767071163717519152353 := by
  unfold tailWord_6326044
  simp only [CollatzResearch.WordTrace]
  refine ⟨115364889946915232572544593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153819853262553643430059457 115364889946915232572544593)
  ·
    refine ⟨86523667460186424429408445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115364889946915232572544593 86523667460186424429408445)
    ·
      refine ⟨32446375297569909161028167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86523667460186424429408445 32446375297569909161028167)
      ·
        refine ⟨48669562946354863741542251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32446375297569909161028167 48669562946354863741542251)
        ·
          refine ⟨73004344419532295612313377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48669562946354863741542251 73004344419532295612313377)
          ·
            refine ⟨54753258314649221709235033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73004344419532295612313377 54753258314649221709235033)
            ·
              refine ⟨41064943735986916281926275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54753258314649221709235033 41064943735986916281926275)
              ·
                refine ⟨61597415603980374422889413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41064943735986916281926275 61597415603980374422889413)
                ·
                  refine ⟨11549515425746320204291765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61597415603980374422889413 11549515425746320204291765)
                  ·
                    refine ⟨1082767071163717519152353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11549515425746320204291765 1082767071163717519152353)
                    ·
                      rfl

theorem cell23_6326044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_6326044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326044 prefixEnd_6326044 := by exact prefixLift 6326044
  have htrace : WordTrace (prefixWord ++ tailWord_6326044) baseStart_6326044 baseEnd_6326044 := by
    simpa [prefixWord, tailWord_6326044, baseEnd_6326044] using wordTrace_append hprefix tailTrace_6326044
  have hstable : (prefixWord ++ tailWord_6326044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326044).length < 2 ^ (prefixWord ++ tailWord_6326044).sum := by decide
  have hdescent : baseEnd_6326044 < baseStart_6326044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326057 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 4, 8]
def baseStart_6326057 : Nat := 118140960795 + 6326057 * 2 ^ 59
def prefixEnd_6326057 : Nat := 4983230072969 + 3 ^ 40 * 6326057 * 2
def baseEnd_6326057 : Nat := 1082769296246553668864833

theorem tailTrace_6326057 : CollatzResearch.WordTrace tailWord_6326057 prefixEnd_6326057 1082769296246553668864833 := by
  unfold tailWord_6326057
  simp only [CollatzResearch.WordTrace]
  refine ⟨230730254042783368365312425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153820169361855578910208283 230730254042783368365312425)
  ·
    refine ⟨173047690532087526273984319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230730254042783368365312425 173047690532087526273984319)
    ·
      refine ⟨259571535798131289410976479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173047690532087526273984319 259571535798131289410976479)
      ·
        refine ⟨389357303697196934116464719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259571535798131289410976479 389357303697196934116464719)
        ·
          refine ⟨584035955545795401174697079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389357303697196934116464719 584035955545795401174697079)
          ·
            refine ⟨876053933318693101762045619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 584035955545795401174697079 876053933318693101762045619)
            ·
              refine ⟨1314080899978039652643068429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 876053933318693101762045619 1314080899978039652643068429)
              ·
                refine ⟨492780337491764869741150661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1314080899978039652643068429 492780337491764869741150661)
                ·
                  refine ⟨92396313279705913076465749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 492780337491764869741150661 92396313279705913076465749)
                  ·
                    refine ⟨1082769296246553668864833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92396313279705913076465749 1082769296246553668864833)
                    ·
                      rfl

theorem cell23_6326057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 8].length) (baseStart_6326057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326057 prefixEnd_6326057 := by exact prefixLift 6326057
  have htrace : WordTrace (prefixWord ++ tailWord_6326057) baseStart_6326057 baseEnd_6326057 := by
    simpa [prefixWord, tailWord_6326057, baseEnd_6326057] using wordTrace_append hprefix tailTrace_6326057
  have hstable : (prefixWord ++ tailWord_6326057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326057).length < 2 ^ (prefixWord ++ tailWord_6326057).sum := by decide
  have hdescent : baseEnd_6326057 < baseStart_6326057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326101 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 4, 2, 3]
def baseStart_6326101 : Nat := 118140960795 + 6326101 * 2 ^ 59
def prefixEnd_6326101 : Nat := 4983230072969 + 3 ^ 40 * 6326101 * 2
def baseEnd_6326101 : Nat := 3248330481888458834444297

theorem tailTrace_6326101 : CollatzResearch.WordTrace tailWord_6326101 prefixEnd_6326101 3248330481888458834444297 := by
  unfold tailWord_6326101
  simp only [CollatzResearch.WordTrace]
  refine ⟨230731858854623963879914157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153821239236415975919942771 230731858854623963879914157)
  ·
    refine ⟨86524447070483986454967809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230731858854623963879914157 86524447070483986454967809)
    ·
      refine ⟨64893335302862989841225857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86524447070483986454967809 64893335302862989841225857)
      ·
        refine ⟨48670001477147242380919393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64893335302862989841225857 48670001477147242380919393)
        ·
          refine ⟨36502501107860431785689545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48670001477147242380919393 36502501107860431785689545)
          ·
            refine ⟨27376875830895323839267159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36502501107860431785689545 27376875830895323839267159)
            ·
              refine ⟨41065313746342985758900739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27376875830895323839267159 41065313746342985758900739)
              ·
                refine ⟨61597970619514478638351109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41065313746342985758900739 61597970619514478638351109)
                ·
                  refine ⟨11549619491158964744690833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61597970619514478638351109 11549619491158964744690833)
                  ·
                    refine ⟨8662214618369223558518125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11549619491158964744690833 8662214618369223558518125)
                    ·
                      refine ⟨3248330481888458834444297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8662214618369223558518125 3248330481888458834444297)
                      ·
                        rfl

theorem cell23_6326101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_6326101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326101 prefixEnd_6326101 := by exact prefixLift 6326101
  have htrace : WordTrace (prefixWord ++ tailWord_6326101) baseStart_6326101 baseEnd_6326101 := by
    simpa [prefixWord, tailWord_6326101, baseEnd_6326101] using wordTrace_append hprefix tailTrace_6326101
  have hstable : (prefixWord ++ tailWord_6326101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326101).length < 2 ^ (prefixWord ++ tailWord_6326101).sum := by decide
  have hdescent : baseEnd_6326101 < baseStart_6326101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326131 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 5, 1, 3]
def baseStart_6326131 : Nat := 118140960795 + 6326131 * 2 ^ 59
def prefixEnd_6326131 : Nat := 4983230072969 + 3 ^ 40 * 6326131 * 2
def baseEnd_6326131 : Nat := 3248345886308093717069159

theorem tailTrace_6326131 : CollatzResearch.WordTrace tailWord_6326131 prefixEnd_6326131 3248345886308093717069159 := by
  unfold tailWord_6326131
  simp only [CollatzResearch.WordTrace]
  refine ⟨230732953044515279003506247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153821968696343519335670831 230732953044515279003506247)
  ·
    refine ⟨346099429566772918505259371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230732953044515279003506247 346099429566772918505259371)
    ·
      refine ⟨519149144350159377757889057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346099429566772918505259371 519149144350159377757889057)
      ·
        refine ⟨389361858262619533318416793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 519149144350159377757889057 389361858262619533318416793)
        ·
          refine ⟨292021393696964649988812595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389361858262619533318416793 292021393696964649988812595)
          ·
            refine ⟨438032090545446974983218893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292021393696964649988812595 438032090545446974983218893)
            ·
              refine ⟨164262033954542615618707085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 438032090545446974983218893 164262033954542615618707085)
              ·
                refine ⟨61598262732953480857015157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164262033954542615618707085 61598262732953480857015157)
                ·
                  refine ⟨5774837131214388830345171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61598262732953480857015157 5774837131214388830345171)
                  ·
                    refine ⟨8662255696821583245517757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5774837131214388830345171 8662255696821583245517757)
                    ·
                      refine ⟨3248345886308093717069159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8662255696821583245517757 3248345886308093717069159)
                      ·
                        rfl

theorem cell23_6326131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 1, 3].length) (baseStart_6326131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326131 prefixEnd_6326131 := by exact prefixLift 6326131
  have htrace : WordTrace (prefixWord ++ tailWord_6326131) baseStart_6326131 baseEnd_6326131 := by
    simpa [prefixWord, tailWord_6326131, baseEnd_6326131] using wordTrace_append hprefix tailTrace_6326131
  have hstable : (prefixWord ++ tailWord_6326131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326131).length < 2 ^ (prefixWord ++ tailWord_6326131).sum := by decide
  have hdescent : baseEnd_6326131 < baseStart_6326131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326165 : List Nat := [1, 3, 2, 1, 1, 3, 3, 4, 1, 1, 3]
def baseStart_6326165 : Nat := 118140960795 + 6326165 * 2 ^ 59
def prefixEnd_6326165 : Nat := 4983230072969 + 3 ^ 40 * 6326165 * 2
def baseEnd_6326165 : Nat := 3248363344650346584044003

theorem tailTrace_6326165 : CollatzResearch.WordTrace tailWord_6326165 prefixEnd_6326165 3248363344650346584044003 := by
  unfold tailWord_6326165
  simp only [CollatzResearch.WordTrace]
  refine ⟨230734193126392102810243949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153822795417594735206829299 230734193126392102810243949)
  ·
    refine ⟨86525322422397038553841481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230734193126392102810243949 86525322422397038553841481)
    ·
      refine ⟨64893991816797778915381111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86525322422397038553841481 64893991816797778915381111)
      ·
        refine ⟨97340987725196668373071667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64893991816797778915381111 97340987725196668373071667)
        ·
          refine ⟨146011481587795002559607501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97340987725196668373071667 146011481587795002559607501)
          ·
            refine ⟨54754305595423125959852813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146011481587795002559607501 54754305595423125959852813)
            ·
              refine ⟨20532864598283672234944805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54754305595423125959852813 20532864598283672234944805)
              ·
                refine ⟨3849912112178188544052151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20532864598283672234944805 3849912112178188544052151)
                ·
                  refine ⟨5774868168267282816078227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3849912112178188544052151 5774868168267282816078227)
                  ·
                    refine ⟨8662302252400924224117341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5774868168267282816078227 8662302252400924224117341)
                    ·
                      refine ⟨3248363344650346584044003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8662302252400924224117341 3248363344650346584044003)
                      ·
                        rfl

theorem cell23_6326165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 1, 1, 3].length) (baseStart_6326165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326165 prefixEnd_6326165 := by exact prefixLift 6326165
  have htrace : WordTrace (prefixWord ++ tailWord_6326165) baseStart_6326165 baseEnd_6326165 := by
    simpa [prefixWord, tailWord_6326165, baseEnd_6326165] using wordTrace_append hprefix tailTrace_6326165
  have hstable : (prefixWord ++ tailWord_6326165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326165).length < 2 ^ (prefixWord ++ tailWord_6326165).sum := by decide
  have hdescent : baseEnd_6326165 < baseStart_6326165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326191 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 3]
def baseStart_6326191 : Nat := 118140960795 + 6326191 * 2 ^ 59
def prefixEnd_6326191 : Nat := 4983230072969 + 3 ^ 40 * 6326191 * 2
def baseEnd_6326191 : Nat := 3248376695147363482318883

theorem tailTrace_6326191 : CollatzResearch.WordTrace tailWord_6326191 prefixEnd_6326191 3248376695147363482318883 := by
  unfold tailWord_6326191
  simp only [CollatzResearch.WordTrace]
  refine ⟨230735141424297909250690427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153823427616198606167126951 230735141424297909250690427)
  ·
    refine ⟨346102712136446863876035641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230735141424297909250690427 346102712136446863876035641)
    ·
      refine ⟨259577034102335147907026731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346102712136446863876035641 259577034102335147907026731)
      ·
        refine ⟨389365551153502721860540097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259577034102335147907026731 389365551153502721860540097)
        ·
          refine ⟨292024163365127041395405073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389365551153502721860540097 292024163365127041395405073)
          ·
            refine ⟨219018122523845281046553805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292024163365127041395405073 219018122523845281046553805)
            ·
              refine ⟨82131795946441980392457677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219018122523845281046553805 82131795946441980392457677)
              ·
                refine ⟨30799423479915742647171629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82131795946441980392457677 30799423479915742647171629)
                ·
                  refine ⟨11549783804968403492689361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30799423479915742647171629 11549783804968403492689361)
                  ·
                    refine ⟨8662337853726302619517021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11549783804968403492689361 8662337853726302619517021)
                    ·
                      refine ⟨3248376695147363482318883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8662337853726302619517021 3248376695147363482318883)
                      ·
                        rfl

theorem cell23_6326191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 3].length) (baseStart_6326191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326191 prefixEnd_6326191 := by exact prefixLift 6326191
  have htrace : WordTrace (prefixWord ++ tailWord_6326191) baseStart_6326191 baseEnd_6326191 := by
    simpa [prefixWord, tailWord_6326191, baseEnd_6326191] using wordTrace_append hprefix tailTrace_6326191
  have hstable : (prefixWord ++ tailWord_6326191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326191).length < 2 ^ (prefixWord ++ tailWord_6326191).sum := by decide
  have hdescent : baseEnd_6326191 < baseStart_6326191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326194 : List Nat := [3, 2, 1, 1, 1, 1, 1, 13]
def baseStart_6326194 : Nat := 118140960795 + 6326194 * 2 ^ 59
def prefixEnd_6326194 : Nat := 4983230072969 + 3 ^ 40 * 6326194 * 2
def baseEnd_6326194 : Nat := 120310305021826924836347

theorem tailTrace_6326194 : CollatzResearch.WordTrace tailWord_6326194 prefixEnd_6326194 120310305021826924836347 := by
  unfold tailWord_6326194
  simp only [CollatzResearch.WordTrace]
  refine ⟨57683812710821760190762409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153823500562191360508699757 57683812710821760190762409)
  ·
    refine ⟨43262859533116320143071807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57683812710821760190762409 43262859533116320143071807)
    ·
      refine ⟨64894289299674480214607711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43262859533116320143071807 64894289299674480214607711)
      ·
        refine ⟨97341433949511720321911567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64894289299674480214607711 97341433949511720321911567)
        ·
          refine ⟨146012150924267580482867351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97341433949511720321911567 146012150924267580482867351)
          ·
            refine ⟨219018226386401370724301027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146012150924267580482867351 219018226386401370724301027)
            ·
              refine ⟨328527339579602056086451541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219018226386401370724301027 328527339579602056086451541)
              ·
                refine ⟨120310305021826924836347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 328527339579602056086451541 120310305021826924836347)
                ·
                  rfl

theorem cell23_6326194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 13].length) (baseStart_6326194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326194 prefixEnd_6326194 := by exact prefixLift 6326194
  have htrace : WordTrace (prefixWord ++ tailWord_6326194) baseStart_6326194 baseEnd_6326194 := by
    simpa [prefixWord, tailWord_6326194, baseEnd_6326194] using wordTrace_append hprefix tailTrace_6326194
  have hstable : (prefixWord ++ tailWord_6326194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326194).length < 2 ^ (prefixWord ++ tailWord_6326194).sum := by decide
  have hdescent : baseEnd_6326194 < baseStart_6326194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326201 : List Nat := [1, 2, 1, 4, 2, 1, 1, 4, 1, 2, 4]
def baseStart_6326201 : Nat := 118140960795 + 6326201 * 2 ^ 59
def prefixEnd_6326201 : Nat := 4983230072969 + 3 ^ 40 * 6326201 * 2
def baseEnd_6326201 : Nat := 3248381829953908443193837

theorem tailTrace_6326201 : CollatzResearch.WordTrace tailWord_6326201 prefixEnd_6326201 3248381829953908443193837 := by
  unfold tailWord_6326201
  simp only [CollatzResearch.WordTrace]
  refine ⟨230735506154261680958554457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153823670769507787305702971 230735506154261680958554457)
  ·
    refine ⟨173051629615696260718915843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230735506154261680958554457 173051629615696260718915843)
    ·
      refine ⟨259577444423544391078373765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173051629615696260718915843 259577444423544391078373765)
      ·
        refine ⟨48670770829414573327195081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259577444423544391078373765 48670770829414573327195081)
        ·
          refine ⟨36503078122060929995396311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48670770829414573327195081 36503078122060929995396311)
          ·
            refine ⟨54754617183091394993094467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36503078122060929995396311 54754617183091394993094467)
            ·
              refine ⟨82131925774637092489641701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54754617183091394993094467 82131925774637092489641701)
              ·
                refine ⟨15399736082744454841807819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82131925774637092489641701 15399736082744454841807819)
                ·
                  refine ⟨23099604124116682262711729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15399736082744454841807819 23099604124116682262711729)
                  ·
                    refine ⟨17324703093087511697033797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23099604124116682262711729 17324703093087511697033797)
                    ·
                      refine ⟨3248381829953908443193837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17324703093087511697033797 3248381829953908443193837)
                      ·
                        rfl

theorem cell23_6326201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_6326201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326201 prefixEnd_6326201 := by exact prefixLift 6326201
  have htrace : WordTrace (prefixWord ++ tailWord_6326201) baseStart_6326201 baseEnd_6326201 := by
    simpa [prefixWord, tailWord_6326201, baseEnd_6326201] using wordTrace_append hprefix tailTrace_6326201
  have hstable : (prefixWord ++ tailWord_6326201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326201).length < 2 ^ (prefixWord ++ tailWord_6326201).sum := by decide
  have hdescent : baseEnd_6326201 < baseStart_6326201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326205 : List Nat := [1, 4, 1, 2, 3, 1, 4, 1, 1, 1, 4]
def baseStart_6326205 : Nat := 118140960795 + 6326205 * 2 ^ 59
def prefixEnd_6326205 : Nat := 4983230072969 + 3 ^ 40 * 6326205 * 2
def baseEnd_6326205 : Nat := 3248383883876526427543819

theorem tailTrace_6326205 : CollatzResearch.WordTrace tailWord_6326205 prefixEnd_6326205 3248383883876526427543819 := by
  unfold tailWord_6326205
  simp only [CollatzResearch.WordTrace]
  refine ⟨230735652046247189641700069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153823768030831459761133379 230735652046247189641700069)
  ·
    refine ⟨43262934758671348057818763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230735652046247189641700069 43262934758671348057818763)
    ·
      refine ⟨64894402138007022086728145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43262934758671348057818763 64894402138007022086728145)
      ·
        refine ⟨48670801603505266565046109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64894402138007022086728145 48670801603505266565046109)
        ·
          refine ⟨18251550601314474961892291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48670801603505266565046109 18251550601314474961892291)
          ·
            refine ⟨27377325901971712442838437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18251550601314474961892291 27377325901971712442838437)
            ·
              refine ⟨5133248606619696083032207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27377325901971712442838437 5133248606619696083032207)
              ·
                refine ⟨7699872909929544124548311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5133248606619696083032207 7699872909929544124548311)
                ·
                  refine ⟨11549809364894316186822467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7699872909929544124548311 11549809364894316186822467)
                  ·
                    refine ⟨17324714047341474280233701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11549809364894316186822467 17324714047341474280233701)
                    ·
                      refine ⟨3248383883876526427543819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17324714047341474280233701 3248383883876526427543819)
                      ·
                        rfl

theorem cell23_6326205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_6326205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326205 prefixEnd_6326205 := by exact prefixLift 6326205
  have htrace : WordTrace (prefixWord ++ tailWord_6326205) baseStart_6326205 baseEnd_6326205 := by
    simpa [prefixWord, tailWord_6326205, baseEnd_6326205] using wordTrace_append hprefix tailTrace_6326205
  have hstable : (prefixWord ++ tailWord_6326205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326205).length < 2 ^ (prefixWord ++ tailWord_6326205).sum := by decide
  have hdescent : baseEnd_6326205 < baseStart_6326205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326208 : List Nat := [2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 3]
def baseStart_6326208 : Nat := 118140960795 + 6326208 * 2 ^ 59
def prefixEnd_6326208 : Nat := 4983230072969 + 3 ^ 40 * 6326208 * 2
def baseEnd_6326208 : Nat := 3248385424318489915806305

theorem tailTrace_6326208 : CollatzResearch.WordTrace tailWord_6326208 prefixEnd_6326208 3248385424318489915806305 := by
  unfold tailWord_6326208
  simp only [CollatzResearch.WordTrace]
  refine ⟨115367880732618160577029639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153823840976824214102706185 115367880732618160577029639)
  ·
    refine ⟨173051821098927240865544459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115367880732618160577029639 173051821098927240865544459)
    ·
      refine ⟨259577731648390861298316689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173051821098927240865544459 259577731648390861298316689)
      ·
        refine ⟨194683298736293145973737517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259577731648390861298316689 194683298736293145973737517)
        ·
          refine ⟨73006237026109929740151569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194683298736293145973737517 73006237026109929740151569)
          ·
            refine ⟨54754677769582447305113677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73006237026109929740151569 54754677769582447305113677)
            ·
              refine ⟨20533004163593417739417629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54754677769582447305113677 20533004163593417739417629)
              ·
                refine ⟨7699876561347531652281611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20533004163593417739417629 7699876561347531652281611)
                ·
                  refine ⟨11549814842021297478422417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7699876561347531652281611 11549814842021297478422417)
                  ·
                    refine ⟨8662361131515973108816813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11549814842021297478422417 8662361131515973108816813)
                    ·
                      refine ⟨3248385424318489915806305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8662361131515973108816813 3248385424318489915806305)
                      ·
                        rfl

theorem cell23_6326208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 3].length) (baseStart_6326208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326208 prefixEnd_6326208 := by exact prefixLift 6326208
  have htrace : WordTrace (prefixWord ++ tailWord_6326208) baseStart_6326208 baseEnd_6326208 := by
    simpa [prefixWord, tailWord_6326208, baseEnd_6326208] using wordTrace_append hprefix tailTrace_6326208
  have hstable : (prefixWord ++ tailWord_6326208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326208).length < 2 ^ (prefixWord ++ tailWord_6326208).sum := by decide
  have hdescent : baseEnd_6326208 < baseStart_6326208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326222 : List Nat := [4, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2]
def baseStart_6326222 : Nat := 118140960795 + 6326222 * 2 ^ 59
def prefixEnd_6326222 : Nat := 4983230072969 + 3 ^ 40 * 6326222 * 2
def baseEnd_6326222 : Nat := 3248392613047652861031241

theorem tailTrace_6326222 : CollatzResearch.WordTrace tailWord_6326222 prefixEnd_6326222 3248392613047652861031241 := by
  unfold tailWord_6326222
  simp only [CollatzResearch.WordTrace]
  refine ⟨28842034010898200193133615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153824181391457067696712613 28842034010898200193133615)
  ·
    refine ⟨43263051016347300289700423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28842034010898200193133615 43263051016347300289700423)
    ·
      refine ⟨64894576524520950434550635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43263051016347300289700423 64894576524520950434550635)
      ·
        refine ⟨97341864786781425651825953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64894576524520950434550635 97341864786781425651825953)
        ·
          refine ⟨73006398590086069238869465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97341864786781425651825953 73006398590086069238869465)
          ·
            refine ⟨54754798942564551929152099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73006398590086069238869465 54754798942564551929152099)
            ·
              refine ⟨82132198413846827893728149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54754798942564551929152099 82132198413846827893728149)
              ·
                refine ⟨3849946800649070057518507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82132198413846827893728149 3849946800649070057518507)
                ·
                  refine ⟨5774920200973605086277761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3849946800649070057518507 5774920200973605086277761)
                  ·
                    refine ⟨4331190150730203814708321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5774920200973605086277761 4331190150730203814708321)
                    ·
                      refine ⟨3248392613047652861031241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4331190150730203814708321 3248392613047652861031241)
                      ·
                        rfl

theorem cell23_6326222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2].length) (baseStart_6326222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326222 prefixEnd_6326222 := by exact prefixLift 6326222
  have htrace : WordTrace (prefixWord ++ tailWord_6326222) baseStart_6326222 baseEnd_6326222 := by
    simpa [prefixWord, tailWord_6326222, baseEnd_6326222] using wordTrace_append hprefix tailTrace_6326222
  have hstable : (prefixWord ++ tailWord_6326222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326222).length < 2 ^ (prefixWord ++ tailWord_6326222).sum := by decide
  have hdescent : baseEnd_6326222 < baseStart_6326222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326224 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 1, 9]
def baseStart_6326224 : Nat := 118140960795 + 6326224 * 2 ^ 59
def prefixEnd_6326224 : Nat := 4983230072969 + 3 ^ 40 * 6326224 * 2
def baseEnd_6326224 : Nat := 1082797880002987284402077

theorem tailTrace_6326224 : CollatzResearch.WordTrace tailWord_6326224 prefixEnd_6326224 1082797880002987284402077 := by
  unfold tailWord_6326224
  simp only [CollatzResearch.WordTrace]
  refine ⟨115368172516589177943320863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153824230022118903924427817 115368172516589177943320863)
  ·
    refine ⟨173052258774883766914981295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115368172516589177943320863 173052258774883766914981295)
    ·
      refine ⟨259578388162325650372471943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173052258774883766914981295 259578388162325650372471943)
      ·
        refine ⟨389367582243488475558707915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259578388162325650372471943 389367582243488475558707915)
        ·
          refine ⟨584051373365232713338061873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389367582243488475558707915 584051373365232713338061873)
          ·
            refine ⟨438038530023924535003546405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 584051373365232713338061873 438038530023924535003546405)
            ·
              refine ⟨82132224379485850313164951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 438038530023924535003546405 82132224379485850313164951)
              ·
                refine ⟨123198336569228775469747427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82132224379485850313164951 123198336569228775469747427)
                ·
                  refine ⟨184797504853843163204621141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123198336569228775469747427 184797504853843163204621141)
                  ·
                    refine ⟨1082797880002987284402077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 184797504853843163204621141 1082797880002987284402077)
                    ·
                      rfl

theorem cell23_6326224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 9].length) (baseStart_6326224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326224 prefixEnd_6326224 := by exact prefixLift 6326224
  have htrace : WordTrace (prefixWord ++ tailWord_6326224) baseStart_6326224 baseEnd_6326224 := by
    simpa [prefixWord, tailWord_6326224, baseEnd_6326224] using wordTrace_append hprefix tailTrace_6326224
  have hstable : (prefixWord ++ tailWord_6326224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326224).length < 2 ^ (prefixWord ++ tailWord_6326224).sum := by decide
  have hdescent : baseEnd_6326224 < baseStart_6326224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326265 : List Nat := [1, 2, 1, 3, 1, 4, 2, 3, 1, 3, 2]
def baseStart_6326265 : Nat := 118140960795 + 6326265 * 2 ^ 59
def prefixEnd_6326265 : Nat := 4983230072969 + 3 ^ 40 * 6326265 * 2
def baseEnd_6326265 : Nat := 3248414692715796192793543

theorem tailTrace_6326265 : CollatzResearch.WordTrace tailWord_6326265 prefixEnd_6326265 3248414692715796192793543 := by
  unfold tailWord_6326265
  simp only [CollatzResearch.WordTrace]
  refine ⟨230737840426029819888884249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153825226950686546592589499 230737840426029819888884249)
  ·
    refine ⟨173053380319522364916663187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230737840426029819888884249 173053380319522364916663187)
    ·
      refine ⟨259580070479283547374994781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173053380319522364916663187 259580070479283547374994781)
      ·
        refine ⟨97342526429731330265623043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259580070479283547374994781 97342526429731330265623043)
        ·
          refine ⟨146013789644596995398434565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97342526429731330265623043 146013789644596995398434565)
          ·
            refine ⟨27377585558361936637206481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146013789644596995398434565 27377585558361936637206481)
            ·
              refine ⟨20533189168771452477904861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27377585558361936637206481 20533189168771452477904861)
              ·
                refine ⟨7699945938289294679214323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20533189168771452477904861 7699945938289294679214323)
                ·
                  refine ⟨11549918907433942018821485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7699945938289294679214323 11549918907433942018821485)
                  ·
                    refine ⟨4331219590287728257058057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11549918907433942018821485 4331219590287728257058057)
                    ·
                      refine ⟨3248414692715796192793543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4331219590287728257058057 3248414692715796192793543)
                      ·
                        rfl

theorem cell23_6326265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 3, 2].length) (baseStart_6326265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326265 prefixEnd_6326265 := by exact prefixLift 6326265
  have htrace : WordTrace (prefixWord ++ tailWord_6326265) baseStart_6326265 baseEnd_6326265 := by
    simpa [prefixWord, tailWord_6326265, baseEnd_6326265] using wordTrace_append hprefix tailTrace_6326265
  have hstable : (prefixWord ++ tailWord_6326265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326265).length < 2 ^ (prefixWord ++ tailWord_6326265).sum := by decide
  have hdescent : baseEnd_6326265 < baseStart_6326265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326291 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 4]
def baseStart_6326291 : Nat := 118140960795 + 6326291 * 2 ^ 59
def prefixEnd_6326291 : Nat := 4983230072969 + 3 ^ 40 * 6326291 * 2
def baseEnd_6326291 : Nat := 3248428043212813091068423

theorem tailTrace_6326291 : CollatzResearch.WordTrace tailWord_6326291 prefixEnd_6326291 3248428043212813091068423 := by
  unfold tailWord_6326291
  simp only [CollatzResearch.WordTrace]
  refine ⟨230738788723935626329330727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153825859149290417552887151 230738788723935626329330727)
  ·
    refine ⟨346108183085903439493996091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230738788723935626329330727 346108183085903439493996091)
    ·
      refine ⟨519162274628855159240994137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346108183085903439493996091 519162274628855159240994137)
      ·
        refine ⟨389371705971641369430745603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 519162274628855159240994137 389371705971641369430745603)
        ·
          refine ⟨584057558957462054146118405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389371705971641369430745603 584057558957462054146118405)
          ·
            refine ⟨109510792304524135152397201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 584057558957462054146118405 109510792304524135152397201)
            ·
              refine ⟨82133094228393101364297901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109510792304524135152397201 82133094228393101364297901)
              ·
                refine ⟨30799910335647413011611713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82133094228393101364297901 30799910335647413011611713)
                ·
                  refine ⟨23099932751735559758708785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30799910335647413011611713 23099932751735559758708785)
                  ·
                    refine ⟨17324949563801669819031589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23099932751735559758708785 17324949563801669819031589)
                    ·
                      refine ⟨3248428043212813091068423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17324949563801669819031589 3248428043212813091068423)
                      ·
                        rfl

theorem cell23_6326291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 4].length) (baseStart_6326291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326291 prefixEnd_6326291 := by exact prefixLift 6326291
  have htrace : WordTrace (prefixWord ++ tailWord_6326291) baseStart_6326291 baseEnd_6326291 := by
    simpa [prefixWord, tailWord_6326291, baseEnd_6326291] using wordTrace_append hprefix tailTrace_6326291
  have hstable : (prefixWord ++ tailWord_6326291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326291).length < 2 ^ (prefixWord ++ tailWord_6326291).sum := by decide
  have hdescent : baseEnd_6326291 < baseStart_6326291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326329 : List Nat := [1, 2, 1, 5, 3, 1, 2, 2, 2, 2, 2]
def baseStart_6326329 : Nat := 118140960795 + 6326329 * 2 ^ 59
def prefixEnd_6326329 : Nat := 4983230072969 + 3 ^ 40 * 6326329 * 2
def baseEnd_6326329 : Nat := 3248447555477683942393249

theorem tailTrace_6326329 : CollatzResearch.WordTrace tailWord_6326329 prefixEnd_6326329 3248447555477683942393249 := by
  unfold tailWord_6326329
  simp only [CollatzResearch.WordTrace]
  refine ⟨230740174697797958819214041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153826783131865305879476027 230740174697797958819214041)
  ·
    refine ⟨173055131023348469114410531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230740174697797958819214041 173055131023348469114410531)
    ·
      refine ⟨259582696535022703671615797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173055131023348469114410531 259582696535022703671615797)
      ·
        refine ⟨24335877800158378469213981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 259582696535022703671615797 24335877800158378469213981)
        ·
          refine ⟨9125954175059391925955243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24335877800158378469213981 9125954175059391925955243)
          ·
            refine ⟨13688931262589087888932865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9125954175059391925955243 13688931262589087888932865)
            ·
              refine ⟨10266698446941815916699649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13688931262589087888932865 10266698446941815916699649)
              ·
                refine ⟨7700023835206361937524737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10266698446941815916699649 7700023835206361937524737)
                ·
                  refine ⟨5775017876404771453143553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7700023835206361937524737 5775017876404771453143553)
                  ·
                    refine ⟨4331263407303578589857665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5775017876404771453143553 4331263407303578589857665)
                    ·
                      refine ⟨3248447555477683942393249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4331263407303578589857665 3248447555477683942393249)
                      ·
                        rfl

theorem cell23_6326329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_6326329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326329 prefixEnd_6326329 := by exact prefixLift 6326329
  have htrace : WordTrace (prefixWord ++ tailWord_6326329) baseStart_6326329 baseEnd_6326329 := by
    simpa [prefixWord, tailWord_6326329, baseEnd_6326329] using wordTrace_append hprefix tailTrace_6326329
  have hstable : (prefixWord ++ tailWord_6326329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326329).length < 2 ^ (prefixWord ++ tailWord_6326329).sum := by decide
  have hdescent : baseEnd_6326329 < baseStart_6326329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326335 : List Nat := [1, 1, 2, 2, 3, 1, 6, 2, 5]
def baseStart_6326335 : Nat := 118140960795 + 6326335 * 2 ^ 59
def prefixEnd_6326335 : Nat := 4983230072969 + 3 ^ 40 * 6326335 * 2
def baseEnd_6326335 : Nat := 360938959595734546546469

theorem tailTrace_6326335 : CollatzResearch.WordTrace tailWord_6326335 prefixEnd_6326335 360938959595734546546469 := by
  unfold tailWord_6326335
  simp only [CollatzResearch.WordTrace]
  refine ⟨230740393535776221843932459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153826929023850814562621639 230740393535776221843932459)
  ·
    refine ⟨346110590303664332765898689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230740393535776221843932459 346110590303664332765898689)
    ·
      refine ⟨259582942727748249574424017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346110590303664332765898689 259582942727748249574424017)
      ·
        refine ⟨194687207045811187180818013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259582942727748249574424017 194687207045811187180818013)
        ·
          refine ⟨73007702642179195192806755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194687207045811187180818013 73007702642179195192806755)
          ·
            refine ⟨109511553963268792789210133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73007702642179195192806755 109511553963268792789210133)
            ·
              refine ⟨5133354092028224661994225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109511553963268792789210133 5133354092028224661994225)
              ·
                refine ⟨3850015569021168496495669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5133354092028224661994225 3850015569021168496495669)
                ·
                  refine ⟨360938959595734546546469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3850015569021168496495669 360938959595734546546469)
                  ·
                    rfl

theorem cell23_6326335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 5].length) (baseStart_6326335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326335 prefixEnd_6326335 := by exact prefixLift 6326335
  have htrace : WordTrace (prefixWord ++ tailWord_6326335) baseStart_6326335 baseEnd_6326335 := by
    simpa [prefixWord, tailWord_6326335, baseEnd_6326335] using wordTrace_append hprefix tailTrace_6326335
  have hstable : (prefixWord ++ tailWord_6326335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326335).length < 2 ^ (prefixWord ++ tailWord_6326335).sum := by decide
  have hdescent : baseEnd_6326335 < baseStart_6326335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326351 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 4]
def baseStart_6326351 : Nat := 118140960795 + 6326351 * 2 ^ 59
def prefixEnd_6326351 : Nat := 4983230072969 + 3 ^ 40 * 6326351 * 2
def baseEnd_6326351 : Nat := 3248458852052082856318147

theorem tailTrace_6326351 : CollatzResearch.WordTrace tailWord_6326351 prefixEnd_6326351 3248458852052082856318147 := by
  unfold tailWord_6326351
  simp only [CollatzResearch.WordTrace]
  refine ⟨230740977103718256576514907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153827318069145504384343271 230740977103718256576514907)
  ·
    refine ⟨346111465655577384864772361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230740977103718256576514907 346111465655577384864772361)
    ·
      refine ⟨259583599241683038648579271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346111465655577384864772361 259583599241683038648579271)
      ·
        refine ⟨389375398862524557972868907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259583599241683038648579271 389375398862524557972868907)
        ·
          refine ⟨584063098293786836959303361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389375398862524557972868907 584063098293786836959303361)
          ·
            refine ⟨438047323720340127719477521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 584063098293786836959303361 438047323720340127719477521)
            ·
              refine ⟨328535492790255095789608141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438047323720340127719477521 328535492790255095789608141)
              ·
                refine ⟨123200809796345660921103053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 328535492790255095789608141 123200809796345660921103053)
                ·
                  refine ⟨46200303673629622845413645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123200809796345660921103053 46200303673629622845413645)
                  ·
                    refine ⟨17325113877611108567030117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46200303673629622845413645 17325113877611108567030117)
                    ·
                      refine ⟨3248458852052082856318147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17325113877611108567030117 3248458852052082856318147)
                      ·
                        rfl

theorem cell23_6326351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 4].length) (baseStart_6326351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326351 prefixEnd_6326351 := by exact prefixLift 6326351
  have htrace : WordTrace (prefixWord ++ tailWord_6326351) baseStart_6326351 baseEnd_6326351 := by
    simpa [prefixWord, tailWord_6326351, baseEnd_6326351] using wordTrace_append hprefix tailTrace_6326351
  have hstable : (prefixWord ++ tailWord_6326351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326351).length < 2 ^ (prefixWord ++ tailWord_6326351).sum := by decide
  have hdescent : baseEnd_6326351 < baseStart_6326351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326365 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 1, 7]
def baseStart_6326365 : Nat := 118140960795 + 6326365 * 2 ^ 59
def prefixEnd_6326365 : Nat := 4983230072969 + 3 ^ 40 * 6326365 * 2
def baseEnd_6326365 : Nat := 1082822013593748600514361

theorem tailTrace_6326365 : CollatzResearch.WordTrace tailWord_6326365 prefixEnd_6326365 1082822013593748600514361 := by
  unfold tailWord_6326365
  simp only [CollatzResearch.WordTrace]
  refine ⟨230741487725667536967524549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153827658483778357978349699 230741487725667536967524549)
  ·
    refine ⟨43264028948562663181410853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230741487725667536967524549 43264028948562663181410853)
    ·
      refine ⟨8112005427855499346514535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43264028948562663181410853 8112005427855499346514535)
      ·
        refine ⟨12168008141783249019771803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8112005427855499346514535 12168008141783249019771803)
        ·
          refine ⟨18252012212674873529657705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12168008141783249019771803 18252012212674873529657705)
          ·
            refine ⟨13689009159506155147243279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18252012212674873529657705 13689009159506155147243279)
            ·
              refine ⟨20533513739259232720864919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13689009159506155147243279 20533513739259232720864919)
              ·
                refine ⟨30800270608888849081297379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20533513739259232720864919 30800270608888849081297379)
                ·
                  refine ⟨46200405913333273621946069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30800270608888849081297379 46200405913333273621946069)
                  ·
                    refine ⟨1082822013593748600514361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46200405913333273621946069 1082822013593748600514361)
                    ·
                      rfl

theorem cell23_6326365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_6326365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326365 prefixEnd_6326365 := by exact prefixLift 6326365
  have htrace : WordTrace (prefixWord ++ tailWord_6326365) baseStart_6326365 baseEnd_6326365 := by
    simpa [prefixWord, tailWord_6326365, baseEnd_6326365] using wordTrace_append hprefix tailTrace_6326365
  have hstable : (prefixWord ++ tailWord_6326365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326365).length < 2 ^ (prefixWord ++ tailWord_6326365).sum := by decide
  have hdescent : baseEnd_6326365 < baseStart_6326365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326368 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 4]
def baseStart_6326368 : Nat := 118140960795 + 6326368 * 2 ^ 59
def prefixEnd_6326368 : Nat := 4983230072969 + 3 ^ 40 * 6326368 * 2
def baseEnd_6326368 : Nat := 3248467581223209289805569

theorem tailTrace_6326368 : CollatzResearch.WordTrace tailWord_6326368 prefixEnd_6326368 3248467581223209289805569 := by
  unfold tailWord_6326368
  simp only [CollatzResearch.WordTrace]
  refine ⟨115370798572328334239941879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153827731429771112319922505 115370798572328334239941879)
  ·
    refine ⟨173056197858492501359912819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115370798572328334239941879 173056197858492501359912819)
    ·
      refine ⟨259584296787738752039869229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173056197858492501359912819 259584296787738752039869229)
      ·
        refine ⟨97344111295402032014950961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259584296787738752039869229 97344111295402032014950961)
        ·
          refine ⟨73008083471551524011213221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97344111295402032014950961 73008083471551524011213221)
          ·
            refine ⟨13689015650915910752102479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73008083471551524011213221 13689015650915910752102479)
            ·
              refine ⟨20533523476373866128153719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13689015650915910752102479 20533523476373866128153719)
              ·
                refine ⟨30800285214560799192230579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20533523476373866128153719 30800285214560799192230579)
                ·
                  refine ⟨46200427821841198788345869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30800285214560799192230579 46200427821841198788345869)
                  ·
                    refine ⟨17325160433190449545629701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46200427821841198788345869 17325160433190449545629701)
                    ·
                      refine ⟨3248467581223209289805569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17325160433190449545629701 3248467581223209289805569)
                      ·
                        rfl

theorem cell23_6326368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_6326368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326368 prefixEnd_6326368 := by exact prefixLift 6326368
  have htrace : WordTrace (prefixWord ++ tailWord_6326368) baseStart_6326368 baseEnd_6326368 := by
    simpa [prefixWord, tailWord_6326368, baseEnd_6326368] using wordTrace_append hprefix tailTrace_6326368
  have hstable : (prefixWord ++ tailWord_6326368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326368).length < 2 ^ (prefixWord ++ tailWord_6326368).sum := by decide
  have hdescent : baseEnd_6326368 < baseStart_6326368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326429 : List Nat := [1, 4, 2, 1, 1, 5, 1, 3, 1, 4]
def baseStart_6326429 : Nat := 118140960795 + 6326429 * 2 ^ 59
def prefixEnd_6326429 : Nat := 4983230072969 + 3 ^ 40 * 6326429 * 2
def baseEnd_6326429 : Nat := 1082832967847711183714263

theorem tailTrace_6326429 : CollatzResearch.WordTrace tailWord_6326429 prefixEnd_6326429 1082832967847711183714263 := by
  unfold tailWord_6326429
  simp only [CollatzResearch.WordTrace]
  refine ⟨230743821997435675897854341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153829214664957117265236227 230743821997435675897854341)
  ·
    refine ⟨43264466624519189230847689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230743821997435675897854341 43264466624519189230847689)
    ·
      refine ⟨32448349968389391923135767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43264466624519189230847689 32448349968389391923135767)
      ·
        refine ⟨48672524952584087884703651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32448349968389391923135767 48672524952584087884703651)
        ·
          refine ⟨73008787428876131827055477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48672524952584087884703651 73008787428876131827055477)
          ·
            refine ⟨6844573821457137358786451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73008787428876131827055477 6844573821457137358786451)
            ·
              refine ⟨10266860732185706038179677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6844573821457137358786451 10266860732185706038179677)
              ·
                refine ⟨3850072774569639764317379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10266860732185706038179677 3850072774569639764317379)
                ·
                  refine ⟨5775109161854459646476069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3850072774569639764317379 5775109161854459646476069)
                  ·
                    refine ⟨1082832967847711183714263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5775109161854459646476069 1082832967847711183714263)
                    ·
                      rfl

theorem cell23_6326429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_6326429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326429 prefixEnd_6326429 := by exact prefixLift 6326429
  have htrace : WordTrace (prefixWord ++ tailWord_6326429) baseStart_6326429 baseEnd_6326429 := by
    simpa [prefixWord, tailWord_6326429, baseEnd_6326429] using wordTrace_append hprefix tailTrace_6326429
  have hstable : (prefixWord ++ tailWord_6326429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326429).length < 2 ^ (prefixWord ++ tailWord_6326429).sum := by decide
  have hdescent : baseEnd_6326429 < baseStart_6326429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326446 : List Nat := [4, 1, 4, 2, 1, 2, 1, 1, 3, 4]
def baseStart_6326446 : Nat := 118140960795 + 6326446 * 2 ^ 59
def prefixEnd_6326446 : Nat := 4983230072969 + 3 ^ 40 * 6326446 * 2
def baseEnd_6326446 : Nat := 1082835877571419994876737

theorem tailTrace_6326446 : CollatzResearch.WordTrace tailWord_6326446 prefixEnd_6326446 1082835877571419994876737 := by
  unfold tailWord_6326446
  simp only [CollatzResearch.WordTrace]
  refine ⟨28843055254796760975152899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153829628025582725200815461 28843055254796760975152899)
  ·
    refine ⟨43264582882195141462729349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28843055254796760975152899 43264582882195141462729349)
    ·
      refine ⟨8112109290411589024261753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43264582882195141462729349 8112109290411589024261753)
      ·
        refine ⟨6084081967808691768196315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8112109290411589024261753 6084081967808691768196315)
        ·
          refine ⟨9126122951713037652294473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6084081967808691768196315 9126122951713037652294473)
          ·
            refine ⟨6844592213784778239220855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9126122951713037652294473 6844592213784778239220855)
            ·
              refine ⟨10266888320677167358831283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6844592213784778239220855 10266888320677167358831283)
              ·
                refine ⟨15400332481015751038246925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10266888320677167358831283 15400332481015751038246925)
                ·
                  refine ⟨5775124680380906639342597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15400332481015751038246925 5775124680380906639342597)
                  ·
                    refine ⟨1082835877571419994876737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5775124680380906639342597 1082835877571419994876737)
                    ·
                      rfl

theorem cell23_6326446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_6326446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326446 prefixEnd_6326446 := by exact prefixLift 6326446
  have htrace : WordTrace (prefixWord ++ tailWord_6326446) baseStart_6326446 baseEnd_6326446 := by
    simpa [prefixWord, tailWord_6326446, baseEnd_6326446] using wordTrace_append hprefix tailTrace_6326446
  have hstable : (prefixWord ++ tailWord_6326446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326446).length < 2 ^ (prefixWord ++ tailWord_6326446).sum := by decide
  have hdescent : baseEnd_6326446 < baseStart_6326446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326503 : List Nat := [1, 1, 5, 3, 1, 3, 2, 2, 1, 1, 3]
def baseStart_6326503 : Nat := 118140960795 + 6326503 * 2 ^ 59
def prefixEnd_6326503 : Nat := 4983230072969 + 3 ^ 40 * 6326503 * 2
def baseEnd_6326503 : Nat := 3248536901111566261617449

theorem tailTrace_6326503 : CollatzResearch.WordTrace tailWord_6326503 prefixEnd_6326503 3248536901111566261617449 := by
  unfold tailWord_6326503
  simp only [CollatzResearch.WordTrace]
  refine ⟨230746520999167586536048163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153831013999445057690698775 230746520999167586536048163)
  ·
    refine ⟨346119781498751379804072245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230746520999167586536048163 346119781498751379804072245)
    ·
      refine ⟨32448729515507941856631773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 346119781498751379804072245 32448729515507941856631773)
      ·
        refine ⟨12168273568315478196236915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32448729515507941856631773 12168273568315478196236915)
        ·
          refine ⟨18252410352473217294355373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12168273568315478196236915 18252410352473217294355373)
          ·
            refine ⟨6844653882177456485383265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18252410352473217294355373 6844653882177456485383265)
            ·
              refine ⟨5133490411633092364037449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6844653882177456485383265 5133490411633092364037449)
              ·
                refine ⟨3850117808724819273028087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5133490411633092364037449 3850117808724819273028087)
                ·
                  refine ⟨5775176713087228909542131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3850117808724819273028087 5775176713087228909542131)
                  ·
                    refine ⟨8662765069630843364313197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5775176713087228909542131 8662765069630843364313197)
                    ·
                      refine ⟨3248536901111566261617449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8662765069630843364313197 3248536901111566261617449)
                      ·
                        rfl

theorem cell23_6326503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_6326503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326503 prefixEnd_6326503 := by exact prefixLift 6326503
  have htrace : WordTrace (prefixWord ++ tailWord_6326503) baseStart_6326503 baseEnd_6326503 := by
    simpa [prefixWord, tailWord_6326503, baseEnd_6326503] using wordTrace_append hprefix tailTrace_6326503
  have hstable : (prefixWord ++ tailWord_6326503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326503).length < 2 ^ (prefixWord ++ tailWord_6326503).sum := by decide
  have hdescent : baseEnd_6326503 < baseStart_6326503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326532 : List Nat := [2, 3, 2, 2, 3, 1, 3, 7]
def baseStart_6326532 : Nat := 118140960795 + 6326532 * 2 ^ 59
def prefixEnd_6326532 : Nat := 4983230072969 + 3 ^ 40 * 6326532 * 2
def baseEnd_6326532 : Nat := 120316733038909135116845

theorem tailTrace_6326532 : CollatzResearch.WordTrace tailWord_6326532 prefixEnd_6326532 120316733038909135116845 := by
  unfold tailWord_6326532
  simp only [CollatzResearch.WordTrace]
  refine ⟨115373789358031262244426925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153831719144041682992569233 115373789358031262244426925)
  ·
    refine ⟨43265171009261723341660097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115373789358031262244426925 43265171009261723341660097)
    ·
      refine ⟨32448878256946292506245073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43265171009261723341660097 32448878256946292506245073)
      ·
        refine ⟨24336658692709719379683805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32448878256946292506245073 24336658692709719379683805)
        ·
          refine ⟨9126247009766144767381427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24336658692709719379683805 9126247009766144767381427)
          ·
            refine ⟨13689370514649217151072141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9126247009766144767381427 13689370514649217151072141)
            ·
              refine ⟨5133513942993456431652053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13689370514649217151072141 5133513942993456431652053)
              ·
                refine ⟨120316733038909135116845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5133513942993456431652053 120316733038909135116845)
                ·
                  rfl

theorem cell23_6326532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 7].length) (baseStart_6326532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326532 prefixEnd_6326532 := by exact prefixLift 6326532
  have htrace : WordTrace (prefixWord ++ tailWord_6326532) baseStart_6326532 baseEnd_6326532 := by
    simpa [prefixWord, tailWord_6326532, baseEnd_6326532] using wordTrace_append hprefix tailTrace_6326532
  have hstable : (prefixWord ++ tailWord_6326532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326532).length < 2 ^ (prefixWord ++ tailWord_6326532).sum := by decide
  have hdescent : baseEnd_6326532 < baseStart_6326532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326542 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3]
def baseStart_6326542 : Nat := 118140960795 + 6326542 * 2 ^ 59
def prefixEnd_6326542 : Nat := 4983230072969 + 3 ^ 40 * 6326542 * 2
def baseEnd_6326542 : Nat := 3248556926857091609029769

theorem tailTrace_6326542 : CollatzResearch.WordTrace tailWord_6326542 prefixEnd_6326542 3248556926857091609029769 := by
  unfold tailWord_6326542
  simp only [CollatzResearch.WordTrace]
  refine ⟨28843492930753287024589735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153831962297350864131145253 28843492930753287024589735)
  ·
    refine ⟨43265239396129930536884603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28843492930753287024589735 43265239396129930536884603)
    ·
      refine ⟨64897859094194895805326905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43265239396129930536884603 64897859094194895805326905)
      ·
        refine ⟨48673394320646171853995179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64897859094194895805326905 48673394320646171853995179)
        ·
          refine ⟨73010091480969257780992769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48673394320646171853995179 73010091480969257780992769)
          ·
            refine ⟨54757568610726943335744577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73010091480969257780992769 54757568610726943335744577)
            ·
              refine ⟨41068176458045207501808433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54757568610726943335744577 41068176458045207501808433)
              ·
                refine ⟨30801132343533905626356325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41068176458045207501808433 30801132343533905626356325)
                ·
                  refine ⟨5775212314412607304941811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30801132343533905626356325 5775212314412607304941811)
                  ·
                    refine ⟨8662818471618910957412717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5775212314412607304941811 8662818471618910957412717)
                    ·
                      refine ⟨3248556926857091609029769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8662818471618910957412717 3248556926857091609029769)
                      ·
                        rfl

theorem cell23_6326542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_6326542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326542 prefixEnd_6326542 := by exact prefixLift 6326542
  have htrace : WordTrace (prefixWord ++ tailWord_6326542) baseStart_6326542 baseEnd_6326542 := by
    simpa [prefixWord, tailWord_6326542, baseEnd_6326542] using wordTrace_append hprefix tailTrace_6326542
  have hstable : (prefixWord ++ tailWord_6326542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326542).length < 2 ^ (prefixWord ++ tailWord_6326542).sum := by decide
  have hdescent : baseEnd_6326542 < baseStart_6326542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326559 : List Nat := [1, 1, 2, 4, 3, 1, 3, 2, 2, 1, 3]
def baseStart_6326559 : Nat := 118140960795 + 6326559 * 2 ^ 59
def prefixEnd_6326559 : Nat := 4983230072969 + 3 ^ 40 * 6326559 * 2
def baseEnd_6326559 : Nat := 3248565656028218042517191

theorem tailTrace_6326559 : CollatzResearch.WordTrace tailWord_6326559 prefixEnd_6326559 3248565656028218042517191 := by
  unfold tailWord_6326559
  simp only [CollatzResearch.WordTrace]
  refine ⟨230748563486964708100086731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153832375657976472066724487 230748563486964708100086731)
  ·
    refine ⟨346122845230447062150130097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230748563486964708100086731 346122845230447062150130097)
    ·
      refine ⟨259592133922835296612597573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346122845230447062150130097 259592133922835296612597573)
      ·
        refine ⟨48673525110531618114862045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259592133922835296612597573 48673525110531618114862045)
        ·
          refine ⟨18252571916449356793073267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48673525110531618114862045 18252571916449356793073267)
          ·
            refine ⟨27378857874674035189609901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18252571916449356793073267 27378857874674035189609901)
            ·
              refine ⟨10267071703002763196103713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27378857874674035189609901 10267071703002763196103713)
              ·
                refine ⟨7700303777252072397077785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10267071703002763196103713 7700303777252072397077785)
                ·
                  refine ⟨5775227832939054297808339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7700303777252072397077785 5775227832939054297808339)
                  ·
                    refine ⟨8662841749408581446712509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5775227832939054297808339 8662841749408581446712509)
                    ·
                      refine ⟨3248565656028218042517191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8662841749408581446712509 3248565656028218042517191)
                      ·
                        rfl

theorem cell23_6326559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_6326559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326559 prefixEnd_6326559 := by exact prefixLift 6326559
  have htrace : WordTrace (prefixWord ++ tailWord_6326559) baseStart_6326559 baseEnd_6326559 := by
    simpa [prefixWord, tailWord_6326559, baseEnd_6326559] using wordTrace_append hprefix tailTrace_6326559
  have hstable : (prefixWord ++ tailWord_6326559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326559).length < 2 ^ (prefixWord ++ tailWord_6326559).sum := by decide
  have hdescent : baseEnd_6326559 < baseStart_6326559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326655 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 4]
def baseStart_6326655 : Nat := 118140960795 + 6326655 * 2 ^ 59
def prefixEnd_6326655 : Nat := 4983230072969 + 3 ^ 40 * 6326655 * 2
def baseEnd_6326655 : Nat := 3248614950171049666916749

theorem tailTrace_6326655 : CollatzResearch.WordTrace tailWord_6326655 prefixEnd_6326655 3248614950171049666916749 := by
  unfold tailWord_6326655
  simp only [CollatzResearch.WordTrace]
  refine ⟨230752064894616916495581419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153834709929744610997054279 230752064894616916495581419)
  ·
    refine ⟨346128097341925374743372129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230752064894616916495581419 346128097341925374743372129)
    ·
      refine ⟨259596073006444031057529097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346128097341925374743372129 259596073006444031057529097)
      ·
        refine ⟨194697054754833023293146823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259596073006444031057529097 194697054754833023293146823)
        ·
          refine ⟨292045582132249534939720235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194697054754833023293146823 292045582132249534939720235)
          ·
            refine ⟨438068373198374302409580353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292045582132249534939720235 438068373198374302409580353)
            ·
              refine ⟨328551279898780726807185265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438068373198374302409580353 328551279898780726807185265)
              ·
                refine ⟨246413459924085545105388949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328551279898780726807185265 246413459924085545105388949)
                ·
                  refine ⟨11550630933941509926815107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 246413459924085545105388949 11550630933941509926815107)
                  ·
                    refine ⟨17325946400912264890222661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11550630933941509926815107 17325946400912264890222661)
                    ·
                      refine ⟨3248614950171049666916749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17325946400912264890222661 3248614950171049666916749)
                      ·
                        rfl

theorem cell23_6326655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_6326655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326655 prefixEnd_6326655 := by exact prefixLift 6326655
  have htrace : WordTrace (prefixWord ++ tailWord_6326655) baseStart_6326655 baseEnd_6326655 := by
    simpa [prefixWord, tailWord_6326655, baseEnd_6326655] using wordTrace_append hprefix tailTrace_6326655
  have hstable : (prefixWord ++ tailWord_6326655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326655).length < 2 ^ (prefixWord ++ tailWord_6326655).sum := by decide
  have hdescent : baseEnd_6326655 < baseStart_6326655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326692 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 4, 2, 3]
def baseStart_6326692 : Nat := 118140960795 + 6326692 * 2 ^ 59
def prefixEnd_6326692 : Nat := 4983230072969 + 3 ^ 40 * 6326692 * 2
def baseEnd_6326692 : Nat := 3248633948955266022154079

theorem tailTrace_6326692 : CollatzResearch.WordTrace tailWord_6326692 prefixEnd_6326692 3248633948955266022154079 := by
  unfold tailWord_6326692
  simp only [CollatzResearch.WordTrace]
  refine ⟨115376707197741435907339165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153835609596988581209785553 115376707197741435907339165)
  ·
    refine ⟨43266265199153038465252187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115376707197741435907339165 43266265199153038465252187)
    ·
      refine ⟨64899397798729557697878281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43266265199153038465252187 64899397798729557697878281)
      ·
        refine ⟨48674548349047168273408711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64899397798729557697878281 48674548349047168273408711)
        ·
          refine ⟨73011822523570752410113067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48674548349047168273408711 73011822523570752410113067)
          ·
            refine ⟨109517733785356128615169601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73011822523570752410113067 109517733785356128615169601)
            ·
              refine ⟨82138300339017096461377201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109517733785356128615169601 82138300339017096461377201)
              ·
                refine ⟨61603725254262822346032901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82138300339017096461377201 61603725254262822346032901)
                ·
                  refine ⟨11550698485174279189881169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61603725254262822346032901 11550698485174279189881169)
                  ·
                    refine ⟨8663023863880709392410877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11550698485174279189881169 8663023863880709392410877)
                    ·
                      refine ⟨3248633948955266022154079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8663023863880709392410877 3248633948955266022154079)
                      ·
                        rfl

theorem cell23_6326692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_6326692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326692 prefixEnd_6326692 := by exact prefixLift 6326692
  have htrace : WordTrace (prefixWord ++ tailWord_6326692) baseStart_6326692 baseEnd_6326692 := by
    simpa [prefixWord, tailWord_6326692, baseEnd_6326692] using wordTrace_append hprefix tailTrace_6326692
  have hstable : (prefixWord ++ tailWord_6326692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326692).length < 2 ^ (prefixWord ++ tailWord_6326692).sum := by decide
  have hdescent : baseEnd_6326692 < baseStart_6326692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326709 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 1, 4, 3]
def baseStart_6326709 : Nat := 118140960795 + 6326709 * 2 ^ 59
def prefixEnd_6326709 : Nat := 4983230072969 + 3 ^ 40 * 6326709 * 2
def baseEnd_6326709 : Nat := 3248642678126392455641501

theorem tailTrace_6326709 : CollatzResearch.WordTrace tailWord_6326709 prefixEnd_6326709 3248642678126392455641501 := by
  unfold tailWord_6326709
  simp only [CollatzResearch.WordTrace]
  refine ⟨230754034436421283718047181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153836022957614189145364787 230754034436421283718047181)
  ·
    refine ⟨86532762913657981394267693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230754034436421283718047181 86532762913657981394267693)
    ·
      refine ⟨32449786092621743022850385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86532762913657981394267693 32449786092621743022850385)
      ·
        refine ⟨24337339569466307267137789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32449786092621743022850385 24337339569466307267137789)
        ·
          refine ⟨9126502338549865225176671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24337339569466307267137789 9126502338549865225176671)
          ·
            refine ⟨13689753507824797837765007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9126502338549865225176671 13689753507824797837765007)
            ·
              refine ⟨20534630261737196756647511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13689753507824797837765007 20534630261737196756647511)
              ·
                refine ⟨30801945392605795134971267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20534630261737196756647511 30801945392605795134971267)
                ·
                  refine ⟨46202918088908692702456901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30801945392605795134971267 46202918088908692702456901)
                  ·
                    refine ⟨8663047141670379881710669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46202918088908692702456901 8663047141670379881710669)
                    ·
                      refine ⟨3248642678126392455641501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8663047141670379881710669 3248642678126392455641501)
                      ·
                        rfl

theorem cell23_6326709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_6326709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326709 prefixEnd_6326709 := by exact prefixLift 6326709
  have htrace : WordTrace (prefixWord ++ tailWord_6326709) baseStart_6326709 baseEnd_6326709 := by
    simpa [prefixWord, tailWord_6326709, baseEnd_6326709] using wordTrace_append hprefix tailTrace_6326709
  have hstable : (prefixWord ++ tailWord_6326709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326709).length < 2 ^ (prefixWord ++ tailWord_6326709).sum := by decide
  have hdescent : baseEnd_6326709 < baseStart_6326709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326716 : List Nat := [2, 2, 2, 4, 1, 1, 1, 5, 1, 4]
def baseStart_6326716 : Nat := 118140960795 + 6326716 * 2 ^ 59
def prefixEnd_6326716 : Nat := 4983230072969 + 3 ^ 40 * 6326716 * 2
def baseEnd_6326716 : Nat := 1082882090830324642751323

theorem tailTrace_6326716 : CollatzResearch.WordTrace tailWord_6326716 prefixEnd_6326716 1082882090830324642751323 := by
  unfold tailWord_6326716
  simp only [CollatzResearch.WordTrace]
  refine ⟨115377144873697961956776001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153836193164930615942368001 115377144873697961956776001)
  ·
    refine ⟨86532858655273471467582001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115377144873697961956776001 86532858655273471467582001)
    ·
      refine ⟨64899643991455103600686501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86532858655273471467582001 64899643991455103600686501)
      ·
        refine ⟨12168683248397831925128719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64899643991455103600686501 12168683248397831925128719)
        ·
          refine ⟨18253024872596747887693079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12168683248397831925128719 18253024872596747887693079)
          ·
            refine ⟨27379537308895121831539619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18253024872596747887693079 27379537308895121831539619)
            ·
              refine ⟨41069305963342682747309429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27379537308895121831539619 41069305963342682747309429)
              ·
                refine ⟨3850247434063376507560259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41069305963342682747309429 3850247434063376507560259)
                ·
                  refine ⟨5775371151095064761340389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3850247434063376507560259 5775371151095064761340389)
                  ·
                    refine ⟨1082882090830324642751323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5775371151095064761340389 1082882090830324642751323)
                    ·
                      rfl

theorem cell23_6326716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_6326716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326716 prefixEnd_6326716 := by exact prefixLift 6326716
  have htrace : WordTrace (prefixWord ++ tailWord_6326716) baseStart_6326716 baseEnd_6326716 := by
    simpa [prefixWord, tailWord_6326716, baseEnd_6326716] using wordTrace_append hprefix tailTrace_6326716
  have hstable : (prefixWord ++ tailWord_6326716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326716).length < 2 ^ (prefixWord ++ tailWord_6326716).sum := by decide
  have hdescent : baseEnd_6326716 < baseStart_6326716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326749 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 3, 5, 2]
def baseStart_6326749 : Nat := 118140960795 + 6326749 * 2 ^ 59
def prefixEnd_6326749 : Nat := 4983230072969 + 3 ^ 40 * 6326749 * 2
def baseEnd_6326749 : Nat := 3248663217352572299141317

theorem tailTrace_6326749 : CollatzResearch.WordTrace tailWord_6326749 prefixEnd_6326749 3248663217352572299141317 := by
  unfold tailWord_6326749
  simp only [CollatzResearch.WordTrace]
  refine ⟨230755493356276370549503301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153836995570850913699668867 230755493356276370549503301)
  ·
    refine ⟨43266655004301819478031869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230755493356276370549503301 43266655004301819478031869)
    ·
      refine ⟨16224995626613182304261951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43266655004301819478031869 16224995626613182304261951)
      ·
        refine ⟨24337493439919773456392927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16224995626613182304261951 24337493439919773456392927)
        ·
          refine ⟨36506240159879660184589391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24337493439919773456392927 36506240159879660184589391)
          ·
            refine ⟨54759360239819490276884087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36506240159879660184589391 54759360239819490276884087)
            ·
              refine ⟨82139040359729235415326131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54759360239819490276884087 82139040359729235415326131)
              ·
                refine ⟨123208560539593853122989197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82139040359729235415326131 123208560539593853122989197)
                ·
                  refine ⟨46203210202347694921120949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123208560539593853122989197 46203210202347694921120949)
                  ·
                    refine ⟨4331550956470096398855089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46203210202347694921120949 4331550956470096398855089)
                    ·
                      refine ⟨3248663217352572299141317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4331550956470096398855089 3248663217352572299141317)
                      ·
                        rfl

theorem cell23_6326749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_6326749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326749 prefixEnd_6326749 := by exact prefixLift 6326749
  have htrace : WordTrace (prefixWord ++ tailWord_6326749) baseStart_6326749 baseEnd_6326749 := by
    simpa [prefixWord, tailWord_6326749, baseEnd_6326749] using wordTrace_append hprefix tailTrace_6326749
  have hstable : (prefixWord ++ tailWord_6326749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326749).length < 2 ^ (prefixWord ++ tailWord_6326749).sum := by decide
  have hdescent : baseEnd_6326749 < baseStart_6326749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326759 : List Nat := [1, 1, 5, 2, 1, 1, 4, 2, 1, 5]
def baseStart_6326759 : Nat := 118140960795 + 6326759 * 2 ^ 59
def prefixEnd_6326759 : Nat := 4983230072969 + 3 ^ 40 * 6326759 * 2
def baseEnd_6326759 : Nat := 1082889450719705753338757

theorem tailTrace_6326759 : CollatzResearch.WordTrace tailWord_6326759 prefixEnd_6326759 1082889450719705753338757 := by
  unfold tailWord_6326759
  simp only [CollatzResearch.WordTrace]
  refine ⟨230755858086240142257367331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153837238724160094838244887 230755858086240142257367331)
  ·
    refine ⟨346133787129360213386050997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230755858086240142257367331 346133787129360213386050997)
    ·
      refine ⟨32450042543377520004942281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 346133787129360213386050997 32450042543377520004942281)
      ·
        refine ⟨24337531907533140003706711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32450042543377520004942281 24337531907533140003706711)
        ·
          refine ⟨36506297861299710005560067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24337531907533140003706711 36506297861299710005560067)
          ·
            refine ⟨54759446791949565008340101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36506297861299710005560067 54759446791949565008340101)
            ·
              refine ⟨10267396273490543439063769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54759446791949565008340101 10267396273490543439063769)
              ·
                refine ⟨7700547205117907579297827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10267396273490543439063769 7700547205117907579297827)
                ·
                  refine ⟨11550820807676861368946741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7700547205117907579297827 11550820807676861368946741)
                  ·
                    refine ⟨1082889450719705753338757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11550820807676861368946741 1082889450719705753338757)
                    ·
                      rfl

theorem cell23_6326759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_6326759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326759 prefixEnd_6326759 := by exact prefixLift 6326759
  have htrace : WordTrace (prefixWord ++ tailWord_6326759) baseStart_6326759 baseEnd_6326759 := by
    simpa [prefixWord, tailWord_6326759, baseEnd_6326759] using wordTrace_append hprefix tailTrace_6326759
  have hstable : (prefixWord ++ tailWord_6326759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326759).length < 2 ^ (prefixWord ++ tailWord_6326759).sum := by decide
  have hdescent : baseEnd_6326759 < baseStart_6326759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326816 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 3]
def baseStart_6326816 : Nat := 118140960795 + 6326816 * 2 ^ 59
def prefixEnd_6326816 : Nat := 4983230072969 + 3 ^ 40 * 6326816 * 2
def baseEnd_6326816 : Nat := 3248697620556423537003509

theorem tailTrace_6326816 : CollatzResearch.WordTrace tailWord_6326816 prefixEnd_6326816 3248697620556423537003509 := by
  unfold tailWord_6326816
  simp only [CollatzResearch.WordTrace]
  refine ⟨115378968523516820496096151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153838624698022427328128201 115378968523516820496096151)
  ·
    refine ⟨173068452785275230744144227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115378968523516820496096151 173068452785275230744144227)
    ·
      refine ⟨259602679177912846116216341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173068452785275230744144227 259602679177912846116216341)
      ·
        refine ⟨12168875586464664661697641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 259602679177912846116216341 12168875586464664661697641)
        ·
          refine ⟨9126656689848498496273231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12168875586464664661697641 9126656689848498496273231)
          ·
            refine ⟨13689985034772747744409847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9126656689848498496273231 13689985034772747744409847)
            ·
              refine ⟨20534977552159121616614771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13689985034772747744409847 20534977552159121616614771)
              ·
                refine ⟨30802466328238682424922157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20534977552159121616614771 30802466328238682424922157)
                ·
                  refine ⟨11550924873089505909345809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30802466328238682424922157 11550924873089505909345809)
                  ·
                    refine ⟨8663193654817129432009357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11550924873089505909345809 8663193654817129432009357)
                    ·
                      refine ⟨3248697620556423537003509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8663193654817129432009357 3248697620556423537003509)
                      ·
                        rfl

theorem cell23_6326816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_6326816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326816 prefixEnd_6326816 := by exact prefixLift 6326816
  have htrace : WordTrace (prefixWord ++ tailWord_6326816) baseStart_6326816 baseEnd_6326816 := by
    simpa [prefixWord, tailWord_6326816, baseEnd_6326816] using wordTrace_append hprefix tailTrace_6326816
  have hstable : (prefixWord ++ tailWord_6326816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326816).length < 2 ^ (prefixWord ++ tailWord_6326816).sum := by decide
  have hdescent : baseEnd_6326816 < baseStart_6326816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326836 : List Nat := [2, 5, 1, 3, 2, 10]
def baseStart_6326836 : Nat := 118140960795 + 6326836 * 2 ^ 59
def prefixEnd_6326836 : Nat := 4983230072969 + 3 ^ 40 * 6326836 * 2
def baseEnd_6326836 : Nat := 13369168272302524521619

theorem tailTrace_6326836 : CollatzResearch.WordTrace tailWord_6326836 prefixEnd_6326836 13369168272302524521619 := by
  unfold tailWord_6326836
  simp only [CollatzResearch.WordTrace]
  refine ⟨115379333253480592203960181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153839111004640789605280241 115379333253480592203960181)
  ·
    refine ⟨10816812492513805519121267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115379333253480592203960181 10816812492513805519121267)
    ·
      refine ⟨16225218738770708278681901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10816812492513805519121267 16225218738770708278681901)
      ·
        refine ⟨6084457027039015604505713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16225218738770708278681901 6084457027039015604505713)
        ·
          refine ⟨4563342770279261703379285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6084457027039015604505713 4563342770279261703379285)
          ·
            refine ⟨13369168272302524521619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4563342770279261703379285 13369168272302524521619)
            ·
              rfl

theorem cell23_6326836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 10].length) (baseStart_6326836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326836 prefixEnd_6326836 := by exact prefixLift 6326836
  have htrace : WordTrace (prefixWord ++ tailWord_6326836) baseStart_6326836 baseEnd_6326836 := by
    simpa [prefixWord, tailWord_6326836, baseEnd_6326836] using wordTrace_append hprefix tailTrace_6326836
  have hstable : (prefixWord ++ tailWord_6326836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326836).length < 2 ^ (prefixWord ++ tailWord_6326836).sum := by decide
  have hdescent : baseEnd_6326836 < baseStart_6326836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326862 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 1, 8]
def baseStart_6326862 : Nat := 118140960795 + 6326862 * 2 ^ 59
def prefixEnd_6326862 : Nat := 4983230072969 + 3 ^ 40 * 6326862 * 2
def baseEnd_6326862 : Nat := 1082907080222176785676099

theorem tailTrace_6326862 : CollatzResearch.WordTrace tailWord_6326862 prefixEnd_6326862 1082907080222176785676099 := by
  unfold tailWord_6326862
  simp only [CollatzResearch.WordTrace]
  refine ⟨28844951850608373856045855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153839743203244660565577893 28844951850608373856045855)
  ·
    refine ⟨43267427775912560784068783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28844951850608373856045855 43267427775912560784068783)
    ·
      refine ⟨64901141663868841176103175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43267427775912560784068783 64901141663868841176103175)
      ·
        refine ⟨97351712495803261764154763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64901141663868841176103175 97351712495803261764154763)
        ·
          refine ⟨146027568743704892646232145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97351712495803261764154763 146027568743704892646232145)
          ·
            refine ⟨109520676557778669484674109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146027568743704892646232145 109520676557778669484674109)
            ·
              refine ⟨41070253709167001056752791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109520676557778669484674109 41070253709167001056752791)
              ·
                refine ⟨61605380563750501585129187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41070253709167001056752791 61605380563750501585129187)
                ·
                  refine ⟨92408070845625752377693781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61605380563750501585129187 92408070845625752377693781)
                  ·
                    refine ⟨1082907080222176785676099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92408070845625752377693781 1082907080222176785676099)
                    ·
                      rfl

theorem cell23_6326862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_6326862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326862 prefixEnd_6326862 := by exact prefixLift 6326862
  have htrace : WordTrace (prefixWord ++ tailWord_6326862) baseStart_6326862 baseEnd_6326862 := by
    simpa [prefixWord, tailWord_6326862, baseEnd_6326862] using wordTrace_append hprefix tailTrace_6326862
  have hstable : (prefixWord ++ tailWord_6326862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326862).length < 2 ^ (prefixWord ++ tailWord_6326862).sum := by decide
  have hdescent : baseEnd_6326862 < baseStart_6326862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326872 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 4, 1, 5]
def baseStart_6326872 : Nat := 118140960795 + 6326872 * 2 ^ 59
def prefixEnd_6326872 : Nat := 4983230072969 + 3 ^ 40 * 6326872 * 2
def baseEnd_6326872 : Nat := 3248726375473075317903251

theorem tailTrace_6326872 : CollatzResearch.WordTrace tailWord_6326872 prefixEnd_6326872 3248726375473075317903251 := by
  unfold tailWord_6326872
  simp only [CollatzResearch.WordTrace]
  refine ⟨115379989767415381278115435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153839986356553841704153913 115379989767415381278115435)
  ·
    refine ⟨173069984651123071917173153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115379989767415381278115435 173069984651123071917173153)
    ·
      refine ⟨129802488488342303937879865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173069984651123071917173153 129802488488342303937879865)
      ·
        refine ⟨97351866366256727953409899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129802488488342303937879865 97351866366256727953409899)
        ·
          refine ⟨146027799549385091930114849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97351866366256727953409899 146027799549385091930114849)
          ·
            refine ⟨109520849662038818947586137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146027799549385091930114849 109520849662038818947586137)
            ·
              refine ⟨82140637246529114210689603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109520849662038818947586137 82140637246529114210689603)
              ·
                refine ⟨123210955869793671316034405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82140637246529114210689603 123210955869793671316034405)
                ·
                  refine ⟨23102054225586313371756451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123210955869793671316034405 23102054225586313371756451)
                  ·
                    refine ⟨34653081338379470057634677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23102054225586313371756451 34653081338379470057634677)
                    ·
                      refine ⟨3248726375473075317903251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34653081338379470057634677 3248726375473075317903251)
                      ·
                        rfl

theorem cell23_6326872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_6326872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326872 prefixEnd_6326872 := by exact prefixLift 6326872
  have htrace : WordTrace (prefixWord ++ tailWord_6326872) baseStart_6326872 baseEnd_6326872 := by
    simpa [prefixWord, tailWord_6326872, baseEnd_6326872] using wordTrace_append hprefix tailTrace_6326872
  have hstable : (prefixWord ++ tailWord_6326872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326872).length < 2 ^ (prefixWord ++ tailWord_6326872).sum := by decide
  have hdescent : baseEnd_6326872 < baseStart_6326872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326903 : List Nat := [1, 1, 3, 1, 1, 3, 5, 2, 2, 2, 2]
def baseStart_6326903 : Nat := 118140960795 + 6326903 * 2 ^ 59
def prefixEnd_6326903 : Nat := 4983230072969 + 3 ^ 40 * 6326903 * 2
def baseEnd_6326903 : Nat := 3248742293373364696615609

theorem tailTrace_6326903 : CollatzResearch.WordTrace tailWord_6326903 prefixEnd_6326903 3248742293373364696615609 := by
  unfold tailWord_6326903
  simp only [CollatzResearch.WordTrace]
  refine ⟨230761110197718454850609363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153840740131812303233739575 230761110197718454850609363)
  ·
    refine ⟨346141665296577682275914045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230761110197718454850609363 346141665296577682275914045)
    ·
      refine ⟨129803124486216630853467767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346141665296577682275914045 129803124486216630853467767)
      ·
        refine ⟨194704686729324946280201651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129803124486216630853467767 194704686729324946280201651)
        ·
          refine ⟨292057030093987419420302477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194704686729324946280201651 292057030093987419420302477)
          ·
            refine ⟨109521386285245282282613429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292057030093987419420302477 109521386285245282282613429)
            ·
              refine ⟨10267629964241745213995009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109521386285245282282613429 10267629964241745213995009)
              ·
                refine ⟨7700722473181308910496257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10267629964241745213995009 7700722473181308910496257)
                ·
                  refine ⟨5775541854885981682872193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7700722473181308910496257 5775541854885981682872193)
                  ·
                    refine ⟨4331656391164486262154145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5775541854885981682872193 4331656391164486262154145)
                    ·
                      refine ⟨3248742293373364696615609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4331656391164486262154145 3248742293373364696615609)
                      ·
                        rfl

theorem cell23_6326903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 2, 2].length) (baseStart_6326903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326903 prefixEnd_6326903 := by exact prefixLift 6326903
  have htrace : WordTrace (prefixWord ++ tailWord_6326903) baseStart_6326903 baseEnd_6326903 := by
    simpa [prefixWord, tailWord_6326903, baseEnd_6326903] using wordTrace_append hprefix tailTrace_6326903
  have hstable : (prefixWord ++ tailWord_6326903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326903).length < 2 ^ (prefixWord ++ tailWord_6326903).sum := by decide
  have hdescent : baseEnd_6326903 < baseStart_6326903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326914 : List Nat := [3, 4, 3, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_6326914 : Nat := 118140960795 + 6326914 * 2 ^ 59
def prefixEnd_6326914 : Nat := 4983230072969 + 3 ^ 40 * 6326914 * 2
def baseEnd_6326914 : Nat := 3248747941660564153578059

theorem tailTrace_6326914 : CollatzResearch.WordTrace tailWord_6326914 prefixEnd_6326914 3248747941660564153578059 := by
  unfold tailWord_6326914
  simp only [CollatzResearch.WordTrace]
  refine ⟨57690377850169650932314949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153841007600452402486173197 57690377850169650932314949)
  ·
    refine ⟨10816945846906809549809053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57690377850169650932314949 10816945846906809549809053)
    ·
      refine ⟨4056354692590053581178395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10816945846906809549809053 4056354692590053581178395)
      ·
        refine ⟨6084532038885080371767593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4056354692590053581178395 6084532038885080371767593)
        ·
          refine ⟨4563399029163810278825695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6084532038885080371767593 4563399029163810278825695)
          ·
            refine ⟨6845098543745715418238543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4563399029163810278825695 6845098543745715418238543)
            ·
              refine ⟨10267647815618573127357815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6845098543745715418238543 10267647815618573127357815)
              ·
                refine ⟨15401471723427859691036723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10267647815618573127357815 15401471723427859691036723)
                ·
                  refine ⟨23102207585141789536555085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15401471723427859691036723 23102207585141789536555085)
                  ·
                    refine ⟨8663327844428171076208157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23102207585141789536555085 8663327844428171076208157)
                    ·
                      refine ⟨3248747941660564153578059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8663327844428171076208157 3248747941660564153578059)
                      ·
                        rfl

theorem cell23_6326914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_6326914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326914 prefixEnd_6326914 := by exact prefixLift 6326914
  have htrace : WordTrace (prefixWord ++ tailWord_6326914) baseStart_6326914 baseEnd_6326914 := by
    simpa [prefixWord, tailWord_6326914, baseEnd_6326914] using wordTrace_append hprefix tailTrace_6326914
  have hstable : (prefixWord ++ tailWord_6326914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326914).length < 2 ^ (prefixWord ++ tailWord_6326914).sum := by decide
  have hdescent : baseEnd_6326914 < baseStart_6326914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326919 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 3]
def baseStart_6326919 : Nat := 118140960795 + 6326919 * 2 ^ 59
def prefixEnd_6326919 : Nat := 4983230072969 + 3 ^ 40 * 6326919 * 2
def baseEnd_6326919 : Nat := 3248750509063836634015535

theorem tailTrace_6326919 : CollatzResearch.WordTrace tailWord_6326919 prefixEnd_6326919 3248750509063836634015535 := by
  unfold tailWord_6326919
  simp only [CollatzResearch.WordTrace]
  refine ⟨230761693765660489583191811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153841129177106993055461207 230761693765660489583191811)
  ·
    refine ⟨346142540648490734374787717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230761693765660489583191811 346142540648490734374787717)
    ·
      refine ⟨64901726371592012695272697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346142540648490734374787717 64901726371592012695272697)
      ·
        refine ⟨48676294778694009521454523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64901726371592012695272697 48676294778694009521454523)
        ·
          refine ⟨73014442168041014282181785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48676294778694009521454523 73014442168041014282181785)
          ·
            refine ⟨54760831626030760711636339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73014442168041014282181785 54760831626030760711636339)
            ·
              refine ⟨82141247439046141067454509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54760831626030760711636339 82141247439046141067454509)
              ·
                refine ⟨30802967789642302900295441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82141247439046141067454509 30802967789642302900295441)
                ·
                  refine ⟨23102225842231727175221581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30802967789642302900295441 23102225842231727175221581)
                  ·
                    refine ⟨8663334690836897690708093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23102225842231727175221581 8663334690836897690708093)
                    ·
                      refine ⟨3248750509063836634015535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8663334690836897690708093 3248750509063836634015535)
                      ·
                        rfl

theorem cell23_6326919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_6326919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326919 prefixEnd_6326919 := by exact prefixLift 6326919
  have htrace : WordTrace (prefixWord ++ tailWord_6326919) baseStart_6326919 baseEnd_6326919 := by
    simpa [prefixWord, tailWord_6326919, baseEnd_6326919] using wordTrace_append hprefix tailTrace_6326919
  have hstable : (prefixWord ++ tailWord_6326919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326919).length < 2 ^ (prefixWord ++ tailWord_6326919).sum := by decide
  have hdescent : baseEnd_6326919 < baseStart_6326919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326929 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 3, 7, 2]
def baseStart_6326929 : Nat := 118140960795 + 6326929 * 2 ^ 59
def prefixEnd_6326929 : Nat := 4983230072969 + 3 ^ 40 * 6326929 * 2
def baseEnd_6326929 : Nat := 3248755643870381594890489

theorem tailTrace_6326929 : CollatzResearch.WordTrace tailWord_6326929 prefixEnd_6326929 3248755643870381594890489 := by
  unfold tailWord_6326929
  simp only [CollatzResearch.WordTrace]
  refine ⟨230762058495624261291055841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153841372330416174194037227 230762058495624261291055841)
  ·
    refine ⟨173071543871718195968291881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230762058495624261291055841 173071543871718195968291881)
    ·
      refine ⟨129803657903788646976218911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173071543871718195968291881 129803657903788646976218911)
      ·
        refine ⟨194705486855682970464328367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129803657903788646976218911 194705486855682970464328367)
        ·
          refine ⟨292058230283524455696492551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194705486855682970464328367 292058230283524455696492551)
          ·
            refine ⟨438087345425286683544738827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292058230283524455696492551 438087345425286683544738827)
            ·
              refine ⟨657131018137930025317108241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438087345425286683544738827 657131018137930025317108241)
              ·
                refine ⟨492848263603447518987831181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 657131018137930025317108241 492848263603447518987831181)
                ·
                  refine ⟨184818098851292819620436693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 492848263603447518987831181 184818098851292819620436693)
                  ·
                    refine ⟨4331674191827175459853985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 184818098851292819620436693 4331674191827175459853985)
                    ·
                      refine ⟨3248755643870381594890489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4331674191827175459853985 3248755643870381594890489)
                      ·
                        rfl

theorem cell23_6326929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 7, 2].length) (baseStart_6326929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326929 prefixEnd_6326929 := by exact prefixLift 6326929
  have htrace : WordTrace (prefixWord ++ tailWord_6326929) baseStart_6326929 baseEnd_6326929 := by
    simpa [prefixWord, tailWord_6326929, baseEnd_6326929] using wordTrace_append hprefix tailTrace_6326929
  have hstable : (prefixWord ++ tailWord_6326929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326929).length < 2 ^ (prefixWord ++ tailWord_6326929).sum := by decide
  have hdescent : baseEnd_6326929 < baseStart_6326929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6326959 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 4]
def baseStart_6326959 : Nat := 118140960795 + 6326959 * 2 ^ 59
def prefixEnd_6326959 : Nat := 4983230072969 + 3 ^ 40 * 6326959 * 2
def baseEnd_6326959 : Nat := 3248771048290016477515351

theorem tailTrace_6326959 : CollatzResearch.WordTrace tailWord_6326959 prefixEnd_6326959 3248771048290016477515351 := by
  unfold tailWord_6326959
  simp only [CollatzResearch.WordTrace]
  refine ⟨230763152685515576414647931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153842101790343717609765287 230763152685515576414647931)
  ·
    refine ⟨346144729028273364621971897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230763152685515576414647931 346144729028273364621971897)
    ·
      refine ⟨259608546771205023466478923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346144729028273364621971897 259608546771205023466478923)
      ·
        refine ⟨389412820156807535199718385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259608546771205023466478923 389412820156807535199718385)
        ·
          refine ⟨292059615117605651399788789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389412820156807535199718385 292059615117605651399788789)
          ·
            refine ⟨27380588917275529818730199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 292059615117605651399788789 27380588917275529818730199)
            ·
              refine ⟨41070883375913294728095299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27380588917275529818730199 41070883375913294728095299)
              ·
                refine ⟨61606325063869942092142949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41070883375913294728095299 61606325063869942092142949)
                ·
                  refine ⟨11551185949475614142276803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61606325063869942092142949 11551185949475614142276803)
                  ·
                    refine ⟨17326778924213421213415205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11551185949475614142276803 17326778924213421213415205)
                    ·
                      refine ⟨3248771048290016477515351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17326778924213421213415205 3248771048290016477515351)
                      ·
                        rfl

theorem cell23_6326959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 4].length) (baseStart_6326959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6326959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6326959 prefixEnd_6326959 := by exact prefixLift 6326959
  have htrace : WordTrace (prefixWord ++ tailWord_6326959) baseStart_6326959 baseEnd_6326959 := by
    simpa [prefixWord, tailWord_6326959, baseEnd_6326959] using wordTrace_append hprefix tailTrace_6326959
  have hstable : (prefixWord ++ tailWord_6326959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6326959).length < 2 ^ (prefixWord ++ tailWord_6326959).sum := by decide
  have hdescent : baseEnd_6326959 < baseStart_6326959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6326959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327059 : List Nat := [1, 1, 1, 2, 1, 3, 3, 4, 1, 6]
def baseStart_6327059 : Nat := 118140960795 + 6327059 * 2 ^ 59
def prefixEnd_6327059 : Nat := 4983230072969 + 3 ^ 40 * 6327059 * 2
def baseEnd_6327059 : Nat := 1082940798785155362088297

theorem tailTrace_6327059 : CollatzResearch.WordTrace tailWord_6327059 prefixEnd_6327059 1082940798785155362088297 := by
  unfold tailWord_6327059
  simp only [CollatzResearch.WordTrace]
  refine ⟨230766799985153293493288231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153844533323435528995525487 230766799985153293493288231)
  ·
    refine ⟨346150199977729940239932347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230766799985153293493288231 346150199977729940239932347)
    ·
      refine ⟨519225299966594910359898521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346150199977729940239932347 519225299966594910359898521)
      ·
        refine ⟨389418974974946182769923891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 519225299966594910359898521 389418974974946182769923891)
        ·
          refine ⟨584128462462419274154885837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389418974974946182769923891 584128462462419274154885837)
          ·
            refine ⟨219048173423407227808082189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 584128462462419274154885837 219048173423407227808082189)
            ·
              refine ⟨82143065033777710428030821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219048173423407227808082189 82143065033777710428030821)
              ·
                refine ⟨15401824693833320705255779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82143065033777710428030821 15401824693833320705255779)
                ·
                  refine ⟨23102737040749981057883669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15401824693833320705255779 23102737040749981057883669)
                  ·
                    refine ⟨1082940798785155362088297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23102737040749981057883669 1082940798785155362088297)
                    ·
                      rfl

theorem cell23_6327059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 6].length) (baseStart_6327059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327059 prefixEnd_6327059 := by exact prefixLift 6327059
  have htrace : WordTrace (prefixWord ++ tailWord_6327059) baseStart_6327059 baseEnd_6327059 := by
    simpa [prefixWord, tailWord_6327059, baseEnd_6327059] using wordTrace_append hprefix tailTrace_6327059
  have hstable : (prefixWord ++ tailWord_6327059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327059).length < 2 ^ (prefixWord ++ tailWord_6327059).sum := by decide
  have hdescent : baseEnd_6327059 < baseStart_6327059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327063 : List Nat := [1, 1, 3, 4, 3, 1, 1, 3, 1, 5]
def baseStart_6327063 : Nat := 118140960795 + 6327063 * 2 ^ 59
def prefixEnd_6327063 : Nat := 4983230072969 + 3 ^ 40 * 6327063 * 2
def baseEnd_6327063 : Nat := 1082941483426028023538291

theorem tailTrace_6327063 : CollatzResearch.WordTrace tailWord_6327063 prefixEnd_6327063 1082941483426028023538291 := by
  unfold tailWord_6327063
  simp only [CollatzResearch.WordTrace]
  refine ⟨230766945877138802176433843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153844630584759201450955895 230766945877138802176433843)
  ·
    refine ⟨346150418815708203264650765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230766945877138802176433843 346150418815708203264650765)
    ·
      refine ⟨129806407055890576224244037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346150418815708203264650765 129806407055890576224244037)
      ·
        refine ⟨24338701322979483042045757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129806407055890576224244037 24338701322979483042045757)
        ·
          refine ⟨9127012996117306140767159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24338701322979483042045757 9127012996117306140767159)
          ·
            refine ⟨13690519494175959211150739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9127012996117306140767159 13690519494175959211150739)
            ·
              refine ⟨20535779241263938816726109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13690519494175959211150739 20535779241263938816726109)
              ·
                refine ⟨7700917215473977056272291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20535779241263938816726109 7700917215473977056272291)
                ·
                  refine ⟨11551375823210965584408437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7700917215473977056272291 11551375823210965584408437)
                  ·
                    refine ⟨1082941483426028023538291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11551375823210965584408437 1082941483426028023538291)
                    ·
                      rfl

theorem cell23_6327063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 5].length) (baseStart_6327063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327063 prefixEnd_6327063 := by exact prefixLift 6327063
  have htrace : WordTrace (prefixWord ++ tailWord_6327063) baseStart_6327063 baseEnd_6327063 := by
    simpa [prefixWord, tailWord_6327063, baseEnd_6327063] using wordTrace_append hprefix tailTrace_6327063
  have hstable : (prefixWord ++ tailWord_6327063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327063).length < 2 ^ (prefixWord ++ tailWord_6327063).sum := by decide
  have hdescent : baseEnd_6327063 < baseStart_6327063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327083 : List Nat := [1, 1, 1, 1, 2, 1, 2, 7, 3, 2, 2]
def baseStart_6327083 : Nat := 118140960795 + 6327083 * 2 ^ 59
def prefixEnd_6327083 : Nat := 4983230072969 + 3 ^ 40 * 6327083 * 2
def baseEnd_6327083 : Nat := 3248834719891173992364781

theorem tailTrace_6327083 : CollatzResearch.WordTrace tailWord_6327083 prefixEnd_6327083 3248834719891173992364781 := by
  unfold tailWord_6327083
  simp only [CollatzResearch.WordTrace]
  refine ⟨230767675337066345592161903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153845116891377563728107935 230767675337066345592161903)
  ·
    refine ⟨346151513005599518388242855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230767675337066345592161903 346151513005599518388242855)
    ·
      refine ⟨519227269508399277582364283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346151513005599518388242855 519227269508399277582364283)
      ·
        refine ⟨778840904262598916373546425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519227269508399277582364283 778840904262598916373546425)
        ·
          refine ⟨584130678196949187280159819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 778840904262598916373546425 584130678196949187280159819)
          ·
            refine ⟨876196017295423780920239729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 584130678196949187280159819 876196017295423780920239729)
            ·
              refine ⟨657147012971567835690179797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 876196017295423780920239729 657147012971567835690179797)
              ·
                refine ⟨15401883116521121148988589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 657147012971567835690179797 15401883116521121148988589)
                ·
                  refine ⟨5775706168695420430870721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15401883116521121148988589 5775706168695420430870721)
                  ·
                    refine ⟨4331779626521565323153041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5775706168695420430870721 4331779626521565323153041)
                    ·
                      refine ⟨3248834719891173992364781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4331779626521565323153041 3248834719891173992364781)
                      ·
                        rfl

theorem cell23_6327083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 2, 2].length) (baseStart_6327083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327083 prefixEnd_6327083 := by exact prefixLift 6327083
  have htrace : WordTrace (prefixWord ++ tailWord_6327083) baseStart_6327083 baseEnd_6327083 := by
    simpa [prefixWord, tailWord_6327083, baseEnd_6327083] using wordTrace_append hprefix tailTrace_6327083
  have hstable : (prefixWord ++ tailWord_6327083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327083).length < 2 ^ (prefixWord ++ tailWord_6327083).sum := by decide
  have hdescent : baseEnd_6327083 < baseStart_6327083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327089 : List Nat := [1, 2, 2, 3, 2, 1, 2, 10]
def baseStart_6327089 : Nat := 118140960795 + 6327089 * 2 ^ 59
def prefixEnd_6327089 : Nat := 4983230072969 + 3 ^ 40 * 6327089 * 2
def baseEnd_6327089 : Nat := 120327325954633369218139

theorem tailTrace_6327089 : CollatzResearch.WordTrace tailWord_6327089 prefixEnd_6327089 120327325954633369218139 := by
  unfold tailWord_6327089
  simp only [CollatzResearch.WordTrace]
  refine ⟨230767894175044608616880321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153845262783363072411253547 230767894175044608616880321)
  ·
    refine ⟨173075920631283456462660241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230767894175044608616880321 173075920631283456462660241)
    ·
      refine ⟨129806940473462592346995181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173075920631283456462660241 129806940473462592346995181)
      ·
        refine ⟨48677602677548472130123193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129806940473462592346995181 48677602677548472130123193)
        ·
          refine ⟨36508202008161354097592395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48677602677548472130123193 36508202008161354097592395)
          ·
            refine ⟨54762303012242031146388593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36508202008161354097592395 54762303012242031146388593)
            ·
              refine ⟨41071727259181523359791445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54762303012242031146388593 41071727259181523359791445)
              ·
                refine ⟨120327325954633369218139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41071727259181523359791445 120327325954633369218139)
                ·
                  rfl

theorem cell23_6327089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 10].length) (baseStart_6327089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327089 prefixEnd_6327089 := by exact prefixLift 6327089
  have htrace : WordTrace (prefixWord ++ tailWord_6327089) baseStart_6327089 baseEnd_6327089 := by
    simpa [prefixWord, tailWord_6327089, baseEnd_6327089] using wordTrace_append hprefix tailTrace_6327089
  have hstable : (prefixWord ++ tailWord_6327089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327089).length < 2 ^ (prefixWord ++ tailWord_6327089).sum := by decide
  have hdescent : baseEnd_6327089 < baseStart_6327089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327093 : List Nat := [1, 3, 3, 1, 3, 3, 1, 1, 1, 6]
def baseStart_6327093 : Nat := 118140960795 + 6327093 * 2 ^ 59
def prefixEnd_6327093 : Nat := 4983230072969 + 3 ^ 40 * 6327093 * 2
def baseEnd_6327093 : Nat := 1082946618232572984413245

theorem tailTrace_6327093 : CollatzResearch.WordTrace tailWord_6327093 prefixEnd_6327093 1082946618232572984413245 := by
  unfold tailWord_6327093
  simp only [CollatzResearch.WordTrace]
  refine ⟨230768040067030117300025933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153845360044686744866683955 230768040067030117300025933)
  ·
    refine ⟨86538015025136293987509725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230768040067030117300025933 86538015025136293987509725)
    ·
      refine ⟨32451755634426110245316147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86538015025136293987509725 32451755634426110245316147)
      ·
        refine ⟨48677633451639165367974221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32451755634426110245316147 48677633451639165367974221)
        ·
          refine ⟨18254112544364687012990333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48677633451639165367974221 18254112544364687012990333)
          ·
            refine ⟨6845292204136757629871375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18254112544364687012990333 6845292204136757629871375)
            ·
              refine ⟨10267938306205136444807063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6845292204136757629871375 10267938306205136444807063)
              ·
                refine ⟨15401907459307704667210595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10267938306205136444807063 15401907459307704667210595)
                ·
                  refine ⟨23102861188961557000815893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15401907459307704667210595 23102861188961557000815893)
                  ·
                    refine ⟨1082946618232572984413245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23102861188961557000815893 1082946618232572984413245)
                    ·
                      rfl

theorem cell23_6327093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_6327093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327093 prefixEnd_6327093 := by exact prefixLift 6327093
  have htrace : WordTrace (prefixWord ++ tailWord_6327093) baseStart_6327093 baseEnd_6327093 := by
    simpa [prefixWord, tailWord_6327093, baseEnd_6327093] using wordTrace_append hprefix tailTrace_6327093
  have hstable : (prefixWord ++ tailWord_6327093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327093).length < 2 ^ (prefixWord ++ tailWord_6327093).sum := by decide
  have hdescent : baseEnd_6327093 < baseStart_6327093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327103 : List Nat := [1, 1, 2, 2, 5, 1, 1, 4, 1, 2, 3]
def baseStart_6327103 : Nat := 118140960795 + 6327103 * 2 ^ 59
def prefixEnd_6327103 : Nat := 4983230072969 + 3 ^ 40 * 6327103 * 2
def baseEnd_6327103 : Nat := 3248844989504263914114689

theorem tailTrace_6327103 : CollatzResearch.WordTrace tailWord_6327103 prefixEnd_6327103 3248844989504263914114689 := by
  unfold tailWord_6327103
  simp only [CollatzResearch.WordTrace]
  refine ⟨230768404796993889007889963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153845603197995926005259975 230768404796993889007889963)
  ·
    refine ⟨346152607195490833511834945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230768404796993889007889963 346152607195490833511834945)
    ·
      refine ⟨259614455396618125133876209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346152607195490833511834945 259614455396618125133876209)
      ·
        refine ⟨194710841547463593850407157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259614455396618125133876209 194710841547463593850407157)
        ·
          refine ⟨18254141395074711923475671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 194710841547463593850407157 18254141395074711923475671)
          ·
            refine ⟨27381212092612067885213507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18254141395074711923475671 27381212092612067885213507)
            ·
              refine ⟨41071818138918101827820261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27381212092612067885213507 41071818138918101827820261)
              ·
                refine ⟨7700965901047144092716299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41071818138918101827820261 7700965901047144092716299)
                ·
                  refine ⟨11551448851570716139074449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7700965901047144092716299 11551448851570716139074449)
                  ·
                    refine ⟨8663586638678037104305837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11551448851570716139074449 8663586638678037104305837)
                    ·
                      refine ⟨3248844989504263914114689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8663586638678037104305837 3248844989504263914114689)
                      ·
                        rfl

theorem cell23_6327103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 2, 3].length) (baseStart_6327103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327103 prefixEnd_6327103 := by exact prefixLift 6327103
  have htrace : WordTrace (prefixWord ++ tailWord_6327103) baseStart_6327103 baseEnd_6327103 := by
    simpa [prefixWord, tailWord_6327103, baseEnd_6327103] using wordTrace_append hprefix tailTrace_6327103
  have hstable : (prefixWord ++ tailWord_6327103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327103).length < 2 ^ (prefixWord ++ tailWord_6327103).sum := by decide
  have hdescent : baseEnd_6327103 < baseStart_6327103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327173 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 3, 4, 2]
def baseStart_6327173 : Nat := 118140960795 + 6327173 * 2 ^ 59
def prefixEnd_6327173 : Nat := 4983230072969 + 3 ^ 40 * 6327173 * 2
def baseEnd_6327173 : Nat := 3248880933150078640239367

theorem tailTrace_6327173 : CollatzResearch.WordTrace tailWord_6327173 prefixEnd_6327173 3248880933150078640239367 := by
  unfold tailWord_6327173
  simp only [CollatzResearch.WordTrace]
  refine ⟨230770957906740290962938173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153847305271160193975292115 230770957906740290962938173)
  ·
    refine ⟨86539109215027609111101815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230770957906740290962938173 86539109215027609111101815)
    ·
      refine ⟨129808663822541413666652723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86539109215027609111101815 129808663822541413666652723)
      ·
        refine ⟨194712995733812120499979085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129808663822541413666652723 194712995733812120499979085)
        ·
          refine ⟨73017373400179545187492157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194712995733812120499979085 73017373400179545187492157)
          ·
            refine ⟨27381515025067329445309559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73017373400179545187492157 27381515025067329445309559)
            ·
              refine ⟨41072272537600994167964339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27381515025067329445309559 41072272537600994167964339)
              ·
                refine ⟨61608408806401491251946509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41072272537600994167964339 61608408806401491251946509)
                ·
                  refine ⟨23103153302400559219479941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61608408806401491251946509 23103153302400559219479941)
                  ·
                    refine ⟨4331841244200104853652489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23103153302400559219479941 4331841244200104853652489)
                    ·
                      refine ⟨3248880933150078640239367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4331841244200104853652489 3248880933150078640239367)
                      ·
                        rfl

theorem cell23_6327173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 4, 2].length) (baseStart_6327173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327173 prefixEnd_6327173 := by exact prefixLift 6327173
  have htrace : WordTrace (prefixWord ++ tailWord_6327173) baseStart_6327173 baseEnd_6327173 := by
    simpa [prefixWord, tailWord_6327173, baseEnd_6327173] using wordTrace_append hprefix tailTrace_6327173
  have hstable : (prefixWord ++ tailWord_6327173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327173).length < 2 ^ (prefixWord ++ tailWord_6327173).sum := by decide
  have hdescent : baseEnd_6327173 < baseStart_6327173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327177 : List Nat := [1, 2, 1, 1, 5, 3, 3, 1, 1, 3, 2]
def baseStart_6327177 : Nat := 118140960795 + 6327177 * 2 ^ 59
def prefixEnd_6327177 : Nat := 4983230072969 + 3 ^ 40 * 6327177 * 2
def baseEnd_6327177 : Nat := 3248882987072696624589349

theorem tailTrace_6327177 : CollatzResearch.WordTrace tailWord_6327177 prefixEnd_6327177 3248882987072696624589349 := by
  unfold tailWord_6327177
  simp only [CollatzResearch.WordTrace]
  refine ⟨230771103798725799646083785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153847402532483866430722523 230771103798725799646083785)
  ·
    refine ⟨173078327849044349734562839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230771103798725799646083785 173078327849044349734562839)
    ·
      refine ⟨259617491773566524601844259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173078327849044349734562839 259617491773566524601844259)
      ·
        refine ⟨389426237660349786902766389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259617491773566524601844259 389426237660349786902766389)
        ·
          refine ⟨36508709780657792522134349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 389426237660349786902766389 36508709780657792522134349)
          ·
            refine ⟨13690766167746672195800381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36508709780657792522134349 13690766167746672195800381)
            ·
              refine ⟨5134037312905002073425143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13690766167746672195800381 5134037312905002073425143)
              ·
                refine ⟨7701055969357503110137715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5134037312905002073425143 7701055969357503110137715)
                ·
                  refine ⟨11551583954036254665206573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7701055969357503110137715 11551583954036254665206573)
                  ·
                    refine ⟨4331843982763595499452465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11551583954036254665206573 4331843982763595499452465)
                    ·
                      refine ⟨3248882987072696624589349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4331843982763595499452465 3248882987072696624589349)
                      ·
                        rfl

theorem cell23_6327177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 1, 3, 2].length) (baseStart_6327177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327177 prefixEnd_6327177 := by exact prefixLift 6327177
  have htrace : WordTrace (prefixWord ++ tailWord_6327177) baseStart_6327177 baseEnd_6327177 := by
    simpa [prefixWord, tailWord_6327177, baseEnd_6327177] using wordTrace_append hprefix tailTrace_6327177
  have hstable : (prefixWord ++ tailWord_6327177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327177).length < 2 ^ (prefixWord ++ tailWord_6327177).sum := by decide
  have hdescent : baseEnd_6327177 < baseStart_6327177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327207 : List Nat := [1, 1, 6, 1, 3, 1, 2, 1, 1, 4, 2]
def baseStart_6327207 : Nat := 118140960795 + 6327207 * 2 ^ 59
def prefixEnd_6327207 : Nat := 4983230072969 + 3 ^ 40 * 6327207 * 2
def baseEnd_6327207 : Nat := 3248898391492331507214211

theorem tailTrace_6327207 : CollatzResearch.WordTrace tailWord_6327207 prefixEnd_6327207 3248898391492331507214211 := by
  unfold tailWord_6327207
  simp only [CollatzResearch.WordTrace]
  refine ⟨230772197988617114769675875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153848131992411409846450583 230772197988617114769675875)
  ·
    refine ⟨346158296982925672154513813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230772197988617114769675875 346158296982925672154513813)
    ·
      refine ⟨16226170171074640882242835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 346158296982925672154513813 16226170171074640882242835)
      ·
        refine ⟨24339255256611961323364253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16226170171074640882242835 24339255256611961323364253)
        ·
          refine ⟨9127220721229485496261595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24339255256611961323364253 9127220721229485496261595)
          ·
            refine ⟨13690831081844228244392393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9127220721229485496261595 13690831081844228244392393)
            ·
              refine ⟨10268123311383171183294295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13690831081844228244392393 10268123311383171183294295)
              ·
                refine ⟨15402184967074756774941443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10268123311383171183294295 15402184967074756774941443)
                ·
                  refine ⟨23103277450612135162412165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15402184967074756774941443 23103277450612135162412165)
                  ·
                    refine ⟨4331864521989775342952281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23103277450612135162412165 4331864521989775342952281)
                    ·
                      refine ⟨3248898391492331507214211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4331864521989775342952281 3248898391492331507214211)
                      ·
                        rfl

theorem cell23_6327207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_6327207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327207 prefixEnd_6327207 := by exact prefixLift 6327207
  have htrace : WordTrace (prefixWord ++ tailWord_6327207) baseStart_6327207 baseEnd_6327207 := by
    simpa [prefixWord, tailWord_6327207, baseEnd_6327207] using wordTrace_append hprefix tailTrace_6327207
  have hstable : (prefixWord ++ tailWord_6327207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327207).length < 2 ^ (prefixWord ++ tailWord_6327207).sum := by decide
  have hdescent : baseEnd_6327207 < baseStart_6327207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327226 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 1, 7]
def baseStart_6327226 : Nat := 118140960795 + 6327226 * 2 ^ 59
def prefixEnd_6327226 : Nat := 4983230072969 + 3 ^ 40 * 6327226 * 2
def baseEnd_6327226 : Nat := 1082969382541588977625541

theorem tailTrace_6327226 : CollatzResearch.WordTrace tailWord_6327226 prefixEnd_6327226 1082969382541588977625541 := by
  unfold tailWord_6327226
  simp only [CollatzResearch.WordTrace]
  refine ⟨57693222743887070253654383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153848593983698854009745021 57693222743887070253654383)
  ·
    refine ⟨86539834115830605380481575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57693222743887070253654383 86539834115830605380481575)
    ·
      refine ⟨129809751173745908070722363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86539834115830605380481575 129809751173745908070722363)
      ·
        refine ⟨194714626760618862106083545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129809751173745908070722363 194714626760618862106083545)
        ·
          refine ⟨146035970070464146579562659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194714626760618862106083545 146035970070464146579562659)
          ·
            refine ⟨219053955105696219869343989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146035970070464146579562659 219053955105696219869343989)
            ·
              refine ⟨20536308291159020612750999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 219053955105696219869343989 20536308291159020612750999)
              ·
                refine ⟨30804462436738530919126499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20536308291159020612750999 30804462436738530919126499)
                ·
                  refine ⟨46206693655107796378689749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30804462436738530919126499 46206693655107796378689749)
                  ·
                    refine ⟨1082969382541588977625541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46206693655107796378689749 1082969382541588977625541)
                    ·
                      rfl

theorem cell23_6327226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_6327226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327226 prefixEnd_6327226 := by exact prefixLift 6327226
  have htrace : WordTrace (prefixWord ++ tailWord_6327226) baseStart_6327226 baseEnd_6327226 := by
    simpa [prefixWord, tailWord_6327226, baseEnd_6327226] using wordTrace_append hprefix tailTrace_6327226
  have hstable : (prefixWord ++ tailWord_6327226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327226).length < 2 ^ (prefixWord ++ tailWord_6327226).sum := by decide
  have hdescent : baseEnd_6327226 < baseStart_6327226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327230 : List Nat := [4, 2, 1, 1, 1, 2, 4, 3, 5]
def baseStart_6327230 : Nat := 118140960795 + 6327230 * 2 ^ 59
def prefixEnd_6327230 : Nat := 4983230072969 + 3 ^ 40 * 6327230 * 2
def baseEnd_6327230 : Nat := 360990022394153879691845

theorem tailTrace_6327230 : CollatzResearch.WordTrace tailWord_6327230 prefixEnd_6327230 360990022394153879691845 := by
  unfold tailWord_6327230
  simp only [CollatzResearch.WordTrace]
  refine ⟨28846629608441723712220393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153848691245022526465175429 28846629608441723712220393)
  ·
    refine ⟨21634972206331292784165295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28846629608441723712220393 21634972206331292784165295)
    ·
      refine ⟨32452458309496939176247943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21634972206331292784165295 32452458309496939176247943)
      ·
        refine ⟨48678687464245408764371915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32452458309496939176247943 48678687464245408764371915)
        ·
          refine ⟨73018031196368113146557873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48678687464245408764371915 73018031196368113146557873)
          ·
            refine ⟨54763523397276084859918405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73018031196368113146557873 54763523397276084859918405)
            ·
              refine ⟨10268160636989265911234701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54763523397276084859918405 10268160636989265911234701)
              ·
                refine ⟨3850560238870974716713013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10268160636989265911234701 3850560238870974716713013)
                ·
                  refine ⟨360990022394153879691845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3850560238870974716713013 360990022394153879691845)
                  ·
                    rfl

theorem cell23_6327230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_6327230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327230 prefixEnd_6327230 := by exact prefixLift 6327230
  have htrace : WordTrace (prefixWord ++ tailWord_6327230) baseStart_6327230 baseEnd_6327230 := by
    simpa [prefixWord, tailWord_6327230, baseEnd_6327230] using wordTrace_append hprefix tailTrace_6327230
  have hstable : (prefixWord ++ tailWord_6327230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327230).length < 2 ^ (prefixWord ++ tailWord_6327230).sum := by decide
  have hdescent : baseEnd_6327230 < baseStart_6327230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327303 : List Nat := [1, 1, 4, 3, 1, 1, 2, 4, 6]
def baseStart_6327303 : Nat := 118140960795 + 6327303 * 2 ^ 59
def prefixEnd_6327303 : Nat := 4983230072969 + 3 ^ 40 * 6327303 * 2
def baseEnd_6327303 : Nat := 360994187292795903512641

theorem tailTrace_6327303 : CollatzResearch.WordTrace tailWord_6327303 prefixEnd_6327303 360994187292795903512641 := by
  unfold tailWord_6327303
  simp only [CollatzResearch.WordTrace]
  refine ⟨230775699396269323165170563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153850466264179548776780375 230775699396269323165170563)
  ·
    refine ⟨346163549094403984747755845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230775699396269323165170563 346163549094403984747755845)
    ·
      refine ⟨64905665455200747140204221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346163549094403984747755845 64905665455200747140204221)
      ·
        refine ⟨24339624545700280177576583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64905665455200747140204221 24339624545700280177576583)
        ·
          refine ⟨36509436818550420266364875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24339624545700280177576583 36509436818550420266364875)
          ·
            refine ⟨54764155227825630399547313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36509436818550420266364875 54764155227825630399547313)
            ·
              refine ⟨41073116420869222799660485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54764155227825630399547313 41073116420869222799660485)
              ·
                refine ⟨7701209328912979274936341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41073116420869222799660485 7701209328912979274936341)
                ·
                  refine ⟨360994187292795903512641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7701209328912979274936341 360994187292795903512641)
                  ·
                    rfl

theorem cell23_6327303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 6].length) (baseStart_6327303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327303 prefixEnd_6327303 := by exact prefixLift 6327303
  have htrace : WordTrace (prefixWord ++ tailWord_6327303) baseStart_6327303 baseEnd_6327303 := by
    simpa [prefixWord, tailWord_6327303, baseEnd_6327303] using wordTrace_append hprefix tailTrace_6327303
  have hstable : (prefixWord ++ tailWord_6327303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327303).length < 2 ^ (prefixWord ++ tailWord_6327303).sum := by decide
  have hdescent : baseEnd_6327303 < baseStart_6327303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327320 : List Nat := [2, 1, 2, 3, 2, 2, 4, 1, 6]
def baseStart_6327320 : Nat := 118140960795 + 6327320 * 2 ^ 59
def prefixEnd_6327320 : Nat := 4983230072969 + 3 ^ 40 * 6327320 * 2
def baseEnd_6327320 : Nat := 360995157200698840566799

theorem tailTrace_6327320 : CollatzResearch.WordTrace tailWord_6327320 prefixEnd_6327320 360995157200698840566799 := by
  unfold tailWord_6327320
  simp only [CollatzResearch.WordTrace]
  refine ⟨115388159718603867534269707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153850879624805156712359609 115388159718603867534269707)
  ·
    refine ⟨173082239577905801301404561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115388159718603867534269707 173082239577905801301404561)
    ·
      refine ⟨129811679683429350976053421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173082239577905801301404561 129811679683429350976053421)
      ·
        refine ⟨48679379881286006616020033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129811679683429350976053421 48679379881286006616020033)
        ·
          refine ⟨36509534910964504962015025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48679379881286006616020033 36509534910964504962015025)
          ·
            refine ⟨27382151183223378721511269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36509534910964504962015025 27382151183223378721511269)
            ·
              refine ⟨5134153346854383510283363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27382151183223378721511269 5134153346854383510283363)
              ·
                refine ⟨7701230020281575265425045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5134153346854383510283363 7701230020281575265425045)
                ·
                  refine ⟨360995157200698840566799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7701230020281575265425045 360995157200698840566799)
                  ·
                    rfl

theorem cell23_6327320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 6].length) (baseStart_6327320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327320 prefixEnd_6327320 := by exact prefixLift 6327320
  have htrace : WordTrace (prefixWord ++ tailWord_6327320) baseStart_6327320 baseEnd_6327320 := by
    simpa [prefixWord, tailWord_6327320, baseEnd_6327320] using wordTrace_append hprefix tailTrace_6327320
  have hstable : (prefixWord ++ tailWord_6327320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327320).length < 2 ^ (prefixWord ++ tailWord_6327320).sum := by decide
  have hdescent : baseEnd_6327320 < baseStart_6327320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327333 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 3, 5]
def baseStart_6327333 : Nat := 118140960795 + 6327333 * 2 ^ 59
def prefixEnd_6327333 : Nat := 4983230072969 + 3 ^ 40 * 6327333 * 2
def baseEnd_6327333 : Nat := 1082987696684932671412877

theorem tailTrace_6327333 : CollatzResearch.WordTrace tailWord_6327333 prefixEnd_6327333 1082987696684932671412877 := by
  unfold tailWord_6327333
  simp only [CollatzResearch.WordTrace]
  refine ⟨230776793586160638288762653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153851195724107092192508435 230776793586160638288762653)
  ·
    refine ⟨86541297594810239358285995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230776793586160638288762653 86541297594810239358285995)
    ·
      refine ⟨129811946392215359037428993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86541297594810239358285995 129811946392215359037428993)
      ·
        refine ⟨97358959794161519278071745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129811946392215359037428993 97358959794161519278071745)
        ·
          refine ⟨73019219845621139458553809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97358959794161519278071745 73019219845621139458553809)
          ·
            refine ⟨54764414884215854593915357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73019219845621139458553809 54764414884215854593915357)
            ·
              refine ⟨20536655581580945472718259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54764414884215854593915357 20536655581580945472718259)
              ·
                refine ⟨30804983372371418209077389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20536655581580945472718259 30804983372371418209077389)
                ·
                  refine ⟨11551868764639281828404021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30804983372371418209077389 11551868764639281828404021)
                  ·
                    refine ⟨1082987696684932671412877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11551868764639281828404021 1082987696684932671412877)
                    ·
                      rfl

theorem cell23_6327333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_6327333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327333 prefixEnd_6327333 := by exact prefixLift 6327333
  have htrace : WordTrace (prefixWord ++ tailWord_6327333) baseStart_6327333 baseEnd_6327333 := by
    simpa [prefixWord, tailWord_6327333, baseEnd_6327333] using wordTrace_append hprefix tailTrace_6327333
  have hstable : (prefixWord ++ tailWord_6327333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327333).length < 2 ^ (prefixWord ++ tailWord_6327333).sum := by decide
  have hdescent : baseEnd_6327333 < baseStart_6327333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327347 : List Nat := [1, 1, 1, 2, 4, 1, 1, 7, 1, 1, 3]
def baseStart_6327347 : Nat := 118140960795 + 6327347 * 2 ^ 59
def prefixEnd_6327347 : Nat := 4983230072969 + 3 ^ 40 * 6327347 * 2
def baseEnd_6327347 : Nat := 3248970278783960959463567

theorem tailTrace_6327347 : CollatzResearch.WordTrace tailWord_6327347 prefixEnd_6327347 3248970278783960959463567 := by
  unfold tailWord_6327347
  simp only [CollatzResearch.WordTrace]
  refine ⟨230777304208109918679772295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153851536138739945786514863 230777304208109918679772295)
  ·
    refine ⟨346165956312164878019658443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230777304208109918679772295 346165956312164878019658443)
    ·
      refine ⟨519248934468247317029487665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346165956312164878019658443 519248934468247317029487665)
      ·
        refine ⟨389436700851185487772115749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 519248934468247317029487665 389436700851185487772115749)
        ·
          refine ⟨73019381409597278957271703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 389436700851185487772115749 73019381409597278957271703)
          ·
            refine ⟨109529072114395918435907555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73019381409597278957271703 109529072114395918435907555)
            ·
              refine ⟨164293608171593877653861333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109529072114395918435907555 164293608171593877653861333)
              ·
                refine ⟨3850631441521731507512375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 164293608171593877653861333 3850631441521731507512375)
                ·
                  refine ⟨5775947162282597261268563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3850631441521731507512375 5775947162282597261268563)
                  ·
                    refine ⟨8663920743423895891902845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5775947162282597261268563 8663920743423895891902845)
                    ·
                      refine ⟨3248970278783960959463567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8663920743423895891902845 3248970278783960959463567)
                      ·
                        rfl

theorem cell23_6327347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 1, 1, 3].length) (baseStart_6327347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327347 prefixEnd_6327347 := by exact prefixLift 6327347
  have htrace : WordTrace (prefixWord ++ tailWord_6327347) baseStart_6327347 baseEnd_6327347 := by
    simpa [prefixWord, tailWord_6327347, baseEnd_6327347] using wordTrace_append hprefix tailTrace_6327347
  have hstable : (prefixWord ++ tailWord_6327347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327347).length < 2 ^ (prefixWord ++ tailWord_6327347).sum := by decide
  have hdescent : baseEnd_6327347 < baseStart_6327347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327357 : List Nat := [1, 4, 1, 3, 1, 2, 2, 2, 2, 3, 2]
def baseStart_6327357 : Nat := 118140960795 + 6327357 * 2 ^ 59
def prefixEnd_6327357 : Nat := 4983230072969 + 3 ^ 40 * 6327357 * 2
def baseEnd_6327357 : Nat := 3248975413590505920338521

theorem tailTrace_6327357 : CollatzResearch.WordTrace tailWord_6327357 prefixEnd_6327357 3248975413590505920338521 := by
  unfold tailWord_6327357
  simp only [CollatzResearch.WordTrace]
  refine ⟨230777668938073690387636325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153851779292049126925090883 230777668938073690387636325)
  ·
    refine ⟨43270812925888816947681811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230777668938073690387636325 43270812925888816947681811)
    ·
      refine ⟨64906219388833225421522717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43270812925888816947681811 64906219388833225421522717)
      ·
        refine ⟨24339832270812459533071019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64906219388833225421522717 24339832270812459533071019)
        ·
          refine ⟨36509748406218689299606529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24339832270812459533071019 36509748406218689299606529)
          ·
            refine ⟨27382311304664016974704897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36509748406218689299606529 27382311304664016974704897)
            ·
              refine ⟨20536733478498012731028673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27382311304664016974704897 20536733478498012731028673)
              ·
                refine ⟨15402550108873509548271505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20536733478498012731028673 15402550108873509548271505)
                ·
                  refine ⟨11551912581655132161203629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15402550108873509548271505 11551912581655132161203629)
                  ·
                    refine ⟨4331967218120674560451361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11551912581655132161203629 4331967218120674560451361)
                    ·
                      refine ⟨3248975413590505920338521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4331967218120674560451361 3248975413590505920338521)
                      ·
                        rfl

theorem cell23_6327357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_6327357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327357 prefixEnd_6327357 := by exact prefixLift 6327357
  have htrace : WordTrace (prefixWord ++ tailWord_6327357) baseStart_6327357 baseEnd_6327357 := by
    simpa [prefixWord, tailWord_6327357, baseEnd_6327357] using wordTrace_append hprefix tailTrace_6327357
  have hstable : (prefixWord ++ tailWord_6327357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327357).length < 2 ^ (prefixWord ++ tailWord_6327357).sum := by decide
  have hdescent : baseEnd_6327357 < baseStart_6327357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327443 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 4]
def baseStart_6327443 : Nat := 118140960795 + 6327443 * 2 ^ 59
def prefixEnd_6327443 : Nat := 4983230072969 + 3 ^ 40 * 6327443 * 2
def baseEnd_6327443 : Nat := 3249019572926792583863125

theorem tailTrace_6327443 : CollatzResearch.WordTrace tailWord_6327443 prefixEnd_6327443 3249019572926792583863125 := by
  unfold tailWord_6327443
  simp only [CollatzResearch.WordTrace]
  refine ⟨230780805615762127075266983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153853870410508084716844655 230780805615762127075266983)
  ·
    refine ⟨346171208423643190612900475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230780805615762127075266983 346171208423643190612900475)
    ·
      refine ⟨519256812635464785919350713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346171208423643190612900475 519256812635464785919350713)
      ·
        refine ⟨389442609476598589439513035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 519256812635464785919350713 389442609476598589439513035)
        ·
          refine ⟨584163914214897884159269553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389442609476598589439513035 584163914214897884159269553)
          ·
            refine ⟨438122935661173413119452165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 584163914214897884159269553 438122935661173413119452165)
            ·
              refine ⟨82148050436470014959897281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 438122935661173413119452165 82148050436470014959897281)
              ·
                refine ⟨61611037827352511219922961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82148050436470014959897281 61611037827352511219922961)
                ·
                  refine ⟨46208278370514383414942221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61611037827352511219922961 46208278370514383414942221)
                  ·
                    refine ⟨17328104388942893780603333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46208278370514383414942221 17328104388942893780603333)
                    ·
                      refine ⟨3249019572926792583863125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17328104388942893780603333 3249019572926792583863125)
                      ·
                        rfl

theorem cell23_6327443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 4].length) (baseStart_6327443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327443 prefixEnd_6327443 := by exact prefixLift 6327443
  have htrace : WordTrace (prefixWord ++ tailWord_6327443) baseStart_6327443 baseEnd_6327443 := by
    simpa [prefixWord, tailWord_6327443, baseEnd_6327443] using wordTrace_append hprefix tailTrace_6327443
  have hstable : (prefixWord ++ tailWord_6327443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327443).length < 2 ^ (prefixWord ++ tailWord_6327443).sum := by decide
  have hdescent : baseEnd_6327443 < baseStart_6327443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327450 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5]
def baseStart_6327450 : Nat := 118140960795 + 6327450 * 2 ^ 59
def prefixEnd_6327450 : Nat := 4983230072969 + 3 ^ 40 * 6327450 * 2
def baseEnd_6327450 : Nat := 3249023167291374056475593

theorem tailTrace_6327450 : CollatzResearch.WordTrace tailWord_6327450 prefixEnd_6327450 3249023167291374056475593 := by
  unfold tailWord_6327450
  simp only [CollatzResearch.WordTrace]
  refine ⟨57695265231684191817692951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153854040617824511513847869 57695265231684191817692951)
  ·
    refine ⟨86542897847526287726539427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57695265231684191817692951 86542897847526287726539427)
    ·
      refine ⟨129814346771289431589809141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86542897847526287726539427 129814346771289431589809141)
      ·
        refine ⟨12170095009808384211544607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129814346771289431589809141 12170095009808384211544607)
        ·
          refine ⟨18255142514712576317316911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12170095009808384211544607 18255142514712576317316911)
          ·
            refine ⟨27382713772068864475975367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18255142514712576317316911 27382713772068864475975367)
            ·
              refine ⟨41074070658103296713963051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27382713772068864475975367 41074070658103296713963051)
              ·
                refine ⟨61611105987154945070944577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41074070658103296713963051 61611105987154945070944577)
                ·
                  refine ⟨46208329490366208803208433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61611105987154945070944577 46208329490366208803208433)
                  ·
                    refine ⟨34656247117774656602406325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46208329490366208803208433 34656247117774656602406325)
                    ·
                      refine ⟨3249023167291374056475593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34656247117774656602406325 3249023167291374056475593)
                      ·
                        rfl

theorem cell23_6327450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_6327450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327450 prefixEnd_6327450 := by exact prefixLift 6327450
  have htrace : WordTrace (prefixWord ++ tailWord_6327450) baseStart_6327450 baseEnd_6327450 := by
    simpa [prefixWord, tailWord_6327450, baseEnd_6327450] using wordTrace_append hprefix tailTrace_6327450
  have hstable : (prefixWord ++ tailWord_6327450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327450).length < 2 ^ (prefixWord ++ tailWord_6327450).sum := by decide
  have hdescent : baseEnd_6327450 < baseStart_6327450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327454 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_6327454 : Nat := 118140960795 + 6327454 * 2 ^ 59
def prefixEnd_6327454 : Nat := 4983230072969 + 3 ^ 40 * 6327454 * 2
def baseEnd_6327454 : Nat := 3249025221213992040825575

theorem tailTrace_6327454 : CollatzResearch.WordTrace tailWord_6327454 prefixEnd_6327454 3249025221213992040825575 := by
  unfold tailWord_6327454
  simp only [CollatzResearch.WordTrace]
  refine ⟨28847650852340284494239677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153854137879148183969278277 28847650852340284494239677)
  ·
    refine ⟨10817869069627606685339879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28847650852340284494239677 10817869069627606685339879)
    ·
      refine ⟨16226803604441410028009819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10817869069627606685339879 16226803604441410028009819)
      ·
        refine ⟨24340205406662115042014729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16226803604441410028009819 24340205406662115042014729)
        ·
          refine ⟨18255154054996586281511047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24340205406662115042014729 18255154054996586281511047)
          ·
            refine ⟨27382731082494879422266571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18255154054996586281511047 27382731082494879422266571)
            ·
              refine ⟨41074096623742319133399857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27382731082494879422266571 41074096623742319133399857)
              ·
                refine ⟨30805572467806739350049893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41074096623742319133399857 30805572467806739350049893)
                ·
                  refine ⟨5776044837713763628134355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30805572467806739350049893 5776044837713763628134355)
                  ·
                    refine ⟨8664067256570645442201533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5776044837713763628134355 8664067256570645442201533)
                    ·
                      refine ⟨3249025221213992040825575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8664067256570645442201533 3249025221213992040825575)
                      ·
                        rfl

theorem cell23_6327454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_6327454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327454 prefixEnd_6327454 := by exact prefixLift 6327454
  have htrace : WordTrace (prefixWord ++ tailWord_6327454) baseStart_6327454 baseEnd_6327454 := by
    simpa [prefixWord, tailWord_6327454, baseEnd_6327454] using wordTrace_append hprefix tailTrace_6327454
  have hstable : (prefixWord ++ tailWord_6327454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327454).length < 2 ^ (prefixWord ++ tailWord_6327454).sum := by decide
  have hdescent : baseEnd_6327454 < baseStart_6327454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327455 : List Nat := [1, 1, 2, 6, 3, 1, 1, 3, 1, 2, 2]
def baseStart_6327455 : Nat := 118140960795 + 6327455 * 2 ^ 59
def prefixEnd_6327455 : Nat := 4983230072969 + 3 ^ 40 * 6327455 * 2
def baseEnd_6327455 : Nat := 3249025734694646536913071

theorem tailTrace_6327455 : CollatzResearch.WordTrace tailWord_6327455 prefixEnd_6327455 3249025734694646536913071 := by
  unfold tailWord_6327455
  simp only [CollatzResearch.WordTrace]
  refine ⟨230781243291718653124703819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153854162194479102083135879 230781243291718653124703819)
  ·
    refine ⟨346171864937577979687055729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230781243291718653124703819 346171864937577979687055729)
    ·
      refine ⟨259628898703183484765291797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346171864937577979687055729 259628898703183484765291797)
      ·
        refine ⟨12170104626711725848373053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 259628898703183484765291797 12170104626711725848373053)
        ·
          refine ⟨4563789235016897193139895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12170104626711725848373053 4563789235016897193139895)
          ·
            refine ⟨6845683852525345789709843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4563789235016897193139895 6845683852525345789709843)
            ·
              refine ⟨10268525778788018684564765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6845683852525345789709843 10268525778788018684564765)
              ·
                refine ⟨3850697167045507006711787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10268525778788018684564765 3850697167045507006711787)
                ·
                  refine ⟨5776045750568260510067681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3850697167045507006711787 5776045750568260510067681)
                  ·
                    refine ⟨4332034312926195382550761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5776045750568260510067681 4332034312926195382550761)
                    ·
                      refine ⟨3249025734694646536913071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4332034312926195382550761 3249025734694646536913071)
                      ·
                        rfl

theorem cell23_6327455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_6327455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327455 prefixEnd_6327455 := by exact prefixLift 6327455
  have htrace : WordTrace (prefixWord ++ tailWord_6327455) baseStart_6327455 baseEnd_6327455 := by
    simpa [prefixWord, tailWord_6327455, baseEnd_6327455] using wordTrace_append hprefix tailTrace_6327455
  have hstable : (prefixWord ++ tailWord_6327455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327455).length < 2 ^ (prefixWord ++ tailWord_6327455).sum := by decide
  have hdescent : baseEnd_6327455 < baseStart_6327455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327483 : List Nat := [1, 1, 1, 1, 1, 2, 4, 5, 7]
def baseStart_6327483 : Nat := 118140960795 + 6327483 * 2 ^ 59
def prefixEnd_6327483 : Nat := 4983230072969 + 3 ^ 40 * 6327483 * 2
def baseEnd_6327483 : Nat := 361004456905885825262549

theorem tailTrace_6327483 : CollatzResearch.WordTrace tailWord_6327483 prefixEnd_6327483 361004456905885825262549 := by
  unfold tailWord_6327483
  simp only [CollatzResearch.WordTrace]
  refine ⟨230782264535617213906723103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153854843023744809271148735 230782264535617213906723103)
  ·
    refine ⟨346173396803425820860084655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230782264535617213906723103 346173396803425820860084655)
    ·
      refine ⟨519260095205138731290126983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346173396803425820860084655 519260095205138731290126983)
      ·
        refine ⟨778890142807708096935190475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519260095205138731290126983 778890142807708096935190475)
        ·
          refine ⟨1168335214211562145402785713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778890142807708096935190475 1168335214211562145402785713)
          ·
            refine ⟨876251410658671609052089285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1168335214211562145402785713 876251410658671609052089285)
            ·
              refine ⟨164297139498500926697266741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 876251410658671609052089285 164297139498500926697266741)
              ·
                refine ⟨15402856827984461877868757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164297139498500926697266741 15402856827984461877868757)
                ·
                  refine ⟨361004456905885825262549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15402856827984461877868757 361004456905885825262549)
                  ·
                    rfl

theorem cell23_6327483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 7].length) (baseStart_6327483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327483 prefixEnd_6327483 := by exact prefixLift 6327483
  have htrace : WordTrace (prefixWord ++ tailWord_6327483) baseStart_6327483 baseEnd_6327483 := by
    simpa [prefixWord, tailWord_6327483, baseEnd_6327483] using wordTrace_append hprefix tailTrace_6327483
  have hstable : (prefixWord ++ tailWord_6327483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327483).length < 2 ^ (prefixWord ++ tailWord_6327483).sum := by decide
  have hdescent : baseEnd_6327483 < baseStart_6327483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327488 : List Nat := [2, 1, 1, 2, 7, 1, 2, 1, 2, 1, 3]
def baseStart_6327488 : Nat := 118140960795 + 6327488 * 2 ^ 59
def prefixEnd_6327488 : Nat := 4983230072969 + 3 ^ 40 * 6327488 * 2
def baseEnd_6327488 : Nat := 3249042679556244907800419

theorem tailTrace_6327488 : CollatzResearch.WordTrace tailWord_6327488 prefixEnd_6327488 3249042679556244907800419 := by
  unfold tailWord_6327488
  simp only [CollatzResearch.WordTrace]
  refine ⟨115391223450299549880327559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153854964600399399840436745 115391223450299549880327559)
  ·
    refine ⟨173086835175449324820491339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115391223450299549880327559 173086835175449324820491339)
    ·
      refine ⟨259630252763173987230737009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173086835175449324820491339 259630252763173987230737009)
      ·
        refine ⟨194722689572380490423052757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259630252763173987230737009 194722689572380490423052757)
        ·
          refine ⟨4563813036852667744290299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 194722689572380490423052757 4563813036852667744290299)
          ·
            refine ⟨6845719555279001616435449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4563813036852667744290299 6845719555279001616435449)
            ·
              refine ⟨5134289666459251212326587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6845719555279001616435449 5134289666459251212326587)
              ·
                refine ⟨7701434499688876818489881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5134289666459251212326587 7701434499688876818489881)
                ·
                  refine ⟨5776075874766657613867411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7701434499688876818489881 5776075874766657613867411)
                  ·
                    refine ⟨8664113812149986420801117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5776075874766657613867411 8664113812149986420801117)
                    ·
                      refine ⟨3249042679556244907800419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8664113812149986420801117 3249042679556244907800419)
                      ·
                        rfl

theorem cell23_6327488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 2, 1, 3].length) (baseStart_6327488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327488 prefixEnd_6327488 := by exact prefixLift 6327488
  have htrace : WordTrace (prefixWord ++ tailWord_6327488) baseStart_6327488 baseEnd_6327488 := by
    simpa [prefixWord, tailWord_6327488, baseEnd_6327488] using wordTrace_append hprefix tailTrace_6327488
  have hstable : (prefixWord ++ tailWord_6327488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327488).length < 2 ^ (prefixWord ++ tailWord_6327488).sum := by decide
  have hdescent : baseEnd_6327488 < baseStart_6327488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327534 : List Nat := [4, 1, 2, 1, 1, 1, 6, 2, 5]
def baseStart_6327534 : Nat := 118140960795 + 6327534 * 2 ^ 59
def prefixEnd_6327534 : Nat := 4983230072969 + 3 ^ 40 * 6327534 * 2
def baseEnd_6327534 : Nat := 361007366629594636425023

theorem tailTrace_6327534 : CollatzResearch.WordTrace tailWord_6327534 prefixEnd_6327534 361007366629594636425023 := by
  unfold tailWord_6327534
  simp only [CollatzResearch.WordTrace]
  refine ⟨28848015582304056202103707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153856083105621633077886437 28848015582304056202103707)
  ·
    refine ⟨43272023373456084303155561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28848015582304056202103707 43272023373456084303155561)
    ·
      refine ⟨32454017530092063227366671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43272023373456084303155561 32454017530092063227366671)
      ·
        refine ⟨48681026295138094841050007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32454017530092063227366671 48681026295138094841050007)
        ·
          refine ⟨73021539442707142261575011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48681026295138094841050007 73021539442707142261575011)
          ·
            refine ⟨109532309164060713392362517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73021539442707142261575011 109532309164060713392362517)
            ·
              refine ⟨5134326992065345940266993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109532309164060713392362517 5134326992065345940266993)
              ·
                refine ⟨3850745244049009455200245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5134326992065345940266993 3850745244049009455200245)
                ·
                  refine ⟨361007366629594636425023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3850745244049009455200245 361007366629594636425023)
                  ·
                    rfl

theorem cell23_6327534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_6327534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327534 prefixEnd_6327534 := by exact prefixLift 6327534
  have htrace : WordTrace (prefixWord ++ tailWord_6327534) baseStart_6327534 baseEnd_6327534 := by
    simpa [prefixWord, tailWord_6327534, baseEnd_6327534] using wordTrace_append hprefix tailTrace_6327534
  have hstable : (prefixWord ++ tailWord_6327534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327534).length < 2 ^ (prefixWord ++ tailWord_6327534).sum := by decide
  have hdescent : baseEnd_6327534 < baseStart_6327534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327580 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_6327580 : Nat := 118140960795 + 6327580 * 2 ^ 59
def prefixEnd_6327580 : Nat := 4983230072969 + 3 ^ 40 * 6327580 * 2
def baseEnd_6327580 : Nat := 3249089919776458547849995

theorem tailTrace_6327580 : CollatzResearch.WordTrace tailWord_6327580 prefixEnd_6327580 3249089919776458547849995 := by
  unfold tailWord_6327580
  simp only [CollatzResearch.WordTrace]
  refine ⟨115392901208132899736502097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153857201610843866315336129 115392901208132899736502097)
  ·
    refine ⟨86544675906099674802376573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115392901208132899736502097 86544675906099674802376573)
    ·
      refine ⟨32454253464787378050891215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86544675906099674802376573 32454253464787378050891215)
      ·
        refine ⟨48681380197181067076336823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32454253464787378050891215 48681380197181067076336823)
        ·
          refine ⟨73022070295771600614505235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48681380197181067076336823 73022070295771600614505235)
          ·
            refine ⟨109533105443657400921757853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73022070295771600614505235 109533105443657400921757853)
            ·
              refine ⟨41074914541371525345659195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109533105443657400921757853 41074914541371525345659195)
              ·
                refine ⟨61612371812057288018488793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41074914541371525345659195 61612371812057288018488793)
                ·
                  refine ⟨46209278859042966013866595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61612371812057288018488793 46209278859042966013866595)
                  ·
                    refine ⟨69313918288564449020799893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46209278859042966013866595 69313918288564449020799893)
                    ·
                      refine ⟨3249089919776458547849995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69313918288564449020799893 3249089919776458547849995)
                      ·
                        rfl

theorem cell23_6327580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_6327580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327580 prefixEnd_6327580 := by exact prefixLift 6327580
  have htrace : WordTrace (prefixWord ++ tailWord_6327580) baseStart_6327580 baseEnd_6327580 := by
    simpa [prefixWord, tailWord_6327580, baseEnd_6327580] using wordTrace_append hprefix tailTrace_6327580
  have hstable : (prefixWord ++ tailWord_6327580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327580).length < 2 ^ (prefixWord ++ tailWord_6327580).sum := by decide
  have hdescent : baseEnd_6327580 < baseStart_6327580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327594 : List Nat := [3, 1, 4, 2, 1, 1, 1, 3, 3, 4]
def baseStart_6327594 : Nat := 118140960795 + 6327594 * 2 ^ 59
def prefixEnd_6327594 : Nat := 4983230072969 + 3 ^ 40 * 6327594 * 2
def baseEnd_6327594 : Nat := 1083032369501873831024977

theorem tailTrace_6327594 : CollatzResearch.WordTrace tailWord_6327594 prefixEnd_6327594 1083032369501873831024977 := by
  unfold tailWord_6327594
  simp only [CollatzResearch.WordTrace]
  refine ⟨57696578259553769966003459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153857542025476719909342557 57696578259553769966003459)
  ·
    refine ⟨86544867389330654949005189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57696578259553769966003459 86544867389330654949005189)
    ·
      refine ⟨16227162635499497802938473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86544867389330654949005189 16227162635499497802938473)
      ·
        refine ⟨12170371976624623352203855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16227162635499497802938473 12170371976624623352203855)
        ·
          refine ⟨18255557964936935028305783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12170371976624623352203855 18255557964936935028305783)
          ·
            refine ⟨27383336947405402542458675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18255557964936935028305783 27383336947405402542458675)
            ·
              refine ⟨41075005421108103813688013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27383336947405402542458675 41075005421108103813688013)
              ·
                refine ⟨15403127032915538930133005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41075005421108103813688013 15403127032915538930133005)
                ·
                  refine ⟨5776172637343327098799877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15403127032915538930133005 5776172637343327098799877)
                  ·
                    refine ⟨1083032369501873831024977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5776172637343327098799877 1083032369501873831024977)
                    ·
                      rfl

theorem cell23_6327594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_6327594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327594 prefixEnd_6327594 := by exact prefixLift 6327594
  have htrace : WordTrace (prefixWord ++ tailWord_6327594) baseStart_6327594 baseEnd_6327594 := by
    simpa [prefixWord, tailWord_6327594, baseEnd_6327594] using wordTrace_append hprefix tailTrace_6327594
  have hstable : (prefixWord ++ tailWord_6327594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327594).length < 2 ^ (prefixWord ++ tailWord_6327594).sum := by decide
  have hdescent : baseEnd_6327594 < baseStart_6327594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327610 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6]
def baseStart_6327610 : Nat := 118140960795 + 6327610 * 2 ^ 59
def prefixEnd_6327610 : Nat := 4983230072969 + 3 ^ 40 * 6327610 * 2
def baseEnd_6327610 : Nat := 3249105324196093430474857

theorem tailTrace_6327610 : CollatzResearch.WordTrace tailWord_6327610 prefixEnd_6327610 3249105324196093430474857 := by
  unfold tailWord_6327610
  simp only [CollatzResearch.WordTrace]
  refine ⟨57696724151539278649149071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153857931070771409731064189 57696724151539278649149071)
  ·
    refine ⟨86545086227308917973723607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57696724151539278649149071 86545086227308917973723607)
    ·
      refine ⟨129817629340963376960585411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86545086227308917973723607 129817629340963376960585411)
      ·
        refine ⟨194726444011445065440878117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129817629340963376960585411 194726444011445065440878117)
        ·
          refine ⟨36511208252145949770164647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194726444011445065440878117 36511208252145949770164647)
          ·
            refine ⟨54766812378218924655246971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36511208252145949770164647 54766812378218924655246971)
            ·
              refine ⟨82150218567328386982870457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54766812378218924655246971 82150218567328386982870457)
              ·
                refine ⟨61612663925496290237152843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82150218567328386982870457 61612663925496290237152843)
                ·
                  refine ⟨92418995888244435355729265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61612663925496290237152843 92418995888244435355729265)
                  ·
                    refine ⟨69314246916183326516796949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92418995888244435355729265 69314246916183326516796949)
                    ·
                      refine ⟨3249105324196093430474857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69314246916183326516796949 3249105324196093430474857)
                      ·
                        rfl

theorem cell23_6327610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_6327610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327610 prefixEnd_6327610 := by exact prefixLift 6327610
  have htrace : WordTrace (prefixWord ++ tailWord_6327610) baseStart_6327610 baseEnd_6327610 := by
    simpa [prefixWord, tailWord_6327610, baseEnd_6327610] using wordTrace_append hprefix tailTrace_6327610
  have hstable : (prefixWord ++ tailWord_6327610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327610).length < 2 ^ (prefixWord ++ tailWord_6327610).sum := by decide
  have hdescent : baseEnd_6327610 < baseStart_6327610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327645 : List Nat := [1, 4, 5, 1, 1, 2, 1, 1, 3, 4]
def baseStart_6327645 : Nat := 118140960795 + 6327645 * 2 ^ 59
def prefixEnd_6327645 : Nat := 4983230072969 + 3 ^ 40 * 6327645 * 2
def baseEnd_6327645 : Nat := 1083041098673000264512399

theorem tailTrace_6327645 : CollatzResearch.WordTrace tailWord_6327645 prefixEnd_6327645 1083041098673000264512399 := by
  unfold tailWord_6327645
  simp only [CollatzResearch.WordTrace]
  refine ⟨230788173161030315574120389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153858782107353543716080259 230788173161030315574120389)
  ·
    refine ⟨43272782467693184170147573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230788173161030315574120389 43272782467693184170147573)
    ·
      refine ⟨4056823356346236015951335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43272782467693184170147573 4056823356346236015951335)
      ·
        refine ⟨6085235034519354023927003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4056823356346236015951335 6085235034519354023927003)
        ·
          refine ⟨9127852551779031035890505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6085235034519354023927003 9127852551779031035890505)
          ·
            refine ⟨6845889413834273276917879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9127852551779031035890505 6845889413834273276917879)
            ·
              refine ⟨10268834120751409915376819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6845889413834273276917879 10268834120751409915376819)
              ·
                refine ⟨15403251181127114873065229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10268834120751409915376819 15403251181127114873065229)
                ·
                  refine ⟨5776219192922668077399461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15403251181127114873065229 5776219192922668077399461)
                  ·
                    refine ⟨1083041098673000264512399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5776219192922668077399461 1083041098673000264512399)
                    ·
                      rfl

theorem cell23_6327645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_6327645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327645 prefixEnd_6327645 := by exact prefixLift 6327645
  have htrace : WordTrace (prefixWord ++ tailWord_6327645) baseStart_6327645 baseEnd_6327645 := by
    simpa [prefixWord, tailWord_6327645, baseEnd_6327645] using wordTrace_append hprefix tailTrace_6327645
  have hstable : (prefixWord ++ tailWord_6327645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327645).length < 2 ^ (prefixWord ++ tailWord_6327645).sum := by decide
  have hdescent : baseEnd_6327645 < baseStart_6327645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327651 : List Nat := [1, 1, 1, 5, 2, 4, 1, 1, 3, 1, 3]
def baseStart_6327651 : Nat := 118140960795 + 6327651 * 2 ^ 59
def prefixEnd_6327651 : Nat := 4983230072969 + 3 ^ 40 * 6327651 * 2
def baseEnd_6327651 : Nat := 3249126376902927770062169

theorem tailTrace_6327651 : CollatzResearch.WordTrace tailWord_6327651 prefixEnd_6327651 3249126376902927770062169 := by
  unfold tailWord_6327651
  simp only [CollatzResearch.WordTrace]
  refine ⟨230788391999008578598838807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153858927999339052399225871 230788391999008578598838807)
  ·
    refine ⟨346182587998512867898258211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230788391999008578598838807 346182587998512867898258211)
    ·
      refine ⟨519273881997769301847387317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346182587998512867898258211 519273881997769301847387317)
      ·
        refine ⟨48681926437290872048192561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 519273881997769301847387317 48681926437290872048192561)
        ·
          refine ⟨36511444827968154036144421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48681926437290872048192561 36511444827968154036144421)
          ·
            refine ⟨6845895905244028881777079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36511444827968154036144421 6845895905244028881777079)
            ·
              refine ⟨10268843857866043322665619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6845895905244028881777079 10268843857866043322665619)
              ·
                refine ⟨15403265786799064983998429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10268843857866043322665619 15403265786799064983998429)
                ·
                  refine ⟨5776224670049649368999411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15403265786799064983998429 5776224670049649368999411)
                  ·
                    refine ⟨8664337005074474053499117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5776224670049649368999411 8664337005074474053499117)
                    ·
                      refine ⟨3249126376902927770062169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8664337005074474053499117 3249126376902927770062169)
                      ·
                        rfl

theorem cell23_6327651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_6327651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327651 prefixEnd_6327651 := by exact prefixLift 6327651
  have htrace : WordTrace (prefixWord ++ tailWord_6327651) baseStart_6327651 baseEnd_6327651 := by
    simpa [prefixWord, tailWord_6327651, baseEnd_6327651] using wordTrace_append hprefix tailTrace_6327651
  have hstable : (prefixWord ++ tailWord_6327651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327651).length < 2 ^ (prefixWord ++ tailWord_6327651).sum := by decide
  have hdescent : baseEnd_6327651 < baseStart_6327651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327657 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 2, 6, 2]
def baseStart_6327657 : Nat := 118140960795 + 6327657 * 2 ^ 59
def prefixEnd_6327657 : Nat := 4983230072969 + 3 ^ 40 * 6327657 * 2
def baseEnd_6327657 : Nat := 3249129457786854746587141

theorem tailTrace_6327657 : CollatzResearch.WordTrace tailWord_6327657 prefixEnd_6327657 3249129457786854746587141 := by
  unfold tailWord_6327657
  simp only [CollatzResearch.WordTrace]
  refine ⟨230788610836986841623557225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153859073891324561082371483 230788610836986841623557225)
  ·
    refine ⟨173091458127740131217667919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230788610836986841623557225 173091458127740131217667919)
    ·
      refine ⟨259637187191610196826501879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173091458127740131217667919 259637187191610196826501879)
      ·
        refine ⟨389455780787415295239752819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259637187191610196826501879 389455780787415295239752819)
        ·
          refine ⟨584183671181122942859629229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389455780787415295239752819 584183671181122942859629229)
          ·
            refine ⟨219068876692921103572360961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 584183671181122942859629229 219068876692921103572360961)
            ·
              refine ⟨164301657519690827679270721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219068876692921103572360961 164301657519690827679270721)
              ·
                refine ⟨123226243139768120759453041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164301657519690827679270721 123226243139768120759453041)
                ·
                  refine ⟨92419682354826090569589781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123226243139768120759453041 92419682354826090569589781)
                  ·
                    refine ⟨4332172610382472995449521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92419682354826090569589781 4332172610382472995449521)
                    ·
                      refine ⟨3249129457786854746587141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4332172610382472995449521 3249129457786854746587141)
                      ·
                        rfl

theorem cell23_6327657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 6, 2].length) (baseStart_6327657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327657 prefixEnd_6327657 := by exact prefixLift 6327657
  have htrace : WordTrace (prefixWord ++ tailWord_6327657) baseStart_6327657 baseEnd_6327657 := by
    simpa [prefixWord, tailWord_6327657, baseEnd_6327657] using wordTrace_append hprefix tailTrace_6327657
  have hstable : (prefixWord ++ tailWord_6327657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327657).length < 2 ^ (prefixWord ++ tailWord_6327657).sum := by decide
  have hdescent : baseEnd_6327657 < baseStart_6327657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327658 : List Nat := [3, 1, 3, 3, 3, 1, 2, 1, 6]
def baseStart_6327658 : Nat := 118140960795 + 6327658 * 2 ^ 59
def prefixEnd_6327658 : Nat := 4983230072969 + 3 ^ 40 * 6327658 * 2
def baseEnd_6327658 : Nat := 361014441251945471408293

theorem tailTrace_6327658 : CollatzResearch.WordTrace tailWord_6327658 prefixEnd_6327658 361014441251945471408293 := by
  unfold tailWord_6327658
  simp only [CollatzResearch.WordTrace]
  refine ⟨57697161827495804698585907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153859098206655479196229085 57697161827495804698585907)
  ·
    refine ⟨86545742741243707047878861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57697161827495804698585907 86545742741243707047878861)
    ·
      refine ⟨32454653527966390142954573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86545742741243707047878861 32454653527966390142954573)
      ·
        refine ⟨12170495072987396303607965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32454653527966390142954573 12170495072987396303607965)
        ·
          refine ⟨4563935652370273613852987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12170495072987396303607965 4563935652370273613852987)
          ·
            refine ⟨6845903478555410420779481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4563935652370273613852987 6845903478555410420779481)
            ·
              refine ⟨5134427608916557815584611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6845903478555410420779481 5134427608916557815584611)
              ·
                refine ⟨7701641413374836723376917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5134427608916557815584611 7701641413374836723376917)
                ·
                  refine ⟨361014441251945471408293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7701641413374836723376917 361014441251945471408293)
                  ·
                    rfl

theorem cell23_6327658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 6].length) (baseStart_6327658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327658 prefixEnd_6327658 := by exact prefixLift 6327658
  have htrace : WordTrace (prefixWord ++ tailWord_6327658) baseStart_6327658 baseEnd_6327658 := by
    simpa [prefixWord, tailWord_6327658, baseEnd_6327658] using wordTrace_append hprefix tailTrace_6327658
  have hstable : (prefixWord ++ tailWord_6327658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327658).length < 2 ^ (prefixWord ++ tailWord_6327658).sum := by decide
  have hdescent : baseEnd_6327658 < baseStart_6327658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327687 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 4]
def baseStart_6327687 : Nat := 118140960795 + 6327687 * 2 ^ 59
def prefixEnd_6327687 : Nat := 4983230072969 + 3 ^ 40 * 6327687 * 2
def baseEnd_6327687 : Nat := 3249144862206489629212003

theorem tailTrace_6327687 : CollatzResearch.WordTrace tailWord_6327687 prefixEnd_6327687 3249144862206489629212003 := by
  unfold tailWord_6327687
  simp only [CollatzResearch.WordTrace]
  refine ⟨230789705026878156747149315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153859803351252104498099543 230789705026878156747149315)
  ·
    refine ⟨346184557540317235120723973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230789705026878156747149315 346184557540317235120723973)
    ·
      refine ⟨64909604538809481585135745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346184557540317235120723973 64909604538809481585135745)
      ·
        refine ⟨48682203404107111188851809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64909604538809481585135745 48682203404107111188851809)
        ·
          refine ⟨36511652553080333391638857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48682203404107111188851809 36511652553080333391638857)
          ·
            refine ⟨27383739414810250043729143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36511652553080333391638857 27383739414810250043729143)
            ·
              refine ⟨41075609122215375065593715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27383739414810250043729143 41075609122215375065593715)
              ·
                refine ⟨61613413683323062598390573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41075609122215375065593715 61613413683323062598390573)
                ·
                  refine ⟨23105030131246148474396465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61613413683323062598390573 23105030131246148474396465)
                  ·
                    refine ⟨17328772598434611355797349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23105030131246148474396465 17328772598434611355797349)
                    ·
                      refine ⟨3249144862206489629212003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17328772598434611355797349 3249144862206489629212003)
                      ·
                        rfl

theorem cell23_6327687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_6327687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327687 prefixEnd_6327687 := by exact prefixLift 6327687
  have htrace : WordTrace (prefixWord ++ tailWord_6327687) baseStart_6327687 baseEnd_6327687 := by
    simpa [prefixWord, tailWord_6327687, baseEnd_6327687] using wordTrace_append hprefix tailTrace_6327687
  have hstable : (prefixWord ++ tailWord_6327687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327687).length < 2 ^ (prefixWord ++ tailWord_6327687).sum := by decide
  have hdescent : baseEnd_6327687 < baseStart_6327687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327714 : List Nat := [3, 3, 1, 2, 1, 4, 1, 8]
def baseStart_6327714 : Nat := 118140960795 + 6327714 * 2 ^ 59
def prefixEnd_6327714 : Nat := 4983230072969 + 3 ^ 40 * 6327714 * 2
def baseEnd_6327714 : Nat := 120339212080894852724977

theorem tailTrace_6327714 : CollatzResearch.WordTrace tailWord_6327714 prefixEnd_6327714 120339212080894852724977 := by
  unfold tailWord_6327714
  simp only [CollatzResearch.WordTrace]
  refine ⟨57697672449445085089595549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153860459865186893572254797 57697672449445085089595549)
  ·
    refine ⟨21636627168541906908598331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57697672449445085089595549 21636627168541906908598331)
    ·
      refine ⟨32454940752812860362897497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21636627168541906908598331 32454940752812860362897497)
      ·
        refine ⟨24341205564609645272173123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32454940752812860362897497 24341205564609645272173123)
        ·
          refine ⟨36511808346914467908259685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24341205564609645272173123 36511808346914467908259685)
          ·
            refine ⟨6845964065046462732798691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36511808346914467908259685 6845964065046462732798691)
            ·
              refine ⟨10268946097569694099198037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6845964065046462732798691 10268946097569694099198037)
              ·
                refine ⟨120339212080894852724977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10268946097569694099198037 120339212080894852724977)
                ·
                  rfl

theorem cell23_6327714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 8].length) (baseStart_6327714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327714 prefixEnd_6327714 := by exact prefixLift 6327714
  have htrace : WordTrace (prefixWord ++ tailWord_6327714) baseStart_6327714 baseEnd_6327714 := by
    simpa [prefixWord, tailWord_6327714, baseEnd_6327714] using wordTrace_append hprefix tailTrace_6327714
  have hstable : (prefixWord ++ tailWord_6327714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327714).length < 2 ^ (prefixWord ++ tailWord_6327714).sum := by decide
  have hdescent : baseEnd_6327714 < baseStart_6327714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327751 : List Nat := [1, 1, 4, 1, 1, 3, 3, 3, 1, 3, 2]
def baseStart_6327751 : Nat := 118140960795 + 6327751 * 2 ^ 59
def prefixEnd_6327751 : Nat := 4983230072969 + 3 ^ 40 * 6327751 * 2
def baseEnd_6327751 : Nat := 3249177724968377378811709

theorem tailTrace_6327751 : CollatzResearch.WordTrace tailWord_6327751 prefixEnd_6327751 3249177724968377378811709 := by
  unfold tailWord_6327751
  simp only [CollatzResearch.WordTrace]
  refine ⟨230792039298646295677479107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153861359532430863784986071 230792039298646295677479107)
  ·
    refine ⟨346188058947969443516218661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230792039298646295677479107 346188058947969443516218661)
    ·
      refine ⟨64910261052744270659290999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346188058947969443516218661 64910261052744270659290999)
      ·
        refine ⟨97365391579116405988936499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64910261052744270659290999 97365391579116405988936499)
        ·
          refine ⟨146048087368674608983404749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97365391579116405988936499 146048087368674608983404749)
          ·
            refine ⟨54768032763252978368776781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146048087368674608983404749 54768032763252978368776781)
            ·
              refine ⟨20538012286219866888291293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54768032763252978368776781 20538012286219866888291293)
              ·
                refine ⟨7701754607332450083109235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20538012286219866888291293 7701754607332450083109235)
                ·
                  refine ⟨11552631910998675124663853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7701754607332450083109235 11552631910998675124663853)
                  ·
                    refine ⟨4332236966624503171748945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11552631910998675124663853 4332236966624503171748945)
                    ·
                      refine ⟨3249177724968377378811709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4332236966624503171748945 3249177724968377378811709)
                      ·
                        rfl

theorem cell23_6327751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 3, 2].length) (baseStart_6327751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327751 prefixEnd_6327751 := by exact prefixLift 6327751
  have htrace : WordTrace (prefixWord ++ tailWord_6327751) baseStart_6327751 baseEnd_6327751 := by
    simpa [prefixWord, tailWord_6327751, baseEnd_6327751] using wordTrace_append hprefix tailTrace_6327751
  have hstable : (prefixWord ++ tailWord_6327751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327751).length < 2 ^ (prefixWord ++ tailWord_6327751).sum := by decide
  have hdescent : baseEnd_6327751 < baseStart_6327751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327767 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 3]
def baseStart_6327767 : Nat := 118140960795 + 6327767 * 2 ^ 59
def prefixEnd_6327767 : Nat := 4983230072969 + 3 ^ 40 * 6327767 * 2
def baseEnd_6327767 : Nat := 3249185940658849316211635

theorem tailTrace_6327767 : CollatzResearch.WordTrace tailWord_6327767 prefixEnd_6327767 3249185940658849316211635 := by
  unfold tailWord_6327767
  simp only [CollatzResearch.WordTrace]
  refine ⟨230792622866588330410061555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153861748577725553606707703 230792622866588330410061555)
  ·
    refine ⟨346188934299882495615092333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230792622866588330410061555 346188934299882495615092333)
    ·
      refine ⟨129820850362455935855659625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346188934299882495615092333 129820850362455935855659625)
      ·
        refine ⟨97365637771841951891744719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129820850362455935855659625 97365637771841951891744719)
        ·
          refine ⟨146048456657762927837617079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97365637771841951891744719 146048456657762927837617079)
          ·
            refine ⟨219072684986644391756425619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146048456657762927837617079 219072684986644391756425619)
            ·
              refine ⟨328609027479966587634638429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219072684986644391756425619 328609027479966587634638429)
              ·
                refine ⟨123228385304987470362989411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 328609027479966587634638429 123228385304987470362989411)
                ·
                  refine ⟨184842577957481205544484117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123228385304987470362989411 184842577957481205544484117)
                  ·
                    refine ⟨8664495841756931509897693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 184842577957481205544484117 8664495841756931509897693)
                    ·
                      refine ⟨3249185940658849316211635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8664495841756931509897693 3249185940658849316211635)
                      ·
                        rfl

theorem cell23_6327767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_6327767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327767 prefixEnd_6327767 := by exact prefixLift 6327767
  have htrace : WordTrace (prefixWord ++ tailWord_6327767) baseStart_6327767 baseEnd_6327767 := by
    simpa [prefixWord, tailWord_6327767, baseEnd_6327767] using wordTrace_append hprefix tailTrace_6327767
  have hstable : (prefixWord ++ tailWord_6327767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327767).length < 2 ^ (prefixWord ++ tailWord_6327767).sum := by decide
  have hdescent : baseEnd_6327767 < baseStart_6327767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327798 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2]
def baseStart_6327798 : Nat := 118140960795 + 6327798 * 2 ^ 59
def prefixEnd_6327798 : Nat := 4983230072969 + 3 ^ 40 * 6327798 * 2
def baseEnd_6327798 : Nat := 3249201858559138694923993

theorem tailTrace_6327798 : CollatzResearch.WordTrace tailWord_6327798 prefixEnd_6327798 3249201858559138694923993 := by
  unfold tailWord_6327798
  simp only [CollatzResearch.WordTrace]
  refine ⟨14424609595592251419027503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153862502352984015136293365 14424609595592251419027503)
  ·
    refine ⟨21636914393388377128541255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14424609595592251419027503 21636914393388377128541255)
    ·
      refine ⟨32455371590082565692811883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21636914393388377128541255 32455371590082565692811883)
      ·
        refine ⟨48683057385123848539217825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32455371590082565692811883 48683057385123848539217825)
        ·
          refine ⟨36512293038842886404413369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48683057385123848539217825 36512293038842886404413369)
          ·
            refine ⟨27384219779132164803310027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36512293038842886404413369 27384219779132164803310027)
            ·
              refine ⟨41076329668698247204965041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27384219779132164803310027 41076329668698247204965041)
              ·
                refine ⟨30807247251523685403723781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41076329668698247204965041 30807247251523685403723781)
                ·
                  refine ⟨5776358859660691013198209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30807247251523685403723781 5776358859660691013198209)
                  ·
                    refine ⟨4332269144745518259898657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5776358859660691013198209 4332269144745518259898657)
                    ·
                      refine ⟨3249201858559138694923993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4332269144745518259898657 3249201858559138694923993)
                      ·
                        rfl

theorem cell23_6327798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_6327798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327798 prefixEnd_6327798 := by exact prefixLift 6327798
  have htrace : WordTrace (prefixWord ++ tailWord_6327798) baseStart_6327798 baseEnd_6327798 := by
    simpa [prefixWord, tailWord_6327798, baseEnd_6327798] using wordTrace_append hprefix tailTrace_6327798
  have hstable : (prefixWord ++ tailWord_6327798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327798).length < 2 ^ (prefixWord ++ tailWord_6327798).sum := by decide
  have hdescent : baseEnd_6327798 < baseStart_6327798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327827 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 7]
def baseStart_6327827 : Nat := 118140960795 + 6327827 * 2 ^ 59
def prefixEnd_6327827 : Nat := 4983230072969 + 3 ^ 40 * 6327827 * 2
def baseEnd_6327827 : Nat := 3249216749498119081461359

theorem tailTrace_6327827 : CollatzResearch.WordTrace tailWord_6327827 prefixEnd_6327827 3249216749498119081461359 := by
  unfold tailWord_6327827
  simp only [CollatzResearch.WordTrace]
  refine ⟨230794811246370960657245735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153863207497580640438163823 230794811246370960657245735)
  ·
    refine ⟨346192216869556440985868603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230794811246370960657245735 346192216869556440985868603)
    ·
      refine ⟨519288325304334661478802905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346192216869556440985868603 519288325304334661478802905)
      ·
        refine ⟨389466243978250996109102179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 519288325304334661478802905 389466243978250996109102179)
        ·
          refine ⟨584199365967376494163653269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389466243978250996109102179 584199365967376494163653269)
          ·
            refine ⟨27384345279720773163921247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 584199365967376494163653269 27384345279720773163921247)
            ·
              refine ⟨41076517919581159745881871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27384345279720773163921247 41076517919581159745881871)
              ·
                refine ⟨61614776879371739618822807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41076517919581159745881871 61614776879371739618822807)
                ·
                  refine ⟨92422165319057609428234211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61614776879371739618822807 92422165319057609428234211)
                  ·
                    refine ⟨138633247978586414142351317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92422165319057609428234211 138633247978586414142351317)
                    ·
                      refine ⟨3249216749498119081461359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 138633247978586414142351317 3249216749498119081461359)
                      ·
                        rfl

theorem cell23_6327827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 7].length) (baseStart_6327827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327827 prefixEnd_6327827 := by exact prefixLift 6327827
  have htrace : WordTrace (prefixWord ++ tailWord_6327827) baseStart_6327827 baseEnd_6327827 := by
    simpa [prefixWord, tailWord_6327827, baseEnd_6327827] using wordTrace_append hprefix tailTrace_6327827
  have hstable : (prefixWord ++ tailWord_6327827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327827).length < 2 ^ (prefixWord ++ tailWord_6327827).sum := by decide
  have hdescent : baseEnd_6327827 < baseStart_6327827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327832 : List Nat := [2, 1, 2, 3, 4, 2, 2, 1, 2, 2, 2]
def baseStart_6327832 : Nat := 118140960795 + 6327832 * 2 ^ 59
def prefixEnd_6327832 : Nat := 4983230072969 + 3 ^ 40 * 6327832 * 2
def baseEnd_6327832 : Nat := 3249219316901391561898837

theorem tailTrace_6327832 : CollatzResearch.WordTrace tailWord_6327832 prefixEnd_6327832 3249219316901391561898837 := by
  unfold tailWord_6327832
  simp only [CollatzResearch.WordTrace]
  refine ⟨115397496805676423255588875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153863329074235231007451833 115397496805676423255588875)
  ·
    refine ⟨173096245208514634883383313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115397496805676423255588875 173096245208514634883383313)
    ·
      refine ⟨129822183906385976162537485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173096245208514634883383313 129822183906385976162537485)
      ·
        refine ⟨48683318964894741060951557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129822183906385976162537485 48683318964894741060951557)
        ·
          refine ⟨9128122305917763948928417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48683318964894741060951557 9128122305917763948928417)
          ·
            refine ⟨6846091729438322961696313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9128122305917763948928417 6846091729438322961696313)
            ·
              refine ⟨5134568797078742221272235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6846091729438322961696313 5134568797078742221272235)
              ·
                refine ⟨7701853195618113331908353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5134568797078742221272235 7701853195618113331908353)
                ·
                  refine ⟨5776389896713584998931265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7701853195618113331908353 5776389896713584998931265)
                  ·
                    refine ⟨4332292422535188749198449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5776389896713584998931265 4332292422535188749198449)
                    ·
                      refine ⟨3249219316901391561898837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4332292422535188749198449 3249219316901391561898837)
                      ·
                        rfl

theorem cell23_6327832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_6327832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327832 prefixEnd_6327832 := by exact prefixLift 6327832
  have htrace : WordTrace (prefixWord ++ tailWord_6327832) baseStart_6327832 baseEnd_6327832 := by
    simpa [prefixWord, tailWord_6327832, baseEnd_6327832] using wordTrace_append hprefix tailTrace_6327832
  have hstable : (prefixWord ++ tailWord_6327832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327832).length < 2 ^ (prefixWord ++ tailWord_6327832).sum := by decide
  have hdescent : baseEnd_6327832 < baseStart_6327832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327908 : List Nat := [2, 3, 1, 1, 2, 5, 1, 1, 2, 2, 3]
def baseStart_6327908 : Nat := 118140960795 + 6327908 * 2 ^ 59
def prefixEnd_6327908 : Nat := 4983230072969 + 3 ^ 40 * 6327908 * 2
def baseEnd_6327908 : Nat := 3249258341431133264548487

theorem tailTrace_6327908 : CollatzResearch.WordTrace tailWord_6327908 prefixEnd_6327908 3249258341431133264548487 := by
  unfold tailWord_6327908
  simp only [CollatzResearch.WordTrace]
  refine ⟨115398882779538755745472189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153865177039385007660629585 115398882779538755745472189)
  ·
    refine ⟨43274581042327033404552071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115398882779538755745472189 43274581042327033404552071)
    ·
      refine ⟨64911871563490550106828107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43274581042327033404552071 64911871563490550106828107)
      ·
        refine ⟨97367807345235825160242161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64911871563490550106828107 97367807345235825160242161)
        ·
          refine ⟨73025855508926868870181621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97367807345235825160242161 73025855508926868870181621)
          ·
            refine ⟨6846173953961893956579527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73025855508926868870181621 6846173953961893956579527)
            ·
              refine ⟨10269260930942840934869291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6846173953961893956579527 10269260930942840934869291)
              ·
                refine ⟨15403891396414261402303937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10269260930942840934869291 15403891396414261402303937)
                ·
                  refine ⟨11552918547310696051727953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15403891396414261402303937 11552918547310696051727953)
                  ·
                    refine ⟨8664688910483022038795965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11552918547310696051727953 8664688910483022038795965)
                    ·
                      refine ⟨3249258341431133264548487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8664688910483022038795965 3249258341431133264548487)
                      ·
                        rfl

theorem cell23_6327908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_6327908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327908 prefixEnd_6327908 := by exact prefixLift 6327908
  have htrace : WordTrace (prefixWord ++ tailWord_6327908) baseStart_6327908 baseEnd_6327908 := by
    simpa [prefixWord, tailWord_6327908, baseEnd_6327908] using wordTrace_append hprefix tailTrace_6327908
  have hstable : (prefixWord ++ tailWord_6327908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327908).length < 2 ^ (prefixWord ++ tailWord_6327908).sum := by decide
  have hdescent : baseEnd_6327908 < baseStart_6327908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327931 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 4, 3, 2]
def baseStart_6327931 : Nat := 118140960795 + 6327931 * 2 ^ 59
def prefixEnd_6327931 : Nat := 4983230072969 + 3 ^ 40 * 6327931 * 2
def baseEnd_6327931 : Nat := 3249270151486186674560881

theorem tailTrace_6327931 : CollatzResearch.WordTrace tailWord_6327931 prefixEnd_6327931 3249270151486186674560881 := by
  unfold tailWord_6327931
  simp only [CollatzResearch.WordTrace]
  refine ⟨230798604437994186419031647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153865736291996124279354431 230798604437994186419031647)
  ·
    refine ⟨346197906656991279628547471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230798604437994186419031647 346197906656991279628547471)
    ·
      refine ⟨519296859985486919442821207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346197906656991279628547471 519296859985486919442821207)
      ·
        refine ⟨778945289978230379164231811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519296859985486919442821207 778945289978230379164231811)
        ·
          refine ⟨1168417934967345568746347717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778945289978230379164231811 1168417934967345568746347717)
          ·
            refine ⟨219078362806377294139940197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1168417934967345568746347717 219078362806377294139940197)
            ·
              refine ⟨41077193026195742651238787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 219078362806377294139940197 41077193026195742651238787)
              ·
                refine ⟨61615789539293613976858181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41077193026195742651238787 61615789539293613976858181)
                ·
                  refine ⟨11552960538617552620660909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61615789539293613976858181 11552960538617552620660909)
                  ·
                    refine ⟨4332360201981582232747841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11552960538617552620660909 4332360201981582232747841)
                    ·
                      refine ⟨3249270151486186674560881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4332360201981582232747841 3249270151486186674560881)
                      ·
                        rfl

theorem cell23_6327931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 3, 2].length) (baseStart_6327931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327931 prefixEnd_6327931 := by exact prefixLift 6327931
  have htrace : WordTrace (prefixWord ++ tailWord_6327931) baseStart_6327931 baseEnd_6327931 := by
    simpa [prefixWord, tailWord_6327931, baseEnd_6327931] using wordTrace_append hprefix tailTrace_6327931
  have hstable : (prefixWord ++ tailWord_6327931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327931).length < 2 ^ (prefixWord ++ tailWord_6327931).sum := by decide
  have hdescent : baseEnd_6327931 < baseStart_6327931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6327972 : List Nat := [2, 3, 1, 2, 2, 4, 1, 3, 1, 1, 3]
def baseStart_6327972 : Nat := 118140960795 + 6327972 * 2 ^ 59
def prefixEnd_6327972 : Nat := 4983230072969 + 3 ^ 40 * 6327972 * 2
def baseEnd_6327972 : Nat := 3249291204193021014148193

theorem tailTrace_6327972 : CollatzResearch.WordTrace tailWord_6327972 prefixEnd_6327972 3249291204193021014148193 := by
  unfold tailWord_6327972
  simp only [CollatzResearch.WordTrace]
  refine ⟨115400049915422825210637085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153866733220563766947516113 115400049915422825210637085)
  ·
    refine ⟨43275018718283559453988907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115400049915422825210637085 43275018718283559453988907)
    ·
      refine ⟨64912528077425339180983361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43275018718283559453988907 64912528077425339180983361)
      ·
        refine ⟨48684396058069004385737521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64912528077425339180983361 48684396058069004385737521)
        ·
          refine ⟨36513297043551753289303141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48684396058069004385737521 36513297043551753289303141)
          ·
            refine ⟨6846243195665953741744339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36513297043551753289303141 6846243195665953741744339)
            ·
              refine ⟨10269364793498930612616509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6846243195665953741744339 10269364793498930612616509)
              ·
                refine ⟨3851011797562098979731191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10269364793498930612616509 3851011797562098979731191)
                ·
                  refine ⟨5776517696343148469596787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3851011797562098979731191 5776517696343148469596787)
                  ·
                    refine ⟨8664776544514722704395181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5776517696343148469596787 8664776544514722704395181)
                    ·
                      refine ⟨3249291204193021014148193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8664776544514722704395181 3249291204193021014148193)
                      ·
                        rfl

theorem cell23_6327972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_6327972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6327972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6327972 prefixEnd_6327972 := by exact prefixLift 6327972
  have htrace : WordTrace (prefixWord ++ tailWord_6327972) baseStart_6327972 baseEnd_6327972 := by
    simpa [prefixWord, tailWord_6327972, baseEnd_6327972] using wordTrace_append hprefix tailTrace_6327972
  have hstable : (prefixWord ++ tailWord_6327972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6327972).length < 2 ^ (prefixWord ++ tailWord_6327972).sum := by decide
  have hdescent : baseEnd_6327972 < baseStart_6327972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6327972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
