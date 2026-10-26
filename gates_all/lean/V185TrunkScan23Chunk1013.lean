import V185TrunkScan23Chunk1012

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5998524 : List Nat := [2, 2, 2, 5, 1, 1, 1, 4, 1, 2, 2]
def baseStart_5998524 : Nat := 118140960795 + 5998524 * 2 ^ 59
def prefixEnd_5998524 : Nat := 4983230072969 + 3 ^ 40 * 5998524 * 2
def baseEnd_5998524 : Nat := 3080126029530593980963297

theorem tailTrace_5998524 : CollatzResearch.WordTrace tailWord_5998524 prefixEnd_5998524 3080126029530593980963297 := by
  unfold tailWord_5998524
  simp only [CollatzResearch.WordTrace]
  refine ⟨109392072060189744591189313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145856096080252992788252417 109392072060189744591189313)
  ·
    refine ⟨82044054045142308443391985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109392072060189744591189313 82044054045142308443391985)
    ·
      refine ⟨61533040533856731332543989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82044054045142308443391985 61533040533856731332543989)
      ·
        refine ⟨5768722550049068562425999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61533040533856731332543989 5768722550049068562425999)
        ·
          refine ⟨8653083825073602843638999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5768722550049068562425999 8653083825073602843638999)
          ·
            refine ⟨12979625737610404265458499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8653083825073602843638999 12979625737610404265458499)
            ·
              refine ⟨19469438606415606398187749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12979625737610404265458499 19469438606415606398187749)
              ·
                refine ⟨3650519738702926199660203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19469438606415606398187749 3650519738702926199660203)
                ·
                  refine ⟨5475779608054389299490305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3650519738702926199660203 5475779608054389299490305)
                  ·
                    refine ⟨4106834706040791974617729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5475779608054389299490305 4106834706040791974617729)
                    ·
                      refine ⟨3080126029530593980963297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4106834706040791974617729 3080126029530593980963297)
                      ·
                        rfl

theorem cell23_5998524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_5998524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998524 prefixEnd_5998524 := by exact prefixLift 5998524
  have htrace : WordTrace (prefixWord ++ tailWord_5998524) baseStart_5998524 baseEnd_5998524 := by
    simpa [prefixWord, tailWord_5998524, baseEnd_5998524] using wordTrace_append hprefix tailTrace_5998524
  have hstable : (prefixWord ++ tailWord_5998524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998524).length < 2 ^ (prefixWord ++ tailWord_5998524).sum := by decide
  have hdescent : baseEnd_5998524 < baseStart_5998524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998539 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 2, 6]
def baseStart_5998539 : Nat := 118140960795 + 5998539 * 2 ^ 59
def prefixEnd_5998539 : Nat := 4983230072969 + 3 ^ 40 * 5998539 * 2
def baseEnd_5998539 : Nat := 1026711243913470474091909

theorem tailTrace_5998539 : CollatzResearch.WordTrace tailWord_5998539 prefixEnd_5998539 1026711243913470474091909 := by
  unfold tailWord_5998539
  simp only [CollatzResearch.WordTrace]
  refine ⟨218784691215325146744174671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145856460810216764496116447 218784691215325146744174671)
  ·
    refine ⟨328177036822987720116262007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218784691215325146744174671 328177036822987720116262007)
    ·
      refine ⟨492265555234481580174393011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328177036822987720116262007 492265555234481580174393011)
      ·
        refine ⟨738398332851722370261589517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492265555234481580174393011 738398332851722370261589517)
        ·
          refine ⟨276899374819395888848096069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 738398332851722370261589517 276899374819395888848096069)
          ·
            refine ⟨51918632778636729159018013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 276899374819395888848096069 51918632778636729159018013)
            ·
              refine ⟨19469487291988773434631755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51918632778636729159018013 19469487291988773434631755)
              ·
                refine ⟨29204230937983160151947633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19469487291988773434631755 29204230937983160151947633)
                ·
                  refine ⟨21903173203487370113960725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29204230937983160151947633 21903173203487370113960725)
                  ·
                    refine ⟨1026711243913470474091909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21903173203487370113960725 1026711243913470474091909)
                    ·
                      rfl

theorem cell23_5998539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 6].length) (baseStart_5998539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998539 prefixEnd_5998539 := by exact prefixLift 5998539
  have htrace : WordTrace (prefixWord ++ tailWord_5998539) baseStart_5998539 baseEnd_5998539 := by
    simpa [prefixWord, tailWord_5998539, baseEnd_5998539] using wordTrace_append hprefix tailTrace_5998539
  have hstable : (prefixWord ++ tailWord_5998539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998539).length < 2 ^ (prefixWord ++ tailWord_5998539).sum := by decide
  have hdescent : baseEnd_5998539 < baseStart_5998539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998563 : List Nat := [1, 1, 1, 6, 1, 2, 2, 2, 1, 4, 2]
def baseStart_5998563 : Nat := 118140960795 + 5998563 * 2 ^ 59
def prefixEnd_5998563 : Nat := 4983230072969 + 3 ^ 40 * 5998563 * 2
def baseEnd_5998563 : Nat := 3080146055276119328375617

theorem tailTrace_5998563 : CollatzResearch.WordTrace tailWord_5998563 prefixEnd_5998563 3080146055276119328375617 := by
  unfold tailWord_5998563
  simp only [CollatzResearch.WordTrace]
  refine ⟨218785566567238198843048343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145857044378158799228698895 218785566567238198843048343)
  ·
    refine ⟨328178349850857298264572515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218785566567238198843048343 328178349850857298264572515)
    ·
      refine ⟨492267524776285947396858773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328178349850857298264572515 492267524776285947396858773)
      ·
        refine ⟨23075040223888403784227755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 492267524776285947396858773 23075040223888403784227755)
        ·
          refine ⟨34612560335832605676341633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23075040223888403784227755 34612560335832605676341633)
          ·
            refine ⟨25959420251874454257256225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34612560335832605676341633 25959420251874454257256225)
            ·
              refine ⟨19469565188905840692942169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25959420251874454257256225 19469565188905840692942169)
              ·
                refine ⟨14602173891679380519706627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19469565188905840692942169 14602173891679380519706627)
                ·
                  refine ⟨21903260837519070779559941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14602173891679380519706627 21903260837519070779559941)
                  ·
                    refine ⟨4106861407034825771167489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21903260837519070779559941 4106861407034825771167489)
                    ·
                      refine ⟨3080146055276119328375617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4106861407034825771167489 3080146055276119328375617)
                      ·
                        rfl

theorem cell23_5998563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_5998563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998563 prefixEnd_5998563 := by exact prefixLift 5998563
  have htrace : WordTrace (prefixWord ++ tailWord_5998563) baseStart_5998563 baseEnd_5998563 := by
    simpa [prefixWord, tailWord_5998563, baseEnd_5998563] using wordTrace_append hprefix tailTrace_5998563
  have hstable : (prefixWord ++ tailWord_5998563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998563).length < 2 ^ (prefixWord ++ tailWord_5998563).sum := by decide
  have hdescent : baseEnd_5998563 < baseStart_5998563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998597 : List Nat := [1, 3, 1, 1, 2, 5, 3, 1, 2, 2, 2]
def baseStart_5998597 : Nat := 118140960795 + 5998597 * 2 ^ 59
def prefixEnd_5998597 : Nat := 4983230072969 + 3 ^ 40 * 5998597 * 2
def baseEnd_5998597 : Nat := 3080163513618372195350461

theorem tailTrace_5998597 : CollatzResearch.WordTrace tailWord_5998597 prefixEnd_5998597 3080163513618372195350461 := by
  unfold tailWord_5998597
  simp only [CollatzResearch.WordTrace]
  refine ⟨218786806649115022649786045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145857871099410015099857363 218786806649115022649786045)
  ·
    refine ⟨82045052493418133493669767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218786806649115022649786045 82045052493418133493669767)
    ·
      refine ⟨123067578740127200240504651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82045052493418133493669767 123067578740127200240504651)
      ·
        refine ⟨184601368110190800360756977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123067578740127200240504651 184601368110190800360756977)
        ·
          refine ⟨138451026082643100270567733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184601368110190800360756977 138451026082643100270567733)
          ·
            refine ⟨12979783695247790650365725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138451026082643100270567733 12979783695247790650365725)
            ·
              refine ⟨4867418885717921493887147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12979783695247790650365725 4867418885717921493887147)
              ·
                refine ⟨7301128328576882240830721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4867418885717921493887147 7301128328576882240830721)
                ·
                  refine ⟨5475846246432661680623041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7301128328576882240830721 5475846246432661680623041)
                  ·
                    refine ⟨4106884684824496260467281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5475846246432661680623041 4106884684824496260467281)
                    ·
                      refine ⟨3080163513618372195350461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4106884684824496260467281 3080163513618372195350461)
                      ·
                        rfl

theorem cell23_5998597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 2, 2, 2].length) (baseStart_5998597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998597 prefixEnd_5998597 := by exact prefixLift 5998597
  have htrace : WordTrace (prefixWord ++ tailWord_5998597) baseStart_5998597 baseEnd_5998597 := by
    simpa [prefixWord, tailWord_5998597, baseEnd_5998597] using wordTrace_append hprefix tailTrace_5998597
  have hstable : (prefixWord ++ tailWord_5998597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998597).length < 2 ^ (prefixWord ++ tailWord_5998597).sum := by decide
  have hdescent : baseEnd_5998597 < baseStart_5998597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998609 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 5]
def baseStart_5998609 : Nat := 118140960795 + 5998609 * 2 ^ 59
def prefixEnd_5998609 : Nat := 4983230072969 + 3 ^ 40 * 5998609 * 2
def baseEnd_5998609 : Nat := 3080169675386226148400405

theorem tailTrace_5998609 : CollatzResearch.WordTrace tailWord_5998609 prefixEnd_5998609 3080169675386226148400405 := by
  unfold tailWord_5998609
  simp only [CollatzResearch.WordTrace]
  refine ⟨218787244325071548699222881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145858162883381032466148587 218787244325071548699222881)
  ·
    refine ⟨164090433243803661524417161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218787244325071548699222881 164090433243803661524417161)
    ·
      refine ⟨123067824932852746143312871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164090433243803661524417161 123067824932852746143312871)
      ·
        refine ⟨184601737399279119214969307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123067824932852746143312871 184601737399279119214969307)
        ·
          refine ⟨276902606098918678822453961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184601737399279119214969307 276902606098918678822453961)
          ·
            refine ⟨207676954574189009116840471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276902606098918678822453961 207676954574189009116840471)
            ·
              refine ⟨311515431861283513675260707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207676954574189009116840471 311515431861283513675260707)
              ·
                refine ⟨467273147791925270512891061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311515431861283513675260707 467273147791925270512891061)
                ·
                  refine ⟨43806857605492994110583537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 467273147791925270512891061 43806857605492994110583537)
                  ·
                    refine ⟨32855143204119745582937653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43806857605492994110583537 32855143204119745582937653)
                    ·
                      refine ⟨3080169675386226148400405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32855143204119745582937653 3080169675386226148400405)
                      ·
                        rfl

theorem cell23_5998609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_5998609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998609 prefixEnd_5998609 := by exact prefixLift 5998609
  have htrace : WordTrace (prefixWord ++ tailWord_5998609) baseStart_5998609 baseEnd_5998609 := by
    simpa [prefixWord, tailWord_5998609, baseEnd_5998609] using wordTrace_append hprefix tailTrace_5998609
  have hstable : (prefixWord ++ tailWord_5998609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998609).length < 2 ^ (prefixWord ++ tailWord_5998609).sum := by decide
  have hdescent : baseEnd_5998609 < baseStart_5998609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998616 : List Nat := [2, 1, 2, 3, 2, 1, 2, 3, 2, 5]
def baseStart_5998616 : Nat := 118140960795 + 5998616 * 2 ^ 59
def prefixEnd_5998616 : Nat := 4983230072969 + 3 ^ 40 * 5998616 * 2
def baseEnd_5998616 : Nat := 1026724423250269207004291

theorem tailTrace_5998616 : CollatzResearch.WordTrace tailWord_5998616 prefixEnd_5998616 1026724423250269207004291 := by
  unfold tailWord_5998616
  simp only [CollatzResearch.WordTrace]
  refine ⟨109393749818023094447363851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145858333090697459263151801 109393749818023094447363851)
  ·
    refine ⟨164090624727034641671045777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109393749818023094447363851 164090624727034641671045777)
    ·
      refine ⟨123067968545275981253284333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164090624727034641671045777 123067968545275981253284333)
      ·
        refine ⟨46150488204478492969981625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123067968545275981253284333 46150488204478492969981625)
        ·
          refine ⟨34612866153358869727486219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46150488204478492969981625 34612866153358869727486219)
          ·
            refine ⟨51919299230038304591229329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34612866153358869727486219 51919299230038304591229329)
            ·
              refine ⟨38939474422528728443421997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51919299230038304591229329 38939474422528728443421997)
              ·
                refine ⟨14602302908448273166283249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38939474422528728443421997 14602302908448273166283249)
                ·
                  refine ⟨10951727181336204874712437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14602302908448273166283249 10951727181336204874712437)
                  ·
                    refine ⟨1026724423250269207004291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10951727181336204874712437 1026724423250269207004291)
                    ·
                      rfl

theorem cell23_5998616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_5998616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998616 prefixEnd_5998616 := by exact prefixLift 5998616
  have htrace : WordTrace (prefixWord ++ tailWord_5998616) baseStart_5998616 baseEnd_5998616 := by
    simpa [prefixWord, tailWord_5998616, baseEnd_5998616] using wordTrace_append hprefix tailTrace_5998616
  have hstable : (prefixWord ++ tailWord_5998616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998616).length < 2 ^ (prefixWord ++ tailWord_5998616).sum := by decide
  have hdescent : baseEnd_5998616 < baseStart_5998616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998620 : List Nat := [2, 2, 3, 1, 3, 3, 1, 3, 5]
def baseStart_5998620 : Nat := 118140960795 + 5998620 * 2 ^ 59
def prefixEnd_5998620 : Nat := 4983230072969 + 3 ^ 40 * 5998620 * 2
def baseEnd_5998620 : Nat := 342241702630380622818095

theorem tailTrace_5998620 : CollatzResearch.WordTrace tailWord_5998620 prefixEnd_5998620 342241702630380622818095 := by
  unfold tailWord_5998620
  simp only [CollatzResearch.WordTrace]
  refine ⟨109393822764015848788936657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145858430352021131718582209 109393822764015848788936657)
  ·
    refine ⟨82045367073011886591702493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109393822764015848788936657 82045367073011886591702493)
    ·
      refine ⟨30767012652379457471888435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82045367073011886591702493 30767012652379457471888435)
      ·
        refine ⟨46150518978569186207832653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30767012652379457471888435 46150518978569186207832653)
        ·
          refine ⟨17306444616963444827937245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46150518978569186207832653 17306444616963444827937245)
          ·
            refine ⟨6489916731361291810476467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17306444616963444827937245 6489916731361291810476467)
            ·
              refine ⟨9734875097041937715714701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6489916731361291810476467 9734875097041937715714701)
              ·
                refine ⟨3650578161390726643393013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9734875097041937715714701 3650578161390726643393013)
                ·
                  refine ⟨342241702630380622818095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3650578161390726643393013 342241702630380622818095)
                  ·
                    rfl

theorem cell23_5998620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 5].length) (baseStart_5998620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998620 prefixEnd_5998620 := by exact prefixLift 5998620
  have htrace : WordTrace (prefixWord ++ tailWord_5998620) baseStart_5998620 baseEnd_5998620 := by
    simpa [prefixWord, tailWord_5998620, baseEnd_5998620] using wordTrace_append hprefix tailTrace_5998620
  have hstable : (prefixWord ++ tailWord_5998620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998620).length < 2 ^ (prefixWord ++ tailWord_5998620).sum := by decide
  have hdescent : baseEnd_5998620 < baseStart_5998620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998626 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_5998626 : Nat := 118140960795 + 5998626 * 2 ^ 59
def prefixEnd_5998626 : Nat := 4983230072969 + 3 ^ 40 * 5998626 * 2
def baseEnd_5998626 : Nat := 3080178404557352581887827

theorem tailTrace_5998626 : CollatzResearch.WordTrace tailWord_5998626 prefixEnd_5998626 3080178404557352581887827 := by
  unfold tailWord_5998626
  simp only [CollatzResearch.WordTrace]
  refine ⟨54696966091502490150647933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145858576244006640401727821 54696966091502490150647933)
  ·
    refine ⟨20511362284313433806492975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54696966091502490150647933 20511362284313433806492975)
    ·
      refine ⟨30767043426470150709739463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20511362284313433806492975 30767043426470150709739463)
      ·
        refine ⟨46150565139705226064609195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30767043426470150709739463 46150565139705226064609195)
        ·
          refine ⟨69225847709557839096913793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46150565139705226064609195 69225847709557839096913793)
          ·
            refine ⟨51919385782168379322685345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69225847709557839096913793 51919385782168379322685345)
            ·
              refine ⟨38939539336626284492014009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51919385782168379322685345 38939539336626284492014009)
              ·
                refine ⟨29204654502469713369010507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38939539336626284492014009 29204654502469713369010507)
                ·
                  refine ⟨43806981753704570053515761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29204654502469713369010507 43806981753704570053515761)
                  ·
                    refine ⟨32855236315278427540136821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43806981753704570053515761 32855236315278427540136821)
                    ·
                      refine ⟨3080178404557352581887827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32855236315278427540136821 3080178404557352581887827)
                      ·
                        rfl

theorem cell23_5998626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_5998626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998626 prefixEnd_5998626 := by exact prefixLift 5998626
  have htrace : WordTrace (prefixWord ++ tailWord_5998626) baseStart_5998626 baseEnd_5998626 := by
    simpa [prefixWord, tailWord_5998626, baseEnd_5998626] using wordTrace_append hprefix tailTrace_5998626
  have hstable : (prefixWord ++ tailWord_5998626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998626).length < 2 ^ (prefixWord ++ tailWord_5998626).sum := by decide
  have hdescent : baseEnd_5998626 < baseStart_5998626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998639 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 5]
def baseStart_5998639 : Nat := 118140960795 + 5998639 * 2 ^ 59
def prefixEnd_5998639 : Nat := 4983230072969 + 3 ^ 40 * 5998639 * 2
def baseEnd_5998639 : Nat := 3080185079805861031025267

theorem tailTrace_5998639 : CollatzResearch.WordTrace tailWord_5998639 prefixEnd_5998639 3080185079805861031025267 := by
  unfold tailWord_5998639
  simp only [CollatzResearch.WordTrace]
  refine ⟨218788338514962863822814971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145858892343308575881876647 218788338514962863822814971)
  ·
    refine ⟨328182507772444295734222457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218788338514962863822814971 328182507772444295734222457)
    ·
      refine ⟨246136880829333221800666843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328182507772444295734222457 246136880829333221800666843)
      ·
        refine ⟨369205321243999832701000265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246136880829333221800666843 369205321243999832701000265)
        ·
          refine ⟨276903990932999874525750199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369205321243999832701000265 276903990932999874525750199)
          ·
            refine ⟨415355986399499811788625299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276903990932999874525750199 415355986399499811788625299)
            ·
              refine ⟨623033979599249717682937949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415355986399499811788625299 623033979599249717682937949)
              ·
                refine ⟨233637742349718644131101731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 623033979599249717682937949 233637742349718644131101731)
                ·
                  refine ⟨350456613524577966196652597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233637742349718644131101731 350456613524577966196652597)
                  ·
                    refine ⟨32855307517929184330936181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 350456613524577966196652597 32855307517929184330936181)
                    ·
                      refine ⟨3080185079805861031025267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32855307517929184330936181 3080185079805861031025267)
                      ·
                        rfl

theorem cell23_5998639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_5998639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998639 prefixEnd_5998639 := by exact prefixLift 5998639
  have htrace : WordTrace (prefixWord ++ tailWord_5998639) baseStart_5998639 baseEnd_5998639 := by
    simpa [prefixWord, tailWord_5998639, baseEnd_5998639] using wordTrace_append hprefix tailTrace_5998639
  have hstable : (prefixWord ++ tailWord_5998639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998639).length < 2 ^ (prefixWord ++ tailWord_5998639).sum := by decide
  have hdescent : baseEnd_5998639 < baseStart_5998639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998653 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 1, 6, 2]
def baseStart_5998653 : Nat := 118140960795 + 5998653 * 2 ^ 59
def prefixEnd_5998653 : Nat := 4983230072969 + 3 ^ 40 * 5998653 * 2
def baseEnd_5998653 : Nat := 3080192268535023976250203

theorem tailTrace_5998653 : CollatzResearch.WordTrace tailWord_5998653 prefixEnd_5998653 3080192268535023976250203 := by
  unfold tailWord_5998653
  simp only [CollatzResearch.WordTrace]
  refine ⟨218788849136912144213824613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145859232757941429475883075 218788849136912144213824613)
  ·
    refine ⟨41022909213171027040092115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218788849136912144213824613 41022909213171027040092115)
    ·
      refine ⟨61534363819756540560138173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41022909213171027040092115 61534363819756540560138173)
      ·
        refine ⟨23075386432408702710051815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61534363819756540560138173 23075386432408702710051815)
        ·
          refine ⟨34613079648613054065077723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23075386432408702710051815 34613079648613054065077723)
          ·
            refine ⟨51919619472919581097616585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34613079648613054065077723 51919619472919581097616585)
            ·
              refine ⟨38939714604689685823212439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51919619472919581097616585 38939714604689685823212439)
              ·
                refine ⟨58409571907034528734818659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38939714604689685823212439 58409571907034528734818659)
                ·
                  refine ⟨87614357860551793102227989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58409571907034528734818659 87614357860551793102227989)
                  ·
                    refine ⟨4106923024713365301666937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87614357860551793102227989 4106923024713365301666937)
                    ·
                      refine ⟨3080192268535023976250203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4106923024713365301666937 3080192268535023976250203)
                      ·
                        rfl

theorem cell23_5998653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_5998653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998653 prefixEnd_5998653 := by exact prefixLift 5998653
  have htrace : WordTrace (prefixWord ++ tailWord_5998653) baseStart_5998653 baseEnd_5998653 := by
    simpa [prefixWord, tailWord_5998653, baseEnd_5998653] using wordTrace_append hprefix tailTrace_5998653
  have hstable : (prefixWord ++ tailWord_5998653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998653).length < 2 ^ (prefixWord ++ tailWord_5998653).sum := by decide
  have hdescent : baseEnd_5998653 < baseStart_5998653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998659 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 10]
def baseStart_5998659 : Nat := 118140960795 + 5998659 * 2 ^ 59
def prefixEnd_5998659 : Nat := 4983230072969 + 3 ^ 40 * 5998659 * 2
def baseEnd_5998659 : Nat := 342243927713216772530575

theorem tailTrace_5998659 : CollatzResearch.WordTrace tailWord_5998659 prefixEnd_5998659 342243927713216772530575 := by
  unfold tailWord_5998659
  simp only [CollatzResearch.WordTrace]
  refine ⟨218789067974890407238543031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145859378649926938159028687 218789067974890407238543031)
  ·
    refine ⟨328183601962335610857814547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218789067974890407238543031 328183601962335610857814547)
    ·
      refine ⟨492275402943503416286721821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328183601962335610857814547 492275402943503416286721821)
      ·
        refine ⟨184603276103813781107520683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 492275402943503416286721821 184603276103813781107520683)
        ·
          refine ⟨276904914155720671661281025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184603276103813781107520683 276904914155720671661281025)
          ·
            refine ⟨207678685616790503745960769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276904914155720671661281025 207678685616790503745960769)
            ·
              refine ⟨155759014212592877809470577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207678685616790503745960769 155759014212592877809470577)
              ·
                refine ⟨116819260659444658357102933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155759014212592877809470577 116819260659444658357102933)
                ·
                  refine ⟨342243927713216772530575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 116819260659444658357102933 342243927713216772530575)
                  ·
                    rfl

theorem cell23_5998659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 10].length) (baseStart_5998659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998659 prefixEnd_5998659 := by exact prefixLift 5998659
  have htrace : WordTrace (prefixWord ++ tailWord_5998659) baseStart_5998659 baseEnd_5998659 := by
    simpa [prefixWord, tailWord_5998659, baseEnd_5998659] using wordTrace_append hprefix tailTrace_5998659
  have hstable : (prefixWord ++ tailWord_5998659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998659).length < 2 ^ (prefixWord ++ tailWord_5998659).sum := by decide
  have hdescent : baseEnd_5998659 < baseStart_5998659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998693 : List Nat := [1, 3, 1, 3, 2, 3, 2, 2, 6]
def baseStart_5998693 : Nat := 118140960795 + 5998693 * 2 ^ 59
def prefixEnd_5998693 : Nat := 4983230072969 + 3 ^ 40 * 5998693 * 2
def baseEnd_5998693 : Nat := 342245867529022646638891

theorem tailTrace_5998693 : CollatzResearch.WordTrace tailWord_5998693 prefixEnd_5998693 342245867529022646638891 := by
  unfold tailWord_5998693
  simp only [CollatzResearch.WordTrace]
  refine ⟨218790308056767231045280733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145860205371178154030187155 218790308056767231045280733)
  ·
    refine ⟨82046365521287711641980275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218790308056767231045280733 82046365521287711641980275)
    ·
      refine ⟨123069548281931567462970413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82046365521287711641980275 123069548281931567462970413)
      ·
        refine ⟨46151080605724337798613905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123069548281931567462970413 46151080605724337798613905)
        ·
          refine ⟨34613310454293253348960429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46151080605724337798613905 34613310454293253348960429)
          ·
            refine ⟨12979991420359970005860161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34613310454293253348960429 12979991420359970005860161)
            ·
              refine ⟨9734993565269977504395121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12979991420359970005860161 9734993565269977504395121)
              ·
                refine ⟨7301245173952483128296341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9734993565269977504395121 7301245173952483128296341)
                ·
                  refine ⟨342245867529022646638891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7301245173952483128296341 342245867529022646638891)
                  ·
                    rfl

theorem cell23_5998693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 6].length) (baseStart_5998693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998693 prefixEnd_5998693 := by exact prefixLift 5998693
  have htrace : WordTrace (prefixWord ++ tailWord_5998693) baseStart_5998693 baseEnd_5998693 := by
    simpa [prefixWord, tailWord_5998693, baseEnd_5998693] using wordTrace_append hprefix tailTrace_5998693
  have hstable : (prefixWord ++ tailWord_5998693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998693).length < 2 ^ (prefixWord ++ tailWord_5998693).sum := by decide
  have hdescent : baseEnd_5998693 < baseStart_5998693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998730 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 1, 5, 2]
def baseStart_5998730 : Nat := 118140960795 + 5998730 * 2 ^ 59
def prefixEnd_5998730 : Nat := 4983230072969 + 3 ^ 40 * 5998730 * 2
def baseEnd_5998730 : Nat := 3080231806545420174987349

theorem tailTrace_5998730 : CollatzResearch.WordTrace tailWord_5998730 prefixEnd_5998730 3080231806545420174987349 := by
  unfold tailWord_5998730
  simp only [CollatzResearch.WordTrace]
  refine ⟨54697914389408296591094411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145861105038422124242918429 54697914389408296591094411)
  ·
    refine ⟨82046871584112444886641617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54697914389408296591094411 82046871584112444886641617)
    ·
      refine ⟨61535153688084333664981213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82046871584112444886641617 61535153688084333664981213)
      ·
        refine ⟨23075682633031625124367955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61535153688084333664981213 23075682633031625124367955)
        ·
          refine ⟨34613523949547437686551933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23075682633031625124367955 34613523949547437686551933)
          ·
            refine ⟨12980071481080289132456975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34613523949547437686551933 12980071481080289132456975)
            ·
              refine ⟨19470107221620433698685463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12980071481080289132456975 19470107221620433698685463)
              ·
                refine ⟨29205160832430650548028195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19470107221620433698685463 29205160832430650548028195)
                ·
                  refine ⟨43807741248645975822042293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29205160832430650548028195 43807741248645975822042293)
                  ·
                    refine ⟨4106975742060560233316465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43807741248645975822042293 4106975742060560233316465)
                    ·
                      refine ⟨3080231806545420174987349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4106975742060560233316465 3080231806545420174987349)
                      ·
                        rfl

theorem cell23_5998730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_5998730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998730 prefixEnd_5998730 := by exact prefixLift 5998730
  have htrace : WordTrace (prefixWord ++ tailWord_5998730) baseStart_5998730 baseEnd_5998730 := by
    simpa [prefixWord, tailWord_5998730, baseEnd_5998730] using wordTrace_append hprefix tailTrace_5998730
  have hstable : (prefixWord ++ tailWord_5998730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998730).length < 2 ^ (prefixWord ++ tailWord_5998730).sum := by decide
  have hdescent : baseEnd_5998730 < baseStart_5998730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998736 : List Nat := [2, 1, 1, 1, 1, 1, 5, 4, 1, 6]
def baseStart_5998736 : Nat := 118140960795 + 5998736 * 2 ^ 59
def prefixEnd_5998736 : Nat := 4983230072969 + 3 ^ 40 * 5998736 * 2
def baseEnd_5998736 : Nat := 1026744962476449050504107

theorem tailTrace_5998736 : CollatzResearch.WordTrace tailWord_5998736 prefixEnd_5998736 1026744962476449050504107 := by
  unfold tailWord_5998736
  simp only [CollatzResearch.WordTrace]
  refine ⟨109395938197805724694548031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145861250930407632926064041 109395938197805724694548031)
  ·
    refine ⟨164093907296708587041822047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109395938197805724694548031 164093907296708587041822047)
    ·
      refine ⟨246140860945062880562733071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164093907296708587041822047 246140860945062880562733071)
      ·
        refine ⟨369211291417594320844099607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246140860945062880562733071 369211291417594320844099607)
        ·
          refine ⟨553816937126391481266149411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369211291417594320844099607 553816937126391481266149411)
          ·
            refine ⟨830725405689587221899224117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553816937126391481266149411 830725405689587221899224117)
            ·
              refine ⟨77880506783398802053052261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 830725405689587221899224117 77880506783398802053052261)
              ·
                refine ⟨14602595021887275384947299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77880506783398802053052261 14602595021887275384947299)
                ·
                  refine ⟨21903892532830913077420949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14602595021887275384947299 21903892532830913077420949)
                  ·
                    refine ⟨1026744962476449050504107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21903892532830913077420949 1026744962476449050504107)
                    ·
                      rfl

theorem cell23_5998736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 1, 6].length) (baseStart_5998736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998736 prefixEnd_5998736 := by exact prefixLift 5998736
  have htrace : WordTrace (prefixWord ++ tailWord_5998736) baseStart_5998736 baseEnd_5998736 := by
    simpa [prefixWord, tailWord_5998736, baseEnd_5998736] using wordTrace_append hprefix tailTrace_5998736
  have hstable : (prefixWord ++ tailWord_5998736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998736).length < 2 ^ (prefixWord ++ tailWord_5998736).sum := by decide
  have hdescent : baseEnd_5998736 < baseStart_5998736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998754 : List Nat := [3, 3, 1, 3, 1, 1, 2, 4, 1, 1, 3]
def baseStart_5998754 : Nat := 118140960795 + 5998754 * 2 ^ 59
def prefixEnd_5998754 : Nat := 4983230072969 + 3 ^ 40 * 5998754 * 2
def baseEnd_5998754 : Nat := 3080244130081128081087239

theorem tailTrace_5998754 : CollatzResearch.WordTrace tailWord_5998754 prefixEnd_5998754 3080244130081128081087239 := by
  unfold tailWord_5998754
  simp only [CollatzResearch.WordTrace]
  refine ⟨54698133227386559615812829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145861688606364158975500877 54698133227386559615812829)
  ·
    refine ⟨20511799960269959855929811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54698133227386559615812829 20511799960269959855929811)
    ·
      refine ⟨30767699940404939783894717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20511799960269959855929811 30767699940404939783894717)
      ·
        refine ⟨11537887477651852418960519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30767699940404939783894717 11537887477651852418960519)
        ·
          refine ⟨17306831216477778628440779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11537887477651852418960519 17306831216477778628440779)
          ·
            refine ⟨25960246824716667942661169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17306831216477778628440779 25960246824716667942661169)
            ·
              refine ⟨19470185118537500956995877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25960246824716667942661169 19470185118537500956995877)
              ·
                refine ⟨3650659709725781429436727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19470185118537500956995877 3650659709725781429436727)
                ·
                  refine ⟨5475989564588672144155091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3650659709725781429436727 5475989564588672144155091)
                  ·
                    refine ⟨8213984346883008216232637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5475989564588672144155091 8213984346883008216232637)
                    ·
                      refine ⟨3080244130081128081087239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8213984346883008216232637 3080244130081128081087239)
                      ·
                        rfl

theorem cell23_5998754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_5998754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998754 prefixEnd_5998754 := by exact prefixLift 5998754
  have htrace : WordTrace (prefixWord ++ tailWord_5998754) baseStart_5998754 baseEnd_5998754 := by
    simpa [prefixWord, tailWord_5998754, baseEnd_5998754] using wordTrace_append hprefix tailTrace_5998754
  have hstable : (prefixWord ++ tailWord_5998754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998754).length < 2 ^ (prefixWord ++ tailWord_5998754).sum := by decide
  have hdescent : baseEnd_5998754 < baseStart_5998754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998810 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3]
def baseStart_5998810 : Nat := 118140960795 + 5998810 * 2 ^ 59
def prefixEnd_5998810 : Nat := 4983230072969 + 3 ^ 40 * 5998810 * 2
def baseEnd_5998810 : Nat := 3080272884997779861986981

theorem tailTrace_5998810 : CollatzResearch.WordTrace tailWord_5998810 prefixEnd_5998810 3080272884997779861986981 := by
  unfold tailWord_5998810
  simp only [CollatzResearch.WordTrace]
  refine ⟨54698643849335840006822471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145863050264895573351526589 54698643849335840006822471)
  ·
    refine ⟨82047965774003760010233707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54698643849335840006822471 82047965774003760010233707)
    ·
      refine ⟨123071948661005640015350561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82047965774003760010233707 123071948661005640015350561)
      ·
        refine ⟨92303961495754230011512921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123071948661005640015350561 92303961495754230011512921)
        ·
          refine ⟨69227971121815672508634691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92303961495754230011512921 69227971121815672508634691)
          ·
            refine ⟨103841956682723508762952037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69227971121815672508634691 103841956682723508762952037)
            ·
              refine ⟨19470366878010657893053507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103841956682723508762952037 19470366878010657893053507)
              ·
                refine ⟨29205550317015986839580261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19470366878010657893053507 29205550317015986839580261)
                ·
                  refine ⟨5476040684440497532421299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29205550317015986839580261 5476040684440497532421299)
                  ·
                    refine ⟨8214061026660746298631949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5476040684440497532421299 8214061026660746298631949)
                    ·
                      refine ⟨3080272884997779861986981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8214061026660746298631949 3080272884997779861986981)
                      ·
                        rfl

theorem cell23_5998810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_5998810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998810 prefixEnd_5998810 := by exact prefixLift 5998810
  have htrace : WordTrace (prefixWord ++ tailWord_5998810) baseStart_5998810 baseEnd_5998810 := by
    simpa [prefixWord, tailWord_5998810, baseEnd_5998810] using wordTrace_append hprefix tailTrace_5998810
  have hstable : (prefixWord ++ tailWord_5998810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998810).length < 2 ^ (prefixWord ++ tailWord_5998810).sum := by decide
  have hdescent : baseEnd_5998810 < baseStart_5998810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998820 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 3, 3, 2]
def baseStart_5998820 : Nat := 118140960795 + 5998820 * 2 ^ 59
def prefixEnd_5998820 : Nat := 4983230072969 + 3 ^ 40 * 5998820 * 2
def baseEnd_5998820 : Nat := 3080278019804324822861935

theorem tailTrace_5998820 : CollatzResearch.WordTrace tailWord_5998820 prefixEnd_5998820 3080278019804324822861935 := by
  unfold tailWord_5998820
  simp only [CollatzResearch.WordTrace]
  refine ⟨109397470063653565867576957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145863293418204754490102609 109397470063653565867576957)
  ·
    refine ⟨41024051273870087200341359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109397470063653565867576957 41024051273870087200341359)
    ·
      refine ⟨61536076910805130800512039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41024051273870087200341359 61536076910805130800512039)
      ·
        refine ⟨92304115366207696200768059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61536076910805130800512039 92304115366207696200768059)
        ·
          refine ⟨138456173049311544301152089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92304115366207696200768059 138456173049311544301152089)
          ·
            refine ⟨103842129786983658225864067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138456173049311544301152089 103842129786983658225864067)
            ·
              refine ⟨155763194680475487338796101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103842129786983658225864067 155763194680475487338796101)
              ·
                refine ⟨29205599002589153876024269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155763194680475487338796101 29205599002589153876024269)
                ·
                  refine ⟨10952099625970932703509101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29205599002589153876024269 10952099625970932703509101)
                  ·
                    refine ⟨4107037359739099763815913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10952099625970932703509101 4107037359739099763815913)
                    ·
                      refine ⟨3080278019804324822861935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4107037359739099763815913 3080278019804324822861935)
                      ·
                        rfl

theorem cell23_5998820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 3, 3, 2].length) (baseStart_5998820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998820 prefixEnd_5998820 := by exact prefixLift 5998820
  have htrace : WordTrace (prefixWord ++ tailWord_5998820) baseStart_5998820 baseEnd_5998820 := by
    simpa [prefixWord, tailWord_5998820, baseEnd_5998820] using wordTrace_append hprefix tailTrace_5998820
  have hstable : (prefixWord ++ tailWord_5998820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998820).length < 2 ^ (prefixWord ++ tailWord_5998820).sum := by decide
  have hdescent : baseEnd_5998820 < baseStart_5998820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998880 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 4]
def baseStart_5998880 : Nat := 118140960795 + 5998880 * 2 ^ 59
def prefixEnd_5998880 : Nat := 4983230072969 + 3 ^ 40 * 5998880 * 2
def baseEnd_5998880 : Nat := 3080308828643594588111659

theorem tailTrace_5998880 : CollatzResearch.WordTrace tailWord_5998880 prefixEnd_5998880 3080308828643594588111659 := by
  unfold tailWord_5998880
  simp only [CollatzResearch.WordTrace]
  refine ⟨109398564253544880991169047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145864752338059841321558729 109398564253544880991169047)
  ·
    refine ⟨164097846380317321486753571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109398564253544880991169047 164097846380317321486753571)
    ·
      refine ⟨246146769570475982230130357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164097846380317321486753571 246146769570475982230130357)
      ·
        refine ⟨23076259647232123334074721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 246146769570475982230130357 23076259647232123334074721)
        ·
          refine ⟨17307194735424092500556041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23076259647232123334074721 17307194735424092500556041)
          ·
            refine ⟨12980396051568069375417031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17307194735424092500556041 12980396051568069375417031)
            ·
              refine ⟨19470594077352104063125547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12980396051568069375417031 19470594077352104063125547)
              ·
                refine ⟨29205891116028156094688321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19470594077352104063125547 29205891116028156094688321)
                ·
                  refine ⟨21904418337021117071016241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29205891116028156094688321 21904418337021117071016241)
                  ·
                    refine ⟨16428313752765837803262181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21904418337021117071016241 16428313752765837803262181)
                    ·
                      refine ⟨3080308828643594588111659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16428313752765837803262181 3080308828643594588111659)
                      ·
                        rfl

theorem cell23_5998880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_5998880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998880 prefixEnd_5998880 := by exact prefixLift 5998880
  have htrace : WordTrace (prefixWord ++ tailWord_5998880) baseStart_5998880 baseEnd_5998880 := by
    simpa [prefixWord, tailWord_5998880, baseEnd_5998880] using wordTrace_append hprefix tailTrace_5998880
  have hstable : (prefixWord ++ tailWord_5998880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998880).length < 2 ^ (prefixWord ++ tailWord_5998880).sum := by decide
  have hdescent : baseEnd_5998880 < baseStart_5998880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998884 : List Nat := [2, 3, 1, 3, 1, 2, 2, 3, 2, 2, 2]
def baseStart_5998884 : Nat := 118140960795 + 5998884 * 2 ^ 59
def prefixEnd_5998884 : Nat := 4983230072969 + 3 ^ 40 * 5998884 * 2
def baseEnd_5998884 : Nat := 3080310882566212572461641

theorem tailTrace_5998884 : CollatzResearch.WordTrace tailWord_5998884 prefixEnd_5998884 3080310882566212572461641 := by
  unfold tailWord_5998884
  simp only [CollatzResearch.WordTrace]
  refine ⟨109398637199537635332741853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145864849599383513776989137 109398637199537635332741853)
  ·
    refine ⟨41024488949826613249778195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109398637199537635332741853 41024488949826613249778195)
    ·
      refine ⟨61536733424739919874667293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41024488949826613249778195 61536733424739919874667293)
      ·
        refine ⟨23076275034277469953000235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61536733424739919874667293 23076275034277469953000235)
        ·
          refine ⟨34614412551416204929500353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23076275034277469953000235 34614412551416204929500353)
          ·
            refine ⟨25960809413562153697125265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34614412551416204929500353 25960809413562153697125265)
            ·
              refine ⟨19470607060171615272843949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25960809413562153697125265 19470607060171615272843949)
              ·
                refine ⟨7301477647564355727316481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19470607060171615272843949 7301477647564355727316481)
                ·
                  refine ⟨5476108235673266795487361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7301477647564355727316481 5476108235673266795487361)
                  ·
                    refine ⟨4107081176754950096615521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5476108235673266795487361 4107081176754950096615521)
                    ·
                      refine ⟨3080310882566212572461641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4107081176754950096615521 3080310882566212572461641)
                      ·
                        rfl

theorem cell23_5998884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_5998884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998884 prefixEnd_5998884 := by exact prefixLift 5998884
  have htrace : WordTrace (prefixWord ++ tailWord_5998884) baseStart_5998884 baseEnd_5998884 := by
    simpa [prefixWord, tailWord_5998884, baseEnd_5998884] using wordTrace_append hprefix tailTrace_5998884
  have hstable : (prefixWord ++ tailWord_5998884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998884).length < 2 ^ (prefixWord ++ tailWord_5998884).sum := by decide
  have hdescent : baseEnd_5998884 < baseStart_5998884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998953 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 2, 4, 4]
def baseStart_5998953 : Nat := 118140960795 + 5998953 * 2 ^ 59
def prefixEnd_5998953 : Nat := 4983230072969 + 3 ^ 40 * 5998953 * 2
def baseEnd_5998953 : Nat := 3080346312731372802498823

theorem tailTrace_5998953 : CollatzResearch.WordTrace tailWord_5998953 prefixEnd_5998953 3080346312731372802498823 := by
  unfold tailWord_5998953
  simp only [CollatzResearch.WordTrace]
  refine ⟨218799791035825295449745513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145866527357216863633163675 218799791035825295449745513)
  ·
    refine ⟨164099843276868971587309135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218799791035825295449745513 164099843276868971587309135)
    ·
      refine ⟨246149764915303457380963703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164099843276868971587309135 246149764915303457380963703)
      ·
        refine ⟨369224647372955186071445555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246149764915303457380963703 369224647372955186071445555)
        ·
          refine ⟨553836971059432779107168333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369224647372955186071445555 553836971059432779107168333)
          ·
            refine ⟨207688864147287292165188125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 553836971059432779107168333 207688864147287292165188125)
            ·
              refine ⟨77883324055232734561945547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207688864147287292165188125 77883324055232734561945547)
              ·
                refine ⟨116824986082849101842918321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77883324055232734561945547 116824986082849101842918321)
                ·
                  refine ⟨87618739562136826382188741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116824986082849101842918321 87618739562136826382188741)
                  ·
                    refine ⟨16428513667900654946660389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87618739562136826382188741 16428513667900654946660389)
                    ·
                      refine ⟨3080346312731372802498823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16428513667900654946660389 3080346312731372802498823)
                      ·
                        rfl

theorem cell23_5998953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 4, 4].length) (baseStart_5998953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998953 prefixEnd_5998953 := by exact prefixLift 5998953
  have htrace : WordTrace (prefixWord ++ tailWord_5998953) baseStart_5998953 baseEnd_5998953 := by
    simpa [prefixWord, tailWord_5998953, baseEnd_5998953] using wordTrace_append hprefix tailTrace_5998953
  have hstable : (prefixWord ++ tailWord_5998953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998953).length < 2 ^ (prefixWord ++ tailWord_5998953).sum := by decide
  have hdescent : baseEnd_5998953 < baseStart_5998953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998960 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 3]
def baseStart_5998960 : Nat := 118140960795 + 5998960 * 2 ^ 59
def prefixEnd_5998960 : Nat := 4983230072969 + 3 ^ 40 * 5998960 * 2
def baseEnd_5998960 : Nat := 3080349907095954275111291

theorem tailTrace_5998960 : CollatzResearch.WordTrace tailWord_5998960 prefixEnd_5998960 3080349907095954275111291 := by
  unfold tailWord_5998960
  simp only [CollatzResearch.WordTrace]
  refine ⟨109400023173399967822625167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145866697564533290430166889 109400023173399967822625167)
  ·
    refine ⟨164100034760099951733937751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109400023173399967822625167 164100034760099951733937751)
    ·
      refine ⟨246150052140149927600906627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164100034760099951733937751 246150052140149927600906627)
      ·
        refine ⟨369225078210224891401359941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246150052140149927600906627 369225078210224891401359941)
        ·
          refine ⟨69229702164417167137754989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 369225078210224891401359941 69229702164417167137754989)
          ·
            refine ⟨25961138311656437676658121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69229702164417167137754989 25961138311656437676658121)
            ·
              refine ⟨19470853733742328257493591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25961138311656437676658121 19470853733742328257493591)
              ·
                refine ⟨29206280600613492386240387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19470853733742328257493591 29206280600613492386240387)
                ·
                  refine ⟨43809420900920238579360581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29206280600613492386240387 43809420900920238579360581)
                  ·
                    refine ⟨8214266418922544733630109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43809420900920238579360581 8214266418922544733630109)
                    ·
                      refine ⟨3080349907095954275111291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8214266418922544733630109 3080349907095954275111291)
                      ·
                        rfl

theorem cell23_5998960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 3].length) (baseStart_5998960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998960 prefixEnd_5998960 := by exact prefixLift 5998960
  have htrace : WordTrace (prefixWord ++ tailWord_5998960) baseStart_5998960 baseEnd_5998960 := by
    simpa [prefixWord, tailWord_5998960, baseEnd_5998960] using wordTrace_append hprefix tailTrace_5998960
  have hstable : (prefixWord ++ tailWord_5998960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998960).length < 2 ^ (prefixWord ++ tailWord_5998960).sum := by decide
  have hdescent : baseEnd_5998960 < baseStart_5998960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998967 : List Nat := [1, 1, 3, 1, 1, 2, 2, 7, 1, 4]
def baseStart_5998967 : Nat := 118140960795 + 5998967 * 2 ^ 59
def prefixEnd_5998967 : Nat := 4983230072969 + 3 ^ 40 * 5998967 * 2
def baseEnd_5998967 : Nat := 1026784500486845249241253

theorem tailTrace_5998967 : CollatzResearch.WordTrace tailWord_5998967 prefixEnd_5998967 1026784500486845249241253 := by
  unfold tailWord_5998967
  simp only [CollatzResearch.WordTrace]
  refine ⟨218800301657774575840755155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145866867771849717227170103 218800301657774575840755155)
  ·
    refine ⟨328200452486661863761132733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218800301657774575840755155 328200452486661863761132733)
    ·
      refine ⟨123075169682498198910424775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328200452486661863761132733 123075169682498198910424775)
      ·
        refine ⟨184612754523747298365637163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123075169682498198910424775 184612754523747298365637163)
        ·
          refine ⟨276919131785620947548455745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184612754523747298365637163 276919131785620947548455745)
          ·
            refine ⟨207689348839215710661341809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276919131785620947548455745 207689348839215710661341809)
            ·
              refine ⟨155767011629411782996006357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207689348839215710661341809 155767011629411782996006357)
              ·
                refine ⟨3650789335064338663968899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 155767011629411782996006357 3650789335064338663968899)
                ·
                  refine ⟨5476184002596507995953349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3650789335064338663968899 5476184002596507995953349)
                  ·
                    refine ⟨1026784500486845249241253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5476184002596507995953349 1026784500486845249241253)
                    ·
                      rfl

theorem cell23_5998967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 1, 4].length) (baseStart_5998967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998967 prefixEnd_5998967 := by exact prefixLift 5998967
  have htrace : WordTrace (prefixWord ++ tailWord_5998967) baseStart_5998967 baseEnd_5998967 := by
    simpa [prefixWord, tailWord_5998967, baseEnd_5998967] using wordTrace_append hprefix tailTrace_5998967
  have hstable : (prefixWord ++ tailWord_5998967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998967).length < 2 ^ (prefixWord ++ tailWord_5998967).sum := by decide
  have hdescent : baseEnd_5998967 < baseStart_5998967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998977 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 4, 2, 3]
def baseStart_5998977 : Nat := 118140960795 + 5998977 * 2 ^ 59
def prefixEnd_5998977 : Nat := 4983230072969 + 3 ^ 40 * 5998977 * 2
def baseEnd_5998977 : Nat := 3080358636267080708598713

theorem tailTrace_5998977 : CollatzResearch.WordTrace tailWord_5998977 prefixEnd_5998977 3080358636267080708598713 := by
  unfold tailWord_5998977
  simp only [CollatzResearch.WordTrace]
  refine ⟨218800666387738347548619185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145867110925158898365746123 218800666387738347548619185)
  ·
    refine ⟨164100499790803760661464389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218800666387738347548619185 164100499790803760661464389)
    ·
      refine ⟨30768843710775705124024573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164100499790803760661464389 30768843710775705124024573)
      ·
        refine ⟨11538316391540889421509215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30768843710775705124024573 11538316391540889421509215)
        ·
          refine ⟨17307474587311334132263823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11538316391540889421509215 17307474587311334132263823)
          ·
            refine ⟨25961211880967001198395735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17307474587311334132263823 25961211880967001198395735)
            ·
              refine ⟨38941817821450501797593603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25961211880967001198395735 38941817821450501797593603)
              ·
                refine ⟨58412726732175752696390405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38941817821450501797593603 58412726732175752696390405)
                ·
                  refine ⟨10952386262282953630573201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58412726732175752696390405 10952386262282953630573201)
                  ·
                    refine ⟨8214289696712215222929901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10952386262282953630573201 8214289696712215222929901)
                    ·
                      refine ⟨3080358636267080708598713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8214289696712215222929901 3080358636267080708598713)
                      ·
                        rfl

theorem cell23_5998977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_5998977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998977 prefixEnd_5998977 := by exact prefixLift 5998977
  have htrace : WordTrace (prefixWord ++ tailWord_5998977) baseStart_5998977 baseEnd_5998977 := by
    simpa [prefixWord, tailWord_5998977, baseEnd_5998977] using wordTrace_append hprefix tailTrace_5998977
  have hstable : (prefixWord ++ tailWord_5998977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998977).length < 2 ^ (prefixWord ++ tailWord_5998977).sum := by decide
  have hdescent : baseEnd_5998977 < baseStart_5998977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998980 : List Nat := [2, 3, 2, 1, 1, 2, 2, 4, 6]
def baseStart_5998980 : Nat := 118140960795 + 5998980 * 2 ^ 59
def prefixEnd_5998980 : Nat := 4983230072969 + 3 ^ 40 * 5998980 * 2
def baseEnd_5998980 : Nat := 342262241856560466317911

theorem tailTrace_5998980 : CollatzResearch.WordTrace tailWord_5998980 prefixEnd_5998980 342262241856560466317911 := by
  unfold tailWord_5998980
  simp only [CollatzResearch.WordTrace]
  refine ⟨109400387903363739530489197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145867183871151652707318929 109400387903363739530489197)
  ·
    refine ⟨41025145463761402323933449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109400387903363739530489197 41025145463761402323933449)
    ·
      refine ⟨30768859097821051742950087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41025145463761402323933449 30768859097821051742950087)
      ·
        refine ⟨46153288646731577614425131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30768859097821051742950087 46153288646731577614425131)
        ·
          refine ⟨69229932970097366421637697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46153288646731577614425131 69229932970097366421637697)
          ·
            refine ⟨51922449727573024816228273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69229932970097366421637697 51922449727573024816228273)
            ·
              refine ⟨38941837295679768612171205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51922449727573024816228273 38941837295679768612171205)
              ·
                refine ⟨7301594492939956614782101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38941837295679768612171205 7301594492939956614782101)
                ·
                  refine ⟨342262241856560466317911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7301594492939956614782101 342262241856560466317911)
                  ·
                    rfl

theorem cell23_5998980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_5998980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998980 prefixEnd_5998980 := by exact prefixLift 5998980
  have htrace : WordTrace (prefixWord ++ tailWord_5998980) baseStart_5998980 baseEnd_5998980 := by
    simpa [prefixWord, tailWord_5998980, baseEnd_5998980] using wordTrace_append hprefix tailTrace_5998980
  have hstable : (prefixWord ++ tailWord_5998980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998980).length < 2 ^ (prefixWord ++ tailWord_5998980).sum := by decide
  have hdescent : baseEnd_5998980 < baseStart_5998980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999007 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 5, 1, 3]
def baseStart_5999007 : Nat := 118140960795 + 5999007 * 2 ^ 59
def prefixEnd_5999007 : Nat := 4983230072969 + 3 ^ 40 * 5999007 * 2
def baseEnd_5999007 : Nat := 3080374040686715591223575

theorem tailTrace_5999007 : CollatzResearch.WordTrace tailWord_5999007 prefixEnd_5999007 3080374040686715591223575 := by
  unfold tailWord_5999007
  simp only [CollatzResearch.WordTrace]
  refine ⟨218801760577629662672211275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145867840385086441781474183 218801760577629662672211275)
  ·
    refine ⟨328202640866444494008316913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218801760577629662672211275 328202640866444494008316913)
    ·
      refine ⟨246151980649833370506237685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328202640866444494008316913 246151980649833370506237685)
      ·
        refine ⟨23076748185921878484959783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 246151980649833370506237685 23076748185921878484959783)
        ·
          refine ⟨34615122278882817727439675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23076748185921878484959783 34615122278882817727439675)
          ·
            refine ⟨51922683418324226591159513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34615122278882817727439675 51922683418324226591159513)
            ·
              refine ⟨38942012563743169943369635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51922683418324226591159513 38942012563743169943369635)
              ·
                refine ⟨58413018845614754915054453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38942012563743169943369635 58413018845614754915054453)
                ·
                  refine ⟨5476220516776383273286355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58413018845614754915054453 5476220516776383273286355)
                  ·
                    refine ⟨8214330775164574909929533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5476220516776383273286355 8214330775164574909929533)
                    ·
                      refine ⟨3080374040686715591223575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8214330775164574909929533 3080374040686715591223575)
                      ·
                        rfl

theorem cell23_5999007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_5999007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999007 prefixEnd_5999007 := by exact prefixLift 5999007
  have htrace : WordTrace (prefixWord ++ tailWord_5999007) baseStart_5999007 baseEnd_5999007 := by
    simpa [prefixWord, tailWord_5999007, baseEnd_5999007] using wordTrace_append hprefix tailTrace_5999007
  have hstable : (prefixWord ++ tailWord_5999007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999007).length < 2 ^ (prefixWord ++ tailWord_5999007).sum := by decide
  have hdescent : baseEnd_5999007 < baseStart_5999007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999050 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 3, 1, 5]
def baseStart_5999050 : Nat := 118140960795 + 5999050 * 2 ^ 59
def prefixEnd_5999050 : Nat := 4983230072969 + 3 ^ 40 * 5999050 * 2
def baseEnd_5999050 : Nat := 3080396120354858922985877

theorem tailTrace_5999050 : CollatzResearch.WordTrace tailWord_5999050 prefixEnd_5999050 3080396120354858922985877 := by
  unfold tailWord_5999050
  simp only [CollatzResearch.WordTrace]
  refine ⟨54700832229118470254006651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145868885944315920677351069 54700832229118470254006651)
  ·
    refine ⟨82051248343677705381009977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54700832229118470254006651 82051248343677705381009977)
    ·
      refine ⟨61538436257758279035757483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82051248343677705381009977 61538436257758279035757483)
      ·
        refine ⟨92307654386637418553636225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61538436257758279035757483 92307654386637418553636225)
        ·
          refine ⟨69230740789978063915227169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92307654386637418553636225 69230740789978063915227169)
          ·
            refine ⟨51923055592483547936420377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69230740789978063915227169 51923055592483547936420377)
            ·
              refine ⟨38942291694362660952315283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51923055592483547936420377 38942291694362660952315283)
              ·
                refine ⟨58413437541543991428472925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38942291694362660952315283 58413437541543991428472925)
                ·
                  refine ⟨21905039078078996785677347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58413437541543991428472925 21905039078078996785677347)
                  ·
                    refine ⟨32857558617118495178516021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21905039078078996785677347 32857558617118495178516021)
                    ·
                      refine ⟨3080396120354858922985877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32857558617118495178516021 3080396120354858922985877)
                      ·
                        rfl

theorem cell23_5999050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_5999050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999050 prefixEnd_5999050 := by exact prefixLift 5999050
  have htrace : WordTrace (prefixWord ++ tailWord_5999050) baseStart_5999050 baseEnd_5999050 := by
    simpa [prefixWord, tailWord_5999050, baseEnd_5999050] using wordTrace_append hprefix tailTrace_5999050
  have hstable : (prefixWord ++ tailWord_5999050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999050).length < 2 ^ (prefixWord ++ tailWord_5999050).sum := by decide
  have hdescent : baseEnd_5999050 < baseStart_5999050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999111 : List Nat := [1, 1, 4, 3, 4, 1, 1, 1, 1, 2, 4]
def baseStart_5999111 : Nat := 118140960795 + 5999111 * 2 ^ 59
def prefixEnd_5999111 : Nat := 4983230072969 + 3 ^ 40 * 5999111 * 2
def baseEnd_5999111 : Nat := 3080427442674783184323097

theorem tailTrace_5999111 : CollatzResearch.WordTrace tailWord_5999111 prefixEnd_5999111 3080427442674783184323097 := by
  unfold tailWord_5999111
  simp only [CollatzResearch.WordTrace]
  refine ⟨218805553769252888433997187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145870369179501925622664791 218805553769252888433997187)
  ·
    refine ⟨328208330653879332650995781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218805553769252888433997187 328208330653879332650995781)
    ·
      refine ⟨61539061997602374872061709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 328208330653879332650995781 61539061997602374872061709)
      ·
        refine ⟨23077148249100890577023141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61539061997602374872061709 23077148249100890577023141)
        ·
          refine ⟨4326965296706416983191839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23077148249100890577023141 4326965296706416983191839)
          ·
            refine ⟨6490447945059625474787759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4326965296706416983191839 6490447945059625474787759)
            ·
              refine ⟨9735671917589438212181639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6490447945059625474787759 9735671917589438212181639)
              ·
                refine ⟨14603507876384157318272459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9735671917589438212181639 14603507876384157318272459)
                ·
                  refine ⟨21905261814576235977408689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14603507876384157318272459 21905261814576235977408689)
                  ·
                    refine ⟨16428946360932176983056517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21905261814576235977408689 16428946360932176983056517)
                    ·
                      refine ⟨3080427442674783184323097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16428946360932176983056517 3080427442674783184323097)
                      ·
                        rfl

theorem cell23_5999111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_5999111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999111 prefixEnd_5999111 := by exact prefixLift 5999111
  have htrace : WordTrace (prefixWord ++ tailWord_5999111) baseStart_5999111 baseEnd_5999111 := by
    simpa [prefixWord, tailWord_5999111, baseEnd_5999111] using wordTrace_append hprefix tailTrace_5999111
  have hstable : (prefixWord ++ tailWord_5999111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999111).length < 2 ^ (prefixWord ++ tailWord_5999111).sum := by decide
  have hdescent : baseEnd_5999111 < baseStart_5999111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999130 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 1, 8]
def baseStart_5999130 : Nat := 118140960795 + 5999130 * 2 ^ 59
def prefixEnd_5999130 : Nat := 4983230072969 + 3 ^ 40 * 5999130 * 2
def baseEnd_5999130 : Nat := 1026812399602406203328503

theorem tailTrace_5999130 : CollatzResearch.WordTrace tailWord_5999130 prefixEnd_5999130 1026812399602406203328503 := by
  unfold tailWord_5999130
  simp only [CollatzResearch.WordTrace]
  refine ⟨54701561689046013669734711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145870831170789369785959229 54701561689046013669734711)
  ·
    refine ⟨82052342533569020504602067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54701561689046013669734711 82052342533569020504602067)
    ·
      refine ⟨123078513800353530756903101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82052342533569020504602067 123078513800353530756903101)
      ·
        refine ⟨46154442675132574033838663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123078513800353530756903101 46154442675132574033838663)
        ·
          refine ⟨69231664012698861050757995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46154442675132574033838663 69231664012698861050757995)
          ·
            refine ⟨103847496019048291576136993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69231664012698861050757995 103847496019048291576136993)
            ·
              refine ⟨77885622014286218682102745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103847496019048291576136993 77885622014286218682102745)
              ·
                refine ⟨58414216510714664011577059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77885622014286218682102745 58414216510714664011577059)
                ·
                  refine ⟨87621324766071996017365589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58414216510714664011577059 87621324766071996017365589)
                  ·
                    refine ⟨1026812399602406203328503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87621324766071996017365589 1026812399602406203328503)
                    ·
                      rfl

theorem cell23_5999130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_5999130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999130 prefixEnd_5999130 := by exact prefixLift 5999130
  have htrace : WordTrace (prefixWord ++ tailWord_5999130) baseStart_5999130 baseEnd_5999130 := by
    simpa [prefixWord, tailWord_5999130, baseEnd_5999130] using wordTrace_append hprefix tailTrace_5999130
  have hstable : (prefixWord ++ tailWord_5999130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999130).length < 2 ^ (prefixWord ++ tailWord_5999130).sum := by decide
  have hdescent : baseEnd_5999130 < baseStart_5999130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999149 : List Nat := [1, 5, 4, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_5999149 : Nat := 118140960795 + 5999149 * 2 ^ 59
def prefixEnd_5999149 : Nat := 4983230072969 + 3 ^ 40 * 5999149 * 2
def baseEnd_5999149 : Nat := 3080446954939654035647923

theorem tailTrace_5999149 : CollatzResearch.WordTrace tailWord_5999149 prefixEnd_5999149 3080446954939654035647923 := by
  unfold tailWord_5999149
  simp only [CollatzResearch.WordTrace]
  refine ⟨218806939743115220923880501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145871293162076813949253667 218806939743115220923880501)
  ·
    refine ⟨20513150600917051961613797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218806939743115220923880501 20513150600917051961613797)
    ·
      refine ⟨3846215737671947242802587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20513150600917051961613797 3846215737671947242802587)
      ·
        refine ⟨5769323606507920864203881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3846215737671947242802587 5769323606507920864203881)
        ·
          refine ⟨4326992704880940648152911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5769323606507920864203881 4326992704880940648152911)
          ·
            refine ⟨6490489057321410972229367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4326992704880940648152911 6490489057321410972229367)
            ·
              refine ⟨9735733585982116458344051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6490489057321410972229367 9735733585982116458344051)
              ·
                refine ⟨14603600378973174687516077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9735733585982116458344051 14603600378973174687516077)
                ·
                  refine ⟨5476350142114940507818529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14603600378973174687516077 5476350142114940507818529)
                  ·
                    refine ⟨4107262606586205380863897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5476350142114940507818529 4107262606586205380863897)
                    ·
                      refine ⟨3080446954939654035647923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4107262606586205380863897 3080446954939654035647923)
                      ·
                        rfl

theorem cell23_5999149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_5999149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999149 prefixEnd_5999149 := by exact prefixLift 5999149
  have htrace : WordTrace (prefixWord ++ tailWord_5999149) baseStart_5999149 baseEnd_5999149 := by
    simpa [prefixWord, tailWord_5999149, baseEnd_5999149] using wordTrace_append hprefix tailTrace_5999149
  have hstable : (prefixWord ++ tailWord_5999149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999149).length < 2 ^ (prefixWord ++ tailWord_5999149).sum := by decide
  have hdescent : baseEnd_5999149 < baseStart_5999149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999157 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 2, 4, 3]
def baseStart_5999157 : Nat := 118140960795 + 5999157 * 2 ^ 59
def prefixEnd_5999157 : Nat := 4983230072969 + 3 ^ 40 * 5999157 * 2
def baseEnd_5999157 : Nat := 3080451062784890004347885

theorem tailTrace_5999157 : CollatzResearch.WordTrace tailWord_5999157 prefixEnd_5999157 3080451062784890004347885 := by
  unfold tailWord_5999157
  simp only [CollatzResearch.WordTrace]
  refine ⟨218807231527086238290171725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145871487684724158860114483 218807231527086238290171725)
  ·
    refine ⟨82052711822657339358814397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218807231527086238290171725 82052711822657339358814397)
    ·
      refine ⟨30769766933496502259555399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82052711822657339358814397 30769766933496502259555399)
      ·
        refine ⟨46154650400244753389333099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30769766933496502259555399 46154650400244753389333099)
        ·
          refine ⟨69231975600367130083999649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46154650400244753389333099 69231975600367130083999649)
          ·
            refine ⟨51923981700275347562999737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69231975600367130083999649 51923981700275347562999737)
            ·
              refine ⟨38942986275206510672249803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51923981700275347562999737 38942986275206510672249803)
              ·
                refine ⟨58414479412809766008374705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38942986275206510672249803 58414479412809766008374705)
                ·
                  refine ⟨43810859559607324506281029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58414479412809766008374705 43810859559607324506281029)
                  ·
                    refine ⟨8214536167426373344927693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43810859559607324506281029 8214536167426373344927693)
                    ·
                      refine ⟨3080451062784890004347885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8214536167426373344927693 3080451062784890004347885)
                      ·
                        rfl

theorem cell23_5999157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_5999157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999157 prefixEnd_5999157 := by exact prefixLift 5999157
  have htrace : WordTrace (prefixWord ++ tailWord_5999157) baseStart_5999157 baseEnd_5999157 := by
    simpa [prefixWord, tailWord_5999157, baseEnd_5999157] using wordTrace_append hprefix tailTrace_5999157
  have hstable : (prefixWord ++ tailWord_5999157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999157).length < 2 ^ (prefixWord ++ tailWord_5999157).sum := by decide
  have hdescent : baseEnd_5999157 < baseStart_5999157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999221 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_5999221 : Nat := 118140960795 + 5999221 * 2 ^ 59
def prefixEnd_5999221 : Nat := 4983230072969 + 3 ^ 40 * 5999221 * 2
def baseEnd_5999221 : Nat := 3080483925546777753947591

theorem tailTrace_5999221 : CollatzResearch.WordTrace tailWord_5999221 prefixEnd_5999221 3080483925546777753947591 := by
  unfold tailWord_5999221
  simp only [CollatzResearch.WordTrace]
  refine ⟨218809565798854377220501517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145873043865902918147001011 218809565798854377220501517)
  ·
    refine ⟨82053587174570391457688069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218809565798854377220501517 82053587174570391457688069)
    ·
      refine ⟨15385047595231948398316513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82053587174570391457688069 15385047595231948398316513)
      ·
        refine ⟨11538785696423961298737385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15385047595231948398316513 11538785696423961298737385)
        ·
          refine ⟨8654089272317970974053039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11538785696423961298737385 8654089272317970974053039)
          ·
            refine ⟨12981133908476956461079559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8654089272317970974053039 12981133908476956461079559)
            ·
              refine ⟨19471700862715434691619339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12981133908476956461079559 19471700862715434691619339)
              ·
                refine ⟨29207551294073152037429009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19471700862715434691619339 29207551294073152037429009)
                ·
                  refine ⟨21905663470554864028071757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29207551294073152037429009 21905663470554864028071757)
                  ·
                    refine ⟨8214623801458074010526909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21905663470554864028071757 8214623801458074010526909)
                    ·
                      refine ⟨3080483925546777753947591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8214623801458074010526909 3080483925546777753947591)
                      ·
                        rfl

theorem cell23_5999221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_5999221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999221 prefixEnd_5999221 := by exact prefixLift 5999221
  have htrace : WordTrace (prefixWord ++ tailWord_5999221) baseStart_5999221 baseEnd_5999221 := by
    simpa [prefixWord, tailWord_5999221, baseEnd_5999221] using wordTrace_append hprefix tailTrace_5999221
  have hstable : (prefixWord ++ tailWord_5999221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999221).length < 2 ^ (prefixWord ++ tailWord_5999221).sum := by decide
  have hdescent : baseEnd_5999221 < baseStart_5999221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999247 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 3]
def baseStart_5999247 : Nat := 118140960795 + 5999247 * 2 ^ 59
def prefixEnd_5999247 : Nat := 4983230072969 + 3 ^ 40 * 5999247 * 2
def baseEnd_5999247 : Nat := 3080497276043794652222471

theorem tailTrace_5999247 : CollatzResearch.WordTrace tailWord_5999247 prefixEnd_5999247 3080497276043794652222471 := by
  unfold tailWord_5999247
  simp only [CollatzResearch.WordTrace]
  refine ⟨218810514096760183660947995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145873676064506789107298663 218810514096760183660947995)
  ·
    refine ⟨328215771145140275491421993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218810514096760183660947995 328215771145140275491421993)
    ·
      refine ⟨246161828358855206618566495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328215771145140275491421993 246161828358855206618566495)
      ·
        refine ⟨369242742538282809927849743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246161828358855206618566495 369242742538282809927849743)
        ·
          refine ⟨553864113807424214891774615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369242742538282809927849743 553864113807424214891774615)
          ·
            refine ⟨830796170711136322337661923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553864113807424214891774615 830796170711136322337661923)
            ·
              refine ⟨1246194256066704483506492885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830796170711136322337661923 1246194256066704483506492885)
              ·
                refine ⟨29207677876563386332183427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1246194256066704483506492885 29207677876563386332183427)
                ·
                  refine ⟨43811516814845079498275141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29207677876563386332183427 43811516814845079498275141)
                  ·
                    refine ⟨8214659402783452405926589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43811516814845079498275141 8214659402783452405926589)
                    ·
                      refine ⟨3080497276043794652222471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8214659402783452405926589 3080497276043794652222471)
                      ·
                        rfl

theorem cell23_5999247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 3].length) (baseStart_5999247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999247 prefixEnd_5999247 := by exact prefixLift 5999247
  have htrace : WordTrace (prefixWord ++ tailWord_5999247) baseStart_5999247 baseEnd_5999247 := by
    simpa [prefixWord, tailWord_5999247, baseEnd_5999247] using wordTrace_append hprefix tailTrace_5999247
  have hstable : (prefixWord ++ tailWord_5999247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999247).length < 2 ^ (prefixWord ++ tailWord_5999247).sum := by decide
  have hdescent : baseEnd_5999247 < baseStart_5999247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999267 : List Nat := [1, 1, 1, 4, 1, 1, 2, 6, 6]
def baseStart_5999267 : Nat := 118140960795 + 5999267 * 2 ^ 59
def prefixEnd_5999267 : Nat := 4983230072969 + 3 ^ 40 * 5999267 * 2
def baseEnd_5999267 : Nat := 342278616184098285996931

theorem tailTrace_5999267 : CollatzResearch.WordTrace tailWord_5999267 prefixEnd_5999267 342278616184098285996931 := by
  unfold tailWord_5999267
  simp only [CollatzResearch.WordTrace]
  refine ⟨218811243556687727076676055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145874162371125151384450703 218811243556687727076676055)
  ·
    refine ⟨328216865335031590615014083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218811243556687727076676055 328216865335031590615014083)
    ·
      refine ⟨492325298002547385922521125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328216865335031590615014083 492325298002547385922521125)
      ·
        refine ⟨92310993375477634860472711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 492325298002547385922521125 92310993375477634860472711)
        ·
          refine ⟨138466490063216452290709067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92310993375477634860472711 138466490063216452290709067)
          ·
            refine ⟨207699735094824678436063601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138466490063216452290709067 207699735094824678436063601)
            ·
              refine ⟨155774801321118508827047701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207699735094824678436063601 155774801321118508827047701)
              ·
                refine ⟨7301943811927430101267861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 155774801321118508827047701 7301943811927430101267861)
                ·
                  refine ⟨342278616184098285996931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7301943811927430101267861 342278616184098285996931)
                  ·
                    rfl

theorem cell23_5999267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 6].length) (baseStart_5999267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999267 prefixEnd_5999267 := by exact prefixLift 5999267
  have htrace : WordTrace (prefixWord ++ tailWord_5999267) baseStart_5999267 baseEnd_5999267 := by
    simpa [prefixWord, tailWord_5999267, baseEnd_5999267] using wordTrace_append hprefix tailTrace_5999267
  have hstable : (prefixWord ++ tailWord_5999267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999267).length < 2 ^ (prefixWord ++ tailWord_5999267).sum := by decide
  have hdescent : baseEnd_5999267 < baseStart_5999267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999278 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_5999278 : Nat := 118140960795 + 5999278 * 2 ^ 59
def prefixEnd_5999278 : Nat := 4983230072969 + 3 ^ 40 * 5999278 * 2
def baseEnd_5999278 : Nat := 3080513193944084030934829

theorem tailTrace_5999278 : CollatzResearch.WordTrace tailWord_5999278 prefixEnd_5999278 3080513193944084030934829 := by
  unfold tailWord_5999278
  simp only [CollatzResearch.WordTrace]
  refine ⟨27351455594955984494415811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145874429839765250636884325 27351455594955984494415811)
  ·
    refine ⟨41027183392433976741623717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27351455594955984494415811 41027183392433976741623717)
    ·
      refine ⟨7692596886081370639054447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41027183392433976741623717 7692596886081370639054447)
      ·
        refine ⟨11538895329122055958581671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7692596886081370639054447 11538895329122055958581671)
        ·
          refine ⟨17308342993683083937872507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11538895329122055958581671 17308342993683083937872507)
          ·
            refine ⟨25962514490524625906808761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17308342993683083937872507 25962514490524625906808761)
            ·
              refine ⟨19471885867893469430106571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25962514490524625906808761 19471885867893469430106571)
              ·
                refine ⟨29207828801840204145159857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19471885867893469430106571 29207828801840204145159857)
                ·
                  refine ⟨21905871601380153108869893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29207828801840204145159857 21905871601380153108869893)
                  ·
                    refine ⟨4107350925258778707913105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21905871601380153108869893 4107350925258778707913105)
                    ·
                      refine ⟨3080513193944084030934829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4107350925258778707913105 3080513193944084030934829)
                      ·
                        rfl

theorem cell23_5999278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_5999278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999278 prefixEnd_5999278 := by exact prefixLift 5999278
  have htrace : WordTrace (prefixWord ++ tailWord_5999278) baseStart_5999278 baseEnd_5999278 := by
    simpa [prefixWord, tailWord_5999278, baseEnd_5999278] using wordTrace_append hprefix tailTrace_5999278
  have hstable : (prefixWord ++ tailWord_5999278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999278).length < 2 ^ (prefixWord ++ tailWord_5999278).sum := by decide
  have hdescent : baseEnd_5999278 < baseStart_5999278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999294 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3]
def baseStart_5999294 : Nat := 118140960795 + 5999294 * 2 ^ 59
def prefixEnd_5999294 : Nat := 4983230072969 + 3 ^ 40 * 5999294 * 2
def baseEnd_5999294 : Nat := 3080521409634555968334755

theorem tailTrace_5999294 : CollatzResearch.WordTrace tailWord_5999294 prefixEnd_5999294 3080521409634555968334755 := by
  unfold tailWord_5999294
  simp only [CollatzResearch.WordTrace]
  refine ⟨27351528540948738835988617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145874818885059940458605957 27351528540948738835988617)
  ·
    refine ⟨20513646405711554126991463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27351528540948738835988617 20513646405711554126991463)
    ·
      refine ⟨30770469608567331190487195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20513646405711554126991463 30770469608567331190487195)
      ·
        refine ⟨46155704412850996785730793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30770469608567331190487195 46155704412850996785730793)
        ·
          refine ⟨34616778309638247589298095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46155704412850996785730793 34616778309638247589298095)
          ·
            refine ⟨51925167464457371383947143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34616778309638247589298095 51925167464457371383947143)
            ·
              refine ⟨77887751196686057075920715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51925167464457371383947143 77887751196686057075920715)
              ·
                refine ⟨116831626795029085613881073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77887751196686057075920715 116831626795029085613881073)
                ·
                  refine ⟨87623720096271814210410805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116831626795029085613881073 87623720096271814210410805)
                  ·
                    refine ⟨8214723759025482582226013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87623720096271814210410805 8214723759025482582226013)
                    ·
                      refine ⟨3080521409634555968334755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8214723759025482582226013 3080521409634555968334755)
                      ·
                        rfl

theorem cell23_5999294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_5999294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999294 prefixEnd_5999294 := by exact prefixLift 5999294
  have htrace : WordTrace (prefixWord ++ tailWord_5999294) baseStart_5999294 baseEnd_5999294 := by
    simpa [prefixWord, tailWord_5999294, baseEnd_5999294] using wordTrace_append hprefix tailTrace_5999294
  have hstable : (prefixWord ++ tailWord_5999294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999294).length < 2 ^ (prefixWord ++ tailWord_5999294).sum := by decide
  have hdescent : baseEnd_5999294 < baseStart_5999294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999321 : List Nat := [1, 2, 1, 2, 3, 2, 3, 2, 2, 3, 2]
def baseStart_5999321 : Nat := 118140960795 + 5999321 * 2 ^ 59
def prefixEnd_5999321 : Nat := 4983230072969 + 3 ^ 40 * 5999321 * 2
def baseEnd_5999321 : Nat := 3080535273612227362697131

theorem tailTrace_5999321 : CollatzResearch.WordTrace tailWord_5999321 prefixEnd_5999321 3080535273612227362697131 := by
  unfold tailWord_5999321
  simp only [CollatzResearch.WordTrace]
  refine ⟨218813213098492094299141817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145875475398994729532761211 218813213098492094299141817)
  ·
    refine ⟨164109909823869070724356363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218813213098492094299141817 164109909823869070724356363)
    ·
      refine ⟨246164864735803606086534545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164109909823869070724356363 246164864735803606086534545)
      ·
        refine ⟨184623648551852704564900909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246164864735803606086534545 184623648551852704564900909)
        ·
          refine ⟨69233868206944764211837841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184623648551852704564900909 69233868206944764211837841)
          ·
            refine ⟨51925401155208573158878381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69233868206944764211837841 51925401155208573158878381)
            ·
              refine ⟨19472025433203214934579393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51925401155208573158878381 19472025433203214934579393)
              ·
                refine ⟨14604019074902411200934545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19472025433203214934579393 14604019074902411200934545)
                ·
                  refine ⟨10953014306176808400700909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14604019074902411200934545 10953014306176808400700909)
                  ·
                    refine ⟨4107380364816303150262841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10953014306176808400700909 4107380364816303150262841)
                    ·
                      refine ⟨3080535273612227362697131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4107380364816303150262841 3080535273612227362697131)
                      ·
                        rfl

theorem cell23_5999321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 3, 2].length) (baseStart_5999321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999321 prefixEnd_5999321 := by exact prefixLift 5999321
  have htrace : WordTrace (prefixWord ++ tailWord_5999321) baseStart_5999321 baseEnd_5999321 := by
    simpa [prefixWord, tailWord_5999321, baseEnd_5999321] using wordTrace_append hprefix tailTrace_5999321
  have hstable : (prefixWord ++ tailWord_5999321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999321).length < 2 ^ (prefixWord ++ tailWord_5999321).sum := by decide
  have hdescent : baseEnd_5999321 < baseStart_5999321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999351 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 5, 2, 2]
def baseStart_5999351 : Nat := 118140960795 + 5999351 * 2 ^ 59
def prefixEnd_5999351 : Nat := 4983230072969 + 3 ^ 40 * 5999351 * 2
def baseEnd_5999351 : Nat := 3080550678031862245321993

theorem tailTrace_5999351 : CollatzResearch.WordTrace tailWord_5999351 prefixEnd_5999351 3080550678031862245321993 := by
  unfold tailWord_5999351
  simp only [CollatzResearch.WordTrace]
  refine ⟨218814307288383409422733907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145876204858922272948489271 218814307288383409422733907)
  ·
    refine ⟨328221460932575114134100861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218814307288383409422733907 328221460932575114134100861)
    ·
      refine ⟨123083047849715667800287823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328221460932575114134100861 123083047849715667800287823)
      ·
        refine ⟨184624571774573501700431735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123083047849715667800287823 184624571774573501700431735)
        ·
          refine ⟨276936857661860252550647603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184624571774573501700431735 276936857661860252550647603)
          ·
            refine ⟨415405286492790378825971405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276936857661860252550647603 415405286492790378825971405)
            ·
              refine ⟨155776982434796392059739277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 415405286492790378825971405 155776982434796392059739277)
              ·
                refine ⟨58416368413048647022402229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155776982434796392059739277 58416368413048647022402229)
                ·
                  refine ⟨5476534538723310658350209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58416368413048647022402229 5476534538723310658350209)
                  ·
                    refine ⟨4107400904042482993762657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5476534538723310658350209 4107400904042482993762657)
                    ·
                      refine ⟨3080550678031862245321993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4107400904042482993762657 3080550678031862245321993)
                      ·
                        rfl

theorem cell23_5999351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 2, 2].length) (baseStart_5999351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999351 prefixEnd_5999351 := by exact prefixLift 5999351
  have htrace : WordTrace (prefixWord ++ tailWord_5999351) baseStart_5999351 baseEnd_5999351 := by
    simpa [prefixWord, tailWord_5999351, baseEnd_5999351] using wordTrace_append hprefix tailTrace_5999351
  have hstable : (prefixWord ++ tailWord_5999351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999351).length < 2 ^ (prefixWord ++ tailWord_5999351).sum := by decide
  have hdescent : baseEnd_5999351 < baseStart_5999351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999357 : List Nat := [1, 4, 1, 1, 1, 1, 3, 11]
def baseStart_5999357 : Nat := 118140960795 + 5999357 * 2 ^ 59
def prefixEnd_5999357 : Nat := 4983230072969 + 3 ^ 40 * 5999357 * 2
def baseEnd_5999357 : Nat := 114094583663547748957295

theorem tailTrace_5999357 : CollatzResearch.WordTrace tailWord_5999357 prefixEnd_5999357 114094583663547748957295 := by
  unfold tailWord_5999357
  simp only [CollatzResearch.WordTrace]
  refine ⟨218814526126361672447452325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145876350750907781631634883 218814526126361672447452325)
  ·
    refine ⟨41027723648692813583897311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218814526126361672447452325 41027723648692813583897311)
    ·
      refine ⟨61541585473039220375845967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41027723648692813583897311 61541585473039220375845967)
      ·
        refine ⟨92312378209558830563768951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61541585473039220375845967 92312378209558830563768951)
        ·
          refine ⟨138468567314338245845653427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92312378209558830563768951 138468567314338245845653427)
          ·
            refine ⟨207702850971507368768480141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138468567314338245845653427 207702850971507368768480141)
            ·
              refine ⟨77888569114315263288180053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207702850971507368768480141 77888569114315263288180053)
              ·
                refine ⟨114094583663547748957295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 77888569114315263288180053 114094583663547748957295)
                ·
                  rfl

theorem cell23_5999357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 11].length) (baseStart_5999357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999357 prefixEnd_5999357 := by exact prefixLift 5999357
  have htrace : WordTrace (prefixWord ++ tailWord_5999357) baseStart_5999357 baseEnd_5999357 := by
    simpa [prefixWord, tailWord_5999357, baseEnd_5999357] using wordTrace_append hprefix tailTrace_5999357
  have hstable : (prefixWord ++ tailWord_5999357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999357).length < 2 ^ (prefixWord ++ tailWord_5999357).sum := by decide
  have hdescent : baseEnd_5999357 < baseStart_5999357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999368 : List Nat := [2, 1, 3, 2, 2, 3, 3, 1, 1, 1, 4]
def baseStart_5999368 : Nat := 118140960795 + 5999368 * 2 ^ 59
def prefixEnd_5999368 : Nat := 4983230072969 + 3 ^ 40 * 5999368 * 2
def baseEnd_5999368 : Nat := 3080559407202988678809415

theorem tailTrace_5999368 : CollatzResearch.WordTrace tailWord_5999368 prefixEnd_5999368 3080559407202988678809415 := by
  unfold tailWord_5999368
  simp only [CollatzResearch.WordTrace]
  refine ⟨109407463664660910663051379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145876618219547880884068505 109407463664660910663051379)
  ·
    refine ⟨164111195496991365994577069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109407463664660910663051379 164111195496991365994577069)
    ·
      refine ⟨61541698311371762247966401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164111195496991365994577069 61541698311371762247966401)
      ·
        refine ⟨46156273733528821685974801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61541698311371762247966401 46156273733528821685974801)
        ·
          refine ⟨34617205300146616264481101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46156273733528821685974801 34617205300146616264481101)
          ·
            refine ⟨12981451987554981099180413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34617205300146616264481101 12981451987554981099180413)
            ·
              refine ⟨4868044495333117912192655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12981451987554981099180413 4868044495333117912192655)
              ·
                refine ⟨7302066742999676868288983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4868044495333117912192655 7302066742999676868288983)
                ·
                  refine ⟨10953100114499515302433475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7302066742999676868288983 10953100114499515302433475)
                  ·
                    refine ⟨16429650171749272953650213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10953100114499515302433475 16429650171749272953650213)
                    ·
                      refine ⟨3080559407202988678809415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16429650171749272953650213 3080559407202988678809415)
                      ·
                        rfl

theorem cell23_5999368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_5999368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999368 prefixEnd_5999368 := by exact prefixLift 5999368
  have htrace : WordTrace (prefixWord ++ tailWord_5999368) baseStart_5999368 baseEnd_5999368 := by
    simpa [prefixWord, tailWord_5999368, baseEnd_5999368] using wordTrace_append hprefix tailTrace_5999368
  have hstable : (prefixWord ++ tailWord_5999368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999368).length < 2 ^ (prefixWord ++ tailWord_5999368).sum := by decide
  have hdescent : baseEnd_5999368 < baseStart_5999368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999384 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 5, 3, 3]
def baseStart_5999384 : Nat := 118140960795 + 5999384 * 2 ^ 59
def prefixEnd_5999384 : Nat := 4983230072969 + 3 ^ 40 * 5999384 * 2
def baseEnd_5999384 : Nat := 3080567622893460616209341

theorem tailTrace_5999384 : CollatzResearch.WordTrace tailWord_5999384 prefixEnd_5999384 3080567622893460616209341 := by
  unfold tailWord_5999384
  simp only [CollatzResearch.WordTrace]
  refine ⟨109407755448631928029342603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145877007264842570705790137 109407755448631928029342603)
  ·
    refine ⟨164111633172947892044013905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109407755448631928029342603 164111633172947892044013905)
    ·
      refine ⟨123083724879710919033010429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164111633172947892044013905 123083724879710919033010429)
      ·
        refine ⟨46156396829891594637378911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123083724879710919033010429 46156396829891594637378911)
        ·
          refine ⟨69234595244837391956068367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46156396829891594637378911 69234595244837391956068367)
          ·
            refine ⟨103851892867256087934102551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69234595244837391956068367 103851892867256087934102551)
            ·
              refine ⟨155777839300884131901153827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103851892867256087934102551 155777839300884131901153827)
              ·
                refine ⟨233666758951326197851730741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155777839300884131901153827 233666758951326197851730741)
                ·
                  refine ⟨21906258651686831048599757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 233666758951326197851730741 21906258651686831048599757)
                  ·
                    refine ⟨8214846994382561643224909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21906258651686831048599757 8214846994382561643224909)
                    ·
                      refine ⟨3080567622893460616209341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8214846994382561643224909 3080567622893460616209341)
                      ·
                        rfl

theorem cell23_5999384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_5999384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999384 prefixEnd_5999384 := by exact prefixLift 5999384
  have htrace : WordTrace (prefixWord ++ tailWord_5999384) baseStart_5999384 baseEnd_5999384 := by
    simpa [prefixWord, tailWord_5999384, baseEnd_5999384] using wordTrace_append hprefix tailTrace_5999384
  have hstable : (prefixWord ++ tailWord_5999384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999384).length < 2 ^ (prefixWord ++ tailWord_5999384).sum := by decide
  have hdescent : baseEnd_5999384 < baseStart_5999384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999402 : List Nat := [3, 1, 4, 3, 1, 1, 1, 2, 3, 2, 2]
def baseStart_5999402 : Nat := 118140960795 + 5999402 * 2 ^ 59
def prefixEnd_5999402 : Nat := 4983230072969 + 3 ^ 40 * 5999402 * 2
def baseEnd_5999402 : Nat := 3080576865545241545784259

theorem tailTrace_5999402 : CollatzResearch.WordTrace tailWord_5999402 prefixEnd_5999402 3080576865545241545784259 := by
  unfold tailWord_5999402
  simp only [CollatzResearch.WordTrace]
  refine ⟨54704041852799661283210115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145877444940799096755226973 54704041852799661283210115)
  ·
    refine ⟨82056062779199491924815173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54704041852799661283210115 82056062779199491924815173)
    ·
      refine ⟨15385511771099904735902845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82056062779199491924815173 15385511771099904735902845)
      ·
        refine ⟨5769566914162464275963567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15385511771099904735902845 5769566914162464275963567)
        ·
          refine ⟨8654350371243696413945351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5769566914162464275963567 8654350371243696413945351)
          ·
            refine ⟨12981525556865544620918027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8654350371243696413945351 12981525556865544620918027)
            ·
              refine ⟨19472288335298316931377041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12981525556865544620918027 19472288335298316931377041)
              ·
                refine ⟨14604216251473737698532781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19472288335298316931377041 14604216251473737698532781)
                ·
                  refine ⟨5476581094302651636949793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14604216251473737698532781 5476581094302651636949793)
                  ·
                    refine ⟨4107435820726988727712345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5476581094302651636949793 4107435820726988727712345)
                    ·
                      refine ⟨3080576865545241545784259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4107435820726988727712345 3080576865545241545784259)
                      ·
                        rfl

theorem cell23_5999402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_5999402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999402 prefixEnd_5999402 := by exact prefixLift 5999402
  have htrace : WordTrace (prefixWord ++ tailWord_5999402) baseStart_5999402 baseEnd_5999402 := by
    simpa [prefixWord, tailWord_5999402, baseEnd_5999402] using wordTrace_append hprefix tailTrace_5999402
  have hstable : (prefixWord ++ tailWord_5999402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999402).length < 2 ^ (prefixWord ++ tailWord_5999402).sum := by decide
  have hdescent : baseEnd_5999402 < baseStart_5999402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999407 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 10]
def baseStart_5999407 : Nat := 118140960795 + 5999407 * 2 ^ 59
def prefixEnd_5999407 : Nat := 4983230072969 + 3 ^ 40 * 5999407 * 2
def baseEnd_5999407 : Nat := 3080579432948514026221735

theorem tailTrace_5999407 : CollatzResearch.WordTrace tailWord_5999407 prefixEnd_5999407 3080579432948514026221735 := by
  unfold tailWord_5999407
  simp only [CollatzResearch.WordTrace]
  refine ⟨218816349776180530986772475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145877566517453687324514983 218816349776180530986772475)
  ·
    refine ⟨328224524664270796480158713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218816349776180530986772475 328224524664270796480158713)
    ·
      refine ⟨246168393498203097360119035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328224524664270796480158713 246168393498203097360119035)
      ·
        refine ⟨369252590247304646040178553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246168393498203097360119035 369252590247304646040178553)
        ·
          refine ⟨276939442685478484530133915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369252590247304646040178553 276939442685478484530133915)
          ·
            refine ⟨415409164028217726795200873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276939442685478484530133915 415409164028217726795200873)
            ·
              refine ⟨311556873021163295096400655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415409164028217726795200873 311556873021163295096400655)
              ·
                refine ⟨467335309531744942644600983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311556873021163295096400655 467335309531744942644600983)
                ·
                  refine ⟨701002964297617413966901475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 467335309531744942644600983 701002964297617413966901475)
                  ·
                    refine ⟨1051504446446426120950352213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 701002964297617413966901475 1051504446446426120950352213)
                    ·
                      refine ⟨3080579432948514026221735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1051504446446426120950352213 3080579432948514026221735)
                      ·
                        rfl

theorem cell23_5999407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_5999407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999407 prefixEnd_5999407 := by exact prefixLift 5999407
  have htrace : WordTrace (prefixWord ++ tailWord_5999407) baseStart_5999407 baseEnd_5999407 := by
    simpa [prefixWord, tailWord_5999407, baseEnd_5999407] using wordTrace_append hprefix tailTrace_5999407
  have hstable : (prefixWord ++ tailWord_5999407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999407).length < 2 ^ (prefixWord ++ tailWord_5999407).sum := by decide
  have hdescent : baseEnd_5999407 < baseStart_5999407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999422 : List Nat := [4, 2, 1, 2, 3, 2, 2, 1, 1, 2, 3]
def baseStart_5999422 : Nat := 118140960795 + 5999422 * 2 ^ 59
def prefixEnd_5999422 : Nat := 4983230072969 + 3 ^ 40 * 5999422 * 2
def baseEnd_5999422 : Nat := 3080587135158331467534167

theorem tailTrace_5999422 : CollatzResearch.WordTrace tailWord_5999422 prefixEnd_5999422 3080587135158331467534167 := by
  unfold tailWord_5999422
  simp only [CollatzResearch.WordTrace]
  refine ⟨27352112108890773568571065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145877931247417459032379013 27352112108890773568571065)
  ·
    refine ⟨20514084081668080176428299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27352112108890773568571065 20514084081668080176428299)
    ·
      refine ⟨30771126122502120264642449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20514084081668080176428299 30771126122502120264642449)
      ·
        refine ⟨23078344591876590198481837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30771126122502120264642449 23078344591876590198481837)
        ·
          refine ⟨8654379221953721324430689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23078344591876590198481837 8654379221953721324430689)
          ·
            refine ⟨6490784416465290993323017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8654379221953721324430689 6490784416465290993323017)
            ·
              refine ⟨4868088312348968244992263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6490784416465290993323017 4868088312348968244992263)
              ·
                refine ⟨7302132468523452367488395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4868088312348968244992263 7302132468523452367488395)
                ·
                  refine ⟨10953198702785178551232593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7302132468523452367488395 10953198702785178551232593)
                  ·
                    refine ⟨8214899027088883913424445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10953198702785178551232593 8214899027088883913424445)
                    ·
                      refine ⟨3080587135158331467534167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8214899027088883913424445 3080587135158331467534167)
                      ·
                        rfl

theorem cell23_5999422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_5999422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999422 prefixEnd_5999422 := by exact prefixLift 5999422
  have htrace : WordTrace (prefixWord ++ tailWord_5999422) baseStart_5999422 baseEnd_5999422 := by
    simpa [prefixWord, tailWord_5999422, baseEnd_5999422] using wordTrace_append hprefix tailTrace_5999422
  have hstable : (prefixWord ++ tailWord_5999422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999422).length < 2 ^ (prefixWord ++ tailWord_5999422).sum := by decide
  have hdescent : baseEnd_5999422 < baseStart_5999422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999452 : List Nat := [2, 2, 4, 2, 1, 2, 3, 1, 2, 1, 3]
def baseStart_5999452 : Nat := 118140960795 + 5999452 * 2 ^ 59
def prefixEnd_5999452 : Nat := 4983230072969 + 3 ^ 40 * 5999452 * 2
def baseEnd_5999452 : Nat := 3080602539577966350159029

theorem tailTrace_5999452 : CollatzResearch.WordTrace tailWord_5999452 prefixEnd_5999452 3080602539577966350159029 := by
  unfold tailWord_5999452
  simp only [CollatzResearch.WordTrace]
  refine ⟨109408995530508751836080305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145878660707345002448107073 109408995530508751836080305)
  ·
    refine ⟨82056746647881563877060229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109408995530508751836080305 82056746647881563877060229)
    ·
      refine ⟨15385639996477793226948793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82056746647881563877060229 15385639996477793226948793)
      ·
        refine ⟨11539229997358344920211595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15385639996477793226948793 11539229997358344920211595)
        ·
          refine ⟨17308844996037517380317393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11539229997358344920211595 17308844996037517380317393)
          ·
            refine ⟨12981633747028138035238045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17308844996037517380317393 12981633747028138035238045)
            ·
              refine ⟨4868112655135551763214267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12981633747028138035238045 4868112655135551763214267)
              ·
                refine ⟨7302168982703327644821401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4868112655135551763214267 7302168982703327644821401)
                ·
                  refine ⟨5476626737027495733616051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7302168982703327644821401 5476626737027495733616051)
                  ·
                    refine ⟨8214940105541243600424077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5476626737027495733616051 8214940105541243600424077)
                    ·
                      refine ⟨3080602539577966350159029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8214940105541243600424077 3080602539577966350159029)
                      ·
                        rfl

theorem cell23_5999452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_5999452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999452 prefixEnd_5999452 := by exact prefixLift 5999452
  have htrace : WordTrace (prefixWord ++ tailWord_5999452) baseStart_5999452 baseEnd_5999452 := by
    simpa [prefixWord, tailWord_5999452, baseEnd_5999452] using wordTrace_append hprefix tailTrace_5999452
  have hstable : (prefixWord ++ tailWord_5999452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999452).length < 2 ^ (prefixWord ++ tailWord_5999452).sum := by decide
  have hdescent : baseEnd_5999452 < baseStart_5999452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999478 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_5999478 : Nat := 118140960795 + 5999478 * 2 ^ 59
def prefixEnd_5999478 : Nat := 4983230072969 + 3 ^ 40 * 5999478 * 2
def baseEnd_5999478 : Nat := 3080615890074983248433909

theorem tailTrace_5999478 : CollatzResearch.WordTrace tailWord_5999478 prefixEnd_5999478 3080615890074983248433909 := by
  unfold tailWord_5999478
  simp only [CollatzResearch.WordTrace]
  refine ⟨13676183709932706882037943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145879292905948873408404725 13676183709932706882037943)
  ·
    refine ⟨20514275564899060323056915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13676183709932706882037943 20514275564899060323056915)
    ·
      refine ⟨30771413347348590484585373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20514275564899060323056915 30771413347348590484585373)
      ·
        refine ⟨11539280005255721431719515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30771413347348590484585373 11539280005255721431719515)
        ·
          refine ⟨17308920007883582147579273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11539280005255721431719515 17308920007883582147579273)
          ·
            refine ⟨12981690005912686610684455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17308920007883582147579273 12981690005912686610684455)
            ·
              refine ⟨19472535008869029916026683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12981690005912686610684455 19472535008869029916026683)
              ·
                refine ⟨29208802513303544874040025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19472535008869029916026683 29208802513303544874040025)
                ·
                  refine ⟨21906601884977658655530019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29208802513303544874040025 21906601884977658655530019)
                  ·
                    refine ⟨32859902827466487983295029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21906601884977658655530019 32859902827466487983295029)
                    ·
                      refine ⟨3080615890074983248433909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32859902827466487983295029 3080615890074983248433909)
                      ·
                        rfl

theorem cell23_5999478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_5999478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999478 prefixEnd_5999478 := by exact prefixLift 5999478
  have htrace : WordTrace (prefixWord ++ tailWord_5999478) baseStart_5999478 baseEnd_5999478 := by
    simpa [prefixWord, tailWord_5999478, baseEnd_5999478] using wordTrace_append hprefix tailTrace_5999478
  have hstable : (prefixWord ++ tailWord_5999478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999478).length < 2 ^ (prefixWord ++ tailWord_5999478).sum := by decide
  have hdescent : baseEnd_5999478 < baseStart_5999478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999498 : List Nat := [3, 1, 2, 4, 1, 3, 1, 1, 7]
def baseStart_5999498 : Nat := 118140960795 + 5999498 * 2 ^ 59
def prefixEnd_5999498 : Nat := 4983230072969 + 3 ^ 40 * 5999498 * 2
def baseEnd_5999498 : Nat := 342291795520897018909313

theorem tailTrace_5999498 : CollatzResearch.WordTrace tailWord_5999498 prefixEnd_5999498 342291795520897018909313 := by
  unfold tailWord_5999498
  simp only [CollatzResearch.WordTrace]
  refine ⟨54704917204712713382083787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145879779212567235685556765 54704917204712713382083787)
  ·
    refine ⟨82057375807069070073125681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54704917204712713382083787 82057375807069070073125681)
    ·
      refine ⟨61543031855301802554844261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82057375807069070073125681 61543031855301802554844261)
      ·
        refine ⟨11539318472869087979033299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61543031855301802554844261 11539318472869087979033299)
        ·
          refine ⟨17308977709303631968549949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11539318472869087979033299 17308977709303631968549949)
          ·
            refine ⟨6490866640988861988206231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17308977709303631968549949 6490866640988861988206231)
            ·
              refine ⟨9736299961483292982309347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6490866640988861988206231 9736299961483292982309347)
              ·
                refine ⟨14604449942224939473464021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9736299961483292982309347 14604449942224939473464021)
                ·
                  refine ⟨342291795520897018909313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14604449942224939473464021 342291795520897018909313)
                  ·
                    rfl

theorem cell23_5999498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 7].length) (baseStart_5999498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999498 prefixEnd_5999498 := by exact prefixLift 5999498
  have htrace : WordTrace (prefixWord ++ tailWord_5999498) baseStart_5999498 baseEnd_5999498 := by
    simpa [prefixWord, tailWord_5999498, baseEnd_5999498] using wordTrace_append hprefix tailTrace_5999498
  have hstable : (prefixWord ++ tailWord_5999498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999498).length < 2 ^ (prefixWord ++ tailWord_5999498).sum := by decide
  have hdescent : baseEnd_5999498 < baseStart_5999498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999531 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 1, 6, 2]
def baseStart_5999531 : Nat := 118140960795 + 5999531 * 2 ^ 59
def prefixEnd_5999531 : Nat := 4983230072969 + 3 ^ 40 * 5999531 * 2
def baseEnd_5999531 : Nat := 3080643104549671541071165

theorem tailTrace_5999531 : CollatzResearch.WordTrace tailWord_5999531 prefixEnd_5999531 3080643104549671541071165 := by
  unfold tailWord_5999531
  simp only [CollatzResearch.WordTrace]
  refine ⟨218820872427731300164286447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145880581618487533442857631 218820872427731300164286447)
  ·
    refine ⟨328231308641596950246429671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218820872427731300164286447 328231308641596950246429671)
    ·
      refine ⟨492346962962395425369644507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328231308641596950246429671 492346962962395425369644507)
      ·
        refine ⟨738520444443593138054466761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492346962962395425369644507 738520444443593138054466761)
        ·
          refine ⟨553890333332694853540850071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 738520444443593138054466761 553890333332694853540850071)
          ·
            refine ⟨830835499999042280311275107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553890333332694853540850071 830835499999042280311275107)
            ·
              refine ⟨1246253249998563420466912661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830835499999042280311275107 1246253249998563420466912661)
              ·
                refine ⟨58418121093682660334386531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1246253249998563420466912661 58418121093682660334386531)
                ·
                  refine ⟨87627181640523990501579797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58418121093682660334386531 87627181640523990501579797)
                  ·
                    refine ⟨4107524139399562054761553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87627181640523990501579797 4107524139399562054761553)
                    ·
                      refine ⟨3080643104549671541071165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4107524139399562054761553 3080643104549671541071165)
                      ·
                        rfl

theorem cell23_5999531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 6, 2].length) (baseStart_5999531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999531 prefixEnd_5999531 := by exact prefixLift 5999531
  have htrace : WordTrace (prefixWord ++ tailWord_5999531) baseStart_5999531 baseEnd_5999531 := by
    simpa [prefixWord, tailWord_5999531, baseEnd_5999531] using wordTrace_append hprefix tailTrace_5999531
  have hstable : (prefixWord ++ tailWord_5999531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999531).length < 2 ^ (prefixWord ++ tailWord_5999531).sum := by decide
  have hdescent : baseEnd_5999531 < baseStart_5999531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999551 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 3]
def baseStart_5999551 : Nat := 118140960795 + 5999551 * 2 ^ 59
def prefixEnd_5999551 : Nat := 4983230072969 + 3 ^ 40 * 5999551 * 2
def baseEnd_5999551 : Nat := 3080653374162761462821073

theorem tailTrace_5999551 : CollatzResearch.WordTrace tailWord_5999551 prefixEnd_5999551 3080653374162761462821073 := by
  unfold tailWord_5999551
  simp only [CollatzResearch.WordTrace]
  refine ⟨218821601887658843580014507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145881067925105895720009671 218821601887658843580014507)
  ·
    refine ⟨328232402831488265370021761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218821601887658843580014507 328232402831488265370021761)
    ·
      refine ⟨246174302123616199027516321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328232402831488265370021761 246174302123616199027516321)
      ·
        refine ⟨184630726592712149270637241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246174302123616199027516321 184630726592712149270637241)
        ·
          refine ⟨138473044944534111952977931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184630726592712149270637241 138473044944534111952977931)
          ·
            refine ⟨207709567416801167929466897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138473044944534111952977931 207709567416801167929466897)
            ·
              refine ⟨155782175562600875947100173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207709567416801167929466897 155782175562600875947100173)
              ·
                refine ⟨58418315835975328480162565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155782175562600875947100173 58418315835975328480162565)
                ·
                  refine ⟨10953434219245374090030481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58418315835975328480162565 10953434219245374090030481)
                  ·
                    refine ⟨8215075664434030567522861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10953434219245374090030481 8215075664434030567522861)
                    ·
                      refine ⟨3080653374162761462821073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8215075664434030567522861 3080653374162761462821073)
                      ·
                        rfl

theorem cell23_5999551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 3].length) (baseStart_5999551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999551 prefixEnd_5999551 := by exact prefixLift 5999551
  have htrace : WordTrace (prefixWord ++ tailWord_5999551) baseStart_5999551 baseEnd_5999551 := by
    simpa [prefixWord, tailWord_5999551, baseEnd_5999551] using wordTrace_append hprefix tailTrace_5999551
  have hstable : (prefixWord ++ tailWord_5999551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999551).length < 2 ^ (prefixWord ++ tailWord_5999551).sum := by decide
  have hdescent : baseEnd_5999551 < baseStart_5999551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999605 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 8]
def baseStart_5999605 : Nat := 118140960795 + 5999605 * 2 ^ 59
def prefixEnd_5999605 : Nat := 4983230072969 + 3 ^ 40 * 5999605 * 2
def baseEnd_5999605 : Nat := 342297900235344916838425

theorem tailTrace_5999605 : CollatzResearch.WordTrace tailWord_5999605 prefixEnd_5999605 342297900235344916838425 := by
  unfold tailWord_5999605
  simp only [CollatzResearch.WordTrace]
  refine ⟨218823571429463210802480269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145882380952975473868320179 218823571429463210802480269)
  ·
    refine ⟨82058839286048704050930101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218823571429463210802480269 82058839286048704050930101)
    ·
      refine ⟨7693016183067066004774697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82058839286048704050930101 7693016183067066004774697)
      ·
        refine ⟨5769762137300299503581023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7693016183067066004774697 5769762137300299503581023)
        ·
          refine ⟨8654643205950449255371535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5769762137300299503581023 8654643205950449255371535)
          ·
            refine ⟨12981964808925673883057303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8654643205950449255371535 12981964808925673883057303)
            ·
              refine ⟨19472947213388510824585955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12981964808925673883057303 19472947213388510824585955)
              ·
                refine ⟨29209420820082766236878933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19472947213388510824585955 29209420820082766236878933)
                ·
                  refine ⟨342297900235344916838425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29209420820082766236878933 342297900235344916838425)
                  ·
                    rfl

theorem cell23_5999605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 8].length) (baseStart_5999605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999605 prefixEnd_5999605 := by exact prefixLift 5999605
  have htrace : WordTrace (prefixWord ++ tailWord_5999605) baseStart_5999605 baseEnd_5999605 := by
    simpa [prefixWord, tailWord_5999605, baseEnd_5999605] using wordTrace_append hprefix tailTrace_5999605
  have hstable : (prefixWord ++ tailWord_5999605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999605).length < 2 ^ (prefixWord ++ tailWord_5999605).sum := by decide
  have hdescent : baseEnd_5999605 < baseStart_5999605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999608 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 4, 3, 2]
def baseStart_5999608 : Nat := 118140960795 + 5999608 * 2 ^ 59
def prefixEnd_5999608 : Nat := 4983230072969 + 3 ^ 40 * 5999608 * 2
def baseEnd_5999608 : Nat := 3080682642560067739808311

theorem tailTrace_5999608 : CollatzResearch.WordTrace tailWord_5999608 prefixEnd_5999608 3080682642560067739808311 := by
  unfold tailWord_5999608
  simp only [CollatzResearch.WordTrace]
  refine ⟨109411840424226171157419739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145882453898968228209892985 109411840424226171157419739)
  ·
    refine ⟨164117760636339256736129609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109411840424226171157419739 164117760636339256736129609)
    ·
      refine ⟨123088320477254442552097207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164117760636339256736129609 123088320477254442552097207)
      ·
        refine ⟨184632480715881663828145811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123088320477254442552097207 184632480715881663828145811)
        ·
          refine ⟨276948721073822495742218717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184632480715881663828145811 276948721073822495742218717)
          ·
            refine ⟨103855770402683435903332019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276948721073822495742218717 103855770402683435903332019)
            ·
              refine ⟨155783655604025153854998029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103855770402683435903332019 155783655604025153854998029)
              ·
                refine ⟨58418870851509432695624261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155783655604025153854998029 58418870851509432695624261)
                ·
                  refine ⟨10953538284658018630429549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58418870851509432695624261 10953538284658018630429549)
                  ·
                    refine ⟨4107576856746756986411081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10953538284658018630429549 4107576856746756986411081)
                    ·
                      refine ⟨3080682642560067739808311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4107576856746756986411081 3080682642560067739808311)
                      ·
                        rfl

theorem cell23_5999608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 4, 3, 2].length) (baseStart_5999608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999608 prefixEnd_5999608 := by exact prefixLift 5999608
  have htrace : WordTrace (prefixWord ++ tailWord_5999608) baseStart_5999608 baseEnd_5999608 := by
    simpa [prefixWord, tailWord_5999608, baseEnd_5999608] using wordTrace_append hprefix tailTrace_5999608
  have hstable : (prefixWord ++ tailWord_5999608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999608).length < 2 ^ (prefixWord ++ tailWord_5999608).sum := by decide
  have hdescent : baseEnd_5999608 < baseStart_5999608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999649 : List Nat := [1, 2, 3, 2, 3, 3, 1, 3, 1, 1, 3]
def baseStart_5999649 : Nat := 118140960795 + 5999649 * 2 ^ 59
def prefixEnd_5999649 : Nat := 4983230072969 + 3 ^ 40 * 5999649 * 2
def baseEnd_5999649 : Nat := 3080703695266902079395623

theorem tailTrace_5999649 : CollatzResearch.WordTrace tailWord_5999649 prefixEnd_5999649 3080703695266902079395623 := by
  unfold tailWord_5999649
  simp only [CollatzResearch.WordTrace]
  refine ⟨218825176241303806317082001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145883450827535870878054667 218825176241303806317082001)
  ·
    refine ⟨164118882180977854737811501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218825176241303806317082001 164118882180977854737811501)
    ·
      refine ⟨61544580817866695526679313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164118882180977854737811501 61544580817866695526679313)
      ·
        refine ⟨46158435613400021645009485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61544580817866695526679313 46158435613400021645009485)
        ·
          refine ⟨17309413355025008116878557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46158435613400021645009485 17309413355025008116878557)
          ·
            refine ⟨6491030008134378043829459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17309413355025008116878557 6491030008134378043829459)
            ·
              refine ⟨9736545012201567065744189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6491030008134378043829459 9736545012201567065744189)
              ·
                refine ⟨3651204379575587649654071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9736545012201567065744189 3651204379575587649654071)
                ·
                  refine ⟨5476806569363381474481107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3651204379575587649654071 5476806569363381474481107)
                  ·
                    refine ⟨8215209854045072211721661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5476806569363381474481107 8215209854045072211721661)
                    ·
                      refine ⟨3080703695266902079395623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8215209854045072211721661 3080703695266902079395623)
                      ·
                        rfl

theorem cell23_5999649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_5999649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999649 prefixEnd_5999649 := by exact prefixLift 5999649
  have htrace : WordTrace (prefixWord ++ tailWord_5999649) baseStart_5999649 baseEnd_5999649 := by
    simpa [prefixWord, tailWord_5999649, baseEnd_5999649] using wordTrace_append hprefix tailTrace_5999649
  have hstable : (prefixWord ++ tailWord_5999649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999649).length < 2 ^ (prefixWord ++ tailWord_5999649).sum := by decide
  have hdescent : baseEnd_5999649 < baseStart_5999649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999672 : List Nat := [2, 1, 2, 1, 5, 1, 3, 1, 3, 2, 2]
def baseStart_5999672 : Nat := 118140960795 + 5999672 * 2 ^ 59
def prefixEnd_5999672 : Nat := 4983230072969 + 3 ^ 40 * 5999672 * 2
def baseEnd_5999672 : Nat := 3080715505321955489408017

theorem tailTrace_5999672 : CollatzResearch.WordTrace tailWord_5999672 prefixEnd_5999672 3080715505321955489408017 := by
  unfold tailWord_5999672
  simp only [CollatzResearch.WordTrace]
  refine ⟨109413007560110240622584635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145884010080146987496779513 109413007560110240622584635)
  ·
    refine ⟨164119511340165360933876953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109413007560110240622584635 164119511340165360933876953)
    ·
      refine ⟨123089633505124020700407715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164119511340165360933876953 123089633505124020700407715)
      ·
        refine ⟨184634450257686031050611573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123089633505124020700407715 184634450257686031050611573)
        ·
          refine ⟨17309479711658065410994835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 184634450257686031050611573 17309479711658065410994835)
          ·
            refine ⟨25964219567487098116492253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17309479711658065410994835 25964219567487098116492253)
            ·
              refine ⟨9736582337807661793684595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25964219567487098116492253 9736582337807661793684595)
              ·
                refine ⟨14604873506711492690526893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9736582337807661793684595 14604873506711492690526893)
                ·
                  refine ⟨5476827565016809758947585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14604873506711492690526893 5476827565016809758947585)
                  ·
                    refine ⟨4107620673762607319210689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5476827565016809758947585 4107620673762607319210689)
                    ·
                      refine ⟨3080715505321955489408017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4107620673762607319210689 3080715505321955489408017)
                      ·
                        rfl

theorem cell23_5999672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 3, 2, 2].length) (baseStart_5999672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999672 prefixEnd_5999672 := by exact prefixLift 5999672
  have htrace : WordTrace (prefixWord ++ tailWord_5999672) baseStart_5999672 baseEnd_5999672 := by
    simpa [prefixWord, tailWord_5999672, baseEnd_5999672] using wordTrace_append hprefix tailTrace_5999672
  have hstable : (prefixWord ++ tailWord_5999672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999672).length < 2 ^ (prefixWord ++ tailWord_5999672).sum := by decide
  have hdescent : baseEnd_5999672 < baseStart_5999672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999678 : List Nat := [4, 2, 1, 3, 1, 1, 1, 10]
def baseStart_5999678 : Nat := 118140960795 + 5999678 * 2 ^ 59
def prefixEnd_5999678 : Nat := 4983230072969 + 3 ^ 40 * 5999678 * 2
def baseEnd_5999678 : Nat := 114100688377995646886407

theorem tailTrace_5999678 : CollatzResearch.WordTrace tailWord_5999678 prefixEnd_5999678 114100688377995646886407 := by
  unfold tailWord_5999678
  simp only [CollatzResearch.WordTrace]
  refine ⟨27353279244774843033735961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145884155972132496179925125 27353279244774843033735961)
  ·
    refine ⟨20514959433581132275301971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27353279244774843033735961 20514959433581132275301971)
    ·
      refine ⟨30772439150371698412952957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20514959433581132275301971 30772439150371698412952957)
      ·
        refine ⟨11539664681389386904857359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30772439150371698412952957 11539664681389386904857359)
        ·
          refine ⟨17309497022084080357286039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11539664681389386904857359 17309497022084080357286039)
          ·
            refine ⟨25964245533126120535929059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17309497022084080357286039 25964245533126120535929059)
            ·
              refine ⟨38946368299689180803893589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25964245533126120535929059 38946368299689180803893589)
              ·
                refine ⟨114100688377995646886407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38946368299689180803893589 114100688377995646886407)
                ·
                  rfl

theorem cell23_5999678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 10].length) (baseStart_5999678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999678 prefixEnd_5999678 := by exact prefixLift 5999678
  have htrace : WordTrace (prefixWord ++ tailWord_5999678) baseStart_5999678 baseEnd_5999678 := by
    simpa [prefixWord, tailWord_5999678, baseEnd_5999678] using wordTrace_append hprefix tailTrace_5999678
  have hstable : (prefixWord ++ tailWord_5999678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999678).length < 2 ^ (prefixWord ++ tailWord_5999678).sum := by decide
  have hdescent : baseEnd_5999678 < baseStart_5999678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999688 : List Nat := [2, 1, 3, 1, 1, 1, 4, 3, 1, 3, 3]
def baseStart_5999688 : Nat := 118140960795 + 5999688 * 2 ^ 59
def prefixEnd_5999688 : Nat := 4983230072969 + 3 ^ 40 * 5999688 * 2
def baseEnd_5999688 : Nat := 3080723721012427426807943

theorem tailTrace_5999688 : CollatzResearch.WordTrace tailWord_5999688 prefixEnd_5999688 3080723721012427426807943 := by
  unfold tailWord_5999688
  simp only [CollatzResearch.WordTrace]
  refine ⟨109413299344081257988875859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145884399125441677318501145 109413299344081257988875859)
  ·
    refine ⟨164119949016121886983313789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109413299344081257988875859 164119949016121886983313789)
    ·
      refine ⟨61544980881045707618742671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164119949016121886983313789 61544980881045707618742671)
      ·
        refine ⟨92317471321568561428114007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61544980881045707618742671 92317471321568561428114007)
        ·
          refine ⟨138476206982352842142171011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92317471321568561428114007 138476206982352842142171011)
          ·
            refine ⟨207714310473529263213256517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138476206982352842142171011 207714310473529263213256517)
            ·
              refine ⟨38946433213786736852485597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 207714310473529263213256517 38946433213786736852485597)
              ·
                refine ⟨14604912455170026319682099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38946433213786736852485597 14604912455170026319682099)
                ·
                  refine ⟨21907368682755039479523149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14604912455170026319682099 21907368682755039479523149)
                  ·
                    refine ⟨8215263256033139804821181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21907368682755039479523149 8215263256033139804821181)
                    ·
                      refine ⟨3080723721012427426807943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8215263256033139804821181 3080723721012427426807943)
                      ·
                        rfl

theorem cell23_5999688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_5999688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999688 prefixEnd_5999688 := by exact prefixLift 5999688
  have htrace : WordTrace (prefixWord ++ tailWord_5999688) baseStart_5999688 baseEnd_5999688 := by
    simpa [prefixWord, tailWord_5999688, baseEnd_5999688] using wordTrace_append hprefix tailTrace_5999688
  have hstable : (prefixWord ++ tailWord_5999688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999688).length < 2 ^ (prefixWord ++ tailWord_5999688).sum := by decide
  have hdescent : baseEnd_5999688 < baseStart_5999688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999709 : List Nat := [1, 4, 4, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_5999709 : Nat := 118140960795 + 5999709 * 2 ^ 59
def prefixEnd_5999709 : Nat := 4983230072969 + 3 ^ 40 * 5999709 * 2
def baseEnd_5999709 : Nat := 3080734504106171844645347

theorem tailTrace_5999709 : CollatzResearch.WordTrace tailWord_5999709 prefixEnd_5999709 3080734504106171844645347 := by
  unfold tailWord_5999709
  simp only [CollatzResearch.WordTrace]
  refine ⟨218827364621086436564266181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145884909747390957709510787 218827364621086436564266181)
  ·
    refine ⟨41030130866453706855799909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218827364621086436564266181 41030130866453706855799909)
    ·
      refine ⟨7693149537460070035462483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41030130866453706855799909 7693149537460070035462483)
      ·
        refine ⟨11539724306190105053193725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7693149537460070035462483 11539724306190105053193725)
        ·
          refine ⟨4327396614821289394947647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11539724306190105053193725 4327396614821289394947647)
          ·
            refine ⟨6491094922231934092421471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4327396614821289394947647 6491094922231934092421471)
            ·
              refine ⟨9736642383347901138632207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6491094922231934092421471 9736642383347901138632207)
              ·
                refine ⟨14604963575021851707948311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9736642383347901138632207 14604963575021851707948311)
                ·
                  refine ⟨21907445362532777561922467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14604963575021851707948311 21907445362532777561922467)
                  ·
                    refine ⟨32861168043799166342883701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21907445362532777561922467 32861168043799166342883701)
                    ·
                      refine ⟨3080734504106171844645347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32861168043799166342883701 3080734504106171844645347)
                      ·
                        rfl

theorem cell23_5999709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_5999709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999709 prefixEnd_5999709 := by exact prefixLift 5999709
  have htrace : WordTrace (prefixWord ++ tailWord_5999709) baseStart_5999709 baseEnd_5999709 := by
    simpa [prefixWord, tailWord_5999709, baseEnd_5999709] using wordTrace_append hprefix tailTrace_5999709
  have hstable : (prefixWord ++ tailWord_5999709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999709).length < 2 ^ (prefixWord ++ tailWord_5999709).sum := by decide
  have hdescent : baseEnd_5999709 < baseStart_5999709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999722 : List Nat := [3, 1, 3, 2, 2, 1, 1, 4, 2, 1, 3]
def baseStart_5999722 : Nat := 118140960795 + 5999722 * 2 ^ 59
def prefixEnd_5999722 : Nat := 4983230072969 + 3 ^ 40 * 5999722 * 2
def baseEnd_5999722 : Nat := 3080741179354680293782787

theorem tailTrace_5999722 : CollatzResearch.WordTrace tailWord_5999722 prefixEnd_5999722 3080741179354680293782787 := by
  unfold tailWord_5999722
  simp only [CollatzResearch.WordTrace]
  refine ⟨54706959692509834946122355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145885225846692893189659613 54706959692509834946122355)
  ·
    refine ⟨82060439538764752419183533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54706959692509834946122355 82060439538764752419183533)
    ·
      refine ⟨30772664827036782157193825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82060439538764752419183533 30772664827036782157193825)
      ·
        refine ⟨23079498620277586617895369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30772664827036782157193825 23079498620277586617895369)
        ·
          refine ⟨17309623965208189963421527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23079498620277586617895369 17309623965208189963421527)
          ·
            refine ⟨25964435947812284945132291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17309623965208189963421527 25964435947812284945132291)
            ·
              refine ⟨38946653921718427417698437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25964435947812284945132291 38946653921718427417698437)
              ·
                refine ⟨7302497610322205140818457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38946653921718427417698437 7302497610322205140818457)
                ·
                  refine ⟨5476873207741653855613843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7302497610322205140818457 5476873207741653855613843)
                  ·
                    refine ⟨8215309811612480783420765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5476873207741653855613843 8215309811612480783420765)
                    ·
                      refine ⟨3080741179354680293782787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8215309811612480783420765 3080741179354680293782787)
                      ·
                        rfl

theorem cell23_5999722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_5999722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999722 prefixEnd_5999722 := by exact prefixLift 5999722
  have htrace : WordTrace (prefixWord ++ tailWord_5999722) baseStart_5999722 baseEnd_5999722 := by
    simpa [prefixWord, tailWord_5999722, baseEnd_5999722] using wordTrace_append hprefix tailTrace_5999722
  have hstable : (prefixWord ++ tailWord_5999722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999722).length < 2 ^ (prefixWord ++ tailWord_5999722).sum := by decide
  have hdescent : baseEnd_5999722 < baseStart_5999722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999762 : List Nat := [3, 2, 3, 1, 1, 2, 2, 2, 1, 4, 2]
def baseStart_5999762 : Nat := 118140960795 + 5999762 * 2 ^ 59
def prefixEnd_5999762 : Nat := 4983230072969 + 3 ^ 40 * 5999762 * 2
def baseEnd_5999762 : Nat := 3080761718580860137282603

theorem tailTrace_5999762 : CollatzResearch.WordTrace tailWord_5999762 prefixEnd_5999762 3080761718580860137282603 := by
  unfold tailWord_5999762
  simp only [CollatzResearch.WordTrace]
  refine ⟨54707324422473606653986385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145886198459929617743963693 54707324422473606653986385)
  ·
    refine ⟨41030493316855204990489789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54707324422473606653986385 41030493316855204990489789)
    ·
      refine ⟨15386434993820701871433671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41030493316855204990489789 15386434993820701871433671)
      ·
        refine ⟨23079652490731052807150507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15386434993820701871433671 23079652490731052807150507)
        ·
          refine ⟨34619478736096579210725761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23079652490731052807150507 34619478736096579210725761)
          ·
            refine ⟨25964609052072434408044321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34619478736096579210725761 25964609052072434408044321)
            ·
              refine ⟨19473456789054325806033241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25964609052072434408044321 19473456789054325806033241)
              ·
                refine ⟨14605092591790744354524931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19473456789054325806033241 14605092591790744354524931)
                ·
                  refine ⟨21907638887686116531787397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14605092591790744354524931 21907638887686116531787397)
                  ·
                    refine ⟨4107682291441146849710137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21907638887686116531787397 4107682291441146849710137)
                    ·
                      refine ⟨3080761718580860137282603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4107682291441146849710137 3080761718580860137282603)
                      ·
                        rfl

theorem cell23_5999762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_5999762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999762 prefixEnd_5999762 := by exact prefixLift 5999762
  have htrace : WordTrace (prefixWord ++ tailWord_5999762) baseStart_5999762 baseEnd_5999762 := by
    simpa [prefixWord, tailWord_5999762, baseEnd_5999762] using wordTrace_append hprefix tailTrace_5999762
  have hstable : (prefixWord ++ tailWord_5999762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999762).length < 2 ^ (prefixWord ++ tailWord_5999762).sum := by decide
  have hdescent : baseEnd_5999762 < baseStart_5999762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999771 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 6]
def baseStart_5999771 : Nat := 118140960795 + 5999771 * 2 ^ 59
def prefixEnd_5999771 : Nat := 4983230072969 + 3 ^ 40 * 5999771 * 2
def baseEnd_5999771 : Nat := 3080766339906750602070061

theorem tailTrace_5999771 : CollatzResearch.WordTrace tailWord_5999771 prefixEnd_5999771 3080766339906750602070061 := by
  unfold tailWord_5999771
  simp only [CollatzResearch.WordTrace]
  refine ⟨218829625946861821153023167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145886417297907880768682111 218829625946861821153023167)
  ·
    refine ⟨328244438920292731729534751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218829625946861821153023167 328244438920292731729534751)
    ·
      refine ⟨492366658380439097594302127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328244438920292731729534751 492366658380439097594302127)
      ·
        refine ⟨738549987570658646391453191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492366658380439097594302127 738549987570658646391453191)
        ·
          refine ⟨1107824981355987969587179787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738549987570658646391453191 1107824981355987969587179787)
          ·
            refine ⟨1661737472033981954380769681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1107824981355987969587179787 1661737472033981954380769681)
            ·
              refine ⟨1246303104025486465785577261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1661737472033981954380769681 1246303104025486465785577261)
              ·
                refine ⟨467363664009557424669591473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1246303104025486465785577261 467363664009557424669591473)
                ·
                  refine ⟨350522748007168068502193605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 467363664009557424669591473 350522748007168068502193605)
                  ·
                    refine ⟨65723015251344012844161301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 350522748007168068502193605 65723015251344012844161301)
                    ·
                      refine ⟨3080766339906750602070061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65723015251344012844161301 3080766339906750602070061)
                      ·
                        rfl

theorem cell23_5999771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 6].length) (baseStart_5999771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999771 prefixEnd_5999771 := by exact prefixLift 5999771
  have htrace : WordTrace (prefixWord ++ tailWord_5999771) baseStart_5999771 baseEnd_5999771 := by
    simpa [prefixWord, tailWord_5999771, baseEnd_5999771] using wordTrace_append hprefix tailTrace_5999771
  have hstable : (prefixWord ++ tailWord_5999771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999771).length < 2 ^ (prefixWord ++ tailWord_5999771).sum := by decide
  have hdescent : baseEnd_5999771 < baseStart_5999771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999805 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 2, 5, 2]
def baseStart_5999805 : Nat := 118140960795 + 5999805 * 2 ^ 59
def prefixEnd_5999805 : Nat := 4983230072969 + 3 ^ 40 * 5999805 * 2
def baseEnd_5999805 : Nat := 3080783798249003469044905

theorem tailTrace_5999805 : CollatzResearch.WordTrace tailWord_5999805 prefixEnd_5999805 3080783798249003469044905 := by
  unfold tailWord_5999805
  simp only [CollatzResearch.WordTrace]
  refine ⟨218830866028738644959760869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145887244019159096639840579 218830866028738644959760869)
  ·
    refine ⟨41030787380388495929955163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218830866028738644959760869 41030787380388495929955163)
    ·
      refine ⟨61546181070582743894932745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41030787380388495929955163 61546181070582743894932745)
      ·
        refine ⟨46159635802937057921199559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61546181070582743894932745 46159635802937057921199559)
        ·
          refine ⟨69239453704405586881799339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46159635802937057921199559 69239453704405586881799339)
          ·
            refine ⟨103859180556608380322699009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69239453704405586881799339 103859180556608380322699009)
            ·
              refine ⟨77894385417456285242024257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103859180556608380322699009 77894385417456285242024257)
              ·
                refine ⟨58420789063092213931518193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77894385417456285242024257 58420789063092213931518193)
                ·
                  refine ⟨43815591797319160448638645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58420789063092213931518193 43815591797319160448638645)
                  ·
                    refine ⟨4107711730998671292059873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43815591797319160448638645 4107711730998671292059873)
                    ·
                      refine ⟨3080783798249003469044905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4107711730998671292059873 3080783798249003469044905)
                      ·
                        rfl

theorem cell23_5999805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_5999805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999805 prefixEnd_5999805 := by exact prefixLift 5999805
  have htrace : WordTrace (prefixWord ++ tailWord_5999805) baseStart_5999805 baseEnd_5999805 := by
    simpa [prefixWord, tailWord_5999805, baseEnd_5999805] using wordTrace_append hprefix tailTrace_5999805
  have hstable : (prefixWord ++ tailWord_5999805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999805).length < 2 ^ (prefixWord ++ tailWord_5999805).sum := by decide
  have hdescent : baseEnd_5999805 < baseStart_5999805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999896 : List Nat := [2, 1, 2, 3, 1, 5, 2, 2, 1, 4]
def baseStart_5999896 : Nat := 118140960795 + 5999896 * 2 ^ 59
def prefixEnd_5999896 : Nat := 4983230072969 + 3 ^ 40 * 5999896 * 2
def baseEnd_5999896 : Nat := 1026943508329520871002329

theorem tailTrace_5999896 : CollatzResearch.WordTrace tailWord_5999896 prefixEnd_5999896 1026943508329520871002329 := by
  unfold tailWord_5999896
  simp only [CollatzResearch.WordTrace]
  refine ⟨109417092535704483750661771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145889456714272645000882361 109417092535704483750661771)
  ·
    refine ⟨164125638803556725625992657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109417092535704483750661771 164125638803556725625992657)
    ·
      refine ⟨123094229102667544219494493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164125638803556725625992657 123094229102667544219494493)
      ·
        refine ⟨46160335913500329082310435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123094229102667544219494493 46160335913500329082310435)
        ·
          refine ⟨69240503870250493623465653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46160335913500329082310435 69240503870250493623465653)
          ·
            refine ⟨6491297237835983777199905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69240503870250493623465653 6491297237835983777199905)
            ·
              refine ⟨4868472928376987832899929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6491297237835983777199905 4868472928376987832899929)
              ·
                refine ⟨3651354696282740874674947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4868472928376987832899929 3651354696282740874674947)
                ·
                  refine ⟨5477032044424111312012421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3651354696282740874674947 5477032044424111312012421)
                  ·
                    refine ⟨1026943508329520871002329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5477032044424111312012421 1026943508329520871002329)
                    ·
                      rfl

theorem cell23_5999896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 1, 4].length) (baseStart_5999896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999896 prefixEnd_5999896 := by exact prefixLift 5999896
  have htrace : WordTrace (prefixWord ++ tailWord_5999896) baseStart_5999896 baseEnd_5999896 := by
    simpa [prefixWord, tailWord_5999896, baseEnd_5999896] using wordTrace_append hprefix tailTrace_5999896
  have hstable : (prefixWord ++ tailWord_5999896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999896).length < 2 ^ (prefixWord ++ tailWord_5999896).sum := by decide
  have hdescent : baseEnd_5999896 < baseStart_5999896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999929 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 1, 5, 2]
def baseStart_5999929 : Nat := 118140960795 + 5999929 * 2 ^ 59
def prefixEnd_5999929 : Nat := 4983230072969 + 3 ^ 40 * 5999929 * 2
def baseEnd_5999929 : Nat := 3080847469850160983894335

theorem tailTrace_5999929 : CollatzResearch.WordTrace tailWord_5999929 prefixEnd_5999929 3080847469850160983894335 := by
  unfold tailWord_5999929
  simp only [CollatzResearch.WordTrace]
  refine ⟨218835388680289414137274841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145890259120192942758183227 218835388680289414137274841)
  ·
    refine ⟨164126541510217060602956131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218835388680289414137274841 164126541510217060602956131)
    ·
      refine ⟨246189812265325590904434197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164126541510217060602956131 246189812265325590904434197)
      ·
        refine ⟨11540147449937137073645353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 246189812265325590904434197 11540147449937137073645353)
        ·
          refine ⟨8655110587452852805234015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11540147449937137073645353 8655110587452852805234015)
          ·
            refine ⟨12982665881179279207851023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8655110587452852805234015 12982665881179279207851023)
            ·
              refine ⟨19473998821768918811776535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12982665881179279207851023 19473998821768918811776535)
              ·
                refine ⟨29210998232653378217664803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19473998821768918811776535 29210998232653378217664803)
                ·
                  refine ⟨43816497348980067326497205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29210998232653378217664803 43816497348980067326497205)
                  ·
                    refine ⟨4107796626466881311859113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43816497348980067326497205 4107796626466881311859113)
                    ·
                      refine ⟨3080847469850160983894335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4107796626466881311859113 3080847469850160983894335)
                      ·
                        rfl

theorem cell23_5999929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_5999929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999929 prefixEnd_5999929 := by exact prefixLift 5999929
  have htrace : WordTrace (prefixWord ++ tailWord_5999929) baseStart_5999929 baseEnd_5999929 := by
    simpa [prefixWord, tailWord_5999929, baseEnd_5999929] using wordTrace_append hprefix tailTrace_5999929
  have hstable : (prefixWord ++ tailWord_5999929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999929).length < 2 ^ (prefixWord ++ tailWord_5999929).sum := by decide
  have hdescent : baseEnd_5999929 < baseStart_5999929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999935 : List Nat := [1, 1, 2, 2, 4, 2, 2, 2, 1, 6]
def baseStart_5999935 : Nat := 118140960795 + 5999935 * 2 ^ 59
def prefixEnd_5999935 : Nat := 4983230072969 + 3 ^ 40 * 5999935 * 2
def baseEnd_5999935 : Nat := 1026950183578029320139769

theorem tailTrace_5999935 : CollatzResearch.WordTrace tailWord_5999935 prefixEnd_5999935 1026950183578029320139769 := by
  unfold tailWord_5999935
  simp only [CollatzResearch.WordTrace]
  refine ⟨218835607518267677161993259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145890405012178451441328839 218835607518267677161993259)
  ·
    refine ⟨328253411277401515742989889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218835607518267677161993259 328253411277401515742989889)
    ·
      refine ⟨246190058458051136807242417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328253411277401515742989889 246190058458051136807242417)
      ·
        refine ⟨184642543843538352605431813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246190058458051136807242417 184642543843538352605431813)
        ·
          refine ⟨34620476970663441113518465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184642543843538352605431813 34620476970663441113518465)
          ·
            refine ⟨25965357727997580835138849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34620476970663441113518465 25965357727997580835138849)
            ·
              refine ⟨19474018295998185626354137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25965357727997580835138849 19474018295998185626354137)
              ·
                refine ⟨14605513721998639219765603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19474018295998185626354137 14605513721998639219765603)
                ·
                  refine ⟨21908270582997958829648405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14605513721998639219765603 21908270582997958829648405)
                  ·
                    refine ⟨1026950183578029320139769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21908270582997958829648405 1026950183578029320139769)
                    ·
                      rfl

theorem cell23_5999935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 6].length) (baseStart_5999935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999935 prefixEnd_5999935 := by exact prefixLift 5999935
  have htrace : WordTrace (prefixWord ++ tailWord_5999935) baseStart_5999935 baseEnd_5999935 := by
    simpa [prefixWord, tailWord_5999935, baseEnd_5999935] using wordTrace_append hprefix tailTrace_5999935
  have hstable : (prefixWord ++ tailWord_5999935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999935).length < 2 ^ (prefixWord ++ tailWord_5999935).sum := by decide
  have hdescent : baseEnd_5999935 < baseStart_5999935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999959 : List Nat := [1, 1, 3, 2, 3, 2, 1, 3, 3, 2, 2]
def baseStart_5999959 : Nat := 118140960795 + 5999959 * 2 ^ 59
def prefixEnd_5999959 : Nat := 4983230072969 + 3 ^ 40 * 5999959 * 2
def baseEnd_5999959 : Nat := 3080862874269795866519197

theorem tailTrace_5999959 : CollatzResearch.WordTrace tailWord_5999959 prefixEnd_5999959 3080862874269795866519197 := by
  unfold tailWord_5999959
  simp only [CollatzResearch.WordTrace]
  refine ⟨218836482870180729260866931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145890988580120486173911287 218836482870180729260866931)
  ·
    refine ⟨328254724305271093891300397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218836482870180729260866931 328254724305271093891300397)
    ·
      refine ⟨123095521614476660209237649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328254724305271093891300397 123095521614476660209237649)
      ·
        refine ⟨92321641210857495156928237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123095521614476660209237649 92321641210857495156928237)
        ·
          refine ⟨34620615454071560683848089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92321641210857495156928237 34620615454071560683848089)
          ·
            refine ⟨25965461590553670512886067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34620615454071560683848089 25965461590553670512886067)
            ·
              refine ⟨38948192385830505769329101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25965461590553670512886067 38948192385830505769329101)
              ·
                refine ⟨14605572144686439663498413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38948192385830505769329101 14605572144686439663498413)
                ·
                  refine ⟨5477089554257414873811905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14605572144686439663498413 5477089554257414873811905)
                  ·
                    refine ⟨4107817165693061155358929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5477089554257414873811905 4107817165693061155358929)
                    ·
                      refine ⟨3080862874269795866519197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4107817165693061155358929 3080862874269795866519197)
                      ·
                        rfl

theorem cell23_5999959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 2, 2].length) (baseStart_5999959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999959 prefixEnd_5999959 := by exact prefixLift 5999959
  have htrace : WordTrace (prefixWord ++ tailWord_5999959) baseStart_5999959 baseEnd_5999959 := by
    simpa [prefixWord, tailWord_5999959, baseEnd_5999959] using wordTrace_append hprefix tailTrace_5999959
  have hstable : (prefixWord ++ tailWord_5999959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999959).length < 2 ^ (prefixWord ++ tailWord_5999959).sum := by decide
  have hdescent : baseEnd_5999959 < baseStart_5999959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5999972 : List Nat := [2, 3, 1, 1, 3, 2, 3, 1, 1, 2, 4]
def baseStart_5999972 : Nat := 118140960795 + 5999972 * 2 ^ 59
def prefixEnd_5999972 : Nat := 4983230072969 + 3 ^ 40 * 5999972 * 2
def baseEnd_5999972 : Nat := 3080869549518304315656637

theorem tailTrace_5999972 : CollatzResearch.WordTrace tailWord_5999972 prefixEnd_5999972 3080869549518304315656637 := by
  unfold tailWord_5999972
  simp only [CollatzResearch.WordTrace]
  refine ⟨109418478509566816240545085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145891304679422421654060113 109418478509566816240545085)
  ·
    refine ⟨41031929441087556090204407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109418478509566816240545085 41031929441087556090204407)
    ·
      refine ⟨61547894161631334135306611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41031929441087556090204407 61547894161631334135306611)
      ·
        refine ⟨92321841242447001202959917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61547894161631334135306611 92321841242447001202959917)
        ·
          refine ⟨34620690465917625451109969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92321841242447001202959917 34620690465917625451109969)
          ·
            refine ⟨25965517849438219088332477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34620690465917625451109969 25965517849438219088332477)
            ·
              refine ⟨9737069193539332158124679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25965517849438219088332477 9737069193539332158124679)
              ·
                refine ⟨14605603790308998237187019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9737069193539332158124679 14605603790308998237187019)
                ·
                  refine ⟨21908405685463497355780529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14605603790308998237187019 21908405685463497355780529)
                  ·
                    refine ⟨16431304264097623016835397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21908405685463497355780529 16431304264097623016835397)
                    ·
                      refine ⟨3080869549518304315656637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16431304264097623016835397 3080869549518304315656637)
                      ·
                        rfl

theorem cell23_5999972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_5999972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5999972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5999972 prefixEnd_5999972 := by exact prefixLift 5999972
  have htrace : WordTrace (prefixWord ++ tailWord_5999972) baseStart_5999972 baseEnd_5999972 := by
    simpa [prefixWord, tailWord_5999972, baseEnd_5999972] using wordTrace_append hprefix tailTrace_5999972
  have hstable : (prefixWord ++ tailWord_5999972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5999972).length < 2 ^ (prefixWord ++ tailWord_5999972).sum := by decide
  have hdescent : baseEnd_5999972 < baseStart_5999972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5999972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000030 : List Nat := [4, 3, 1, 2, 3, 1, 1, 2, 1, 2, 3]
def baseStart_6000030 : Nat := 118140960795 + 6000030 * 2 ^ 59
def prefixEnd_6000030 : Nat := 4983230072969 + 3 ^ 40 * 6000030 * 2
def baseEnd_6000030 : Nat := 3080899331396265088731371

theorem tailTrace_6000030 : CollatzResearch.WordTrace tailWord_6000030 prefixEnd_6000030 3080899331396265088731371 := by
  unfold tailWord_6000030
  simp only [CollatzResearch.WordTrace]
  refine ⟨27354884056615438548337693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145892714968615672257801029 27354884056615438548337693)
  ·
    refine ⟨10258081521230789455626635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27354884056615438548337693 10258081521230789455626635)
    ·
      refine ⟨15387122281846184183439953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10258081521230789455626635 15387122281846184183439953)
      ·
        refine ⟨11540341711384638137579965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15387122281846184183439953 11540341711384638137579965)
        ·
          refine ⟨4327628141769239301592487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11540341711384638137579965 4327628141769239301592487)
          ·
            refine ⟨6491442212653858952388731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4327628141769239301592487 6491442212653858952388731)
            ·
              refine ⟨9737163318980788428583097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6491442212653858952388731 9737163318980788428583097)
              ·
                refine ⟨7302872489235591321437323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9737163318980788428583097 7302872489235591321437323)
                ·
                  refine ⟨10954308733853386982155985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7302872489235591321437323 10954308733853386982155985)
                  ·
                    refine ⟨8215731550390040236616989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10954308733853386982155985 8215731550390040236616989)
                    ·
                      refine ⟨3080899331396265088731371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8215731550390040236616989 3080899331396265088731371)
                      ·
                        rfl

theorem cell23_6000030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_6000030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000030 prefixEnd_6000030 := by exact prefixLift 6000030
  have htrace : WordTrace (prefixWord ++ tailWord_6000030) baseStart_6000030 baseEnd_6000030 := by
    simpa [prefixWord, tailWord_6000030, baseEnd_6000030] using wordTrace_append hprefix tailTrace_6000030
  have hstable : (prefixWord ++ tailWord_6000030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000030).length < 2 ^ (prefixWord ++ tailWord_6000030).sum := by decide
  have hdescent : baseEnd_6000030 < baseStart_6000030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000035 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 5]
def baseStart_6000035 : Nat := 118140960795 + 6000035 * 2 ^ 59
def prefixEnd_6000035 : Nat := 4983230072969 + 3 ^ 40 * 6000035 * 2
def baseEnd_6000035 : Nat := 3080901898799537569168847

theorem tailTrace_6000035 : CollatzResearch.WordTrace tailWord_6000035 prefixEnd_6000035 3080901898799537569168847 := by
  unfold tailWord_6000035
  simp only [CollatzResearch.WordTrace]
  refine ⟨218839254817905394240633559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145892836545270262827089039 218839254817905394240633559)
  ·
    refine ⟨328258882226858091360950339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218839254817905394240633559 328258882226858091360950339)
    ·
      refine ⟨492388323340287137041425509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328258882226858091360950339 492388323340287137041425509)
      ·
        refine ⟨92322810626303838195267283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 492388323340287137041425509 92322810626303838195267283)
        ·
          refine ⟨138484215939455757292900925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92322810626303838195267283 138484215939455757292900925)
          ·
            refine ⟨51931580977295908984837847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138484215939455757292900925 51931580977295908984837847)
            ·
              refine ⟨77897371465943863477256771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51931580977295908984837847 77897371465943863477256771)
              ·
                refine ⟨116846057198915795215885157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77897371465943863477256771 116846057198915795215885157)
                ·
                  refine ⟨21908635724796711602978467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116846057198915795215885157 21908635724796711602978467)
                  ·
                    refine ⟨32862953587195067404467701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21908635724796711602978467 32862953587195067404467701)
                    ·
                      refine ⟨3080901898799537569168847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32862953587195067404467701 3080901898799537569168847)
                      ·
                        rfl

theorem cell23_6000035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_6000035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000035 prefixEnd_6000035 := by exact prefixLift 6000035
  have htrace : WordTrace (prefixWord ++ tailWord_6000035) baseStart_6000035 baseEnd_6000035 := by
    simpa [prefixWord, tailWord_6000035, baseEnd_6000035] using wordTrace_append hprefix tailTrace_6000035
  have hstable : (prefixWord ++ tailWord_6000035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000035).length < 2 ^ (prefixWord ++ tailWord_6000035).sum := by decide
  have hdescent : baseEnd_6000035 < baseStart_6000035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000049 : List Nat := [1, 2, 2, 4, 1, 1, 3, 2, 1, 4, 2]
def baseStart_6000049 : Nat := 118140960795 + 6000049 * 2 ^ 59
def prefixEnd_6000049 : Nat := 4983230072969 + 3 ^ 40 * 6000049 * 2
def baseEnd_6000049 : Nat := 3080909087528700514393783

theorem tailTrace_6000049 : CollatzResearch.WordTrace tailWord_6000049 prefixEnd_6000049 3080909087528700514393783 := by
  unfold tailWord_6000049
  simp only [CollatzResearch.WordTrace]
  refine ⟨218839765439854674631643201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145893176959903116421095467 218839765439854674631643201)
  ·
    refine ⟨164129824079891005973732401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218839765439854674631643201 164129824079891005973732401)
    ·
      refine ⟨123097368059918254480299301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164129824079891005973732401 123097368059918254480299301)
      ·
        refine ⟨23080756511234672715056119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123097368059918254480299301 23080756511234672715056119)
        ·
          refine ⟨34621134766852009072584179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23080756511234672715056119 34621134766852009072584179)
          ·
            refine ⟨51931702150278013608876269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34621134766852009072584179 51931702150278013608876269)
            ·
              refine ⟨19474388306354255103328601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51931702150278013608876269 19474388306354255103328601)
              ·
                refine ⟨14605791229765691327496451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19474388306354255103328601 14605791229765691327496451)
                ·
                  refine ⟨21908686844648536991244677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14605791229765691327496451 21908686844648536991244677)
                  ·
                    refine ⟨4107878783371600685858377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21908686844648536991244677 4107878783371600685858377)
                    ·
                      refine ⟨3080909087528700514393783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4107878783371600685858377 3080909087528700514393783)
                      ·
                        rfl

theorem cell23_6000049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_6000049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000049 prefixEnd_6000049 := by exact prefixLift 6000049
  have htrace : WordTrace (prefixWord ++ tailWord_6000049) baseStart_6000049 baseEnd_6000049 := by
    simpa [prefixWord, tailWord_6000049, baseEnd_6000049] using wordTrace_append hprefix tailTrace_6000049
  have hstable : (prefixWord ++ tailWord_6000049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000049).length < 2 ^ (prefixWord ++ tailWord_6000049).sum := by decide
  have hdescent : baseEnd_6000049 < baseStart_6000049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000053 : List Nat := [1, 3, 3, 2, 2, 2, 3, 1, 1, 3, 2]
def baseStart_6000053 : Nat := 118140960795 + 6000053 * 2 ^ 59
def prefixEnd_6000053 : Nat := 4983230072969 + 3 ^ 40 * 6000053 * 2
def baseEnd_6000053 : Nat := 3080911141451318498743765

theorem tailTrace_6000053 : CollatzResearch.WordTrace tailWord_6000053 prefixEnd_6000053 3080911141451318498743765 := by
  unfold tailWord_6000053
  simp only [CollatzResearch.WordTrace]
  refine ⟨218839911331840183314788813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145893274221226788876525875 218839911331840183314788813)
  ·
    refine ⟨82064966749440068743045805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218839911331840183314788813 82064966749440068743045805)
    ·
      refine ⟨30774362531040025778642177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82064966749440068743045805 30774362531040025778642177)
      ·
        refine ⟨23080771898280019333981633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30774362531040025778642177 23080771898280019333981633)
        ·
          refine ⟨17310578923710014500486225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23080771898280019333981633 17310578923710014500486225)
          ·
            refine ⟨12982934192782510875364669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17310578923710014500486225 12982934192782510875364669)
            ·
              refine ⟨4868600322293441578261751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12982934192782510875364669 4868600322293441578261751)
              ·
                refine ⟨7302900483440162367392627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4868600322293441578261751 7302900483440162367392627)
                ·
                  refine ⟨10954350725160243551088941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7302900483440162367392627 10954350725160243551088941)
                  ·
                    refine ⟨4107881521935091331658353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10954350725160243551088941 4107881521935091331658353)
                    ·
                      refine ⟨3080911141451318498743765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4107881521935091331658353 3080911141451318498743765)
                      ·
                        rfl

theorem cell23_6000053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_6000053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000053 prefixEnd_6000053 := by exact prefixLift 6000053
  have htrace : WordTrace (prefixWord ++ tailWord_6000053) baseStart_6000053 baseEnd_6000053 := by
    simpa [prefixWord, tailWord_6000053, baseEnd_6000053] using wordTrace_append hprefix tailTrace_6000053
  have hstable : (prefixWord ++ tailWord_6000053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000053).length < 2 ^ (prefixWord ++ tailWord_6000053).sum := by decide
  have hdescent : baseEnd_6000053 < baseStart_6000053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000062 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_6000062 : Nat := 118140960795 + 6000062 * 2 ^ 59
def prefixEnd_6000062 : Nat := 4983230072969 + 3 ^ 40 * 6000062 * 2
def baseEnd_6000062 : Nat := 3080915762777208963531223

theorem tailTrace_6000062 : CollatzResearch.WordTrace tailWord_6000062 prefixEnd_6000062 3080915762777208963531223 := by
  unfold tailWord_6000062
  simp only [CollatzResearch.WordTrace]
  refine ⟨27355029948600947231483305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145893493059205051901244293 27355029948600947231483305)
  ·
    refine ⟨20516272461450710423612479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27355029948600947231483305 20516272461450710423612479)
    ·
      refine ⟨30774408692176065635418719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20516272461450710423612479 30774408692176065635418719)
      ·
        refine ⟨46161613038264098453128079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30774408692176065635418719 46161613038264098453128079)
        ·
          refine ⟨69242419557396147679692119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46161613038264098453128079 69242419557396147679692119)
          ·
            refine ⟨103863629336094221519538179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69242419557396147679692119 103863629336094221519538179)
            ·
              refine ⟨155795444004141332279307269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103863629336094221519538179 155795444004141332279307269)
              ·
                refine ⟨29211645750776499802370113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155795444004141332279307269 29211645750776499802370113)
                ·
                  refine ⟨21908734313082374851777585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29211645750776499802370113 21908734313082374851777585)
                  ·
                    refine ⟨16431550734811781138833189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21908734313082374851777585 16431550734811781138833189)
                    ·
                      refine ⟨3080915762777208963531223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16431550734811781138833189 3080915762777208963531223)
                      ·
                        rfl

theorem cell23_6000062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_6000062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000062 prefixEnd_6000062 := by exact prefixLift 6000062
  have htrace : WordTrace (prefixWord ++ tailWord_6000062) baseStart_6000062 baseEnd_6000062 := by
    simpa [prefixWord, tailWord_6000062, baseEnd_6000062] using wordTrace_append hprefix tailTrace_6000062
  have hstable : (prefixWord ++ tailWord_6000062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000062).length < 2 ^ (prefixWord ++ tailWord_6000062).sum := by decide
  have hdescent : baseEnd_6000062 < baseStart_6000062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000106 : List Nat := [3, 1, 3, 1, 4, 1, 2, 3, 5]
def baseStart_6000106 : Nat := 118140960795 + 6000106 * 2 ^ 59
def prefixEnd_6000106 : Nat := 4983230072969 + 3 ^ 40 * 6000106 * 2
def baseEnd_6000106 : Nat := 342326483991778532375669

theorem tailTrace_6000106 : CollatzResearch.WordTrace tailWord_6000106 prefixEnd_6000106 342326483991778532375669 := by
  unfold tailWord_6000106
  simp only [CollatzResearch.WordTrace]
  refine ⟨54710461100162043341617043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145894562933765448910978781 54710461100162043341617043)
  ·
    refine ⟨82065691650243065012425565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54710461100162043341617043 82065691650243065012425565)
    ·
      refine ⟨30774634368841149379659587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82065691650243065012425565 30774634368841149379659587)
      ·
        refine ⟨46161951553261724069489381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30774634368841149379659587 46161951553261724069489381)
        ·
          refine ⟨8655365916236573263029259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46161951553261724069489381 8655365916236573263029259)
          ·
            refine ⟨12983048874354859894543889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8655365916236573263029259 12983048874354859894543889)
            ·
              refine ⟨9737286655766144920907917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12983048874354859894543889 9737286655766144920907917)
              ·
                refine ⟨3651482495912304345340469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9737286655766144920907917 3651482495912304345340469)
                ·
                  refine ⟨342326483991778532375669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3651482495912304345340469 342326483991778532375669)
                  ·
                    rfl

theorem cell23_6000106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 5].length) (baseStart_6000106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000106 prefixEnd_6000106 := by exact prefixLift 6000106
  have htrace : WordTrace (prefixWord ++ tailWord_6000106) baseStart_6000106 baseEnd_6000106 := by
    simpa [prefixWord, tailWord_6000106, baseEnd_6000106] using wordTrace_append hprefix tailTrace_6000106
  have hstable : (prefixWord ++ tailWord_6000106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000106).length < 2 ^ (prefixWord ++ tailWord_6000106).sum := by decide
  have hdescent : baseEnd_6000106 < baseStart_6000106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000122 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4]
def baseStart_6000122 : Nat := 118140960795 + 6000122 * 2 ^ 59
def prefixEnd_6000122 : Nat := 4983230072969 + 3 ^ 40 * 6000122 * 2
def baseEnd_6000122 : Nat := 3080946571616478728780947

theorem tailTrace_6000122 : CollatzResearch.WordTrace tailWord_6000122 prefixEnd_6000122 3080946571616478728780947 := by
  unfold tailWord_6000122
  simp only [CollatzResearch.WordTrace]
  refine ⟨54710606992147552024762655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145894951979060138732700413 54710606992147552024762655)
  ·
    refine ⟨82065910488221328037143983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54710606992147552024762655 82065910488221328037143983)
    ·
      refine ⟨123098865732331992055715975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82065910488221328037143983 123098865732331992055715975)
      ·
        refine ⟨184648298598497988083573963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123098865732331992055715975 184648298598497988083573963)
        ·
          refine ⟨276972447897746982125360945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184648298598497988083573963 276972447897746982125360945)
          ·
            refine ⟨207729335923310236594020709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276972447897746982125360945 207729335923310236594020709)
            ·
              refine ⟨38949250485620669361378883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 207729335923310236594020709 38949250485620669361378883)
              ·
                refine ⟨58423875728431004042068325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38949250485620669361378883 58423875728431004042068325)
                ·
                  refine ⟨10954476699080813257887811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58423875728431004042068325 10954476699080813257887811)
                  ·
                    refine ⟨16431715048621219886831717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10954476699080813257887811 16431715048621219886831717)
                    ·
                      refine ⟨3080946571616478728780947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16431715048621219886831717 3080946571616478728780947)
                      ·
                        rfl

theorem cell23_6000122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_6000122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000122 prefixEnd_6000122 := by exact prefixLift 6000122
  have htrace : WordTrace (prefixWord ++ tailWord_6000122) baseStart_6000122 baseEnd_6000122 := by
    simpa [prefixWord, tailWord_6000122, baseEnd_6000122] using wordTrace_append hprefix tailTrace_6000122
  have hstable : (prefixWord ++ tailWord_6000122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000122).length < 2 ^ (prefixWord ++ tailWord_6000122).sum := by decide
  have hdescent : baseEnd_6000122 < baseStart_6000122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000134 : List Nat := [6, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_6000134 : Nat := 118140960795 + 6000134 * 2 ^ 59
def prefixEnd_6000134 : Nat := 4983230072969 + 3 ^ 40 * 6000134 * 2
def baseEnd_6000134 : Nat := 3080952733384332681830893

theorem tailTrace_6000134 : CollatzResearch.WordTrace tailWord_6000134 prefixEnd_6000134 3080952733384332681830893 := by
  unfold tailWord_6000134
  simp only [CollatzResearch.WordTrace]
  refine ⟨6838839551392085442140233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 145895243763031156098991637 6838839551392085442140233)
  ·
    refine ⟨5129129663544064081605175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6838839551392085442140233 5129129663544064081605175)
    ·
      refine ⟨7693694495316096122407763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5129129663544064081605175 7693694495316096122407763)
      ·
        refine ⟨11540541742974144183611645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7693694495316096122407763 11540541742974144183611645)
        ·
          refine ⟨4327703153615304068854367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11540541742974144183611645 4327703153615304068854367)
          ·
            refine ⟨6491554730422956103281551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4327703153615304068854367 6491554730422956103281551)
            ·
              refine ⟨9737332095634434154922327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6491554730422956103281551 9737332095634434154922327)
              ·
                refine ⟨14605998143451651232383491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9737332095634434154922327 14605998143451651232383491)
                ·
                  refine ⟨21908997215177476848575237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14605998143451651232383491 21908997215177476848575237)
                  ·
                    refine ⟨4107936977845776909107857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21908997215177476848575237 4107936977845776909107857)
                    ·
                      refine ⟨3080952733384332681830893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4107936977845776909107857 3080952733384332681830893)
                      ·
                        rfl

theorem cell23_6000134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_6000134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000134 prefixEnd_6000134 := by exact prefixLift 6000134
  have htrace : WordTrace (prefixWord ++ tailWord_6000134) baseStart_6000134 baseEnd_6000134 := by
    simpa [prefixWord, tailWord_6000134, baseEnd_6000134] using wordTrace_append hprefix tailTrace_6000134
  have hstable : (prefixWord ++ tailWord_6000134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000134).length < 2 ^ (prefixWord ++ tailWord_6000134).sum := by decide
  have hdescent : baseEnd_6000134 < baseStart_6000134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000149 : List Nat := [1, 3, 2, 1, 3, 2, 2, 2, 3, 4]
def baseStart_6000149 : Nat := 118140960795 + 6000149 * 2 ^ 59
def prefixEnd_6000149 : Nat := 4983230072969 + 3 ^ 40 * 6000149 * 2
def baseEnd_6000149 : Nat := 1026986811864716707714441

theorem tailTrace_6000149 : CollatzResearch.WordTrace tailWord_6000149 prefixEnd_6000149 1026986811864716707714441 := by
  unfold tailWord_6000149
  simp only [CollatzResearch.WordTrace]
  refine ⟨218843412739492391710283501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145895608492994927806855667 218843412739492391710283501)
  ·
    refine ⟨82066279777309646891356313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218843412739492391710283501 82066279777309646891356313)
    ·
      refine ⟨61549709832982235168517235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82066279777309646891356313 61549709832982235168517235)
      ·
        refine ⟨92324564749473352752775853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61549709832982235168517235 92324564749473352752775853)
        ·
          refine ⟨34621711781052507282290945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92324564749473352752775853 34621711781052507282290945)
          ·
            refine ⟨25966283835789380461718209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34621711781052507282290945 25966283835789380461718209)
            ·
              refine ⟨19474712876842035346288657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25966283835789380461718209 19474712876842035346288657)
              ·
                refine ⟨14606034657631526509716493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19474712876842035346288657 14606034657631526509716493)
                ·
                  refine ⟨5477262996611822441143685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14606034657631526509716493 5477262996611822441143685)
                  ·
                    refine ⟨1026986811864716707714441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5477262996611822441143685 1026986811864716707714441)
                    ·
                      rfl

theorem cell23_6000149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_6000149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000149 prefixEnd_6000149 := by exact prefixLift 6000149
  have htrace : WordTrace (prefixWord ++ tailWord_6000149) baseStart_6000149 baseEnd_6000149 := by
    simpa [prefixWord, tailWord_6000149, baseEnd_6000149] using wordTrace_append hprefix tailTrace_6000149
  have hstable : (prefixWord ++ tailWord_6000149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000149).length < 2 ^ (prefixWord ++ tailWord_6000149).sum := by decide
  have hdescent : baseEnd_6000149 < baseStart_6000149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000155 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 9]
def baseStart_6000155 : Nat := 118140960795 + 6000155 * 2 ^ 59
def prefixEnd_6000155 : Nat := 4983230072969 + 3 ^ 40 * 6000155 * 2
def baseEnd_6000155 : Nat := 3080963516478077099668295

theorem tailTrace_6000155 : CollatzResearch.WordTrace tailWord_6000155 prefixEnd_6000155 3080963516478077099668295 := by
  unfold tailWord_6000155
  simp only [CollatzResearch.WordTrace]
  refine ⟨218843631577470654735001919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145895754384980436490001279 218843631577470654735001919)
  ·
    refine ⟨328265447366205982102502879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218843631577470654735001919 328265447366205982102502879)
    ·
      refine ⟨492398171049308973153754319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328265447366205982102502879 492398171049308973153754319)
      ·
        refine ⟨738597256573963459730631479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492398171049308973153754319 738597256573963459730631479)
        ·
          refine ⟨1107895884860945189595947219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738597256573963459730631479 1107895884860945189595947219)
          ·
            refine ⟨1661843827291417784393920829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1107895884860945189595947219 1661843827291417784393920829)
            ·
              refine ⟨623191435234281669147720311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1661843827291417784393920829 623191435234281669147720311)
              ·
                refine ⟨934787152851422503721580467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623191435234281669147720311 934787152851422503721580467)
                ·
                  refine ⟨1402180729277133755582370701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 934787152851422503721580467 1402180729277133755582370701)
                  ·
                    refine ⟨525817773478925158343389013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1402180729277133755582370701 525817773478925158343389013)
                    ·
                      refine ⟨3080963516478077099668295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 525817773478925158343389013 3080963516478077099668295)
                      ·
                        rfl

theorem cell23_6000155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 9].length) (baseStart_6000155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000155 prefixEnd_6000155 := by exact prefixLift 6000155
  have htrace : WordTrace (prefixWord ++ tailWord_6000155) baseStart_6000155 baseEnd_6000155 := by
    simpa [prefixWord, tailWord_6000155, baseEnd_6000155] using wordTrace_append hprefix tailTrace_6000155
  have hstable : (prefixWord ++ tailWord_6000155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000155).length < 2 ^ (prefixWord ++ tailWord_6000155).sum := by decide
  have hdescent : baseEnd_6000155 < baseStart_6000155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000162 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 8]
def baseStart_6000162 : Nat := 118140960795 + 6000162 * 2 ^ 59
def prefixEnd_6000162 : Nat := 4983230072969 + 3 ^ 40 * 6000162 * 2
def baseEnd_6000162 : Nat := 342329678982517619142307

theorem tailTrace_6000162 : CollatzResearch.WordTrace tailWord_6000162 prefixEnd_6000162 342329678982517619142307 := by
  unfold tailWord_6000162
  simp only [CollatzResearch.WordTrace]
  refine ⟨54710971722111323732626685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145895924592296863287004493 54710971722111323732626685)
  ·
    refine ⟨20516614395791746399735007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54710971722111323732626685 20516614395791746399735007)
    ·
      refine ⟨30774921593687619599602511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20516614395791746399735007 30774921593687619599602511)
      ·
        refine ⟨46162382390531429399403767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30774921593687619599602511 46162382390531429399403767)
        ·
          refine ⟨69243573585797144099105651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46162382390531429399403767 69243573585797144099105651)
          ·
            refine ⟨103865360378695716148658477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69243573585797144099105651 103865360378695716148658477)
            ·
              refine ⟨38949510142010893555746929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103865360378695716148658477 38949510142010893555746929)
              ·
                refine ⟨29212132606508170166810197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38949510142010893555746929 29212132606508170166810197)
                ·
                  refine ⟨342329678982517619142307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29212132606508170166810197 342329678982517619142307)
                  ·
                    rfl

theorem cell23_6000162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_6000162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000162 prefixEnd_6000162 := by exact prefixLift 6000162
  have htrace : WordTrace (prefixWord ++ tailWord_6000162) baseStart_6000162 baseEnd_6000162 := by
    simpa [prefixWord, tailWord_6000162, baseEnd_6000162] using wordTrace_append hprefix tailTrace_6000162
  have hstable : (prefixWord ++ tailWord_6000162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000162).length < 2 ^ (prefixWord ++ tailWord_6000162).sum := by decide
  have hdescent : baseEnd_6000162 < baseStart_6000162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000183 : List Nat := [1, 1, 3, 1, 2, 5, 3, 2, 1, 4]
def baseStart_6000183 : Nat := 118140960795 + 6000183 * 2 ^ 59
def prefixEnd_6000183 : Nat := 4983230072969 + 3 ^ 40 * 6000183 * 2
def baseEnd_6000183 : Nat := 1026992631312134330039389

theorem tailTrace_6000183 : CollatzResearch.WordTrace tailWord_6000183 prefixEnd_6000183 1026992631312134330039389 := by
  unfold tailWord_6000183
  simp only [CollatzResearch.WordTrace]
  refine ⟨218844652821369215517021203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145896435214246143678014135 218844652821369215517021203)
  ·
    refine ⟨328266979232053823275531805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218844652821369215517021203 328266979232053823275531805)
    ·
      refine ⟨123100117212020183728324427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328266979232053823275531805 123100117212020183728324427)
      ·
        refine ⟨184650175818030275592486641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123100117212020183728324427 184650175818030275592486641)
        ·
          refine ⟨138487631863522706694364981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184650175818030275592486641 138487631863522706694364981)
          ·
            refine ⟨12983215487205253752596717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138487631863522706694364981 12983215487205253752596717)
            ·
              refine ⟨4868705807701970157223769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12983215487205253752596717 4868705807701970157223769)
              ·
                refine ⟨3651529355776477617917827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4868705807701970157223769 3651529355776477617917827)
                ·
                  refine ⟨5477294033664716426876741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3651529355776477617917827 5477294033664716426876741)
                  ·
                    refine ⟨1026992631312134330039389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5477294033664716426876741 1026992631312134330039389)
                    ·
                      rfl

theorem cell23_6000183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 1, 4].length) (baseStart_6000183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000183 prefixEnd_6000183 := by exact prefixLift 6000183
  have htrace : WordTrace (prefixWord ++ tailWord_6000183) baseStart_6000183 baseEnd_6000183 := by
    simpa [prefixWord, tailWord_6000183, baseEnd_6000183] using wordTrace_append hprefix tailTrace_6000183
  have hstable : (prefixWord ++ tailWord_6000183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000183).length < 2 ^ (prefixWord ++ tailWord_6000183).sum := by decide
  have hdescent : baseEnd_6000183 < baseStart_6000183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000192 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 3, 5]
def baseStart_6000192 : Nat := 118140960795 + 6000192 * 2 ^ 59
def prefixEnd_6000192 : Nat := 4983230072969 + 3 ^ 40 * 6000192 * 2
def baseEnd_6000192 : Nat := 1026994171754097818301875

theorem tailTrace_6000192 : CollatzResearch.WordTrace tailWord_6000192 prefixEnd_6000192 1026994171754097818301875 := by
  unfold tailWord_6000192
  simp only [CollatzResearch.WordTrace]
  refine ⟨109422490539168305027049415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145896654052224406702732553 109422490539168305027049415)
  ·
    refine ⟨164133735808752457540574123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109422490539168305027049415 164133735808752457540574123)
    ·
      refine ⟨246200603713128686310861185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164133735808752457540574123 246200603713128686310861185)
      ·
        refine ⟨184650452784846514733145889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246200603713128686310861185 184650452784846514733145889)
        ·
          refine ⟨138487839588634886049859417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184650452784846514733145889 138487839588634886049859417)
          ·
            refine ⟨103865879691476164537394563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138487839588634886049859417 103865879691476164537394563)
            ·
              refine ⟨155798819537214246806091845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103865879691476164537394563 155798819537214246806091845)
              ·
                refine ⟨29212278663227671276142221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155798819537214246806091845 29212278663227671276142221)
                ·
                  refine ⟨10954604498710376728553333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29212278663227671276142221 10954604498710376728553333)
                  ·
                    refine ⟨1026994171754097818301875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10954604498710376728553333 1026994171754097818301875)
                    ·
                      rfl

theorem cell23_6000192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 3, 5].length) (baseStart_6000192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000192 prefixEnd_6000192 := by exact prefixLift 6000192
  have htrace : WordTrace (prefixWord ++ tailWord_6000192) baseStart_6000192 baseEnd_6000192 := by
    simpa [prefixWord, tailWord_6000192, baseEnd_6000192] using wordTrace_append hprefix tailTrace_6000192
  have hstable : (prefixWord ++ tailWord_6000192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000192).length < 2 ^ (prefixWord ++ tailWord_6000192).sum := by decide
  have hdescent : baseEnd_6000192 < baseStart_6000192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000240 : List Nat := [2, 1, 1, 1, 6, 1, 4, 2, 1, 1, 3]
def baseStart_6000240 : Nat := 118140960795 + 6000240 * 2 ^ 59
def prefixEnd_6000240 : Nat := 4983230072969 + 3 ^ 40 * 6000240 * 2
def baseEnd_6000240 : Nat := 3081007162333709267105405

theorem tailTrace_6000240 : CollatzResearch.WordTrace tailWord_6000240 prefixEnd_6000240 3081007162333709267105405 := by
  unfold tailWord_6000240
  simp only [CollatzResearch.WordTrace]
  refine ⟨109423365891081357125923087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145897821188108476167897449 109423365891081357125923087)
  ·
    refine ⟨164135048836622035688884631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109423365891081357125923087 164135048836622035688884631)
    ·
      refine ⟨246202573254933053533326947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164135048836622035688884631 246202573254933053533326947)
      ·
        refine ⟨369303859882399580299990421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246202573254933053533326947 369303859882399580299990421)
        ·
          refine ⟨17311118431987480326562051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 369303859882399580299990421 17311118431987480326562051)
          ·
            refine ⟨25966677647981220489843077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17311118431987480326562051 25966677647981220489843077)
            ·
              refine ⟨4868752058996478841845577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25966677647981220489843077 4868752058996478841845577)
              ·
                refine ⟨3651564044247359131384183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4868752058996478841845577 3651564044247359131384183)
                ·
                  refine ⟨5477346066371038697076275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3651564044247359131384183 5477346066371038697076275)
                  ·
                    refine ⟨8216019099556558045614413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5477346066371038697076275 8216019099556558045614413)
                    ·
                      refine ⟨3081007162333709267105405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8216019099556558045614413 3081007162333709267105405)
                      ·
                        rfl

theorem cell23_6000240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 1, 1, 3].length) (baseStart_6000240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000240 prefixEnd_6000240 := by exact prefixLift 6000240
  have htrace : WordTrace (prefixWord ++ tailWord_6000240) baseStart_6000240 baseEnd_6000240 := by
    simpa [prefixWord, tailWord_6000240, baseEnd_6000240] using wordTrace_append hprefix tailTrace_6000240
  have hstable : (prefixWord ++ tailWord_6000240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000240).length < 2 ^ (prefixWord ++ tailWord_6000240).sum := by decide
  have hdescent : baseEnd_6000240 < baseStart_6000240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000246 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_6000246 : Nat := 118140960795 + 6000246 * 2 ^ 59
def prefixEnd_6000246 : Nat := 4983230072969 + 3 ^ 40 * 6000246 * 2
def baseEnd_6000246 : Nat := 3081010243217636243630377

theorem tailTrace_6000246 : CollatzResearch.WordTrace tailWord_6000246 prefixEnd_6000246 3081010243217636243630377 := by
  unfold tailWord_6000246
  simp only [CollatzResearch.WordTrace]
  refine ⟨13677934413758811079785287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145897967080093984851043061 13677934413758811079785287)
  ·
    refine ⟨20516901620638216619677931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13677934413758811079785287 20516901620638216619677931)
    ·
      refine ⟨30775352430957324929516897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20516901620638216619677931 30775352430957324929516897)
      ·
        refine ⟨23081514323217993697137673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30775352430957324929516897 23081514323217993697137673)
        ·
          refine ⟨17311135742413495272853255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23081514323217993697137673 17311135742413495272853255)
          ·
            refine ⟨25966703613620242909279883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17311135742413495272853255 25966703613620242909279883)
            ·
              refine ⟨38950055420430364363919825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25966703613620242909279883 38950055420430364363919825)
              ·
                refine ⟨29212541565322773272939869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38950055420430364363919825 29212541565322773272939869)
                ·
                  refine ⟨10954703086996039977352451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29212541565322773272939869 10954703086996039977352451)
                  ·
                    refine ⟨16432054630494059966028677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10954703086996039977352451 16432054630494059966028677)
                    ·
                      refine ⟨3081010243217636243630377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16432054630494059966028677 3081010243217636243630377)
                      ·
                        rfl

theorem cell23_6000246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_6000246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000246 prefixEnd_6000246 := by exact prefixLift 6000246
  have htrace : WordTrace (prefixWord ++ tailWord_6000246) baseStart_6000246 baseEnd_6000246 := by
    simpa [prefixWord, tailWord_6000246, baseEnd_6000246] using wordTrace_append hprefix tailTrace_6000246
  have hstable : (prefixWord ++ tailWord_6000246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000246).length < 2 ^ (prefixWord ++ tailWord_6000246).sum := by decide
  have hdescent : baseEnd_6000246 < baseStart_6000246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000249 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 5, 2, 3]
def baseStart_6000249 : Nat := 118140960795 + 6000249 * 2 ^ 59
def prefixEnd_6000249 : Nat := 4983230072969 + 3 ^ 40 * 6000249 * 2
def baseEnd_6000249 : Nat := 3081011783659599731892863

theorem tailTrace_6000249 : CollatzResearch.WordTrace tailWord_6000249 prefixEnd_6000249 3081011783659599731892863 := by
  unfold tailWord_6000249
  simp only [CollatzResearch.WordTrace]
  refine ⟨218847060039130108788923801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145898040026086739192615867 218847060039130108788923801)
  ·
    refine ⟨164135295029347581591692851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218847060039130108788923801 164135295029347581591692851)
    ·
      refine ⟨246202942544021372387539277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164135295029347581591692851 246202942544021372387539277)
      ·
        refine ⟨92326103454008014645327229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246202942544021372387539277 92326103454008014645327229)
        ·
          refine ⟨34622288795253005491997711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92326103454008014645327229 34622288795253005491997711)
          ·
            refine ⟨51933433192879508237996567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34622288795253005491997711 51933433192879508237996567)
            ·
              refine ⟨77900149789319262356994851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51933433192879508237996567 77900149789319262356994851)
              ·
                refine ⟨116850224683978893535492277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77900149789319262356994851 116850224683978893535492277)
                ·
                  refine ⟨10954708564123021268952401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116850224683978893535492277 10954708564123021268952401)
                  ·
                    refine ⟨8216031423092265951714301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10954708564123021268952401 8216031423092265951714301)
                    ·
                      refine ⟨3081011783659599731892863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8216031423092265951714301 3081011783659599731892863)
                      ·
                        rfl

theorem cell23_6000249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_6000249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000249 prefixEnd_6000249 := by exact prefixLift 6000249
  have htrace : WordTrace (prefixWord ++ tailWord_6000249) baseStart_6000249 baseEnd_6000249 := by
    simpa [prefixWord, tailWord_6000249, baseEnd_6000249] using wordTrace_append hprefix tailTrace_6000249
  have hstable : (prefixWord ++ tailWord_6000249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000249).length < 2 ^ (prefixWord ++ tailWord_6000249).sum := by decide
  have hdescent : baseEnd_6000249 < baseStart_6000249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000263 : List Nat := [1, 1, 4, 2, 1, 4, 1, 2, 3, 2, 2]
def baseStart_6000263 : Nat := 118140960795 + 6000263 * 2 ^ 59
def prefixEnd_6000263 : Nat := 4983230072969 + 3 ^ 40 * 6000263 * 2
def baseEnd_6000263 : Nat := 3081018972388762677117799

theorem tailTrace_6000263 : CollatzResearch.WordTrace tailWord_6000263 prefixEnd_6000263 3081018972388762677117799 := by
  unfold tailWord_6000263
  simp only [CollatzResearch.WordTrace]
  refine ⟨218847570661079389179933443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145898380440719592786622295 218847570661079389179933443)
  ·
    refine ⟨328271355991619083769900165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218847570661079389179933443 328271355991619083769900165)
    ·
      refine ⟨61550879248428578206856281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 328271355991619083769900165 61550879248428578206856281)
      ·
        refine ⟨46163159436321433655142211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61550879248428578206856281 46163159436321433655142211)
        ·
          refine ⟨69244739154482150482713317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46163159436321433655142211 69244739154482150482713317)
          ·
            refine ⟨12983388591465403215508747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69244739154482150482713317 12983388591465403215508747)
            ·
              refine ⟨19475082887198104823263121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12983388591465403215508747 19475082887198104823263121)
              ·
                refine ⟨14606312165398578617447341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19475082887198104823263121 14606312165398578617447341)
                ·
                  refine ⟨5477367062024466981542753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14606312165398578617447341 5477367062024466981542753)
                  ·
                    refine ⟨4108025296518350236157065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5477367062024466981542753 4108025296518350236157065)
                    ·
                      refine ⟨3081018972388762677117799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4108025296518350236157065 3081018972388762677117799)
                      ·
                        rfl

theorem cell23_6000263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_6000263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000263 prefixEnd_6000263 := by exact prefixLift 6000263
  have htrace : WordTrace (prefixWord ++ tailWord_6000263) baseStart_6000263 baseEnd_6000263 := by
    simpa [prefixWord, tailWord_6000263, baseEnd_6000263] using wordTrace_append hprefix tailTrace_6000263
  have hstable : (prefixWord ++ tailWord_6000263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000263).length < 2 ^ (prefixWord ++ tailWord_6000263).sum := by decide
  have hdescent : baseEnd_6000263 < baseStart_6000263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000266 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 3, 2, 3]
def baseStart_6000266 : Nat := 118140960795 + 6000266 * 2 ^ 59
def prefixEnd_6000266 : Nat := 4983230072969 + 3 ^ 40 * 6000266 * 2
def baseEnd_6000266 : Nat := 3081020512830726165380285

theorem tailTrace_6000266 : CollatzResearch.WordTrace tailWord_6000266 prefixEnd_6000266 3081020512830726165380285 := by
  unfold tailWord_6000266
  simp only [CollatzResearch.WordTrace]
  refine ⟨54711920020017130173073163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145898453386712347128195101 54711920020017130173073163)
  ·
    refine ⟨82067880030025695259609745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54711920020017130173073163 82067880030025695259609745)
    ·
      refine ⟨61550910022519271444707309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82067880030025695259609745 61550910022519271444707309)
      ·
        refine ⟨23081591258444726791765241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61550910022519271444707309 23081591258444726791765241)
        ·
          refine ⟨17311193443833545093823931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23081591258444726791765241 17311193443833545093823931)
          ·
            refine ⟨25966790165750317640735897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17311193443833545093823931 25966790165750317640735897)
            ·
              refine ⟨19475092624312738230551923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25966790165750317640735897 19475092624312738230551923)
              ·
                refine ⟨29212638936469107345827885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19475092624312738230551923 29212638936469107345827885)
                ·
                  refine ⟨10954739601175915254685457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29212638936469107345827885 10954739601175915254685457)
                  ·
                    refine ⟨8216054700881936441014093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10954739601175915254685457 8216054700881936441014093)
                    ·
                      refine ⟨3081020512830726165380285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8216054700881936441014093 3081020512830726165380285)
                      ·
                        rfl

theorem cell23_6000266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_6000266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000266 prefixEnd_6000266 := by exact prefixLift 6000266
  have htrace : WordTrace (prefixWord ++ tailWord_6000266) baseStart_6000266 baseEnd_6000266 := by
    simpa [prefixWord, tailWord_6000266, baseEnd_6000266] using wordTrace_append hprefix tailTrace_6000266
  have hstable : (prefixWord ++ tailWord_6000266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000266).length < 2 ^ (prefixWord ++ tailWord_6000266).sum := by decide
  have hdescent : baseEnd_6000266 < baseStart_6000266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000280 : List Nat := [2, 1, 2, 4, 1, 2, 1, 5, 1, 2, 2]
def baseStart_6000280 : Nat := 118140960795 + 6000280 * 2 ^ 59
def prefixEnd_6000280 : Nat := 4983230072969 + 3 ^ 40 * 6000280 * 2
def baseEnd_6000280 : Nat := 3081027701559889110605221

theorem tailTrace_6000280 : CollatzResearch.WordTrace tailWord_6000280 prefixEnd_6000280 3081027701559889110605221 := by
  unfold tailWord_6000280
  simp only [CollatzResearch.WordTrace]
  refine ⟨109424095351008900541651147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145898793801345200722201529 109424095351008900541651147)
  ·
    refine ⟨164136143026513350812476721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109424095351008900541651147 164136143026513350812476721)
    ·
      refine ⟨123102107269885013109357541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164136143026513350812476721 123102107269885013109357541)
      ·
        refine ⟨23081645113103439958004539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123102107269885013109357541 23081645113103439958004539)
        ·
          refine ⟨34622467669655159937006809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23081645113103439958004539 34622467669655159937006809)
          ·
            refine ⟨25966850752241369952755107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34622467669655159937006809 25966850752241369952755107)
            ·
              refine ⟨38950276128362054929132661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25966850752241369952755107 38950276128362054929132661)
              ·
                refine ⟨3651588387033942649606187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38950276128362054929132661 3651588387033942649606187)
                ·
                  refine ⟨5477382580550913974409281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3651588387033942649606187 5477382580550913974409281)
                  ·
                    refine ⟨4108036935413185480806961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5477382580550913974409281 4108036935413185480806961)
                    ·
                      refine ⟨3081027701559889110605221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4108036935413185480806961 3081027701559889110605221)
                      ·
                        rfl

theorem cell23_6000280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_6000280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000280 prefixEnd_6000280 := by exact prefixLift 6000280
  have htrace : WordTrace (prefixWord ++ tailWord_6000280) baseStart_6000280 baseEnd_6000280 := by
    simpa [prefixWord, tailWord_6000280, baseEnd_6000280] using wordTrace_append hprefix tailTrace_6000280
  have hstable : (prefixWord ++ tailWord_6000280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000280).length < 2 ^ (prefixWord ++ tailWord_6000280).sum := by decide
  have hdescent : baseEnd_6000280 < baseStart_6000280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000306 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2]
def baseStart_6000306 : Nat := 118140960795 + 6000306 * 2 ^ 59
def prefixEnd_6000306 : Nat := 4983230072969 + 3 ^ 40 * 6000306 * 2
def baseEnd_6000306 : Nat := 3081041052056906008880101

theorem tailTrace_6000306 : CollatzResearch.WordTrace tailWord_6000306 prefixEnd_6000306 3081041052056906008880101 := by
  unfold tailWord_6000306
  simp only [CollatzResearch.WordTrace]
  refine ⟨54712284749980901880937193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145899425999949071682499181 54712284749980901880937193)
  ·
    refine ⟨41034213562485676410702895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54712284749980901880937193 41034213562485676410702895)
    ·
      refine ⟨61551320343728514616054343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41034213562485676410702895 61551320343728514616054343)
      ·
        refine ⟨92326980515592771924081515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61551320343728514616054343 92326980515592771924081515)
        ·
          refine ⟨138490470773389157886122273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92326980515592771924081515 138490470773389157886122273)
          ·
            refine ⟨103867853080041868414591705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138490470773389157886122273 103867853080041868414591705)
            ·
              refine ⟨77900889810031401310943779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103867853080041868414591705 77900889810031401310943779)
              ·
                refine ⟨116851334715047101966415669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77900889810031401310943779 116851334715047101966415669)
                ·
                  refine ⟨10954812629535665809351469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116851334715047101966415669 10954812629535665809351469)
                  ·
                    refine ⟨4108054736075874678506801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10954812629535665809351469 4108054736075874678506801)
                    ·
                      refine ⟨3081041052056906008880101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4108054736075874678506801 3081041052056906008880101)
                      ·
                        rfl

theorem cell23_6000306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2].length) (baseStart_6000306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000306 prefixEnd_6000306 := by exact prefixLift 6000306
  have htrace : WordTrace (prefixWord ++ tailWord_6000306) baseStart_6000306 baseEnd_6000306 := by
    simpa [prefixWord, tailWord_6000306, baseEnd_6000306] using wordTrace_append hprefix tailTrace_6000306
  have hstable : (prefixWord ++ tailWord_6000306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000306).length < 2 ^ (prefixWord ++ tailWord_6000306).sum := by decide
  have hdescent : baseEnd_6000306 < baseStart_6000306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000310 : List Nat := [5, 1, 3, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_6000310 : Nat := 118140960795 + 6000310 * 2 ^ 59
def prefixEnd_6000310 : Nat := 4983230072969 + 3 ^ 40 * 6000310 * 2
def baseEnd_6000310 : Nat := 3081043105979523993230083

theorem tailTrace_6000310 : CollatzResearch.WordTrace tailWord_6000310 prefixEnd_6000310 3081043105979523993230083 := by
  unfold tailWord_6000310
  simp only [CollatzResearch.WordTrace]
  refine ⟨13678080305744319762930899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145899523261272744137929589 13678080305744319762930899)
  ·
    refine ⟨20517120458616479644396349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13678080305744319762930899 20517120458616479644396349)
    ·
      refine ⟨7693920171981179866648631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20517120458616479644396349 7693920171981179866648631)
      ·
        refine ⟨11540880257971769799972947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7693920171981179866648631 11540880257971769799972947)
        ·
          refine ⟨17311320386957654699959421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11540880257971769799972947 17311320386957654699959421)
          ·
            refine ⟨6491745145109120512484783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17311320386957654699959421 6491745145109120512484783)
            ·
              refine ⟨9737617717663680768727175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6491745145109120512484783 9737617717663680768727175)
              ·
                refine ⟨14606426576495521153090763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9737617717663680768727175 14606426576495521153090763)
                ·
                  refine ⟨21909639864743281729636145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14606426576495521153090763 21909639864743281729636145)
                  ·
                    refine ⟨16432229898557461297227109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21909639864743281729636145 16432229898557461297227109)
                    ·
                      refine ⟨3081043105979523993230083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16432229898557461297227109 3081043105979523993230083)
                      ·
                        rfl

theorem cell23_6000310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_6000310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000310 prefixEnd_6000310 := by exact prefixLift 6000310
  have htrace : WordTrace (prefixWord ++ tailWord_6000310) baseStart_6000310 baseEnd_6000310 := by
    simpa [prefixWord, tailWord_6000310, baseEnd_6000310] using wordTrace_append hprefix tailTrace_6000310
  have hstable : (prefixWord ++ tailWord_6000310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000310).length < 2 ^ (prefixWord ++ tailWord_6000310).sum := by decide
  have hdescent : baseEnd_6000310 < baseStart_6000310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000340 : List Nat := [2, 4, 1, 3, 1, 1, 2, 3, 1, 3, 2]
def baseStart_6000340 : Nat := 118140960795 + 6000340 * 2 ^ 59
def prefixEnd_6000340 : Nat := 4983230072969 + 3 ^ 40 * 6000340 * 2
def baseEnd_6000340 : Nat := 3081058510399158875854945

theorem tailTrace_6000340 : CollatzResearch.WordTrace tailWord_6000340 prefixEnd_6000340 3081058510399158875854945 := by
  unfold tailWord_6000340
  simp only [CollatzResearch.WordTrace]
  refine ⟨109425189540900215665243237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145900252721200287553657649 109425189540900215665243237)
  ·
    refine ⟨20517223038918790437233107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109425189540900215665243237 20517223038918790437233107)
    ·
      refine ⟨30775834558378185655849661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20517223038918790437233107 30775834558378185655849661)
      ·
        refine ⟨11540937959391819620943623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30775834558378185655849661 11540937959391819620943623)
        ·
          refine ⟨17311406939087729431415435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11540937959391819620943623 17311406939087729431415435)
          ·
            refine ⟨25967110408631594147123153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17311406939087729431415435 25967110408631594147123153)
            ·
              refine ⟨19475332806473695610342365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25967110408631594147123153 19475332806473695610342365)
              ·
                refine ⟨7303249802427635853878387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19475332806473695610342365 7303249802427635853878387)
                ·
                  refine ⟨10954874703641453780817581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7303249802427635853878387 10954874703641453780817581)
                  ·
                    refine ⟨4108078013865545167806593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10954874703641453780817581 4108078013865545167806593)
                    ·
                      refine ⟨3081058510399158875854945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4108078013865545167806593 3081058510399158875854945)
                      ·
                        rfl

theorem cell23_6000340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_6000340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000340 prefixEnd_6000340 := by exact prefixLift 6000340
  have htrace : WordTrace (prefixWord ++ tailWord_6000340) baseStart_6000340 baseEnd_6000340 := by
    simpa [prefixWord, tailWord_6000340, baseEnd_6000340] using wordTrace_append hprefix tailTrace_6000340
  have hstable : (prefixWord ++ tailWord_6000340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000340).length < 2 ^ (prefixWord ++ tailWord_6000340).sum := by decide
  have hdescent : baseEnd_6000340 < baseStart_6000340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000370 : List Nat := [3, 2, 1, 3, 1, 1, 3, 3, 2, 2, 2]
def baseStart_6000370 : Nat := 118140960795 + 6000370 * 2 ^ 59
def prefixEnd_6000370 : Nat := 4983230072969 + 3 ^ 40 * 6000370 * 2
def baseEnd_6000370 : Nat := 3081073914818793758479807

theorem tailTrace_6000370 : CollatzResearch.WordTrace tailWord_6000370 prefixEnd_6000370 3081073914818793758479807 := by
  unfold tailWord_6000370
  simp only [CollatzResearch.WordTrace]
  refine ⟨54712868317922936613519641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145900982181127830969385709 54712868317922936613519641)
  ·
    refine ⟨41034651238442202460139731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54712868317922936613519641 41034651238442202460139731)
    ·
      refine ⟨61551976857663303690209597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41034651238442202460139731 61551976857663303690209597)
      ·
        refine ⟨23081991321623738883828599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61551976857663303690209597 23081991321623738883828599)
        ·
          refine ⟨34622986982435608325742899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23081991321623738883828599 34622986982435608325742899)
          ·
            refine ⟨51934480473653412488614349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34622986982435608325742899 51934480473653412488614349)
            ·
              refine ⟨19475430177620029683230381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51934480473653412488614349 19475430177620029683230381)
              ·
                refine ⟨7303286316607511131211393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19475430177620029683230381 7303286316607511131211393)
                ·
                  refine ⟨5477464737455633348408545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7303286316607511131211393 5477464737455633348408545)
                  ·
                    refine ⟨4108098553091725011306409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5477464737455633348408545 4108098553091725011306409)
                    ·
                      refine ⟨3081073914818793758479807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4108098553091725011306409 3081073914818793758479807)
                      ·
                        rfl

theorem cell23_6000370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_6000370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000370 prefixEnd_6000370 := by exact prefixLift 6000370
  have htrace : WordTrace (prefixWord ++ tailWord_6000370) baseStart_6000370 baseEnd_6000370 := by
    simpa [prefixWord, tailWord_6000370, baseEnd_6000370] using wordTrace_append hprefix tailTrace_6000370
  have hstable : (prefixWord ++ tailWord_6000370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000370).length < 2 ^ (prefixWord ++ tailWord_6000370).sum := by decide
  have hdescent : baseEnd_6000370 < baseStart_6000370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000410 : List Nat := [3, 1, 1, 3, 2, 4, 2, 2, 5]
def baseStart_6000410 : Nat := 118140960795 + 6000410 * 2 ^ 59
def prefixEnd_6000410 : Nat := 4983230072969 + 3 ^ 40 * 6000410 * 2
def baseEnd_6000410 : Nat := 342343828227219289108847

theorem tailTrace_6000410 : CollatzResearch.WordTrace tailWord_6000410 prefixEnd_6000410 342343828227219289108847 := by
  unfold tailWord_6000410
  simp only [CollatzResearch.WordTrace]
  refine ⟨54713233047886708321383671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145901954794364555523689789 54713233047886708321383671)
  ·
    refine ⟨82069849571830062482075507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54713233047886708321383671 82069849571830062482075507)
    ·
      refine ⟨123104774357745093723113261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82069849571830062482075507 123104774357745093723113261)
      ·
        refine ⟨46164290384154410146167473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123104774357745093723113261 46164290384154410146167473)
        ·
          refine ⟨34623217788115807609625605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46164290384154410146167473 34623217788115807609625605)
          ·
            refine ⟨6491853335271713926804801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34623217788115807609625605 6491853335271713926804801)
            ·
              refine ⟨4868890001453785445103601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6491853335271713926804801 4868890001453785445103601)
              ·
                refine ⟨3651667501090339083827701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4868890001453785445103601 3651667501090339083827701)
                ·
                  refine ⟨342343828227219289108847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3651667501090339083827701 342343828227219289108847)
                  ·
                    rfl

theorem cell23_6000410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 5].length) (baseStart_6000410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000410 prefixEnd_6000410 := by exact prefixLift 6000410
  have htrace : WordTrace (prefixWord ++ tailWord_6000410) baseStart_6000410 baseEnd_6000410 := by
    simpa [prefixWord, tailWord_6000410, baseEnd_6000410] using wordTrace_append hprefix tailTrace_6000410
  have hstable : (prefixWord ++ tailWord_6000410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000410).length < 2 ^ (prefixWord ++ tailWord_6000410).sum := by decide
  have hdescent : baseEnd_6000410 < baseStart_6000410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000439 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 4]
def baseStart_6000439 : Nat := 118140960795 + 6000439 * 2 ^ 59
def prefixEnd_6000439 : Nat := 4983230072969 + 3 ^ 40 * 6000439 * 2
def baseEnd_6000439 : Nat := 3081109344983953988516989

theorem tailTrace_6000439 : CollatzResearch.WordTrace tailWord_6000439 prefixEnd_6000439 3081109344983953988516989 := by
  unfold tailWord_6000439
  simp only [CollatzResearch.WordTrace]
  refine ⟨218853989908441771238340371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145902659938961180825560247 218853989908441771238340371)
  ·
    refine ⟨328280984862662656857510557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218853989908441771238340371 328280984862662656857510557)
    ·
      refine ⟨123105369323498496321566459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328280984862662656857510557 123105369323498496321566459)
      ·
        refine ⟨184658053985247744482349689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123105369323498496321566459 184658053985247744482349689)
        ·
          refine ⟨138493540488935808361762267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184658053985247744482349689 138493540488935808361762267)
          ·
            refine ⟨207740310733403712542643401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138493540488935808361762267 207740310733403712542643401)
            ·
              refine ⟨155805233050052784406982551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207740310733403712542643401 155805233050052784406982551)
              ·
                refine ⟨233707849575079176610473827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155805233050052784406982551 233707849575079176610473827)
                ·
                  refine ⟨350561774362618764915710741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233707849575079176610473827 350561774362618764915710741)
                  ·
                    refine ⟨16432583173247754605423941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 350561774362618764915710741 16432583173247754605423941)
                    ·
                      refine ⟨3081109344983953988516989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16432583173247754605423941 3081109344983953988516989)
                      ·
                        rfl

theorem cell23_6000439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_6000439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000439 prefixEnd_6000439 := by exact prefixLift 6000439
  have htrace : WordTrace (prefixWord ++ tailWord_6000439) baseStart_6000439 baseEnd_6000439 := by
    simpa [prefixWord, tailWord_6000439, baseEnd_6000439] using wordTrace_append hprefix tailTrace_6000439
  have hstable : (prefixWord ++ tailWord_6000439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000439).length < 2 ^ (prefixWord ++ tailWord_6000439).sum := by decide
  have hdescent : baseEnd_6000439 < baseStart_6000439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000466 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 8]
def baseStart_6000466 : Nat := 118140960795 + 6000466 * 2 ^ 59
def prefixEnd_6000466 : Nat := 4983230072969 + 3 ^ 40 * 6000466 * 2
def baseEnd_6000466 : Nat := 342347023217958375875485

theorem tailTrace_6000466 : CollatzResearch.WordTrace tailWord_6000466 prefixEnd_6000466 342347023217958375875485 := by
  unfold tailWord_6000466
  simp only [CollatzResearch.WordTrace]
  refine ⟨54713743669835988712393313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145903316452895969899715501 54713743669835988712393313)
  ·
    refine ⟨41035307752376991534294985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54713743669835988712393313 41035307752376991534294985)
    ·
      refine ⟨30776480814282743650721239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41035307752376991534294985 30776480814282743650721239)
      ·
        refine ⟨46164721221424115476081859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30776480814282743650721239 46164721221424115476081859)
        ·
          refine ⟨69247081832136173214122789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46164721221424115476081859 69247081832136173214122789)
          ·
            refine ⟨12983827843525532477648023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69247081832136173214122789 12983827843525532477648023)
            ·
              refine ⟨19475741765288298716472035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12983827843525532477648023 19475741765288298716472035)
              ·
                refine ⟨29213612647932448074708053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19475741765288298716472035 29213612647932448074708053)
                ·
                  refine ⟨342347023217958375875485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29213612647932448074708053 342347023217958375875485)
                  ·
                    rfl

theorem cell23_6000466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_6000466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000466 prefixEnd_6000466 := by exact prefixLift 6000466
  have htrace : WordTrace (prefixWord ++ tailWord_6000466) baseStart_6000466 baseEnd_6000466 := by
    simpa [prefixWord, tailWord_6000466, baseEnd_6000466] using wordTrace_append hprefix tailTrace_6000466
  have hstable : (prefixWord ++ tailWord_6000466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000466).length < 2 ^ (prefixWord ++ tailWord_6000466).sum := by decide
  have hdescent : baseEnd_6000466 < baseStart_6000466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000489 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 2, 1, 7]
def baseStart_6000489 : Nat := 118140960795 + 6000489 * 2 ^ 59
def prefixEnd_6000489 : Nat := 4983230072969 + 3 ^ 40 * 6000489 * 2
def baseEnd_6000489 : Nat := 3081135019016678792891759

theorem tailTrace_6000489 : CollatzResearch.WordTrace tailWord_6000489 prefixEnd_6000489 3081135019016678792891759 := by
  unfold tailWord_6000489
  simp only [CollatzResearch.WordTrace]
  refine ⟨218855813558260629777660521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145903875705507086518440347 218855813558260629777660521)
  ·
    refine ⟨164141860168695472333245391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218855813558260629777660521 164141860168695472333245391)
    ·
      refine ⟨246212790253043208499868087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164141860168695472333245391 246212790253043208499868087)
      ·
        refine ⟨369319185379564812749802131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246212790253043208499868087 369319185379564812749802131)
        ·
          refine ⟨553978778069347219124703197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369319185379564812749802131 553978778069347219124703197)
          ·
            refine ⟨207742041776005207171763699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 553978778069347219124703197 207742041776005207171763699)
            ·
              refine ⟨311613062664007810757645549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207742041776005207171763699 311613062664007810757645549)
              ·
                refine ⟨116854898499002929034117081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311613062664007810757645549 116854898499002929034117081)
                ·
                  refine ⟨87641173874252196775587811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116854898499002929034117081 87641173874252196775587811)
                  ·
                    refine ⟨131461760811378295163381717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87641173874252196775587811 131461760811378295163381717)
                    ·
                      refine ⟨3081135019016678792891759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 131461760811378295163381717 3081135019016678792891759)
                      ·
                        rfl

theorem cell23_6000489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_6000489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000489 prefixEnd_6000489 := by exact prefixLift 6000489
  have htrace : WordTrace (prefixWord ++ tailWord_6000489) baseStart_6000489 baseEnd_6000489 := by
    simpa [prefixWord, tailWord_6000489, baseEnd_6000489] using wordTrace_append hprefix tailTrace_6000489
  have hstable : (prefixWord ++ tailWord_6000489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000489).length < 2 ^ (prefixWord ++ tailWord_6000489).sum := by decide
  have hdescent : baseEnd_6000489 < baseStart_6000489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000553 : List Nat := [1, 2, 1, 1, 1, 1, 4, 6, 1, 2, 3]
def baseStart_6000553 : Nat := 118140960795 + 6000553 * 2 ^ 59
def prefixEnd_6000553 : Nat := 4983230072969 + 3 ^ 40 * 6000553 * 2
def baseEnd_6000553 : Nat := 3081167881778566542491465

theorem tailTrace_6000553 : CollatzResearch.WordTrace tailWord_6000553 prefixEnd_6000553 3081167881778566542491465 := by
  unfold tailWord_6000553
  simp only [CollatzResearch.WordTrace]
  refine ⟨218858147830028768707990313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145905431886685845805326875 218858147830028768707990313)
  ·
    refine ⟨164143610872521576530992735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218858147830028768707990313 164143610872521576530992735)
    ·
      refine ⟨246215416308782364796489103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164143610872521576530992735 246215416308782364796489103)
      ·
        refine ⟨369323124463173547194733655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246215416308782364796489103 369323124463173547194733655)
        ·
          refine ⟨553984686694760320792100483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369323124463173547194733655 553984686694760320792100483)
          ·
            refine ⟨830977030042140481188150725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553984686694760320792100483 830977030042140481188150725)
            ·
              refine ⟨155808193132901340222778261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 830977030042140481188150725 155808193132901340222778261)
              ·
                refine ⟨7303509053104750322942731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 155808193132901340222778261 7303509053104750322942731)
                ·
                  refine ⟨10955263579657125484414097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7303509053104750322942731 10955263579657125484414097)
                  ·
                    refine ⟨8216447684742844113310573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10955263579657125484414097 8216447684742844113310573)
                    ·
                      refine ⟨3081167881778566542491465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8216447684742844113310573 3081167881778566542491465)
                      ·
                        rfl

theorem cell23_6000553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 2, 3].length) (baseStart_6000553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000553 prefixEnd_6000553 := by exact prefixLift 6000553
  have htrace : WordTrace (prefixWord ++ tailWord_6000553) baseStart_6000553 baseEnd_6000553 := by
    simpa [prefixWord, tailWord_6000553, baseEnd_6000553] using wordTrace_append hprefix tailTrace_6000553
  have hstable : (prefixWord ++ tailWord_6000553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000553).length < 2 ^ (prefixWord ++ tailWord_6000553).sum := by decide
  have hdescent : baseEnd_6000553 < baseStart_6000553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000564 : List Nat := [2, 5, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_6000564 : Nat := 118140960795 + 6000564 * 2 ^ 59
def prefixEnd_6000564 : Nat := 4983230072969 + 3 ^ 40 * 6000564 * 2
def baseEnd_6000564 : Nat := 1027057843355255333151305

theorem tailTrace_6000564 : CollatzResearch.WordTrace tailWord_6000564 prefixEnd_6000564 1027057843355255333151305 := by
  unfold tailWord_6000564
  simp only [CollatzResearch.WordTrace]
  refine ⟨109429274516494458793320373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145905699355325945057760497 109429274516494458793320373)
  ·
    refine ⟨10258994485921355511873785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109429274516494458793320373 10258994485921355511873785)
    ·
      refine ⟨7694245864441016633905339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10258994485921355511873785 7694245864441016633905339)
      ·
        refine ⟨11541368796661524950858009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7694245864441016633905339 11541368796661524950858009)
        ·
          refine ⟨8656026597496143713143507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11541368796661524950858009 8656026597496143713143507)
          ·
            refine ⟨12984039896244215569715261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8656026597496143713143507 12984039896244215569715261)
            ·
              refine ⟨4869014961091580838643223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12984039896244215569715261 4869014961091580838643223)
              ·
                refine ⟨7303522441637371257964835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4869014961091580838643223 7303522441637371257964835)
                ·
                  refine ⟨10955283662456056886947253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7303522441637371257964835 10955283662456056886947253)
                  ·
                    refine ⟨1027057843355255333151305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10955283662456056886947253 1027057843355255333151305)
                    ·
                      rfl

theorem cell23_6000564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_6000564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000564 prefixEnd_6000564 := by exact prefixLift 6000564
  have htrace : WordTrace (prefixWord ++ tailWord_6000564) baseStart_6000564 baseEnd_6000564 := by
    simpa [prefixWord, tailWord_6000564, baseEnd_6000564] using wordTrace_append hprefix tailTrace_6000564
  have hstable : (prefixWord ++ tailWord_6000564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000564).length < 2 ^ (prefixWord ++ tailWord_6000564).sum := by decide
  have hdescent : baseEnd_6000564 < baseStart_6000564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000567 : List Nat := [1, 1, 3, 1, 3, 1, 1, 7, 1, 2, 2]
def baseStart_6000567 : Nat := 118140960795 + 6000567 * 2 ^ 59
def prefixEnd_6000567 : Nat := 4983230072969 + 3 ^ 40 * 6000567 * 2
def baseEnd_6000567 : Nat := 3081175070507729487716401

theorem tailTrace_6000567 : CollatzResearch.WordTrace tailWord_6000567 prefixEnd_6000567 3081175070507729487716401 := by
  unfold tailWord_6000567
  simp only [CollatzResearch.WordTrace]
  refine ⟨218858658451978049098999955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145905772301318699399333303 218858658451978049098999955)
  ·
    refine ⟨328287987677967073648499933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218858658451978049098999955 328287987677967073648499933)
    ·
      refine ⟨123107995379237652618187475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328287987677967073648499933 123107995379237652618187475)
      ·
        refine ⟨184661993068856478927281213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123107995379237652618187475 184661993068856478927281213)
        ·
          refine ⟨69248247400821179597730455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184661993068856478927281213 69248247400821179597730455)
          ·
            refine ⟨103872371101231769396595683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69248247400821179597730455 103872371101231769396595683)
            ·
              refine ⟨155808556651847654094893525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103872371101231769396595683 155808556651847654094893525)
              ·
                refine ⟨3651763046527679392849067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 155808556651847654094893525 3651763046527679392849067)
                ·
                  refine ⟨5477644569791519089273601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3651763046527679392849067 5477644569791519089273601)
                  ·
                    refine ⟨4108233427343639316955201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5477644569791519089273601 4108233427343639316955201)
                    ·
                      refine ⟨3081175070507729487716401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4108233427343639316955201 3081175070507729487716401)
                      ·
                        rfl

theorem cell23_6000567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 1, 2, 2].length) (baseStart_6000567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000567 prefixEnd_6000567 := by exact prefixLift 6000567
  have htrace : WordTrace (prefixWord ++ tailWord_6000567) baseStart_6000567 baseEnd_6000567 := by
    simpa [prefixWord, tailWord_6000567, baseEnd_6000567] using wordTrace_append hprefix tailTrace_6000567
  have hstable : (prefixWord ++ tailWord_6000567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000567).length < 2 ^ (prefixWord ++ tailWord_6000567).sum := by decide
  have hdescent : baseEnd_6000567 < baseStart_6000567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000584 : List Nat := [2, 1, 3, 1, 4, 2, 1, 4, 1, 2, 2]
def baseStart_6000584 : Nat := 118140960795 + 6000584 * 2 ^ 59
def prefixEnd_6000584 : Nat := 4983230072969 + 3 ^ 40 * 6000584 * 2
def baseEnd_6000584 : Nat := 3081183799678855921203823

theorem tailTrace_6000584 : CollatzResearch.WordTrace tailWord_6000584 prefixEnd_6000584 3081183799678855921203823 := by
  unfold tailWord_6000584
  simp only [CollatzResearch.WordTrace]
  refine ⟨109429639246458230501184403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145906185661944307334912537 109429639246458230501184403)
  ·
    refine ⟨164144458869687345751776605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109429639246458230501184403 164144458869687345751776605)
    ·
      refine ⟨61554172076132754656916227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164144458869687345751776605 61554172076132754656916227)
      ·
        refine ⟨92331258114199131985374341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61554172076132754656916227 92331258114199131985374341)
        ·
          refine ⟨17312110896412337247257689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92331258114199131985374341 17312110896412337247257689)
          ·
            refine ⟨12984083172309252935443267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17312110896412337247257689 12984083172309252935443267)
            ·
              refine ⟨19476124758463879403164901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12984083172309252935443267 19476124758463879403164901)
              ·
                refine ⟨3651773392211977388093419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19476124758463879403164901 3651773392211977388093419)
                ·
                  refine ⟨5477660088317966082140129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3651773392211977388093419 5477660088317966082140129)
                  ·
                    refine ⟨4108245066238474561605097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5477660088317966082140129 4108245066238474561605097)
                    ·
                      refine ⟨3081183799678855921203823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4108245066238474561605097 3081183799678855921203823)
                      ·
                        rfl

theorem cell23_6000584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 1, 2, 2].length) (baseStart_6000584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000584 prefixEnd_6000584 := by exact prefixLift 6000584
  have htrace : WordTrace (prefixWord ++ tailWord_6000584) baseStart_6000584 baseEnd_6000584 := by
    simpa [prefixWord, tailWord_6000584, baseEnd_6000584] using wordTrace_append hprefix tailTrace_6000584
  have hstable : (prefixWord ++ tailWord_6000584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000584).length < 2 ^ (prefixWord ++ tailWord_6000584).sum := by decide
  have hdescent : baseEnd_6000584 < baseStart_6000584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000586 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 2, 7]
def baseStart_6000586 : Nat := 118140960795 + 6000586 * 2 ^ 59
def prefixEnd_6000586 : Nat := 4983230072969 + 3 ^ 40 * 6000586 * 2
def baseEnd_6000586 : Nat := 1027061608880054971126271

theorem tailTrace_6000586 : CollatzResearch.WordTrace tailWord_6000586 prefixEnd_6000586 1027061608880054971126271 := by
  unfold tailWord_6000586
  simp only [CollatzResearch.WordTrace]
  refine ⟨54714837859727303835985403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145906234292606143562627741 54714837859727303835985403)
  ·
    refine ⟨82072256789590955753978105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54714837859727303835985403 82072256789590955753978105)
    ·
      refine ⟨61554192592193216815483579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82072256789590955753978105 61554192592193216815483579)
      ·
        refine ⟨92331288888289825223225369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61554192592193216815483579 92331288888289825223225369)
        ·
          refine ⟨69248466666217368917419027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92331288888289825223225369 69248466666217368917419027)
          ·
            refine ⟨103872699999326053376128541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69248466666217368917419027 103872699999326053376128541)
            ·
              refine ⟨38952262499747270016048203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103872699999326053376128541 38952262499747270016048203)
              ·
                refine ⟨58428393749620905024072305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38952262499747270016048203 58428393749620905024072305)
                ·
                  refine ⟨43821295312215678768054229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58428393749620905024072305 43821295312215678768054229)
                  ·
                    refine ⟨1027061608880054971126271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43821295312215678768054229 1027061608880054971126271)
                    ·
                      rfl

theorem cell23_6000586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_6000586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000586 prefixEnd_6000586 := by exact prefixLift 6000586
  have htrace : WordTrace (prefixWord ++ tailWord_6000586) baseStart_6000586 baseEnd_6000586 := by
    simpa [prefixWord, tailWord_6000586, baseEnd_6000586] using wordTrace_append hprefix tailTrace_6000586
  have hstable : (prefixWord ++ tailWord_6000586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000586).length < 2 ^ (prefixWord ++ tailWord_6000586).sum := by decide
  have hdescent : baseEnd_6000586 < baseStart_6000586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000600 : List Nat := [2, 1, 2, 2, 2, 2, 1, 5, 2, 1, 3]
def baseStart_6000600 : Nat := 118140960795 + 6000600 * 2 ^ 59
def prefixEnd_6000600 : Nat := 4983230072969 + 3 ^ 40 * 6000600 * 2
def baseEnd_6000600 : Nat := 3081192015369327858603749

theorem tailTrace_6000600 : CollatzResearch.WordTrace tailWord_6000600 prefixEnd_6000600 3081192015369327858603749 := by
  unfold tailWord_6000600
  simp only [CollatzResearch.WordTrace]
  refine ⟨109429931030429247867475627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145906574707238997156634169 109429931030429247867475627)
  ·
    refine ⟨164144896545643871801213441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109429931030429247867475627 164144896545643871801213441)
    ·
      refine ⟨123108672409232903850910081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164144896545643871801213441 123108672409232903850910081)
      ·
        refine ⟨92331504306924677888182561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123108672409232903850910081 92331504306924677888182561)
        ·
          refine ⟨69248628230193508416136921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92331504306924677888182561 69248628230193508416136921)
          ·
            refine ⟨51936471172645131312102691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69248628230193508416136921 51936471172645131312102691)
            ·
              refine ⟨77904706758967696968154037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51936471172645131312102691 77904706758967696968154037)
              ·
                refine ⟨7303566258653221590764441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77904706758967696968154037 7303566258653221590764441)
                ·
                  refine ⟨5477674693989916193073331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7303566258653221590764441 5477674693989916193073331)
                  ·
                    refine ⟨8216512040984874289609997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5477674693989916193073331 8216512040984874289609997)
                    ·
                      refine ⟨3081192015369327858603749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8216512040984874289609997 3081192015369327858603749)
                      ·
                        rfl

theorem cell23_6000600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_6000600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000600 prefixEnd_6000600 := by exact prefixLift 6000600
  have htrace : WordTrace (prefixWord ++ tailWord_6000600) baseStart_6000600 baseEnd_6000600 := by
    simpa [prefixWord, tailWord_6000600, baseEnd_6000600] using wordTrace_append hprefix tailTrace_6000600
  have hstable : (prefixWord ++ tailWord_6000600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000600).length < 2 ^ (prefixWord ++ tailWord_6000600).sum := by decide
  have hdescent : baseEnd_6000600 < baseStart_6000600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000616 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 3, 8]
def baseStart_6000616 : Nat := 118140960795 + 6000616 * 2 ^ 59
def prefixEnd_6000616 : Nat := 4983230072969 + 3 ^ 40 * 6000616 * 2
def baseEnd_6000616 : Nat := 1027066743686599932001225

theorem tailTrace_6000616 : CollatzResearch.WordTrace tailWord_6000616 prefixEnd_6000616 1027066743686599932001225 := by
  unfold tailWord_6000616
  simp only [CollatzResearch.WordTrace]
  refine ⟨109430222814400265233766851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145906963752533686978355801 109430222814400265233766851)
  ·
    refine ⟨164145334221600397850650277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109430222814400265233766851 164145334221600397850650277)
    ·
      refine ⟨30777250166550074596996927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164145334221600397850650277 30777250166550074596996927)
      ·
        refine ⟨46165875249825111895495391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30777250166550074596996927 46165875249825111895495391)
        ·
          refine ⟨69248812874737667843243087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46165875249825111895495391 69248812874737667843243087)
          ·
            refine ⟨103873219312106501764864631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69248812874737667843243087 103873219312106501764864631)
            ·
              refine ⟨155809828968159752647296947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103873219312106501764864631 155809828968159752647296947)
              ·
                refine ⟨233714743452239628970945421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155809828968159752647296947 233714743452239628970945421)
                ·
                  refine ⟨87643028794589860864104533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233714743452239628970945421 87643028794589860864104533)
                  ·
                    refine ⟨1027066743686599932001225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87643028794589860864104533 1027066743686599932001225)
                    ·
                      rfl

theorem cell23_6000616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_6000616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000616 prefixEnd_6000616 := by exact prefixLift 6000616
  have htrace : WordTrace (prefixWord ++ tailWord_6000616) baseStart_6000616 baseEnd_6000616 := by
    simpa [prefixWord, tailWord_6000616, baseEnd_6000616] using wordTrace_append hprefix tailTrace_6000616
  have hstable : (prefixWord ++ tailWord_6000616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000616).length < 2 ^ (prefixWord ++ tailWord_6000616).sum := by decide
  have hdescent : baseEnd_6000616 < baseStart_6000616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000621 : List Nat := [1, 5, 1, 4, 1, 2, 2, 1, 1, 2, 3]
def baseStart_6000621 : Nat := 118140960795 + 6000621 * 2 ^ 59
def prefixEnd_6000621 : Nat := 4983230072969 + 3 ^ 40 * 6000621 * 2
def baseEnd_6000621 : Nat := 3081202798463072276441153

theorem tailTrace_6000621 : CollatzResearch.WordTrace tailWord_6000621 prefixEnd_6000621 3081202798463072276441153 := by
  unfold tailWord_6000621
  simp only [CollatzResearch.WordTrace]
  refine ⟨218860627993782416321465717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145907085329188277547643811 218860627993782416321465717)
  ·
    refine ⟨20518183874417101530137411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218860627993782416321465717 20518183874417101530137411)
    ·
      refine ⟨30777275811625652295206117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20518183874417101530137411 30777275811625652295206117)
      ·
        refine ⟨5770739214679809805351147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30777275811625652295206117 5770739214679809805351147)
        ·
          refine ⟨8656108822019714708026721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5770739214679809805351147 8656108822019714708026721)
          ·
            refine ⟨6492081616514786031020041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8656108822019714708026721 6492081616514786031020041)
            ·
              refine ⟨4869061212386089523265031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6492081616514786031020041 4869061212386089523265031)
              ·
                refine ⟨7303591818579134284897547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4869061212386089523265031 7303591818579134284897547)
                ·
                  refine ⟨10955387727868701427346321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7303591818579134284897547 10955387727868701427346321)
                  ·
                    refine ⟨8216540795901526070509741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10955387727868701427346321 8216540795901526070509741)
                    ·
                      refine ⟨3081202798463072276441153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8216540795901526070509741 3081202798463072276441153)
                      ·
                        rfl

theorem cell23_6000621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_6000621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000621 prefixEnd_6000621 := by exact prefixLift 6000621
  have htrace : WordTrace (prefixWord ++ tailWord_6000621) baseStart_6000621 baseEnd_6000621 := by
    simpa [prefixWord, tailWord_6000621, baseEnd_6000621] using wordTrace_append hprefix tailTrace_6000621
  have hstable : (prefixWord ++ tailWord_6000621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000621).length < 2 ^ (prefixWord ++ tailWord_6000621).sum := by decide
  have hdescent : baseEnd_6000621 < baseStart_6000621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000693 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 4, 5]
def baseStart_6000693 : Nat := 118140960795 + 6000693 * 2 ^ 59
def prefixEnd_6000693 : Nat := 4983230072969 + 3 ^ 40 * 6000693 * 2
def baseEnd_6000693 : Nat := 1027079923023398664913607

theorem tailTrace_6000693 : CollatzResearch.WordTrace tailWord_6000693 prefixEnd_6000693 1027079923023398664913607 := by
  unfold tailWord_6000693
  simp only [CollatzResearch.WordTrace]
  refine ⟨218863254049521572618086733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145908836033014381745391155 218863254049521572618086733)
  ·
    refine ⟨82073720268570589731782525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218863254049521572618086733 82073720268570589731782525)
    ·
      refine ⟨30777645100713971149418447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82073720268570589731782525 30777645100713971149418447)
      ·
        refine ⟨46166467651070956724127671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30777645100713971149418447 46166467651070956724127671)
        ·
          refine ⟨69249701476606435086191507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46166467651070956724127671 69249701476606435086191507)
          ·
            refine ⟨103874552214909652629287261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69249701476606435086191507 103874552214909652629287261)
            ·
              refine ⟨38952957080591119735982723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103874552214909652629287261 38952957080591119735982723)
              ·
                refine ⟨58429435620886679603974085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38952957080591119735982723 58429435620886679603974085)
                ·
                  refine ⟨10955519178916252425745141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58429435620886679603974085 10955519178916252425745141)
                  ·
                    refine ⟨1027079923023398664913607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10955519178916252425745141 1027079923023398664913607)
                    ·
                      rfl

theorem cell23_6000693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_6000693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000693 prefixEnd_6000693 := by exact prefixLift 6000693
  have htrace : WordTrace (prefixWord ++ tailWord_6000693) baseStart_6000693 baseEnd_6000693 := by
    simpa [prefixWord, tailWord_6000693, baseEnd_6000693] using wordTrace_append hprefix tailTrace_6000693
  have hstable : (prefixWord ++ tailWord_6000693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000693).length < 2 ^ (prefixWord ++ tailWord_6000693).sum := by decide
  have hdescent : baseEnd_6000693 < baseStart_6000693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000697 : List Nat := [1, 2, 1, 5, 4, 1, 1, 1, 7]
def baseStart_6000697 : Nat := 118140960795 + 6000697 * 2 ^ 59
def prefixEnd_6000697 : Nat := 4983230072969 + 3 ^ 40 * 6000697 * 2
def baseEnd_6000697 : Nat := 342360202554757108787867

theorem tailTrace_6000697 : CollatzResearch.WordTrace tailWord_6000697 prefixEnd_6000697 342360202554757108787867 := by
  unfold tailWord_6000697
  simp only [CollatzResearch.WordTrace]
  refine ⟨218863399941507081301232345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145908933294338054200821563 218863399941507081301232345)
  ·
    refine ⟨164147549956130310975924259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218863399941507081301232345 164147549956130310975924259)
    ·
      refine ⟨246221324934195466463886389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164147549956130310975924259 246221324934195466463886389)
      ·
        refine ⟨23083249212580824980989349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 246221324934195466463886389 23083249212580824980989349)
        ·
          refine ⟨4328109227358904683935503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23083249212580824980989349 4328109227358904683935503)
          ·
            refine ⟨6492163841038357025903255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4328109227358904683935503 6492163841038357025903255)
            ·
              refine ⟨9738245761557535538854883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6492163841038357025903255 9738245761557535538854883)
              ·
                refine ⟨14607368642336303308282325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9738245761557535538854883 14607368642336303308282325)
                ·
                  refine ⟨342360202554757108787867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14607368642336303308282325 342360202554757108787867)
                  ·
                    rfl

theorem cell23_6000697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 7].length) (baseStart_6000697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000697 prefixEnd_6000697 := by exact prefixLift 6000697
  have htrace : WordTrace (prefixWord ++ tailWord_6000697) baseStart_6000697 baseEnd_6000697 := by
    simpa [prefixWord, tailWord_6000697, baseEnd_6000697] using wordTrace_append hprefix tailTrace_6000697
  have hstable : (prefixWord ++ tailWord_6000697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000697).length < 2 ^ (prefixWord ++ tailWord_6000697).sum := by decide
  have hdescent : baseEnd_6000697 < baseStart_6000697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000700 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 2, 5, 2]
def baseStart_6000700 : Nat := 118140960795 + 6000700 * 2 ^ 59
def prefixEnd_6000700 : Nat := 4983230072969 + 3 ^ 40 * 6000700 * 2
def baseEnd_6000700 : Nat := 3081243363434777467353289

theorem tailTrace_6000700 : CollatzResearch.WordTrace tailWord_6000700 prefixEnd_6000700 3081243363434777467353289 := by
  unfold tailWord_6000700
  simp only [CollatzResearch.WordTrace]
  refine ⟨109431754680248106406795777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145909006240330808542394369 109431754680248106406795777)
  ·
    refine ⟨82073816010186079805096833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109431754680248106406795777 82073816010186079805096833)
    ·
      refine ⟨61555362007639559853822625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82073816010186079805096833 61555362007639559853822625)
      ·
        refine ⟨46166521505729669890366969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61555362007639559853822625 46166521505729669890366969)
        ·
          refine ⟨34624891129297252417775227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46166521505729669890366969 34624891129297252417775227)
          ·
            refine ⟨51937336693945878626662841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34624891129297252417775227 51937336693945878626662841)
            ·
              refine ⟨38953002520459408969997131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51937336693945878626662841 38953002520459408969997131)
              ·
                refine ⟨58429503780689113454995697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38953002520459408969997131 58429503780689113454995697)
                ·
                  refine ⟨43822127835516835091246773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58429503780689113454995697 43822127835516835091246773)
                  ·
                    refine ⟨4108324484579703289804385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43822127835516835091246773 4108324484579703289804385)
                    ·
                      refine ⟨3081243363434777467353289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4108324484579703289804385 3081243363434777467353289)
                      ·
                        rfl

theorem cell23_6000700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_6000700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000700 prefixEnd_6000700 := by exact prefixLift 6000700
  have htrace : WordTrace (prefixWord ++ tailWord_6000700) baseStart_6000700 baseEnd_6000700 := by
    simpa [prefixWord, tailWord_6000700, baseEnd_6000700] using wordTrace_append hprefix tailTrace_6000700
  have hstable : (prefixWord ++ tailWord_6000700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000700).length < 2 ^ (prefixWord ++ tailWord_6000700).sum := by decide
  have hdescent : baseEnd_6000700 < baseStart_6000700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000713 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 4, 1, 4]
def baseStart_6000713 : Nat := 118140960795 + 6000713 * 2 ^ 59
def prefixEnd_6000713 : Nat := 4983230072969 + 3 ^ 40 * 6000713 * 2
def baseEnd_6000713 : Nat := 3081250038683285916490729

theorem tailTrace_6000713 : CollatzResearch.WordTrace tailWord_6000713 prefixEnd_6000713 3081250038683285916490729 := by
  unfold tailWord_6000713
  simp only [CollatzResearch.WordTrace]
  refine ⟨218863983509449116033814793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145909322339632744022543195 218863983509449116033814793)
  ·
    refine ⟨164147987632086837025361095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218863983509449116033814793 164147987632086837025361095)
    ·
      refine ⟨246221981448130255538041643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164147987632086837025361095 246221981448130255538041643)
      ·
        refine ⟨369332972172195383307062465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246221981448130255538041643 369332972172195383307062465)
        ·
          refine ⟨276999729129146537480296849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369332972172195383307062465 276999729129146537480296849)
          ·
            refine ⟨207749796846859903110222637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276999729129146537480296849 207749796846859903110222637)
            ·
              refine ⟨77906173817572463666333489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207749796846859903110222637 77906173817572463666333489)
              ·
                refine ⟨58429630363179347749750117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77906173817572463666333489 58429630363179347749750117)
                ·
                  refine ⟨10955555693096127703078147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58429630363179347749750117 10955555693096127703078147)
                  ·
                    refine ⟨16433333539644191554617221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10955555693096127703078147 16433333539644191554617221)
                    ·
                      refine ⟨3081250038683285916490729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16433333539644191554617221 3081250038683285916490729)
                      ·
                        rfl

theorem cell23_6000713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 1, 4].length) (baseStart_6000713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000713 prefixEnd_6000713 := by exact prefixLift 6000713
  have htrace : WordTrace (prefixWord ++ tailWord_6000713) baseStart_6000713 baseEnd_6000713 := by
    simpa [prefixWord, tailWord_6000713, baseEnd_6000713] using wordTrace_append hprefix tailTrace_6000713
  have hstable : (prefixWord ++ tailWord_6000713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000713).length < 2 ^ (prefixWord ++ tailWord_6000713).sum := by decide
  have hdescent : baseEnd_6000713 < baseStart_6000713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000730 : List Nat := [3, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4]
def baseStart_6000730 : Nat := 118140960795 + 6000730 * 2 ^ 59
def prefixEnd_6000730 : Nat := 4983230072969 + 3 ^ 40 * 6000730 * 2
def baseEnd_6000730 : Nat := 3081258767854412349978151

theorem tailTrace_6000730 : CollatzResearch.WordTrace tailWord_6000730 prefixEnd_6000730 3081258767854412349978151 := by
  unfold tailWord_6000730
  simp only [CollatzResearch.WordTrace]
  refine ⟨54716150887596881984295911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145909735700258351958122429 54716150887596881984295911)
  ·
    refine ⟨82074226331395322976443867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54716150887596881984295911 82074226331395322976443867)
    ·
      refine ⟨123111339497092984464665801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82074226331395322976443867 123111339497092984464665801)
      ·
        refine ⟨92333504622819738348499351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123111339497092984464665801 92333504622819738348499351)
        ·
          refine ⟨138500256934229607522749027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92333504622819738348499351 138500256934229607522749027)
          ·
            refine ⟨207750385401344411284123541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138500256934229607522749027 207750385401344411284123541)
            ·
              refine ⟨9738299315688019278943291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 207750385401344411284123541 9738299315688019278943291)
              ·
                refine ⟨14607448973532028918414937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9738299315688019278943291 14607448973532028918414937)
                ·
                  refine ⟨10955586730149021688811203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14607448973532028918414937 10955586730149021688811203)
                  ·
                    refine ⟨16433380095223532533216805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10955586730149021688811203 16433380095223532533216805)
                    ·
                      refine ⟨3081258767854412349978151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16433380095223532533216805 3081258767854412349978151)
                      ·
                        rfl

theorem cell23_6000730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_6000730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000730 prefixEnd_6000730 := by exact prefixLift 6000730
  have htrace : WordTrace (prefixWord ++ tailWord_6000730) baseStart_6000730 baseEnd_6000730 := by
    simpa [prefixWord, tailWord_6000730, baseEnd_6000730] using wordTrace_append hprefix tailTrace_6000730
  have hstable : (prefixWord ++ tailWord_6000730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000730).length < 2 ^ (prefixWord ++ tailWord_6000730).sum := by decide
  have hdescent : baseEnd_6000730 < baseStart_6000730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000743 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_6000743 : Nat := 118140960795 + 6000743 * 2 ^ 59
def prefixEnd_6000743 : Nat := 4983230072969 + 3 ^ 40 * 6000743 * 2
def baseEnd_6000743 : Nat := 3081265443102920799115591

theorem tailTrace_6000743 : CollatzResearch.WordTrace tailWord_6000743 prefixEnd_6000743 3081265443102920799115591 := by
  unfold tailWord_6000743
  simp only [CollatzResearch.WordTrace]
  refine ⟨218865077699340431157406883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145910051799560287438271255 218865077699340431157406883)
  ·
    refine ⟨328297616549010646736110325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218865077699340431157406883 328297616549010646736110325)
    ·
      refine ⟨30777901551469748131510343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 328297616549010646736110325 30777901551469748131510343)
      ·
        refine ⟨46166852327204622197265515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30777901551469748131510343 46166852327204622197265515)
        ·
          refine ⟨69250278490806933295898273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46166852327204622197265515 69250278490806933295898273)
          ·
            refine ⟨51937708868105199971923705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69250278490806933295898273 51937708868105199971923705)
            ·
              refine ⟨38953281651078899978942779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51937708868105199971923705 38953281651078899978942779)
              ·
                refine ⟨58429922476618349968414169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38953281651078899978942779 58429922476618349968414169)
                ·
                  refine ⟨43822441857463762476310627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58429922476618349968414169 43822441857463762476310627)
                  ·
                    refine ⟨65733662786195643714465941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43822441857463762476310627 65733662786195643714465941)
                    ·
                      refine ⟨3081265443102920799115591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65733662786195643714465941 3081265443102920799115591)
                      ·
                        rfl

theorem cell23_6000743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_6000743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000743 prefixEnd_6000743 := by exact prefixLift 6000743
  have htrace : WordTrace (prefixWord ++ tailWord_6000743) baseStart_6000743 baseEnd_6000743 := by
    simpa [prefixWord, tailWord_6000743, baseEnd_6000743] using wordTrace_append hprefix tailTrace_6000743
  have hstable : (prefixWord ++ tailWord_6000743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000743).length < 2 ^ (prefixWord ++ tailWord_6000743).sum := by decide
  have hdescent : baseEnd_6000743 < baseStart_6000743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000763 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 3]
def baseStart_6000763 : Nat := 118140960795 + 6000763 * 2 ^ 59
def prefixEnd_6000763 : Nat := 4983230072969 + 3 ^ 40 * 6000763 * 2
def baseEnd_6000763 : Nat := 3081275712716010720865499

theorem tailTrace_6000763 : CollatzResearch.WordTrace tailWord_6000763 prefixEnd_6000763 3081275712716010720865499 := by
  unfold tailWord_6000763
  simp only [CollatzResearch.WordTrace]
  refine ⟨218865807159267974573134943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145910538106178649715423295 218865807159267974573134943)
  ·
    refine ⟨328298710738901961859702415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218865807159267974573134943 328298710738901961859702415)
    ·
      refine ⟨492448066108352942789553623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328298710738901961859702415 492448066108352942789553623)
      ·
        refine ⟨738672099162529414184330435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492448066108352942789553623 738672099162529414184330435)
        ·
          refine ⟨1108008148743794121276495653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738672099162529414184330435 1108008148743794121276495653)
          ·
            refine ⟨207751527889461397739342935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1108008148743794121276495653 207751527889461397739342935)
            ·
              refine ⟨311627291834192096609014403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207751527889461397739342935 311627291834192096609014403)
              ·
                refine ⟨467440937751288144913521605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311627291834192096609014403 467440937751288144913521605)
                ·
                  refine ⟨87645175828366527171285301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 467440937751288144913521605 87645175828366527171285301)
                  ·
                    refine ⟨8216735233909361922307997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87645175828366527171285301 8216735233909361922307997)
                    ·
                      refine ⟨3081275712716010720865499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8216735233909361922307997 3081275712716010720865499)
                      ·
                        rfl

theorem cell23_6000763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 3].length) (baseStart_6000763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000763 prefixEnd_6000763 := by exact prefixLift 6000763
  have htrace : WordTrace (prefixWord ++ tailWord_6000763) baseStart_6000763 baseEnd_6000763 := by
    simpa [prefixWord, tailWord_6000763, baseEnd_6000763] using wordTrace_append hprefix tailTrace_6000763
  have hstable : (prefixWord ++ tailWord_6000763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000763).length < 2 ^ (prefixWord ++ tailWord_6000763).sum := by decide
  have hdescent : baseEnd_6000763 < baseStart_6000763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000804 : List Nat := [2, 3, 1, 2, 5, 1, 1, 2, 6]
def baseStart_6000804 : Nat := 118140960795 + 6000804 * 2 ^ 59
def prefixEnd_6000804 : Nat := 4983230072969 + 3 ^ 40 * 6000804 * 2
def baseEnd_6000804 : Nat := 342366307269205006716979

theorem tailTrace_6000804 : CollatzResearch.WordTrace tailWord_6000804 prefixEnd_6000804 342366307269205006716979 := by
  unfold tailWord_6000804
  simp only [CollatzResearch.WordTrace]
  refine ⟨109433651276059719287688733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145911535034746292383584977 109433651276059719287688733)
  ·
    refine ⟨41037619228522394732883275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109433651276059719287688733 41037619228522394732883275)
    ·
      refine ⟨61556428842783592099324913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41037619228522394732883275 61556428842783592099324913)
      ·
        refine ⟨46167321632087694074493685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61556428842783592099324913 46167321632087694074493685)
        ·
          refine ⟨4328186403008221319483783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46167321632087694074493685 4328186403008221319483783)
          ·
            refine ⟨6492279604512331979225675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4328186403008221319483783 6492279604512331979225675)
            ·
              refine ⟨9738419406768497968838513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6492279604512331979225675 9738419406768497968838513)
              ·
                refine ⟨7303814555076373476628885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9738419406768497968838513 7303814555076373476628885)
                ·
                  refine ⟨342366307269205006716979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7303814555076373476628885 342366307269205006716979)
                  ·
                    rfl

theorem cell23_6000804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_6000804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000804 prefixEnd_6000804 := by exact prefixLift 6000804
  have htrace : WordTrace (prefixWord ++ tailWord_6000804) baseStart_6000804 baseEnd_6000804 := by
    simpa [prefixWord, tailWord_6000804, baseEnd_6000804] using wordTrace_append hprefix tailTrace_6000804
  have hstable : (prefixWord ++ tailWord_6000804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000804).length < 2 ^ (prefixWord ++ tailWord_6000804).sum := by decide
  have hdescent : baseEnd_6000804 < baseStart_6000804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000843 : List Nat := [1, 1, 1, 1, 3, 2, 5, 9]
def baseStart_6000843 : Nat := 118140960795 + 6000843 * 2 ^ 59
def prefixEnd_6000843 : Nat := 4983230072969 + 3 ^ 40 * 6000843 * 2
def baseEnd_6000843 : Nat := 114122844117347052143153

theorem tailTrace_6000843 : CollatzResearch.WordTrace tailWord_6000843 prefixEnd_6000843 114122844117347052143153 := by
  unfold tailWord_6000843
  simp only [CollatzResearch.WordTrace]
  refine ⟨218868724998978148236047183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145912483332652098824031455 218868724998978148236047183)
  ·
    refine ⟨328303087498467222354070775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218868724998978148236047183 328303087498467222354070775)
    ·
      refine ⟨492454631247700833531106163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328303087498467222354070775 492454631247700833531106163)
      ·
        refine ⟨738681946871551250296659245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492454631247700833531106163 738681946871551250296659245)
        ·
          refine ⟨277005730076831718861247217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 738681946871551250296659245 277005730076831718861247217)
          ·
            refine ⟨207754297557623789145935413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277005730076831718861247217 207754297557623789145935413)
            ·
              refine ⟨19476965396027230232431445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 207754297557623789145935413 19476965396027230232431445)
              ·
                refine ⟨114122844117347052143153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19476965396027230232431445 114122844117347052143153)
                ·
                  rfl

theorem cell23_6000843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 9].length) (baseStart_6000843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000843 prefixEnd_6000843 := by exact prefixLift 6000843
  have htrace : WordTrace (prefixWord ++ tailWord_6000843) baseStart_6000843 baseEnd_6000843 := by
    simpa [prefixWord, tailWord_6000843, baseEnd_6000843] using wordTrace_append hprefix tailTrace_6000843
  have hstable : (prefixWord ++ tailWord_6000843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000843).length < 2 ^ (prefixWord ++ tailWord_6000843).sum := by decide
  have hdescent : baseEnd_6000843 < baseStart_6000843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000857 : List Nat := [1, 2, 1, 2, 3, 1, 4, 3, 1, 2, 3]
def baseStart_6000857 : Nat := 118140960795 + 6000857 * 2 ^ 59
def prefixEnd_6000857 : Nat := 4983230072969 + 3 ^ 40 * 6000857 * 2
def baseEnd_6000857 : Nat := 3081323979897533353090067

theorem tailTrace_6000857 : CollatzResearch.WordTrace tailWord_6000857 prefixEnd_6000857 3081323979897533353090067 := by
  unfold tailWord_6000857
  simp only [CollatzResearch.WordTrace]
  refine ⟨218869235620927428627056825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145912823747284952418037883 218869235620927428627056825)
  ·
    refine ⟨164151926715695571470292619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218869235620927428627056825 164151926715695571470292619)
    ·
      refine ⟨246227890073543357205438929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164151926715695571470292619 246227890073543357205438929)
      ·
        refine ⟨184670917555157517904079197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246227890073543357205438929 184670917555157517904079197)
        ·
          refine ⟨69251594083184069214029699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184670917555157517904079197 69251594083184069214029699)
          ·
            refine ⟨103877391124776103821044549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69251594083184069214029699 103877391124776103821044549)
            ·
              refine ⟨19477010835895519466445853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103877391124776103821044549 19477010835895519466445853)
              ·
                refine ⟨7303879063460819799917195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19477010835895519466445853 7303879063460819799917195)
                ·
                  refine ⟨10955818595191229699875793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7303879063460819799917195 10955818595191229699875793)
                  ·
                    refine ⟨8216863946393422274906845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10955818595191229699875793 8216863946393422274906845)
                    ·
                      refine ⟨3081323979897533353090067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8216863946393422274906845 3081323979897533353090067)
                      ·
                        rfl

theorem cell23_6000857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 2, 3].length) (baseStart_6000857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000857 prefixEnd_6000857 := by exact prefixLift 6000857
  have htrace : WordTrace (prefixWord ++ tailWord_6000857) baseStart_6000857 baseEnd_6000857 := by
    simpa [prefixWord, tailWord_6000857, baseEnd_6000857] using wordTrace_append hprefix tailTrace_6000857
  have hstable : (prefixWord ++ tailWord_6000857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000857).length < 2 ^ (prefixWord ++ tailWord_6000857).sum := by decide
  have hdescent : baseEnd_6000857 < baseStart_6000857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000871 : List Nat := [1, 1, 5, 3, 1, 1, 3, 1, 3, 2, 2]
def baseStart_6000871 : Nat := 118140960795 + 6000871 * 2 ^ 59
def prefixEnd_6000871 : Nat := 4983230072969 + 3 ^ 40 * 6000871 * 2
def baseEnd_6000871 : Nat := 3081331168626696298315003

theorem tailTrace_6000871 : CollatzResearch.WordTrace tailWord_6000871 prefixEnd_6000871 3081331168626696298315003 := by
  unfold tailWord_6000871
  simp only [CollatzResearch.WordTrace]
  refine ⟨218869746242876709018066467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145913164161917806012044311 218869746242876709018066467)
  ·
    refine ⟨328304619364315063527099701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218869746242876709018066467 328304619364315063527099701)
    ·
      refine ⟨30778558065404537205665597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 328304619364315063527099701 30778558065404537205665597)
      ·
        refine ⟨11541959274526701452124599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30778558065404537205665597 11541959274526701452124599)
        ·
          refine ⟨17312938911790052178186899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11541959274526701452124599 17312938911790052178186899)
          ·
            refine ⟨25969408367685078267280349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17312938911790052178186899 25969408367685078267280349)
            ·
              refine ⟨9738528137881904350230131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25969408367685078267280349 9738528137881904350230131)
              ·
                refine ⟨14607792206822856525345197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9738528137881904350230131 14607792206822856525345197)
                ·
                  refine ⟨5477922077558571197004449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14607792206822856525345197 5477922077558571197004449)
                  ·
                    refine ⟨4108441558168928397753337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5477922077558571197004449 4108441558168928397753337)
                    ·
                      refine ⟨3081331168626696298315003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4108441558168928397753337 3081331168626696298315003)
                      ·
                        rfl

theorem cell23_6000871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_6000871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000871 prefixEnd_6000871 := by exact prefixLift 6000871
  have htrace : WordTrace (prefixWord ++ tailWord_6000871) baseStart_6000871 baseEnd_6000871 := by
    simpa [prefixWord, tailWord_6000871, baseEnd_6000871] using wordTrace_append hprefix tailTrace_6000871
  have hstable : (prefixWord ++ tailWord_6000871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000871).length < 2 ^ (prefixWord ++ tailWord_6000871).sum := by decide
  have hdescent : baseEnd_6000871 < baseStart_6000871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000873 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 1, 9]
def baseStart_6000873 : Nat := 118140960795 + 6000873 * 2 ^ 59
def prefixEnd_6000873 : Nat := 4983230072969 + 3 ^ 40 * 6000873 * 2
def baseEnd_6000873 : Nat := 1027110731862668430163331

theorem tailTrace_6000873 : CollatzResearch.WordTrace tailWord_6000873 prefixEnd_6000873 1027110731862668430163331 := by
  unfold tailWord_6000873
  simp only [CollatzResearch.WordTrace]
  refine ⟨218869819188869463359639273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145913212792579642239759515 218869819188869463359639273)
  ·
    refine ⟨164152364391652097519729455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218869819188869463359639273 164152364391652097519729455)
    ·
      refine ⟨246228546587478146279594183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164152364391652097519729455 246228546587478146279594183)
      ·
        refine ⟨369342819881217219419391275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246228546587478146279594183 369342819881217219419391275)
        ·
          refine ⟨554014229821825829129086913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369342819881217219419391275 554014229821825829129086913)
          ·
            refine ⟨415510672366369371846815185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 554014229821825829129086913 415510672366369371846815185)
            ·
              refine ⟨311633004274777028885111389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415510672366369371846815185 311633004274777028885111389)
              ·
                refine ⟨116862376603041385831916771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311633004274777028885111389 116862376603041385831916771)
                ·
                  refine ⟨175293564904562078747875157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116862376603041385831916771 175293564904562078747875157)
                  ·
                    refine ⟨1027110731862668430163331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 175293564904562078747875157 1027110731862668430163331)
                    ·
                      rfl

theorem cell23_6000873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 9].length) (baseStart_6000873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000873 prefixEnd_6000873 := by exact prefixLift 6000873
  have htrace : WordTrace (prefixWord ++ tailWord_6000873) baseStart_6000873 baseEnd_6000873 := by
    simpa [prefixWord, tailWord_6000873, baseEnd_6000873] using wordTrace_append hprefix tailTrace_6000873
  have hstable : (prefixWord ++ tailWord_6000873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000873).length < 2 ^ (prefixWord ++ tailWord_6000873).sum := by decide
  have hdescent : baseEnd_6000873 < baseStart_6000873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000877 : List Nat := [1, 5, 1, 2, 3, 1, 2, 8]
def baseStart_6000877 : Nat := 118140960795 + 6000877 * 2 ^ 59
def prefixEnd_6000877 : Nat := 4983230072969 + 3 ^ 40 * 6000877 * 2
def baseEnd_6000877 : Nat := 114123490722615676845925

theorem tailTrace_6000877 : CollatzResearch.WordTrace tailWord_6000877 prefixEnd_6000877 114123490722615676845925 := by
  unfold tailWord_6000877
  simp only [CollatzResearch.WordTrace]
  refine ⟨218869965080854972042784885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145913310053903314695189923 218869965080854972042784885)
  ·
    refine ⟨20519059226330153629011083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218869965080854972042784885 20519059226330153629011083)
    ·
      refine ⟨30778588839495230443516625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20519059226330153629011083 30778588839495230443516625)
      ·
        refine ⟨23083941629621422832637469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30778588839495230443516625 23083941629621422832637469)
        ·
          refine ⟨8656478111108033562239051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23083941629621422832637469 8656478111108033562239051)
          ·
            refine ⟨12984717166662050343358577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8656478111108033562239051 12984717166662050343358577)
            ·
              refine ⟨9738537874996537757518933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12984717166662050343358577 9738537874996537757518933)
              ·
                refine ⟨114123490722615676845925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9738537874996537757518933 114123490722615676845925)
                ·
                  rfl

theorem cell23_6000877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 8].length) (baseStart_6000877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000877 prefixEnd_6000877 := by exact prefixLift 6000877
  have htrace : WordTrace (prefixWord ++ tailWord_6000877) baseStart_6000877 baseEnd_6000877 := by
    simpa [prefixWord, tailWord_6000877, baseEnd_6000877] using wordTrace_append hprefix tailTrace_6000877
  have hstable : (prefixWord ++ tailWord_6000877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000877).length < 2 ^ (prefixWord ++ tailWord_6000877).sum := by decide
  have hdescent : baseEnd_6000877 < baseStart_6000877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000920 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 2, 6]
def baseStart_6000920 : Nat := 118140960795 + 6000920 * 2 ^ 59
def prefixEnd_6000920 : Nat := 4983230072969 + 3 ^ 40 * 6000920 * 2
def baseEnd_6000920 : Nat := 1027118776392922202200759

theorem tailTrace_6000920 : CollatzResearch.WordTrace tailWord_6000920 prefixEnd_6000920 1027118776392922202200759 := by
  unfold tailWord_6000920
  simp only [CollatzResearch.WordTrace]
  refine ⟨109435766709849595193300107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145914355613132793591066809 109435766709849595193300107)
  ·
    refine ⟨164153650064774392789950161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109435766709849595193300107 164153650064774392789950161)
    ·
      refine ⟨123115237548580794592462621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164153650064774392789950161 123115237548580794592462621)
      ·
        refine ⟨46168214080717797972173483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123115237548580794592462621 46168214080717797972173483)
        ·
          refine ⟨69252321121076696958260225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46168214080717797972173483 69252321121076696958260225)
          ·
            refine ⟨51939240840807522718695169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69252321121076696958260225 51939240840807522718695169)
            ·
              refine ⟨38954430630605642039021377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51939240840807522718695169 38954430630605642039021377)
              ·
                refine ⟨29215822972954231529266033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38954430630605642039021377 29215822972954231529266033)
                ·
                  refine ⟨21911867229715673646949525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29215822972954231529266033 21911867229715673646949525)
                  ·
                    refine ⟨1027118776392922202200759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21911867229715673646949525 1027118776392922202200759)
                    ·
                      rfl

theorem cell23_6000920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_6000920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000920 prefixEnd_6000920 := by exact prefixLift 6000920
  have htrace : WordTrace (prefixWord ++ tailWord_6000920) baseStart_6000920 baseEnd_6000920 := by
    simpa [prefixWord, tailWord_6000920, baseEnd_6000920] using wordTrace_append hprefix tailTrace_6000920
  have hstable : (prefixWord ++ tailWord_6000920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000920).length < 2 ^ (prefixWord ++ tailWord_6000920).sum := by decide
  have hdescent : baseEnd_6000920 < baseStart_6000920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000922 : List Nat := [3, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2]
def baseStart_6000922 : Nat := 118140960795 + 6000922 * 2 ^ 59
def prefixEnd_6000922 : Nat := 4983230072969 + 3 ^ 40 * 6000922 * 2
def baseEnd_6000922 : Nat := 3081357356140075598777269

theorem tailTrace_6000922 : CollatzResearch.WordTrace tailWord_6000922 prefixEnd_6000922 3081357356140075598777269 := by
  unfold tailWord_6000922
  simp only [CollatzResearch.WordTrace]
  refine ⟨54717901591422986182043255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145914404243794629818782013 54717901591422986182043255)
  ·
    refine ⟨82076852387134479273064883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54717901591422986182043255 82076852387134479273064883)
    ·
      refine ⟨123115278580701718909597325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82076852387134479273064883 123115278580701718909597325)
      ·
        refine ⟨46168229467763144591098997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123115278580701718909597325 46168229467763144591098997)
        ·
          refine ⟨4328271512602794805415531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46168229467763144591098997 4328271512602794805415531)
          ·
            refine ⟨6492407268904192208123297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4328271512602794805415531 6492407268904192208123297)
            ·
              refine ⟨4869305451678144156092473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6492407268904192208123297 4869305451678144156092473)
              ·
                refine ⟨3651979088758608117069355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4869305451678144156092473 3651979088758608117069355)
                ·
                  refine ⟨5477968633137912175604033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3651979088758608117069355 5477968633137912175604033)
                  ·
                    refine ⟨4108476474853434131703025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5477968633137912175604033 4108476474853434131703025)
                    ·
                      refine ⟨3081357356140075598777269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4108476474853434131703025 3081357356140075598777269)
                      ·
                        rfl

theorem cell23_6000922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_6000922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000922 prefixEnd_6000922 := by exact prefixLift 6000922
  have htrace : WordTrace (prefixWord ++ tailWord_6000922) baseStart_6000922 baseEnd_6000922 := by
    simpa [prefixWord, tailWord_6000922, baseEnd_6000922] using wordTrace_append hprefix tailTrace_6000922
  have hstable : (prefixWord ++ tailWord_6000922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000922).length < 2 ^ (prefixWord ++ tailWord_6000922).sum := by decide
  have hdescent : baseEnd_6000922 < baseStart_6000922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000940 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 4]
def baseStart_6000940 : Nat := 118140960795 + 6000940 * 2 ^ 59
def prefixEnd_6000940 : Nat := 4983230072969 + 3 ^ 40 * 6000940 * 2
def baseEnd_6000940 : Nat := 3081366598791856528352185

theorem tailTrace_6000940 : CollatzResearch.WordTrace tailWord_6000940 prefixEnd_6000940 3081366598791856528352185 := by
  unfold tailWord_6000940
  simp only [CollatzResearch.WordTrace]
  refine ⟨109436131439813366901164137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145914841919751155868218849 109436131439813366901164137)
  ·
    refine ⟨82077098579860025175873103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109436131439813366901164137 82077098579860025175873103)
    ·
      refine ⟨123115647869790037763809655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82077098579860025175873103 123115647869790037763809655)
      ·
        refine ⟨184673471804685056645714483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123115647869790037763809655 184673471804685056645714483)
        ·
          refine ⟨277010207707027584968571725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184673471804685056645714483 277010207707027584968571725)
          ·
            refine ⟨103878827890135344363214397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277010207707027584968571725 103878827890135344363214397)
            ·
              refine ⟨38954560458800754136205399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103878827890135344363214397 38954560458800754136205399)
              ·
                refine ⟨58431840688201131204308099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38954560458800754136205399 58431840688201131204308099)
                ·
                  refine ⟨87647761032301696806462149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58431840688201131204308099 87647761032301696806462149)
                  ·
                    refine ⟨16433955193556568151211653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87647761032301696806462149 16433955193556568151211653)
                    ·
                      refine ⟨3081366598791856528352185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16433955193556568151211653 3081366598791856528352185)
                      ·
                        rfl

theorem cell23_6000940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_6000940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000940 prefixEnd_6000940 := by exact prefixLift 6000940
  have htrace : WordTrace (prefixWord ++ tailWord_6000940) baseStart_6000940 baseEnd_6000940 := by
    simpa [prefixWord, tailWord_6000940, baseEnd_6000940] using wordTrace_append hprefix tailTrace_6000940
  have hstable : (prefixWord ++ tailWord_6000940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000940).length < 2 ^ (prefixWord ++ tailWord_6000940).sum := by decide
  have hdescent : baseEnd_6000940 < baseStart_6000940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000977 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 2, 3, 3]
def baseStart_6000977 : Nat := 118140960795 + 6000977 * 2 ^ 59
def prefixEnd_6000977 : Nat := 4983230072969 + 3 ^ 40 * 6000977 * 2
def baseEnd_6000977 : Nat := 3081385597576072883589515

theorem tailTrace_6000977 : CollatzResearch.WordTrace tailWord_6000977 prefixEnd_6000977 3081385597576072883589515 := by
  unfold tailWord_6000977
  simp only [CollatzResearch.WordTrace]
  refine ⟨218873612380492689121425185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145915741586995126080950123 218873612380492689121425185)
  ·
    refine ⟨164155209285369516841068889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218873612380492689121425185 164155209285369516841068889)
    ·
      refine ⟨123116406964027137630801667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164155209285369516841068889 123116406964027137630801667)
      ·
        refine ⟨184674610446040706446202501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123116406964027137630801667 184674610446040706446202501)
        ·
          refine ⟨34626489458632632458662969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184674610446040706446202501 34626489458632632458662969)
          ·
            refine ⟨25969867093974474343997227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34626489458632632458662969 25969867093974474343997227)
            ·
              refine ⟨38954800640961711515995841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25969867093974474343997227 38954800640961711515995841)
              ·
                refine ⟨29216100480721283636996881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38954800640961711515995841 29216100480721283636996881)
                ·
                  refine ⟨21912075360540962727747661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29216100480721283636996881 21912075360540962727747661)
                  ·
                    refine ⟨8217028260202861022905373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21912075360540962727747661 8217028260202861022905373)
                    ·
                      refine ⟨3081385597576072883589515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8217028260202861022905373 3081385597576072883589515)
                      ·
                        rfl

theorem cell23_6000977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 3, 3].length) (baseStart_6000977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000977 prefixEnd_6000977 := by exact prefixLift 6000977
  have htrace : WordTrace (prefixWord ++ tailWord_6000977) baseStart_6000977 baseEnd_6000977 := by
    simpa [prefixWord, tailWord_6000977, baseEnd_6000977] using wordTrace_append hprefix tailTrace_6000977
  have hstable : (prefixWord ++ tailWord_6000977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000977).length < 2 ^ (prefixWord ++ tailWord_6000977).sum := by decide
  have hdescent : baseEnd_6000977 < baseStart_6000977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6000994 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_6000994 : Nat := 118140960795 + 6000994 * 2 ^ 59
def prefixEnd_6000994 : Nat := 4983230072969 + 3 ^ 40 * 6000994 * 2
def baseEnd_6000994 : Nat := 3081394326747199317076937

theorem tailTrace_6000994 : CollatzResearch.WordTrace tailWord_6000994 prefixEnd_6000994 3081394326747199317076937 := by
  unfold tailWord_6000994
  simp only [CollatzResearch.WordTrace]
  refine ⟨54718558105357775256198509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145916154947620734016529357 54718558105357775256198509)
  ·
    refine ⟨20519459289509165721074441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54718558105357775256198509 20519459289509165721074441)
    ·
      refine ⟨15389594467131874290805831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20519459289509165721074441 15389594467131874290805831)
      ·
        refine ⟨23084391700697811436208747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15389594467131874290805831 23084391700697811436208747)
        ·
          refine ⟨34626587551046717154313121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23084391700697811436208747 34626587551046717154313121)
          ·
            refine ⟨25969940663285037865734841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34626587551046717154313121 25969940663285037865734841)
            ·
              refine ⟨19477455497463778399301131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25969940663285037865734841 19477455497463778399301131)
              ·
                refine ⟨29216183246195667598951697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19477455497463778399301131 29216183246195667598951697)
                ·
                  refine ⟨21912137434646750699213773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29216183246195667598951697 21912137434646750699213773)
                  ·
                    refine ⟨8217051537992531512205165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21912137434646750699213773 8217051537992531512205165)
                    ·
                      refine ⟨3081394326747199317076937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8217051537992531512205165 3081394326747199317076937)
                      ·
                        rfl

theorem cell23_6000994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_6000994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6000994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6000994 prefixEnd_6000994 := by exact prefixLift 6000994
  have htrace : WordTrace (prefixWord ++ tailWord_6000994) baseStart_6000994 baseEnd_6000994 := by
    simpa [prefixWord, tailWord_6000994, baseEnd_6000994] using wordTrace_append hprefix tailTrace_6000994
  have hstable : (prefixWord ++ tailWord_6000994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6000994).length < 2 ^ (prefixWord ++ tailWord_6000994).sum := by decide
  have hdescent : baseEnd_6000994 < baseStart_6000994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6000994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001017 : List Nat := [1, 2, 1, 3, 2, 1, 1, 5, 2, 1, 4]
def baseStart_6001017 : Nat := 118140960795 + 6001017 * 2 ^ 59
def prefixEnd_6001017 : Nat := 4983230072969 + 3 ^ 40 * 6001017 * 2
def baseEnd_6001017 : Nat := 3081406136802252727089331

theorem tailTrace_6001017 : CollatzResearch.WordTrace tailWord_6001017 prefixEnd_6001017 3081406136802252727089331 := by
  unfold tailWord_6001017
  simp only [CollatzResearch.WordTrace]
  refine ⟨218875071300347775952881305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145916714200231850635254203 218875071300347775952881305)
  ·
    refine ⟨164156303475260831964660979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218875071300347775952881305 164156303475260831964660979)
    ·
      refine ⟨246234455212891247946991469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164156303475260831964660979 246234455212891247946991469)
      ·
        refine ⟨92337920704834217980121801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246234455212891247946991469 92337920704834217980121801)
        ·
          refine ⟨69253440528625663485091351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92337920704834217980121801 69253440528625663485091351)
          ·
            refine ⟨103880160792938495227637027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69253440528625663485091351 103880160792938495227637027)
            ·
              refine ⟨155820241189407742841455541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103880160792938495227637027 155820241189407742841455541)
              ·
                refine ⟨14608147611506975891386457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 155820241189407742841455541 14608147611506975891386457)
                ·
                  refine ⟨10956110708630231918539843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14608147611506975891386457 10956110708630231918539843)
                  ·
                    refine ⟨16434166062945347877809765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10956110708630231918539843 16434166062945347877809765)
                    ·
                      refine ⟨3081406136802252727089331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16434166062945347877809765 3081406136802252727089331)
                      ·
                        rfl

theorem cell23_6001017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_6001017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001017 prefixEnd_6001017 := by exact prefixLift 6001017
  have htrace : WordTrace (prefixWord ++ tailWord_6001017) baseStart_6001017 baseEnd_6001017 := by
    simpa [prefixWord, tailWord_6001017, baseEnd_6001017] using wordTrace_append hprefix tailTrace_6001017
  have hstable : (prefixWord ++ tailWord_6001017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001017).length < 2 ^ (prefixWord ++ tailWord_6001017).sum := by decide
  have hdescent : baseEnd_6001017 < baseStart_6001017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001046 : List Nat := [5, 3, 1, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_6001046 : Nat := 118140960795 + 6001046 * 2 ^ 59
def prefixEnd_6001046 : Nat := 4983230072969 + 3 ^ 40 * 6001046 * 2
def baseEnd_6001046 : Nat := 3081421027741233113626699

theorem tailTrace_6001046 : CollatzResearch.WordTrace tailWord_6001046 prefixEnd_6001046 3081421027741233113626699 := by
  unfold tailWord_6001046
  simp only [CollatzResearch.WordTrace]
  refine ⟨13679758063577669619105437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145917419344828475937124661 13679758063577669619105437)
  ·
    refine ⟨5129909273841626107164539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13679758063577669619105437 5129909273841626107164539)
    ·
      refine ⟨7694863910762439160746809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5129909273841626107164539 7694863910762439160746809)
      ·
        refine ⟨5771147933071829370560107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7694863910762439160746809 5771147933071829370560107)
        ·
          refine ⟨8656721899607744055840161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5771147933071829370560107 8656721899607744055840161)
          ·
            refine ⟨6492541424705808041880121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8656721899607744055840161 6492541424705808041880121)
            ·
              refine ⟨4869406068529356031410091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6492541424705808041880121 4869406068529356031410091)
              ·
                refine ⟨7304109102794034047115137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4869406068529356031410091 7304109102794034047115137)
                ·
                  refine ⟨5478081827095525535336353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7304109102794034047115137 5478081827095525535336353)
                  ·
                    refine ⟨4108561370321644151502265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5478081827095525535336353 4108561370321644151502265)
                    ·
                      refine ⟨3081421027741233113626699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4108561370321644151502265 3081421027741233113626699)
                      ·
                        rfl

theorem cell23_6001046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_6001046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001046 prefixEnd_6001046 := by exact prefixLift 6001046
  have htrace : WordTrace (prefixWord ++ tailWord_6001046) baseStart_6001046 baseEnd_6001046 := by
    simpa [prefixWord, tailWord_6001046, baseEnd_6001046] using wordTrace_append hprefix tailTrace_6001046
  have hstable : (prefixWord ++ tailWord_6001046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001046).length < 2 ^ (prefixWord ++ tailWord_6001046).sum := by decide
  have hdescent : baseEnd_6001046 < baseStart_6001046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001122 : List Nat := [3, 3, 3, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_6001122 : Nat := 118140960795 + 6001122 * 2 ^ 59
def prefixEnd_6001122 : Nat := 4983230072969 + 3 ^ 40 * 6001122 * 2
def baseEnd_6001122 : Nat := 3081460052270974816276349

theorem tailTrace_6001122 : CollatzResearch.WordTrace tailWord_6001122 prefixEnd_6001122 3081460052270974816276349 := by
  unfold tailWord_6001122
  simp only [CollatzResearch.WordTrace]
  refine ⟨54719725241241844721363405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145919267309978252590302413 54719725241241844721363405)
  ·
    refine ⟨20519896965465691770511277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54719725241241844721363405 20519896965465691770511277)
    ·
      refine ⟨7694961362049634413941729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20519896965465691770511277 7694961362049634413941729)
      ·
        refine ⟨5771221021537225810456297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7694961362049634413941729 5771221021537225810456297)
        ·
          refine ⟨4328415766152919357842223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5771221021537225810456297 4328415766152919357842223)
          ·
            refine ⟨6492623649229379036763335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4328415766152919357842223 6492623649229379036763335)
            ·
              refine ⟨9738935473844068555145003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6492623649229379036763335 9738935473844068555145003)
              ·
                refine ⟨14608403210766102832717505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9738935473844068555145003 14608403210766102832717505)
                ·
                  refine ⟨10956302408074577124538129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14608403210766102832717505 10956302408074577124538129)
                  ·
                    refine ⟨8217226806055932843403597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10956302408074577124538129 8217226806055932843403597)
                    ·
                      refine ⟨3081460052270974816276349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8217226806055932843403597 3081460052270974816276349)
                      ·
                        rfl

theorem cell23_6001122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_6001122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001122 prefixEnd_6001122 := by exact prefixLift 6001122
  have htrace : WordTrace (prefixWord ++ tailWord_6001122) baseStart_6001122 baseEnd_6001122 := by
    simpa [prefixWord, tailWord_6001122, baseEnd_6001122] using wordTrace_append hprefix tailTrace_6001122
  have hstable : (prefixWord ++ tailWord_6001122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001122).length < 2 ^ (prefixWord ++ tailWord_6001122).sum := by decide
  have hdescent : baseEnd_6001122 < baseStart_6001122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001128 : List Nat := [2, 1, 4, 1, 1, 5, 1, 1, 2, 3, 2]
def baseStart_6001128 : Nat := 118140960795 + 6001128 * 2 ^ 59
def prefixEnd_6001128 : Nat := 4983230072969 + 3 ^ 40 * 6001128 * 2
def baseEnd_6001128 : Nat := 3081463133154901792801321

theorem tailTrace_6001128 : CollatzResearch.WordTrace tailWord_6001128 prefixEnd_6001128 3081463133154901792801321 := by
  unfold tailWord_6001128
  simp only [CollatzResearch.WordTrace]
  refine ⟨109439559901472820955086019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145919413201963761273448025 109439559901472820955086019)
  ·
    refine ⟨164159339852209231432629029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109439559901472820955086019 164159339852209231432629029)
    ·
      refine ⟨30779876222289230893617943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164159339852209231432629029 30779876222289230893617943)
      ·
        refine ⟨46169814333433846340426915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30779876222289230893617943 46169814333433846340426915)
        ·
          refine ⟨69254721500150769510640373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46169814333433846340426915 69254721500150769510640373)
          ·
            refine ⟨6492630140639134641622535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69254721500150769510640373 6492630140639134641622535)
            ·
              refine ⟨9738945210958701962433803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6492630140639134641622535 9738945210958701962433803)
              ·
                refine ⟨14608417816438052943650705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9738945210958701962433803 14608417816438052943650705)
                ·
                  refine ⟨10956313362328539707738029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14608417816438052943650705 10956313362328539707738029)
                  ·
                    refine ⟨4108617510873202390401761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10956313362328539707738029 4108617510873202390401761)
                    ·
                      refine ⟨3081463133154901792801321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4108617510873202390401761 3081463133154901792801321)
                      ·
                        rfl

theorem cell23_6001128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_6001128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001128 prefixEnd_6001128 := by exact prefixLift 6001128
  have htrace : WordTrace (prefixWord ++ tailWord_6001128) baseStart_6001128 baseEnd_6001128 := by
    simpa [prefixWord, tailWord_6001128, baseEnd_6001128] using wordTrace_append hprefix tailTrace_6001128
  have hstable : (prefixWord ++ tailWord_6001128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001128).length < 2 ^ (prefixWord ++ tailWord_6001128).sum := by decide
  have hdescent : baseEnd_6001128 < baseStart_6001128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001134 : List Nat := [4, 1, 2, 1, 2, 2, 2, 2, 1, 6]
def baseStart_6001134 : Nat := 118140960795 + 6001134 * 2 ^ 59
def prefixEnd_6001134 : Nat := 4983230072969 + 3 ^ 40 * 6001134 * 2
def baseEnd_6001134 : Nat := 1027155404679609589775431

theorem tailTrace_6001134 : CollatzResearch.WordTrace tailWord_6001134 prefixEnd_6001134 1027155404679609589775431 := by
  unfold tailWord_6001134
  simp only [CollatzResearch.WordTrace]
  refine ⟨27359917330115488116861307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145919559093949269956593637 27359917330115488116861307)
  ·
    refine ⟨41039875995173232175291961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27359917330115488116861307 41039875995173232175291961)
    ·
      refine ⟨30779906996379924131468971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41039875995173232175291961 30779906996379924131468971)
      ·
        refine ⟨46169860494569886197203457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30779906996379924131468971 46169860494569886197203457)
        ·
          refine ⟨34627395370927414647902593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46169860494569886197203457 34627395370927414647902593)
          ·
            refine ⟨25970546528195560985926945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34627395370927414647902593 25970546528195560985926945)
            ·
              refine ⟨19477909896146670739445209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25970546528195560985926945 19477909896146670739445209)
              ·
                refine ⟨14608432422110003054583907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19477909896146670739445209 14608432422110003054583907)
                ·
                  refine ⟨21912648633165004581875861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14608432422110003054583907 21912648633165004581875861)
                  ·
                    refine ⟨1027155404679609589775431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21912648633165004581875861 1027155404679609589775431)
                    ·
                      rfl

theorem cell23_6001134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_6001134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001134 prefixEnd_6001134 := by exact prefixLift 6001134
  have htrace : WordTrace (prefixWord ++ tailWord_6001134) baseStart_6001134 baseEnd_6001134 := by
    simpa [prefixWord, tailWord_6001134, baseEnd_6001134] using wordTrace_append hprefix tailTrace_6001134
  have hstable : (prefixWord ++ tailWord_6001134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001134).length < 2 ^ (prefixWord ++ tailWord_6001134).sum := by decide
  have hdescent : baseEnd_6001134 < baseStart_6001134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001181 : List Nat := [1, 4, 2, 2, 1, 4, 2, 7]
def baseStart_6001181 : Nat := 118140960795 + 6001181 * 2 ^ 59
def prefixEnd_6001181 : Nat := 4983230072969 + 3 ^ 40 * 6001181 * 2
def baseEnd_6001181 : Nat := 114129272134429262423651

theorem tailTrace_6001181 : CollatzResearch.WordTrace tailWord_6001181 prefixEnd_6001181 114129272134429262423651 := by
  unfold tailWord_6001181
  simp only [CollatzResearch.WordTrace]
  refine ⟨218881052871753631961851397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145920701914502421307900931 218881052871753631961851397)
  ·
    refine ⟨41040197413453805992847137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218881052871753631961851397 41040197413453805992847137)
    ·
      refine ⟨30780148060090354494635353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41040197413453805992847137 30780148060090354494635353)
      ·
        refine ⟨23085111045067765870976515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30780148060090354494635353 23085111045067765870976515)
        ·
          refine ⟨34627666567601648806464773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23085111045067765870976515 34627666567601648806464773)
          ·
            refine ⟨6492687481425309151212145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34627666567601648806464773 6492687481425309151212145)
            ·
              refine ⟨4869515611068981863409109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6492687481425309151212145 4869515611068981863409109)
              ·
                refine ⟨114129272134429262423651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4869515611068981863409109 114129272134429262423651)
                ·
                  rfl

theorem cell23_6001181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 7].length) (baseStart_6001181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001181 prefixEnd_6001181 := by exact prefixLift 6001181
  have htrace : WordTrace (prefixWord ++ tailWord_6001181) baseStart_6001181 baseEnd_6001181 := by
    simpa [prefixWord, tailWord_6001181, baseEnd_6001181] using wordTrace_append hprefix tailTrace_6001181
  have hstable : (prefixWord ++ tailWord_6001181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001181).length < 2 ^ (prefixWord ++ tailWord_6001181).sum := by decide
  have hdescent : baseEnd_6001181 < baseStart_6001181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001192 : List Nat := [2, 1, 5, 2, 1, 1, 3, 3, 1, 2, 2]
def baseStart_6001192 : Nat := 118140960795 + 6001192 * 2 ^ 59
def prefixEnd_6001192 : Nat := 4983230072969 + 3 ^ 40 * 6001192 * 2
def baseEnd_6001192 : Nat := 3081495995916789542401027

theorem tailTrace_6001192 : CollatzResearch.WordTrace tailWord_6001192 prefixEnd_6001192 3081495995916789542401027 := by
  unfold tailWord_6001192
  simp only [CollatzResearch.WordTrace]
  refine ⟨109440727037356890420250915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145920969383142520560334553 109440727037356890420250915)
  ·
    refine ⟨164161090556035335630376373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109440727037356890420250915 164161090556035335630376373)
    ·
      refine ⟨15390102239628312715347785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164161090556035335630376373 15390102239628312715347785)
      ·
        refine ⟨11542576679721234536510839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15390102239628312715347785 11542576679721234536510839)
        ·
          refine ⟨17313865019581851804766259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11542576679721234536510839 17313865019581851804766259)
          ·
            refine ⟨25970797529372777707149389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17313865019581851804766259 25970797529372777707149389)
            ·
              refine ⟨9739049073514791640181021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25970797529372777707149389 9739049073514791640181021)
              ·
                refine ⟨3652143402568046865067883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9739049073514791640181021 3652143402568046865067883)
                ·
                  refine ⟨5478215103852070297601825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3652143402568046865067883 5478215103852070297601825)
                  ·
                    refine ⟨4108661327889052723201369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5478215103852070297601825 4108661327889052723201369)
                    ·
                      refine ⟨3081495995916789542401027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4108661327889052723201369 3081495995916789542401027)
                      ·
                        rfl

theorem cell23_6001192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_6001192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001192 prefixEnd_6001192 := by exact prefixLift 6001192
  have htrace : WordTrace (prefixWord ++ tailWord_6001192) baseStart_6001192 baseEnd_6001192 := by
    simpa [prefixWord, tailWord_6001192, baseEnd_6001192] using wordTrace_append hprefix tailTrace_6001192
  have hstable : (prefixWord ++ tailWord_6001192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001192).length < 2 ^ (prefixWord ++ tailWord_6001192).sum := by decide
  have hdescent : baseEnd_6001192 < baseStart_6001192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001234 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_6001234 : Nat := 118140960795 + 6001234 * 2 ^ 59
def prefixEnd_6001234 : Nat := 4983230072969 + 3 ^ 40 * 6001234 * 2
def baseEnd_6001234 : Nat := 3081517562104278378075833

theorem tailTrace_6001234 : CollatzResearch.WordTrace tailWord_6001234 prefixEnd_6001234 3081517562104278378075833 := by
  unfold tailWord_6001234
  simp only [CollatzResearch.WordTrace]
  refine ⟨54720746485140405503382689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145921990627041081342353837 54720746485140405503382689)
  ·
    refine ⟨41040559863855304127537017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54720746485140405503382689 41040559863855304127537017)
    ·
      refine ⟨30780419897891478095652763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41040559863855304127537017 30780419897891478095652763)
      ·
        refine ⟨46170629846837217143479145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30780419897891478095652763 46170629846837217143479145)
        ·
          refine ⟨34627972385127912857609359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46170629846837217143479145 34627972385127912857609359)
          ·
            refine ⟨51941958577691869286414039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34627972385127912857609359 51941958577691869286414039)
            ·
              refine ⟨77912937866537803929621059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51941958577691869286414039 77912937866537803929621059)
              ·
                refine ⟨116869406799806705894431589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77912937866537803929621059 116869406799806705894431589)
                ·
                  refine ⟨21913013774963757355205923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116869406799806705894431589 21913013774963757355205923)
                  ·
                    refine ⟨32869520662445636032808885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21913013774963757355205923 32869520662445636032808885)
                    ·
                      refine ⟨3081517562104278378075833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32869520662445636032808885 3081517562104278378075833)
                      ·
                        rfl

theorem cell23_6001234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_6001234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001234 prefixEnd_6001234 := by exact prefixLift 6001234
  have htrace : WordTrace (prefixWord ++ tailWord_6001234) baseStart_6001234 baseEnd_6001234 := by
    simpa [prefixWord, tailWord_6001234, baseEnd_6001234] using wordTrace_append hprefix tailTrace_6001234
  have hstable : (prefixWord ++ tailWord_6001234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001234).length < 2 ^ (prefixWord ++ tailWord_6001234).sum := by decide
  have hdescent : baseEnd_6001234 < baseStart_6001234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001281 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 2, 3, 3]
def baseStart_6001281 : Nat := 118140960795 + 6001281 * 2 ^ 59
def prefixEnd_6001281 : Nat := 4983230072969 + 3 ^ 40 * 6001281 * 2
def baseEnd_6001281 : Nat := 3081541695695039694188117

theorem tailTrace_6001281 : CollatzResearch.WordTrace tailWord_6001281 prefixEnd_6001281 3081541695695039694188117 := by
  unfold tailWord_6001281
  simp only [CollatzResearch.WordTrace]
  refine ⟨218884700171391349040491697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145923133447594232693661131 218884700171391349040491697)
  ·
    refine ⟨164163525128543511780368773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218884700171391349040491697 164163525128543511780368773)
    ·
      refine ⟨30780660961601908458819145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164163525128543511780368773 30780660961601908458819145)
      ·
        refine ⟨23085495721201431344114359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30780660961601908458819145 23085495721201431344114359)
        ·
          refine ⟨34628243581802147016171539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23085495721201431344114359 34628243581802147016171539)
          ·
            refine ⟨51942365372703220524257309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34628243581802147016171539 51942365372703220524257309)
            ·
              refine ⟨19478387014763707696596491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51942365372703220524257309 19478387014763707696596491)
              ·
                refine ⟨29217580522145561544894737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19478387014763707696596491 29217580522145561544894737)
                ·
                  refine ⟨21913185391609171158671053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29217580522145561544894737 21913185391609171158671053)
                  ·
                    refine ⟨8217444521853439184501645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21913185391609171158671053 8217444521853439184501645)
                    ·
                      refine ⟨3081541695695039694188117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8217444521853439184501645 3081541695695039694188117)
                      ·
                        rfl

theorem cell23_6001281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_6001281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001281 prefixEnd_6001281 := by exact prefixLift 6001281
  have htrace : WordTrace (prefixWord ++ tailWord_6001281) baseStart_6001281 baseEnd_6001281 := by
    simpa [prefixWord, tailWord_6001281, baseEnd_6001281] using wordTrace_append hprefix tailTrace_6001281
  have hstable : (prefixWord ++ tailWord_6001281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001281).length < 2 ^ (prefixWord ++ tailWord_6001281).sum := by decide
  have hdescent : baseEnd_6001281 < baseStart_6001281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001321 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 2, 4, 2]
def baseStart_6001321 : Nat := 118140960795 + 6001321 * 2 ^ 59
def prefixEnd_6001321 : Nat := 4983230072969 + 3 ^ 40 * 6001321 * 2
def baseEnd_6001321 : Nat := 3081562234921219537687933

theorem tailTrace_6001321 : CollatzResearch.WordTrace tailWord_6001321 prefixEnd_6001321 3081562234921219537687933 := by
  unfold tailWord_6001321
  simp only [CollatzResearch.WordTrace]
  refine ⟨218886159091246435871947817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145924106060830957247965211 218886159091246435871947817)
  ·
    refine ⟨164164619318434826903960863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218886159091246435871947817 164164619318434826903960863)
    ·
      refine ⟨246246928977652240355941295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164164619318434826903960863 246246928977652240355941295)
      ·
        refine ⟨369370393466478360533911943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246246928977652240355941295 369370393466478360533911943)
        ·
          refine ⟨554055590199717540800867915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369370393466478360533911943 554055590199717540800867915)
          ·
            refine ⟨831083385299576311201301873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554055590199717540800867915 831083385299576311201301873)
            ·
              refine ⟨623312538974682233400976405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831083385299576311201301873 623312538974682233400976405)
              ·
                refine ⟨29217775264438229690670769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 623312538974682233400976405 29217775264438229690670769)
                ·
                  refine ⟨21913331448328672268003077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29217775264438229690670769 21913331448328672268003077)
                  ·
                    refine ⟨4108749646561626050250577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21913331448328672268003077 4108749646561626050250577)
                    ·
                      refine ⟨3081562234921219537687933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4108749646561626050250577 3081562234921219537687933)
                      ·
                        rfl

theorem cell23_6001321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 4, 2].length) (baseStart_6001321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001321 prefixEnd_6001321 := by exact prefixLift 6001321
  have htrace : WordTrace (prefixWord ++ tailWord_6001321) baseStart_6001321 baseEnd_6001321 := by
    simpa [prefixWord, tailWord_6001321, baseEnd_6001321] using wordTrace_append hprefix tailTrace_6001321
  have hstable : (prefixWord ++ tailWord_6001321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001321).length < 2 ^ (prefixWord ++ tailWord_6001321).sum := by decide
  have hdescent : baseEnd_6001321 < baseStart_6001321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001331 : List Nat := [1, 1, 1, 2, 3, 4, 1, 3, 3, 4]
def baseStart_6001331 : Nat := 118140960795 + 6001331 * 2 ^ 59
def prefixEnd_6001331 : Nat := 4983230072969 + 3 ^ 40 * 6001331 * 2
def baseEnd_6001331 : Nat := 1027189123242588166187629

theorem tailTrace_6001331 : CollatzResearch.WordTrace tailWord_6001331 prefixEnd_6001331 1027189123242588166187629 := by
  unfold tailWord_6001331
  simp only [CollatzResearch.WordTrace]
  refine ⟨218886523821210207579811847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145924349214140138386541231 218886523821210207579811847)
  ·
    refine ⟨328329785731815311369717771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218886523821210207579811847 328329785731815311369717771)
    ·
      refine ⟨492494678597722967054576657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328329785731815311369717771 492494678597722967054576657)
      ·
        refine ⟨369371008948292225290932493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 492494678597722967054576657 369371008948292225290932493)
        ·
          refine ⟨138514128355609584484099685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 369371008948292225290932493 138514128355609584484099685)
          ·
            refine ⟨25971399066676797090768691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138514128355609584484099685 25971399066676797090768691)
            ·
              refine ⟨38957098600015195636153037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25971399066676797090768691 38957098600015195636153037)
              ·
                refine ⟨14608911975005698363557389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38957098600015195636153037 14608911975005698363557389)
                ·
                  refine ⟨5478341990627136886334021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14608911975005698363557389 5478341990627136886334021)
                  ·
                    refine ⟨1027189123242588166187629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5478341990627136886334021 1027189123242588166187629)
                    ·
                      rfl

theorem cell23_6001331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 4].length) (baseStart_6001331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001331 prefixEnd_6001331 := by exact prefixLift 6001331
  have htrace : WordTrace (prefixWord ++ tailWord_6001331) baseStart_6001331 baseEnd_6001331 := by
    simpa [prefixWord, tailWord_6001331, baseEnd_6001331] using wordTrace_append hprefix tailTrace_6001331
  have hstable : (prefixWord ++ tailWord_6001331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001331).length < 2 ^ (prefixWord ++ tailWord_6001331).sum := by decide
  have hdescent : baseEnd_6001331 < baseStart_6001331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001341 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 1, 4, 3]
def baseStart_6001341 : Nat := 118140960795 + 6001341 * 2 ^ 59
def prefixEnd_6001341 : Nat := 4983230072969 + 3 ^ 40 * 6001341 * 2
def baseEnd_6001341 : Nat := 3081572504534309459437841

theorem tailTrace_6001341 : CollatzResearch.WordTrace tailWord_6001341 prefixEnd_6001341 3081572504534309459437841 := by
  unfold tailWord_6001341
  simp only [CollatzResearch.WordTrace]
  refine ⟨218886888551173979287675877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145924592367449319525117251 218886888551173979287675877)
  ·
    refine ⟨41041291603345121116439227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218886888551173979287675877 41041291603345121116439227)
    ·
      refine ⟨61561937405017681674658841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41041291603345121116439227 61561937405017681674658841)
      ·
        refine ⟨46171453053763261255994131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61561937405017681674658841 46171453053763261255994131)
        ·
          refine ⟨69257179580644891883991197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46171453053763261255994131 69257179580644891883991197)
          ·
            refine ⟨25971442342741834456496699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69257179580644891883991197 25971442342741834456496699)
            ·
              refine ⟨38957163514112751684745049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25971442342741834456496699 38957163514112751684745049)
              ·
                refine ⟨29217872635584563763558787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38957163514112751684745049 29217872635584563763558787)
                ·
                  refine ⟨43826808953376845645338181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29217872635584563763558787 43826808953376845645338181)
                  ·
                    refine ⟨8217526678758158558500909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43826808953376845645338181 8217526678758158558500909)
                    ·
                      refine ⟨3081572504534309459437841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8217526678758158558500909 3081572504534309459437841)
                      ·
                        rfl

theorem cell23_6001341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_6001341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001341 prefixEnd_6001341 := by exact prefixLift 6001341
  have htrace : WordTrace (prefixWord ++ tailWord_6001341) baseStart_6001341 baseEnd_6001341 := by
    simpa [prefixWord, tailWord_6001341, baseEnd_6001341] using wordTrace_append hprefix tailTrace_6001341
  have hstable : (prefixWord ++ tailWord_6001341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001341).length < 2 ^ (prefixWord ++ tailWord_6001341).sum := by decide
  have hdescent : baseEnd_6001341 < baseStart_6001341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001348 : List Nat := [2, 3, 3, 1, 1, 2, 2, 2, 3, 4]
def baseStart_6001348 : Nat := 118140960795 + 6001348 * 2 ^ 59
def prefixEnd_6001348 : Nat := 4983230072969 + 3 ^ 40 * 6001348 * 2
def baseEnd_6001348 : Nat := 1027192032966296977350103

theorem tailTrace_6001348 : CollatzResearch.WordTrace tailWord_6001348 prefixEnd_6001348 1027192032966296977350103 := by
  unfold tailWord_6001348
  simp only [CollatzResearch.WordTrace]
  refine ⟨109443571931074309741590349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145924762574765746322120465 109443571931074309741590349)
  ·
    refine ⟨41041339474152866153096381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109443571931074309741590349 41041339474152866153096381)
    ·
      refine ⟨15390502302807324807411143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41041339474152866153096381 15390502302807324807411143)
      ·
        refine ⟨23085753454210987211116715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15390502302807324807411143 23085753454210987211116715)
        ·
          refine ⟨34628630181316480816675073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23085753454210987211116715 34628630181316480816675073)
          ·
            refine ⟨25971472635987360612506305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34628630181316480816675073 25971472635987360612506305)
            ·
              refine ⟨19478604476990520459379729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25971472635987360612506305 19478604476990520459379729)
              ·
                refine ⟨14608953357742890344534797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19478604476990520459379729 14608953357742890344534797)
                ·
                  refine ⟨5478357509153583879200549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14608953357742890344534797 5478357509153583879200549)
                  ·
                    refine ⟨1027192032966296977350103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5478357509153583879200549 1027192032966296977350103)
                    ·
                      rfl

theorem cell23_6001348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_6001348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001348 prefixEnd_6001348 := by exact prefixLift 6001348
  have htrace : WordTrace (prefixWord ++ tailWord_6001348) baseStart_6001348 baseEnd_6001348 := by
    simpa [prefixWord, tailWord_6001348, baseEnd_6001348] using wordTrace_append hprefix tailTrace_6001348
  have hstable : (prefixWord ++ tailWord_6001348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001348).length < 2 ^ (prefixWord ++ tailWord_6001348).sum := by decide
  have hdescent : baseEnd_6001348 < baseStart_6001348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001415 : List Nat := [1, 1, 4, 4, 1, 1, 1, 3, 2, 3, 2]
def baseStart_6001415 : Nat := 118140960795 + 6001415 * 2 ^ 59
def prefixEnd_6001415 : Nat := 4983230072969 + 3 ^ 40 * 6001415 * 2
def baseEnd_6001415 : Nat := 3081610502102742169912501

theorem tailTrace_6001415 : CollatzResearch.WordTrace tailWord_6001415 prefixEnd_6001415 3081610502102742169912501 := by
  unfold tailWord_6001415
  simp only [CollatzResearch.WordTrace]
  refine ⟨218889587552905889925869699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145926391701937259950579799 218889587552905889925869699)
  ·
    refine ⟨328334381329358834888804549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218889587552905889925869699 328334381329358834888804549)
    ·
      refine ⟨61562696499254781541650853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 328334381329358834888804549 61562696499254781541650853)
      ·
        refine ⟨11543005593610271539059535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61562696499254781541650853 11543005593610271539059535)
        ·
          refine ⟨17314508390415407308589303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11543005593610271539059535 17314508390415407308589303)
          ·
            refine ⟨25971762585623110962883955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17314508390415407308589303 25971762585623110962883955)
            ·
              refine ⟨38957643878434666444325933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25971762585623110962883955 38957643878434666444325933)
              ·
                refine ⟨14609116454412999916622225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38957643878434666444325933 14609116454412999916622225)
                ·
                  refine ⟨10956837340809749937466669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14609116454412999916622225 10956837340809749937466669)
                  ·
                    refine ⟨4108814002803656226550001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10956837340809749937466669 4108814002803656226550001)
                    ·
                      refine ⟨3081610502102742169912501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4108814002803656226550001 3081610502102742169912501)
                      ·
                        rfl

theorem cell23_6001415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_6001415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001415 prefixEnd_6001415 := by exact prefixLift 6001415
  have htrace : WordTrace (prefixWord ++ tailWord_6001415) baseStart_6001415 baseEnd_6001415 := by
    simpa [prefixWord, tailWord_6001415, baseEnd_6001415] using wordTrace_append hprefix tailTrace_6001415
  have hstable : (prefixWord ++ tailWord_6001415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001415).length < 2 ^ (prefixWord ++ tailWord_6001415).sum := by decide
  have hdescent : baseEnd_6001415 < baseStart_6001415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001424 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 6]
def baseStart_6001424 : Nat := 118140960795 + 6001424 * 2 ^ 59
def prefixEnd_6001424 : Nat := 4983230072969 + 3 ^ 40 * 6001424 * 2
def baseEnd_6001424 : Nat := 3081615123428632634699959

theorem tailTrace_6001424 : CollatzResearch.WordTrace tailWord_6001424 prefixEnd_6001424 3081615123428632634699959 := by
  unfold tailWord_6001424
  simp only [CollatzResearch.WordTrace]
  refine ⟨109444957904936642231473663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145926610539915522975298217 109444957904936642231473663)
  ·
    refine ⟨164167436857404963347210495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109444957904936642231473663 164167436857404963347210495)
    ·
      refine ⟨246251155286107445020815743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164167436857404963347210495 246251155286107445020815743)
      ·
        refine ⟨369376732929161167531223615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246251155286107445020815743 369376732929161167531223615)
        ·
          refine ⟨554065099393741751296835423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369376732929161167531223615 554065099393741751296835423)
          ·
            refine ⟨831097649090612626945253135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554065099393741751296835423 831097649090612626945253135)
            ·
              refine ⟨1246646473635918940417879703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831097649090612626945253135 1246646473635918940417879703)
              ·
                refine ⟨1869969710453878410626819555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1246646473635918940417879703 1869969710453878410626819555)
                ·
                  refine ⟨2804954565680817615940229333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1869969710453878410626819555 2804954565680817615940229333)
                  ·
                    refine ⟨65741122633144162873599125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2804954565680817615940229333 65741122633144162873599125)
                    ·
                      refine ⟨3081615123428632634699959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65741122633144162873599125 3081615123428632634699959)
                      ·
                        rfl

theorem cell23_6001424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_6001424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001424 prefixEnd_6001424 := by exact prefixLift 6001424
  have htrace : WordTrace (prefixWord ++ tailWord_6001424) baseStart_6001424 baseEnd_6001424 := by
    simpa [prefixWord, tailWord_6001424, baseEnd_6001424] using wordTrace_append hprefix tailTrace_6001424
  have hstable : (prefixWord ++ tailWord_6001424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001424).length < 2 ^ (prefixWord ++ tailWord_6001424).sum := by decide
  have hdescent : baseEnd_6001424 < baseStart_6001424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001439 : List Nat := [1, 1, 2, 4, 2, 4, 2, 2, 1, 1, 3]
def baseStart_6001439 : Nat := 118140960795 + 6001439 * 2 ^ 59
def prefixEnd_6001439 : Nat := 4983230072969 + 3 ^ 40 * 6001439 * 2
def baseEnd_6001439 : Nat := 3081622825638450076012391

theorem tailTrace_6001439 : CollatzResearch.WordTrace tailWord_6001439 prefixEnd_6001439 3081622825638450076012391 := by
  unfold tailWord_6001439
  simp only [CollatzResearch.WordTrace]
  refine ⟨218890462904818942024743371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145926975269879294683162247 218890462904818942024743371)
  ·
    refine ⟨328335694357228413037115057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218890462904818942024743371 328335694357228413037115057)
    ·
      refine ⟨246251770767921309777836293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328335694357228413037115057 246251770767921309777836293)
      ·
        refine ⟨46172207018985245583344305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246251770767921309777836293 46172207018985245583344305)
        ·
          refine ⟨34629155264238934187508229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46172207018985245583344305 34629155264238934187508229)
          ·
            refine ⟨6492966612044800160157793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34629155264238934187508229 6492966612044800160157793)
            ·
              refine ⟨4869724959033600120118345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6492966612044800160157793 4869724959033600120118345)
              ·
                refine ⟨3652293719275200090088759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4869724959033600120118345 3652293719275200090088759)
                ·
                  refine ⟨5478440578912800135133139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3652293719275200090088759 5478440578912800135133139)
                  ·
                    refine ⟨8217660868369200202699709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5478440578912800135133139 8217660868369200202699709)
                    ·
                      refine ⟨3081622825638450076012391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8217660868369200202699709 3081622825638450076012391)
                      ·
                        rfl

theorem cell23_6001439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_6001439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001439 prefixEnd_6001439 := by exact prefixLift 6001439
  have htrace : WordTrace (prefixWord ++ tailWord_6001439) baseStart_6001439 baseEnd_6001439 := by
    simpa [prefixWord, tailWord_6001439, baseEnd_6001439] using wordTrace_append hprefix tailTrace_6001439
  have hstable : (prefixWord ++ tailWord_6001439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001439).length < 2 ^ (prefixWord ++ tailWord_6001439).sum := by decide
  have hdescent : baseEnd_6001439 < baseStart_6001439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001441 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 4]
def baseStart_6001441 : Nat := 118140960795 + 6001441 * 2 ^ 59
def prefixEnd_6001441 : Nat := 4983230072969 + 3 ^ 40 * 6001441 * 2
def baseEnd_6001441 : Nat := 3081623852599759068187381

theorem tailTrace_6001441 : CollatzResearch.WordTrace tailWord_6001441 prefixEnd_6001441 3081623852599759068187381 := by
  unfold tailWord_6001441
  simp only [CollatzResearch.WordTrace]
  refine ⟨218890535850811696366316177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145927023900541130910877451 218890535850811696366316177)
  ·
    refine ⟨164167901888108772274737133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218890535850811696366316177 164167901888108772274737133)
    ·
      refine ⟨61562963208040789603026425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164167901888108772274737133 61562963208040789603026425)
      ·
        refine ⟨46172222406030592202269819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61562963208040789603026425 46172222406030592202269819)
        ·
          refine ⟨69258333609045888303404729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46172222406030592202269819 69258333609045888303404729)
          ·
            refine ⟨51943750206784416227553547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69258333609045888303404729 51943750206784416227553547)
            ·
              refine ⟨77915625310176624341330321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51943750206784416227553547 77915625310176624341330321)
              ·
                refine ⟨58436718982632468255997741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77915625310176624341330321 58436718982632468255997741)
                ·
                  refine ⟨21913769618487175595999153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58436718982632468255997741 21913769618487175595999153)
                  ·
                    refine ⟨16435327213865381696999365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21913769618487175595999153 16435327213865381696999365)
                    ·
                      refine ⟨3081623852599759068187381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16435327213865381696999365 3081623852599759068187381)
                      ·
                        rfl

theorem cell23_6001441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_6001441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001441 prefixEnd_6001441 := by exact prefixLift 6001441
  have htrace : WordTrace (prefixWord ++ tailWord_6001441) baseStart_6001441 baseEnd_6001441 := by
    simpa [prefixWord, tailWord_6001441, baseEnd_6001441] using wordTrace_append hprefix tailTrace_6001441
  have hstable : (prefixWord ++ tailWord_6001441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001441).length < 2 ^ (prefixWord ++ tailWord_6001441).sum := by decide
  have hdescent : baseEnd_6001441 < baseStart_6001441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001445 : List Nat := [1, 3, 1, 2, 3, 1, 2, 3, 3, 2, 2]
def baseStart_6001445 : Nat := 118140960795 + 6001445 * 2 ^ 59
def prefixEnd_6001445 : Nat := 4983230072969 + 3 ^ 40 * 6001445 * 2
def baseEnd_6001445 : Nat := 3081625906522377052537363

theorem tailTrace_6001445 : CollatzResearch.WordTrace tailWord_6001445 prefixEnd_6001445 3081625906522377052537363 := by
  unfold tailWord_6001445
  simp only [CollatzResearch.WordTrace]
  refine ⟨218890681742797205049461789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145927121161864803366307859 218890681742797205049461789)
  ·
    refine ⟨82084005653548951893548171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218890681742797205049461789 82084005653548951893548171)
    ·
      refine ⟨123126008480323427840322257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82084005653548951893548171 123126008480323427840322257)
      ·
        refine ⟨92344506360242570880241693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123126008480323427840322257 92344506360242570880241693)
        ·
          refine ⟨34629189885090964080090635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92344506360242570880241693 34629189885090964080090635)
          ·
            refine ⟨51943784827636446120135953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34629189885090964080090635 51943784827636446120135953)
            ·
              refine ⟨38957838620727334590101965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51943784827636446120135953 38957838620727334590101965)
              ·
                refine ⟨14609189482772750471288237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38957838620727334590101965 14609189482772750471288237)
                ·
                  refine ⟨5478446056039781426733089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14609189482772750471288237 5478446056039781426733089)
                  ·
                    refine ⟨4108834542029836070049817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5478446056039781426733089 4108834542029836070049817)
                    ·
                      refine ⟨3081625906522377052537363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4108834542029836070049817 3081625906522377052537363)
                      ·
                        rfl

theorem cell23_6001445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 2, 2].length) (baseStart_6001445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001445 prefixEnd_6001445 := by exact prefixLift 6001445
  have htrace : WordTrace (prefixWord ++ tailWord_6001445) baseStart_6001445 baseEnd_6001445 := by
    simpa [prefixWord, tailWord_6001445, baseEnd_6001445] using wordTrace_append hprefix tailTrace_6001445
  have hstable : (prefixWord ++ tailWord_6001445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001445).length < 2 ^ (prefixWord ++ tailWord_6001445).sum := by decide
  have hdescent : baseEnd_6001445 < baseStart_6001445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001448 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_6001448 : Nat := 118140960795 + 6001448 * 2 ^ 59
def prefixEnd_6001448 : Nat := 4983230072969 + 3 ^ 40 * 6001448 * 2
def baseEnd_6001448 : Nat := 3081627446964340540799849

theorem tailTrace_6001448 : CollatzResearch.WordTrace tailWord_6001448 prefixEnd_6001448 3081627446964340540799849 := by
  unfold tailWord_6001448
  simp only [CollatzResearch.WordTrace]
  refine ⟨109445395580893168280910499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145927194107857557707880665 109445395580893168280910499)
  ·
    refine ⟨164168093371339752421365749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109445395580893168280910499 164168093371339752421365749)
    ·
      refine ⟨15390758753563101789503039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164168093371339752421365749 15390758753563101789503039)
      ·
        refine ⟨23086138130344652684254559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15390758753563101789503039 23086138130344652684254559)
        ·
          refine ⟨34629207195516979026381839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23086138130344652684254559 34629207195516979026381839)
          ·
            refine ⟨51943810793275468539572759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34629207195516979026381839 51943810793275468539572759)
            ·
              refine ⟨77915716189913202809359139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51943810793275468539572759 77915716189913202809359139)
              ·
                refine ⟨116873574284869804214038709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77915716189913202809359139 116873574284869804214038709)
                ·
                  refine ⟨10956897589206544145066129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116873574284869804214038709 10956897589206544145066129)
                  ·
                    refine ⟨8217673191904908108799597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10956897589206544145066129 8217673191904908108799597)
                    ·
                      refine ⟨3081627446964340540799849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8217673191904908108799597 3081627446964340540799849)
                      ·
                        rfl

theorem cell23_6001448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_6001448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001448 prefixEnd_6001448 := by exact prefixLift 6001448
  have htrace : WordTrace (prefixWord ++ tailWord_6001448) baseStart_6001448 baseEnd_6001448 := by
    simpa [prefixWord, tailWord_6001448, baseEnd_6001448] using wordTrace_append hprefix tailTrace_6001448
  have hstable : (prefixWord ++ tailWord_6001448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001448).length < 2 ^ (prefixWord ++ tailWord_6001448).sum := by decide
  have hdescent : baseEnd_6001448 < baseStart_6001448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001458 : List Nat := [3, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4]
def baseStart_6001458 : Nat := 118140960795 + 6001458 * 2 ^ 59
def prefixEnd_6001458 : Nat := 4983230072969 + 3 ^ 40 * 6001458 * 2
def baseEnd_6001458 : Nat := 3081632581770885501674803

theorem tailTrace_6001458 : CollatzResearch.WordTrace tailWord_6001458 prefixEnd_6001458 3081632581770885501674803 := by
  unfold tailWord_6001458
  simp only [CollatzResearch.WordTrace]
  refine ⟨54722788972937527067421257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145927437261166738846456685 54722788972937527067421257)
  ·
    refine ⟨41042091729703145300565943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54722788972937527067421257 41042091729703145300565943)
    ·
      refine ⟨61563137594554717950848915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41042091729703145300565943 61563137594554717950848915)
      ·
        refine ⟨92344706391832076926273373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61563137594554717950848915 92344706391832076926273373)
        ·
          refine ⟨34629264896937028847352515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92344706391832076926273373 34629264896937028847352515)
          ·
            refine ⟨51943897345405543271028773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34629264896937028847352515 51943897345405543271028773)
            ·
              refine ⟨9739480752263539363317895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51943897345405543271028773 9739480752263539363317895)
              ·
                refine ⟨14609221128395309044976843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9739480752263539363317895 14609221128395309044976843)
                ·
                  refine ⟨21913831692592963567465265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14609221128395309044976843 21913831692592963567465265)
                  ·
                    refine ⟨16435373769444722675598949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21913831692592963567465265 16435373769444722675598949)
                    ·
                      refine ⟨3081632581770885501674803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16435373769444722675598949 3081632581770885501674803)
                      ·
                        rfl

theorem cell23_6001458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_6001458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001458 prefixEnd_6001458 := by exact prefixLift 6001458
  have htrace : WordTrace (prefixWord ++ tailWord_6001458) baseStart_6001458 baseEnd_6001458 := by
    simpa [prefixWord, tailWord_6001458, baseEnd_6001458] using wordTrace_append hprefix tailTrace_6001458
  have hstable : (prefixWord ++ tailWord_6001458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001458).length < 2 ^ (prefixWord ++ tailWord_6001458).sum := by decide
  have hdescent : baseEnd_6001458 < baseStart_6001458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001476 : List Nat := [2, 3, 4, 2, 2, 1, 2, 1, 1, 5]
def baseStart_6001476 : Nat := 118140960795 + 6001476 * 2 ^ 59
def prefixEnd_6001476 : Nat := 4983230072969 + 3 ^ 40 * 6001476 * 2
def baseEnd_6001476 : Nat := 1027213941474222143749907

theorem tailTrace_6001476 : CollatzResearch.WordTrace tailWord_6001476 prefixEnd_6001476 1027213941474222143749907 := by
  unfold tailWord_6001476
  simp only [CollatzResearch.WordTrace]
  refine ⟨109445906202842448671920141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145927874937123264895893521 109445906202842448671920141)
  ·
    refine ⟨41042214826065918251970053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109445906202842448671920141 41042214826065918251970053)
    ·
      refine ⟨7695415279887359672244385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41042214826065918251970053 7695415279887359672244385)
      ·
        refine ⟨5771561459915519754183289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7695415279887359672244385 5771561459915519754183289)
        ·
          refine ⟨4328671094936639815637467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5771561459915519754183289 4328671094936639815637467)
          ·
            refine ⟨6493006642404959723456201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4328671094936639815637467 6493006642404959723456201)
            ·
              refine ⟨4869754981803719792592151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6493006642404959723456201 4869754981803719792592151)
              ·
                refine ⟨7304632472705579688888227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4869754981803719792592151 7304632472705579688888227)
                ·
                  refine ⟨10956948709058369533332341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7304632472705579688888227 10956948709058369533332341)
                  ·
                    refine ⟨1027213941474222143749907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10956948709058369533332341 1027213941474222143749907)
                    ·
                      rfl

theorem cell23_6001476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_6001476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001476 prefixEnd_6001476 := by exact prefixLift 6001476
  have htrace : WordTrace (prefixWord ++ tailWord_6001476) baseStart_6001476 baseEnd_6001476 := by
    simpa [prefixWord, tailWord_6001476, baseEnd_6001476] using wordTrace_append hprefix tailTrace_6001476
  have hstable : (prefixWord ++ tailWord_6001476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001476).length < 2 ^ (prefixWord ++ tailWord_6001476).sum := by decide
  have hdescent : baseEnd_6001476 < baseStart_6001476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001495 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 4, 1, 3]
def baseStart_6001495 : Nat := 118140960795 + 6001495 * 2 ^ 59
def prefixEnd_6001495 : Nat := 4983230072969 + 3 ^ 40 * 6001495 * 2
def baseEnd_6001495 : Nat := 3081651580555101856912133

theorem tailTrace_6001495 : CollatzResearch.WordTrace tailWord_6001495 prefixEnd_6001495 3081651580555101856912133 := by
  unfold tailWord_6001495
  simp only [CollatzResearch.WordTrace]
  refine ⟨218892505392616063588781939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145928336928410709059187959 218892505392616063588781939)
  ·
    refine ⟨328338758088924095383172909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218892505392616063588781939 328338758088924095383172909)
    ·
      refine ⟨123127034283346535768689841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328338758088924095383172909 123127034283346535768689841)
      ·
        refine ⟨92345275712509901826517381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123127034283346535768689841 92345275712509901826517381)
        ·
          refine ⟨17314739196095606592472009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92345275712509901826517381 17314739196095606592472009)
          ·
            refine ⟨12986054397071704944354007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17314739196095606592472009 12986054397071704944354007)
            ·
              refine ⟨19479081595607557416531011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12986054397071704944354007 19479081595607557416531011)
              ·
                refine ⟨29218622393411336124796517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19479081595607557416531011 29218622393411336124796517)
                ·
                  refine ⟨5478491698764625523399347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29218622393411336124796517 5478491698764625523399347)
                  ·
                    refine ⟨8217737548146938285099021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5478491698764625523399347 8217737548146938285099021)
                    ·
                      refine ⟨3081651580555101856912133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8217737548146938285099021 3081651580555101856912133)
                      ·
                        rfl

theorem cell23_6001495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_6001495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001495 prefixEnd_6001495 := by exact prefixLift 6001495
  have htrace : WordTrace (prefixWord ++ tailWord_6001495) baseStart_6001495 baseEnd_6001495 := by
    simpa [prefixWord, tailWord_6001495, baseEnd_6001495] using wordTrace_append hprefix tailTrace_6001495
  have hstable : (prefixWord ++ tailWord_6001495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001495).length < 2 ^ (prefixWord ++ tailWord_6001495).sum := by decide
  have hdescent : baseEnd_6001495 < baseStart_6001495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001531 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 4]
def baseStart_6001531 : Nat := 118140960795 + 6001531 * 2 ^ 59
def prefixEnd_6001531 : Nat := 4983230072969 + 3 ^ 40 * 6001531 * 2
def baseEnd_6001531 : Nat := 3081670065858663716061967

theorem tailTrace_6001531 : CollatzResearch.WordTrace tailWord_6001531 prefixEnd_6001531 3081670065858663716061967 := by
  unfold tailWord_6001531
  simp only [CollatzResearch.WordTrace]
  refine ⟨218893818420485641737092447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145929212280323761158061631 218893818420485641737092447)
  ·
    refine ⟨328340727630728462605638671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218893818420485641737092447 328340727630728462605638671)
    ·
      refine ⟨492511091446092693908458007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328340727630728462605638671 492511091446092693908458007)
      ·
        refine ⟨738766637169139040862687011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492511091446092693908458007 738766637169139040862687011)
        ·
          refine ⟨1108149955753708561294030517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738766637169139040862687011 1108149955753708561294030517)
          ·
            refine ⟨103889058351910177621315361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1108149955753708561294030517 103889058351910177621315361)
            ·
              refine ⟨77916793763932633215986521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103889058351910177621315361 77916793763932633215986521)
              ·
                refine ⟨58437595322949474911989891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77916793763932633215986521 58437595322949474911989891)
                ·
                  refine ⟨87656392984424212367984837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58437595322949474911989891 87656392984424212367984837)
                  ·
                    refine ⟨16435573684579539818997157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87656392984424212367984837 16435573684579539818997157)
                    ·
                      refine ⟨3081670065858663716061967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16435573684579539818997157 3081670065858663716061967)
                      ·
                        rfl

theorem cell23_6001531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 4].length) (baseStart_6001531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001531 prefixEnd_6001531 := by exact prefixLift 6001531
  have htrace : WordTrace (prefixWord ++ tailWord_6001531) baseStart_6001531 baseEnd_6001531 := by
    simpa [prefixWord, tailWord_6001531, baseEnd_6001531] using wordTrace_append hprefix tailTrace_6001531
  have hstable : (prefixWord ++ tailWord_6001531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001531).length < 2 ^ (prefixWord ++ tailWord_6001531).sum := by decide
  have hdescent : baseEnd_6001531 < baseStart_6001531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001535 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 4, 2, 2]
def baseStart_6001535 : Nat := 118140960795 + 6001535 * 2 ^ 59
def prefixEnd_6001535 : Nat := 4983230072969 + 3 ^ 40 * 6001535 * 2
def baseEnd_6001535 : Nat := 3081672119781281700411949

theorem tailTrace_6001535 : CollatzResearch.WordTrace tailWord_6001535 prefixEnd_6001535 3081672119781281700411949 := by
  unfold tailWord_6001535
  simp only [CollatzResearch.WordTrace]
  refine ⟨218893964312471150420238059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145929309541647433613492039 218893964312471150420238059)
  ·
    refine ⟨328340946468706725630357089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218893964312471150420238059 328340946468706725630357089)
    ·
      refine ⟨246255709851530044222767817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328340946468706725630357089 246255709851530044222767817)
      ·
        refine ⟨184691782388647533167075863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246255709851530044222767817 184691782388647533167075863)
        ·
          refine ⟨277037673582971299750613795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184691782388647533167075863 277037673582971299750613795)
          ·
            refine ⟨415556510374456949625920693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277037673582971299750613795 415556510374456949625920693)
            ·
              refine ⟨38958422847605339027430065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 415556510374456949625920693 38958422847605339027430065)
              ·
                refine ⟨29218817135704004270572549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38958422847605339027430065 29218817135704004270572549)
                ·
                  refine ⟨5478528212944500800732353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29218817135704004270572549 5478528212944500800732353)
                  ·
                    refine ⟨4108896159708375600549265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5478528212944500800732353 4108896159708375600549265)
                    ·
                      refine ⟨3081672119781281700411949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4108896159708375600549265 3081672119781281700411949)
                      ·
                        rfl

theorem cell23_6001535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 2, 2].length) (baseStart_6001535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001535 prefixEnd_6001535 := by exact prefixLift 6001535
  have htrace : WordTrace (prefixWord ++ tailWord_6001535) baseStart_6001535 baseEnd_6001535 := by
    simpa [prefixWord, tailWord_6001535, baseEnd_6001535] using wordTrace_append hprefix tailTrace_6001535
  have hstable : (prefixWord ++ tailWord_6001535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001535).length < 2 ^ (prefixWord ++ tailWord_6001535).sum := by decide
  have hdescent : baseEnd_6001535 < baseStart_6001535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001568 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 3]
def baseStart_6001568 : Nat := 118140960795 + 6001568 * 2 ^ 59
def prefixEnd_6001568 : Nat := 4983230072969 + 3 ^ 40 * 6001568 * 2
def baseEnd_6001568 : Nat := 3081689064642880071299297

theorem tailTrace_6001568 : CollatzResearch.WordTrace tailWord_6001568 prefixEnd_6001568 3081689064642880071299297 := by
  unfold tailWord_6001568
  simp only [CollatzResearch.WordTrace]
  refine ⟨109447583960675798528094679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145930111947567731370792905 109447583960675798528094679)
  ·
    refine ⟨164171375941013697792142019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109447583960675798528094679 164171375941013697792142019)
    ·
      refine ⟨246257063911520546688213029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164171375941013697792142019 246257063911520546688213029)
      ·
        refine ⟨46173199483410102504039943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246257063911520546688213029 46173199483410102504039943)
        ·
          refine ⟨69259799225115153756059915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46173199483410102504039943 69259799225115153756059915)
          ·
            refine ⟨103889698837672730634089873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69259799225115153756059915 103889698837672730634089873)
            ·
              refine ⟨77917274128254547975567405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103889698837672730634089873 77917274128254547975567405)
              ·
                refine ⟨29218977798095455490837777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77917274128254547975567405 29218977798095455490837777)
                ·
                  refine ⟨21914233348571591618128333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29218977798095455490837777 21914233348571591618128333)
                  ·
                    refine ⟨8217837505714346856798125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21914233348571591618128333 8217837505714346856798125)
                    ·
                      refine ⟨3081689064642880071299297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8217837505714346856798125 3081689064642880071299297)
                      ·
                        rfl

theorem cell23_6001568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_6001568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001568 prefixEnd_6001568 := by exact prefixLift 6001568
  have htrace : WordTrace (prefixWord ++ tailWord_6001568) baseStart_6001568 baseEnd_6001568 := by
    simpa [prefixWord, tailWord_6001568, baseEnd_6001568] using wordTrace_append hprefix tailTrace_6001568
  have hstable : (prefixWord ++ tailWord_6001568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001568).length < 2 ^ (prefixWord ++ tailWord_6001568).sum := by decide
  have hdescent : baseEnd_6001568 < baseStart_6001568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001569 : List Nat := [1, 2, 3, 4, 1, 2, 1, 3, 2, 2, 2]
def baseStart_6001569 : Nat := 118140960795 + 6001569 * 2 ^ 59
def prefixEnd_6001569 : Nat := 4983230072969 + 3 ^ 40 * 6001569 * 2
def baseEnd_6001569 : Nat := 3081689578123534567386793

theorem tailTrace_6001569 : CollatzResearch.WordTrace tailWord_6001569 prefixEnd_6001569 3081689578123534567386793 := by
  unfold tailWord_6001569
  simp only [CollatzResearch.WordTrace]
  refine ⟨218895204394347974226975761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145930136262898649484650507 218895204394347974226975761)
  ·
    refine ⟨164171403295760980670231821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218895204394347974226975761 164171403295760980670231821)
    ·
      refine ⟨61564276235910367751336933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164171403295760980670231821 61564276235910367751336933)
      ·
        refine ⟨11543301794233193953375675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61564276235910367751336933 11543301794233193953375675)
        ·
          refine ⟨17314952691349790930063513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11543301794233193953375675 17314952691349790930063513)
          ·
            refine ⟨12986214518512343197547635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17314952691349790930063513 12986214518512343197547635)
            ·
              refine ⟨19479321777768514796321453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12986214518512343197547635 19479321777768514796321453)
              ·
                refine ⟨7304745666663193048620545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19479321777768514796321453 7304745666663193048620545)
                ·
                  refine ⟨5478559249997394786465409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7304745666663193048620545 5478559249997394786465409)
                  ·
                    refine ⟨4108919437498046089849057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5478559249997394786465409 4108919437498046089849057)
                    ·
                      refine ⟨3081689578123534567386793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4108919437498046089849057 3081689578123534567386793)
                      ·
                        rfl

theorem cell23_6001569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_6001569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001569 prefixEnd_6001569 := by exact prefixLift 6001569
  have htrace : WordTrace (prefixWord ++ tailWord_6001569) baseStart_6001569 baseEnd_6001569 := by
    simpa [prefixWord, tailWord_6001569, baseEnd_6001569] using wordTrace_append hprefix tailTrace_6001569
  have hstable : (prefixWord ++ tailWord_6001569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001569).length < 2 ^ (prefixWord ++ tailWord_6001569).sum := by decide
  have hdescent : baseEnd_6001569 < baseStart_6001569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001571 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 3, 7]
def baseStart_6001571 : Nat := 118140960795 + 6001571 * 2 ^ 59
def prefixEnd_6001571 : Nat := 4983230072969 + 3 ^ 40 * 6001571 * 2
def baseEnd_6001571 : Nat := 1027230201694947853187261

theorem tailTrace_6001571 : CollatzResearch.WordTrace tailWord_6001571 prefixEnd_6001571 1027230201694947853187261 := by
  unfold tailWord_6001571
  simp only [CollatzResearch.WordTrace]
  refine ⟨218895277340340728568548567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145930184893560485712365711 218895277340340728568548567)
  ·
    refine ⟨328342916010511092852822851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218895277340340728568548567 328342916010511092852822851)
    ·
      refine ⟨492514374015766639279234277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328342916010511092852822851 492514374015766639279234277)
      ·
        refine ⟨92346445127956244864856427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 492514374015766639279234277 92346445127956244864856427)
        ·
          refine ⟨138519667691934367297284641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92346445127956244864856427 138519667691934367297284641)
          ·
            refine ⟨103889750768950775472963481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138519667691934367297284641 103889750768950775472963481)
            ·
              refine ⟨77917313076713081604722611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103889750768950775472963481 77917313076713081604722611)
              ·
                refine ⟨116875969615069622407083917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77917313076713081604722611 116875969615069622407083917)
                ·
                  refine ⟨43828488605651108402656469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116875969615069622407083917 43828488605651108402656469)
                  ·
                    refine ⟨1027230201694947853187261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43828488605651108402656469 1027230201694947853187261)
                    ·
                      rfl

theorem cell23_6001571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 7].length) (baseStart_6001571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001571 prefixEnd_6001571 := by exact prefixLift 6001571
  have htrace : WordTrace (prefixWord ++ tailWord_6001571) baseStart_6001571 baseEnd_6001571 := by
    simpa [prefixWord, tailWord_6001571, baseEnd_6001571] using wordTrace_append hprefix tailTrace_6001571
  have hstable : (prefixWord ++ tailWord_6001571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001571).length < 2 ^ (prefixWord ++ tailWord_6001571).sum := by decide
  have hdescent : baseEnd_6001571 < baseStart_6001571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001590 : List Nat := [5, 1, 4, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_6001590 : Nat := 118140960795 + 6001590 * 2 ^ 59
def prefixEnd_6001590 : Nat := 4983230072969 + 3 ^ 40 * 6001590 * 2
def baseEnd_6001590 : Nat := 3081700361217278985224197

theorem tailTrace_6001590 : CollatzResearch.WordTrace tailWord_6001590 prefixEnd_6001590 3081700361217278985224197 := by
  unfold tailWord_6001590
  simp only [CollatzResearch.WordTrace]
  refine ⟨13680998145454493425843139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145930646884847929875660149 13680998145454493425843139)
  ·
    refine ⟨20521497218181740138764709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13680998145454493425843139 20521497218181740138764709)
    ·
      refine ⟨3847780728409076276018383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20521497218181740138764709 3847780728409076276018383)
      ·
        refine ⟨5771671092613614414027575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3847780728409076276018383 5771671092613614414027575)
        ·
          refine ⟨8657506638920421621041363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5771671092613614414027575 8657506638920421621041363)
          ·
            refine ⟨12986259958380632431562045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8657506638920421621041363 12986259958380632431562045)
            ·
              refine ⟨4869847484392737161835767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12986259958380632431562045 4869847484392737161835767)
              ·
                refine ⟨7304771226589105742753651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4869847484392737161835767 7304771226589105742753651)
                ·
                  refine ⟨10957156839883658614130477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7304771226589105742753651 10957156839883658614130477)
                  ·
                    refine ⟨4108933814956371980298929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10957156839883658614130477 4108933814956371980298929)
                    ·
                      refine ⟨3081700361217278985224197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4108933814956371980298929 3081700361217278985224197)
                      ·
                        rfl

theorem cell23_6001590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_6001590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001590 prefixEnd_6001590 := by exact prefixLift 6001590
  have htrace : WordTrace (prefixWord ++ tailWord_6001590) baseStart_6001590 baseEnd_6001590 := by
    simpa [prefixWord, tailWord_6001590, baseEnd_6001590] using wordTrace_append hprefix tailTrace_6001590
  have hstable : (prefixWord ++ tailWord_6001590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001590).length < 2 ^ (prefixWord ++ tailWord_6001590).sum := by decide
  have hdescent : baseEnd_6001590 < baseStart_6001590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001598 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_6001598 : Nat := 118140960795 + 6001598 * 2 ^ 59
def prefixEnd_6001598 : Nat := 4983230072969 + 3 ^ 40 * 6001598 * 2
def baseEnd_6001598 : Nat := 3081704469062514953924159

theorem tailTrace_6001598 : CollatzResearch.WordTrace tailWord_6001598 prefixEnd_6001598 3081704469062514953924159 := by
  unfold tailWord_6001598
  simp only [CollatzResearch.WordTrace]
  refine ⟨27362032763905364022472681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145930841407495274786520965 27362032763905364022472681)
  ·
    refine ⟨20521524572929023016854511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27362032763905364022472681 20521524572929023016854511)
    ·
      refine ⟨30782286859393534525281767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20521524572929023016854511 30782286859393534525281767)
      ·
        refine ⟨46173430289090301787922651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30782286859393534525281767 46173430289090301787922651)
        ·
          refine ⟨69260145433635452681883977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46173430289090301787922651 69260145433635452681883977)
          ·
            refine ⟨51945109075226589511412983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69260145433635452681883977 51945109075226589511412983)
            ·
              refine ⟨77917663612839884267119475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51945109075226589511412983 77917663612839884267119475)
              ·
                refine ⟨116876495419259826400679213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77917663612839884267119475 116876495419259826400679213)
                ·
                  refine ⟨43828685782222434900254705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116876495419259826400679213 43828685782222434900254705)
                  ·
                    refine ⟨32871514336666826175191029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43828685782222434900254705 32871514336666826175191029)
                    ·
                      refine ⟨3081704469062514953924159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32871514336666826175191029 3081704469062514953924159)
                      ·
                        rfl

theorem cell23_6001598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_6001598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001598 prefixEnd_6001598 := by exact prefixLift 6001598
  have htrace : WordTrace (prefixWord ++ tailWord_6001598) baseStart_6001598 baseEnd_6001598 := by
    simpa [prefixWord, tailWord_6001598, baseEnd_6001598] using wordTrace_append hprefix tailTrace_6001598
  have hstable : (prefixWord ++ tailWord_6001598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001598).length < 2 ^ (prefixWord ++ tailWord_6001598).sum := by decide
  have hdescent : baseEnd_6001598 < baseStart_6001598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001625 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 1, 6, 2]
def baseStart_6001625 : Nat := 118140960795 + 6001625 * 2 ^ 59
def prefixEnd_6001625 : Nat := 4983230072969 + 3 ^ 40 * 6001625 * 2
def baseEnd_6001625 : Nat := 3081718333040186348286535

theorem tailTrace_6001625 : CollatzResearch.WordTrace tailWord_6001625 prefixEnd_6001625 3081718333040186348286535 := by
  unfold tailWord_6001625
  simp only [CollatzResearch.WordTrace]
  refine ⟨218897246882145095791014329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145931497921430063860676219 218897246882145095791014329)
  ·
    refine ⟨164172935161608821843260747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218897246882145095791014329 164172935161608821843260747)
    ·
      refine ⟨246259402742413232764891121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164172935161608821843260747 246259402742413232764891121)
      ·
        refine ⟨184694552056809924573668341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246259402742413232764891121 184694552056809924573668341)
        ·
          refine ⟨17315114255325930428781407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 184694552056809924573668341 17315114255325930428781407)
          ·
            refine ⟨25972671382988895643172111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17315114255325930428781407 25972671382988895643172111)
            ·
              refine ⟨38959007074483343464758167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25972671382988895643172111 38959007074483343464758167)
              ·
                refine ⟨58438510611725015197137251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38959007074483343464758167 58438510611725015197137251)
                ·
                  refine ⟨87657765917587522795705877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58438510611725015197137251 87657765917587522795705877)
                  ·
                    refine ⟨4108957777386915131048713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87657765917587522795705877 4108957777386915131048713)
                    ·
                      refine ⟨3081718333040186348286535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4108957777386915131048713 3081718333040186348286535)
                      ·
                        rfl

theorem cell23_6001625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 6, 2].length) (baseStart_6001625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001625 prefixEnd_6001625 := by exact prefixLift 6001625
  have htrace : WordTrace (prefixWord ++ tailWord_6001625) baseStart_6001625 baseEnd_6001625 := by
    simpa [prefixWord, tailWord_6001625, baseEnd_6001625] using wordTrace_append hprefix tailTrace_6001625
  have hstable : (prefixWord ++ tailWord_6001625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001625).length < 2 ^ (prefixWord ++ tailWord_6001625).sum := by decide
  have hdescent : baseEnd_6001625 < baseStart_6001625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001635 : List Nat := [1, 1, 1, 6, 1, 1, 3, 2, 3, 4]
def baseStart_6001635 : Nat := 118140960795 + 6001635 * 2 ^ 59
def prefixEnd_6001635 : Nat := 4983230072969 + 3 ^ 40 * 6001635 * 2
def baseEnd_6001635 : Nat := 1027241155948910436387163

theorem tailTrace_6001635 : CollatzResearch.WordTrace tailWord_6001635 prefixEnd_6001635 1027241155948910436387163 := by
  unfold tailWord_6001635
  simp only [CollatzResearch.WordTrace]
  refine ⟨218897611612108867498878359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145931741074739244999252239 218897611612108867498878359)
  ·
    refine ⟨328346417418163301248317539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218897611612108867498878359 328346417418163301248317539)
    ·
      refine ⟨492519626127244951872476309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328346417418163301248317539 492519626127244951872476309)
      ·
        refine ⟨23086857474714607119022327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 492519626127244951872476309 23086857474714607119022327)
        ·
          refine ⟨34630286212071910678533491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23086857474714607119022327 34630286212071910678533491)
          ·
            refine ⟨51945429318107866017800237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34630286212071910678533491 51945429318107866017800237)
            ·
              refine ⟨19479535994290449756675089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51945429318107866017800237 19479535994290449756675089)
              ·
                refine ⟨14609651995717837317506317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19479535994290449756675089 14609651995717837317506317)
                ·
                  refine ⟨5478619498394188994064869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14609651995717837317506317 5478619498394188994064869)
                  ·
                    refine ⟨1027241155948910436387163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5478619498394188994064869 1027241155948910436387163)
                    ·
                      rfl

theorem cell23_6001635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 4].length) (baseStart_6001635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001635 prefixEnd_6001635 := by exact prefixLift 6001635
  have htrace : WordTrace (prefixWord ++ tailWord_6001635) baseStart_6001635 baseEnd_6001635 := by
    simpa [prefixWord, tailWord_6001635, baseEnd_6001635] using wordTrace_append hprefix tailTrace_6001635
  have hstable : (prefixWord ++ tailWord_6001635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001635).length < 2 ^ (prefixWord ++ tailWord_6001635).sum := by decide
  have hdescent : baseEnd_6001635 < baseStart_6001635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001642 : List Nat := [3, 1, 3, 1, 2, 4, 1, 1, 2, 1, 4]
def baseStart_6001642 : Nat := 118140960795 + 6001642 * 2 ^ 59
def prefixEnd_6001642 : Nat := 4983230072969 + 3 ^ 40 * 6001642 * 2
def baseEnd_6001642 : Nat := 3081727062211312781773957

theorem tailTrace_6001642 : CollatzResearch.WordTrace tailWord_6001642 prefixEnd_6001642 3081727062211312781773957 := by
  unfold tailWord_6001642
  simp only [CollatzResearch.WordTrace]
  refine ⟨54724466730770876923595795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145931911282055671796255453 54724466730770876923595795)
  ·
    refine ⟨82086700096156315385393693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54724466730770876923595795 82086700096156315385393693)
    ·
      refine ⟨30782512536058618269522635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82086700096156315385393693 30782512536058618269522635)
      ·
        refine ⟨46173768804087927404283953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30782512536058618269522635 46173768804087927404283953)
        ·
          refine ⟨34630326603065945553212965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46173768804087927404283953 34630326603065945553212965)
          ·
            refine ⟨6493186238074864791227431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34630326603065945553212965 6493186238074864791227431)
            ·
              refine ⟨9739779357112297186841147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6493186238074864791227431 9739779357112297186841147)
              ·
                refine ⟨14609669035668445780261721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9739779357112297186841147 14609669035668445780261721)
                ·
                  refine ⟨10957251776751334335196291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14609669035668445780261721 10957251776751334335196291)
                  ·
                    refine ⟨16435877665127001502794437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10957251776751334335196291 16435877665127001502794437)
                    ·
                      refine ⟨3081727062211312781773957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16435877665127001502794437 3081727062211312781773957)
                      ·
                        rfl

theorem cell23_6001642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_6001642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001642 prefixEnd_6001642 := by exact prefixLift 6001642
  have htrace : WordTrace (prefixWord ++ tailWord_6001642) baseStart_6001642 baseEnd_6001642 := by
    simpa [prefixWord, tailWord_6001642, baseEnd_6001642] using wordTrace_append hprefix tailTrace_6001642
  have hstable : (prefixWord ++ tailWord_6001642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001642).length < 2 ^ (prefixWord ++ tailWord_6001642).sum := by decide
  have hdescent : baseEnd_6001642 < baseStart_6001642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001658 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3]
def baseStart_6001658 : Nat := 118140960795 + 6001658 * 2 ^ 59
def prefixEnd_6001658 : Nat := 4983230072969 + 3 ^ 40 * 6001658 * 2
def baseEnd_6001658 : Nat := 3081735277901784719173883

theorem tailTrace_6001658 : CollatzResearch.WordTrace tailWord_6001658 prefixEnd_6001658 3081735277901784719173883 := by
  unfold tailWord_6001658
  simp only [CollatzResearch.WordTrace]
  refine ⟨54724612622756385606741407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145932300327350361617977085 54724612622756385606741407)
  ·
    refine ⟨82086918934134578410112111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54724612622756385606741407 82086918934134578410112111)
    ·
      refine ⟨123130378401201867615168167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82086918934134578410112111 123130378401201867615168167)
      ·
        refine ⟨184695567601802801422752251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123130378401201867615168167 184695567601802801422752251)
        ·
          refine ⟨277043351402704202134128377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184695567601802801422752251 277043351402704202134128377)
          ·
            refine ⟨207782513552028151600596283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277043351402704202134128377 207782513552028151600596283)
            ·
              refine ⟨311673770328042227400894425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207782513552028151600596283 311673770328042227400894425)
              ·
                refine ⟨233755327746031670550670819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 311673770328042227400894425 233755327746031670550670819)
                ·
                  refine ⟨350632991619047505826006229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233755327746031670550670819 350632991619047505826006229)
                  ·
                    refine ⟨8217960741071425917797021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 350632991619047505826006229 8217960741071425917797021)
                    ·
                      refine ⟨3081735277901784719173883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8217960741071425917797021 3081735277901784719173883)
                      ·
                        rfl

theorem cell23_6001658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3].length) (baseStart_6001658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001658 prefixEnd_6001658 := by exact prefixLift 6001658
  have htrace : WordTrace (prefixWord ++ tailWord_6001658) baseStart_6001658 baseEnd_6001658 := by
    simpa [prefixWord, tailWord_6001658, baseEnd_6001658] using wordTrace_append hprefix tailTrace_6001658
  have hstable : (prefixWord ++ tailWord_6001658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001658).length < 2 ^ (prefixWord ++ tailWord_6001658).sum := by decide
  have hdescent : baseEnd_6001658 < baseStart_6001658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001665 : List Nat := [1, 2, 4, 1, 2, 2, 3, 2, 6]
def baseStart_6001665 : Nat := 118140960795 + 6001665 * 2 ^ 59
def prefixEnd_6001665 : Nat := 4983230072969 + 3 ^ 40 * 6001665 * 2
def baseEnd_6001665 : Nat := 342415430251818465754039

theorem tailTrace_6001665 : CollatzResearch.WordTrace tailWord_6001665 prefixEnd_6001665 342415430251818465754039 := by
  unfold tailWord_6001665
  simp only [CollatzResearch.WordTrace]
  refine ⟨218898705802000182622470449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145932470534666788414980299 218898705802000182622470449)
  ·
    refine ⟨164174029351500136966852837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218898705802000182622470449 164174029351500136966852837)
    ·
      refine ⟨30782630503406275681284907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164174029351500136966852837 30782630503406275681284907)
      ·
        refine ⟨46173945755109413521927361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30782630503406275681284907 46173945755109413521927361)
        ·
          refine ⟨34630459316332060141445521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46173945755109413521927361 34630459316332060141445521)
          ·
            refine ⟨25972844487249045106084141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34630459316332060141445521 25972844487249045106084141)
            ·
              refine ⟨9739816682718391914781553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25972844487249045106084141 9739816682718391914781553)
              ·
                refine ⟨7304862512038793936086165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9739816682718391914781553 7304862512038793936086165)
                ·
                  refine ⟨342415430251818465754039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7304862512038793936086165 342415430251818465754039)
                  ·
                    rfl

theorem cell23_6001665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 6].length) (baseStart_6001665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001665 prefixEnd_6001665 := by exact prefixLift 6001665
  have htrace : WordTrace (prefixWord ++ tailWord_6001665) baseStart_6001665 baseEnd_6001665 := by
    simpa [prefixWord, tailWord_6001665, baseEnd_6001665] using wordTrace_append hprefix tailTrace_6001665
  have hstable : (prefixWord ++ tailWord_6001665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001665).length < 2 ^ (prefixWord ++ tailWord_6001665).sum := by decide
  have hdescent : baseEnd_6001665 < baseStart_6001665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001695 : List Nat := [1, 1, 2, 4, 1, 3, 1, 4, 1, 5]
def baseStart_6001695 : Nat := 118140960795 + 6001695 * 2 ^ 59
def prefixEnd_6001695 : Nat := 4983230072969 + 3 ^ 40 * 6001695 * 2
def baseEnd_6001695 : Nat := 1027251425562000358137071

theorem tailTrace_6001695 : CollatzResearch.WordTrace tailWord_6001695 prefixEnd_6001695 1027251425562000358137071 := by
  unfold tailWord_6001695
  simp only [CollatzResearch.WordTrace]
  refine ⟨218899799991891497746062539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145933199994594331830708359 218899799991891497746062539)
  ·
    refine ⟨328349699987837246619093809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218899799991891497746062539 328349699987837246619093809)
    ·
      refine ⟨246262274990877934964320357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328349699987837246619093809 246262274990877934964320357)
      ·
        refine ⟨46174176560789612805810067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246262274990877934964320357 46174176560789612805810067)
        ·
          refine ⟨69261264841184419208715101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46174176560789612805810067 69261264841184419208715101)
          ·
            refine ⟨25972974315444157203268163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69261264841184419208715101 25972974315444157203268163)
            ·
              refine ⟨38959461473166235804902245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25972974315444157203268163 38959461473166235804902245)
              ·
                refine ⟨7304899026218669213419171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38959461473166235804902245 7304899026218669213419171)
                ·
                  refine ⟨10957348539328003820128757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7304899026218669213419171 10957348539328003820128757)
                  ·
                    refine ⟨1027251425562000358137071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10957348539328003820128757 1027251425562000358137071)
                    ·
                      rfl

theorem cell23_6001695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 5].length) (baseStart_6001695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001695 prefixEnd_6001695 := by exact prefixLift 6001695
  have htrace : WordTrace (prefixWord ++ tailWord_6001695) baseStart_6001695 baseEnd_6001695 := by
    simpa [prefixWord, tailWord_6001695, baseEnd_6001695] using wordTrace_append hprefix tailTrace_6001695
  have hstable : (prefixWord ++ tailWord_6001695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001695).length < 2 ^ (prefixWord ++ tailWord_6001695).sum := by decide
  have hdescent : baseEnd_6001695 < baseStart_6001695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001708 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 3, 6]
def baseStart_6001708 : Nat := 118140960795 + 6001708 * 2 ^ 59
def prefixEnd_6001708 : Nat := 4983230072969 + 3 ^ 40 * 6001708 * 2
def baseEnd_6001708 : Nat := 1027253650644836507849551

theorem tailTrace_6001708 : CollatzResearch.WordTrace tailWord_6001708 prefixEnd_6001708 1027253650644836507849551 := by
  unfold tailWord_6001708
  simp only [CollatzResearch.WordTrace]
  refine ⟨109450137070422200483142889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145933516093896267310857185 109450137070422200483142889)
  ·
    refine ⟨82087602802816650362357167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109450137070422200483142889 82087602802816650362357167)
    ·
      refine ⟨123131404204224975543535751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82087602802816650362357167 123131404204224975543535751)
      ·
        refine ⟨184697106306337463315303627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123131404204224975543535751 184697106306337463315303627)
        ·
          refine ⟨277045659459506194972955441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184697106306337463315303627 277045659459506194972955441)
          ·
            refine ⟨207784244594629646229716581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277045659459506194972955441 207784244594629646229716581)
            ·
              refine ⟨38959545861493058668071859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 207784244594629646229716581 38959545861493058668071859)
              ·
                refine ⟨58439318792239588002107789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38959545861493058668071859 58439318792239588002107789)
                ·
                  refine ⟨21914744547089845500790421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58439318792239588002107789 21914744547089845500790421)
                  ·
                    refine ⟨1027253650644836507849551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21914744547089845500790421 1027253650644836507849551)
                    ·
                      rfl

theorem cell23_6001708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_6001708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001708 prefixEnd_6001708 := by exact prefixLift 6001708
  have htrace : WordTrace (prefixWord ++ tailWord_6001708) baseStart_6001708 baseEnd_6001708 := by
    simpa [prefixWord, tailWord_6001708, baseEnd_6001708] using wordTrace_append hprefix tailTrace_6001708
  have hstable : (prefixWord ++ tailWord_6001708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001708).length < 2 ^ (prefixWord ++ tailWord_6001708).sum := by decide
  have hdescent : baseEnd_6001708 < baseStart_6001708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001726 : List Nat := [4, 2, 1, 3, 1, 3, 1, 1, 3, 1, 3]
def baseStart_6001726 : Nat := 118140960795 + 6001726 * 2 ^ 59
def prefixEnd_6001726 : Nat := 4983230072969 + 3 ^ 40 * 6001726 * 2
def baseEnd_6001726 : Nat := 3081770194586290453123571

theorem tailTrace_6001726 : CollatzResearch.WordTrace tailWord_6001726 prefixEnd_6001726 3081770194586290453123571 := by
  unfold tailWord_6001726
  simp only [CollatzResearch.WordTrace]
  refine ⟨27362616331847398755055129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145933953769852793360294021 27362616331847398755055129)
  ·
    refine ⟨20521962248885549066291347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27362616331847398755055129 20521962248885549066291347)
    ·
      refine ⟨30782943373328323599437021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20521962248885549066291347 30782943373328323599437021)
      ·
        refine ⟨11543603764998121349788883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30782943373328323599437021 11543603764998121349788883)
        ·
          refine ⟨17315405647497182024683325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11543603764998121349788883 17315405647497182024683325)
          ·
            refine ⟨6493277117811443259256247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17315405647497182024683325 6493277117811443259256247)
            ·
              refine ⟨9739915676717164888884371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6493277117811443259256247 9739915676717164888884371)
              ·
                refine ⟨14609873515075747333326557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9739915676717164888884371 14609873515075747333326557)
                ·
                  refine ⟨5478702568153405249997459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14609873515075747333326557 5478702568153405249997459)
                  ·
                    refine ⟨8218053852230107874996189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5478702568153405249997459 8218053852230107874996189)
                    ·
                      refine ⟨3081770194586290453123571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8218053852230107874996189 3081770194586290453123571)
                      ·
                        rfl

theorem cell23_6001726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_6001726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001726 prefixEnd_6001726 := by exact prefixLift 6001726
  have htrace : WordTrace (prefixWord ++ tailWord_6001726) baseStart_6001726 baseEnd_6001726 := by
    simpa [prefixWord, tailWord_6001726, baseEnd_6001726] using wordTrace_append hprefix tailTrace_6001726
  have hstable : (prefixWord ++ tailWord_6001726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001726).length < 2 ^ (prefixWord ++ tailWord_6001726).sum := by decide
  have hdescent : baseEnd_6001726 < baseStart_6001726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001728 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 6]
def baseStart_6001728 : Nat := 118140960795 + 6001728 * 2 ^ 59
def prefixEnd_6001728 : Nat := 4983230072969 + 3 ^ 40 * 6001728 * 2
def baseEnd_6001728 : Nat := 3081771221547599445298561

theorem tailTrace_6001728 : CollatzResearch.WordTrace tailWord_6001728 prefixEnd_6001728 3081771221547599445298561 := by
  unfold tailWord_6001728
  simp only [CollatzResearch.WordTrace]
  refine ⟨109450501800385972191006919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145934002400514629588009225 109450501800385972191006919)
  ·
    refine ⟨164175752700578958286510379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109450501800385972191006919 164175752700578958286510379)
    ·
      refine ⟨246263629050868437429765569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164175752700578958286510379 246263629050868437429765569)
      ·
        refine ⟨184697721788151328072324177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246263629050868437429765569 184697721788151328072324177)
        ·
          refine ⟨138523291341113496054243133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184697721788151328072324177 138523291341113496054243133)
          ·
            refine ⟨51946234252917561020341175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138523291341113496054243133 51946234252917561020341175)
            ·
              refine ⟨77919351379376341530511763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51946234252917561020341175 77919351379376341530511763)
              ·
                refine ⟨116879027069064512295767645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77919351379376341530511763 116879027069064512295767645)
                ·
                  refine ⟨43829635150899192110912867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116879027069064512295767645 43829635150899192110912867)
                  ·
                    refine ⟨65744452726348788166369301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43829635150899192110912867 65744452726348788166369301)
                    ·
                      refine ⟨3081771221547599445298561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65744452726348788166369301 3081771221547599445298561)
                      ·
                        rfl

theorem cell23_6001728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_6001728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001728 prefixEnd_6001728 := by exact prefixLift 6001728
  have htrace : WordTrace (prefixWord ++ tailWord_6001728) baseStart_6001728 baseEnd_6001728 := by
    simpa [prefixWord, tailWord_6001728, baseEnd_6001728] using wordTrace_append hprefix tailTrace_6001728
  have hstable : (prefixWord ++ tailWord_6001728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001728).length < 2 ^ (prefixWord ++ tailWord_6001728).sum := by decide
  have hdescent : baseEnd_6001728 < baseStart_6001728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001735 : List Nat := [1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 5]
def baseStart_6001735 : Nat := 118140960795 + 6001735 * 2 ^ 59
def prefixEnd_6001735 : Nat := 4983230072969 + 3 ^ 40 * 6001735 * 2
def baseEnd_6001735 : Nat := 3081774815912180917911029

theorem tailTrace_6001735 : CollatzResearch.WordTrace tailWord_6001735 prefixEnd_6001735 3081774815912180917911029 := by
  unfold tailWord_6001735
  simp only [CollatzResearch.WordTrace]
  refine ⟨218901258911746584577518659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145934172607831056385012439 218901258911746584577518659)
  ·
    refine ⟨328351888367619876866277989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218901258911746584577518659 328351888367619876866277989)
    ·
      refine ⟨61565979068928726912427123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 328351888367619876866277989 61565979068928726912427123)
      ·
        refine ⟨92348968603393090368640685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61565979068928726912427123 92348968603393090368640685)
        ·
          refine ⟨34630863226272408888240257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92348968603393090368640685 34630863226272408888240257)
          ·
            refine ⟨25973147419704306666180193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34630863226272408888240257 25973147419704306666180193)
            ·
              refine ⟨19479860564778229999635145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25973147419704306666180193 19479860564778229999635145)
              ·
                refine ⟨14609895423583672499726359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19479860564778229999635145 14609895423583672499726359)
                ·
                  refine ⟨21914843135375508749589539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14609895423583672499726359 21914843135375508749589539)
                  ·
                    refine ⟨32872264703063263124384309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21914843135375508749589539 32872264703063263124384309)
                    ·
                      refine ⟨3081774815912180917911029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32872264703063263124384309 3081774815912180917911029)
                      ·
                        rfl

theorem cell23_6001735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_6001735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001735 prefixEnd_6001735 := by exact prefixLift 6001735
  have htrace : WordTrace (prefixWord ++ tailWord_6001735) baseStart_6001735 baseEnd_6001735 := by
    simpa [prefixWord, tailWord_6001735, baseEnd_6001735] using wordTrace_append hprefix tailTrace_6001735
  have hstable : (prefixWord ++ tailWord_6001735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001735).length < 2 ^ (prefixWord ++ tailWord_6001735).sum := by decide
  have hdescent : baseEnd_6001735 < baseStart_6001735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001738 : List Nat := [3, 1, 2, 1, 1, 2, 3, 10]
def baseStart_6001738 : Nat := 118140960795 + 6001738 * 2 ^ 59
def prefixEnd_6001738 : Nat := 4983230072969 + 3 ^ 40 * 6001738 * 2
def baseEnd_6001738 : Nat := 114139865050153496524945

theorem tailTrace_6001738 : CollatzResearch.WordTrace tailWord_6001738 prefixEnd_6001738 114139865050153496524945 := by
  unfold tailWord_6001738
  simp only [CollatzResearch.WordTrace]
  refine ⟨54725342082683929022469467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145934245553823810726585245 54725342082683929022469467)
  ·
    refine ⟨82088013124025893533704201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54725342082683929022469467 82088013124025893533704201)
    ·
      refine ⟨61566009843019420150278151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82088013124025893533704201 61566009843019420150278151)
      ·
        refine ⟨92349014764529130225417227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61566009843019420150278151 92349014764529130225417227)
        ·
          refine ⟨138523522146793695338125841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92349014764529130225417227 138523522146793695338125841)
          ·
            refine ⟨103892641610095271503594381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138523522146793695338125841 103892641610095271503594381)
            ·
              refine ⟨38959740603785726813847893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103892641610095271503594381 38959740603785726813847893)
              ·
                refine ⟨114139865050153496524945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38959740603785726813847893 114139865050153496524945)
                ·
                  rfl

theorem cell23_6001738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 10].length) (baseStart_6001738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001738 prefixEnd_6001738 := by exact prefixLift 6001738
  have htrace : WordTrace (prefixWord ++ tailWord_6001738) baseStart_6001738 baseEnd_6001738 := by
    simpa [prefixWord, tailWord_6001738, baseEnd_6001738] using wordTrace_append hprefix tailTrace_6001738
  have hstable : (prefixWord ++ tailWord_6001738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001738).length < 2 ^ (prefixWord ++ tailWord_6001738).sum := by decide
  have hdescent : baseEnd_6001738 < baseStart_6001738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001742 : List Nat := [4, 1, 1, 1, 1, 3, 3, 3, 2, 4]
def baseStart_6001742 : Nat := 118140960795 + 6001742 * 2 ^ 59
def prefixEnd_6001742 : Nat := 4983230072969 + 3 ^ 40 * 6001742 * 2
def baseEnd_6001742 : Nat := 1027259470092254130174499

theorem tailTrace_6001742 : CollatzResearch.WordTrace tailWord_6001742 prefixEnd_6001742 1027259470092254130174499 := by
  unfold tailWord_6001742
  simp only [CollatzResearch.WordTrace]
  refine ⟨27362689277840153096627935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145934342815147483182015653 27362689277840153096627935)
  ·
    refine ⟨41044033916760229644941903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27362689277840153096627935 41044033916760229644941903)
    ·
      refine ⟨61566050875140344467412855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41044033916760229644941903 61566050875140344467412855)
      ·
        refine ⟨92349076312710516701119283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61566050875140344467412855 92349076312710516701119283)
        ·
          refine ⟨138523614469065775051678925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92349076312710516701119283 138523614469065775051678925)
          ·
            refine ⟨51946355425899665644379597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138523614469065775051678925 51946355425899665644379597)
            ·
              refine ⟨19479883284712374616642349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51946355425899665644379597 19479883284712374616642349)
              ·
                refine ⟨7304956231767140481240881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19479883284712374616642349 7304956231767140481240881)
                ·
                  refine ⟨5478717173825355360930661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7304956231767140481240881 5478717173825355360930661)
                  ·
                    refine ⟨1027259470092254130174499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5478717173825355360930661 1027259470092254130174499)
                    ·
                      rfl

theorem cell23_6001742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_6001742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001742 prefixEnd_6001742 := by exact prefixLift 6001742
  have htrace : WordTrace (prefixWord ++ tailWord_6001742) baseStart_6001742 baseEnd_6001742 := by
    simpa [prefixWord, tailWord_6001742, baseEnd_6001742] using wordTrace_append hprefix tailTrace_6001742
  have hstable : (prefixWord ++ tailWord_6001742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001742).length < 2 ^ (prefixWord ++ tailWord_6001742).sum := by decide
  have hdescent : baseEnd_6001742 < baseStart_6001742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001762 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_6001762 : Nat := 118140960795 + 6001762 * 2 ^ 59
def prefixEnd_6001762 : Nat := 4983230072969 + 3 ^ 40 * 6001762 * 2
def baseEnd_6001762 : Nat := 3081788679889852312273405

theorem tailTrace_6001762 : CollatzResearch.WordTrace tailWord_6001762 prefixEnd_6001762 3081788679889852312273405 := by
  unfold tailWord_6001762
  simp only [CollatzResearch.WordTrace]
  refine ⟨54725560920662192047187885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145934829121765845459167693 54725560920662192047187885)
  ·
    refine ⟨20522085345248322017695457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54725560920662192047187885 20522085345248322017695457)
    ·
      refine ⟨15391564008936241513271593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20522085345248322017695457 15391564008936241513271593)
      ·
        refine ⟨11543673006702181134953695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15391564008936241513271593 11543673006702181134953695)
        ·
          refine ⟨17315509510053271702430543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11543673006702181134953695 17315509510053271702430543)
          ·
            refine ⟨25973264265079907553645815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17315509510053271702430543 25973264265079907553645815)
            ·
              refine ⟨38959896397619861330468723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25973264265079907553645815 38959896397619861330468723)
              ·
                refine ⟨58439844596429791995703085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38959896397619861330468723 58439844596429791995703085)
                ·
                  refine ⟨21914941723661171998388657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58439844596429791995703085 21914941723661171998388657)
                  ·
                    refine ⟨16436206292745878998791493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21914941723661171998388657 16436206292745878998791493)
                    ·
                      refine ⟨3081788679889852312273405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16436206292745878998791493 3081788679889852312273405)
                      ·
                        rfl

theorem cell23_6001762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_6001762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001762 prefixEnd_6001762 := by exact prefixLift 6001762
  have htrace : WordTrace (prefixWord ++ tailWord_6001762) baseStart_6001762 baseEnd_6001762 := by
    simpa [prefixWord, tailWord_6001762, baseEnd_6001762] using wordTrace_append hprefix tailTrace_6001762
  have hstable : (prefixWord ++ tailWord_6001762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001762).length < 2 ^ (prefixWord ++ tailWord_6001762).sum := by decide
  have hdescent : baseEnd_6001762 < baseStart_6001762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001769 : List Nat := [1, 2, 1, 1, 1, 7, 3, 1, 1, 2, 3]
def baseStart_6001769 : Nat := 118140960795 + 6001769 * 2 ^ 59
def prefixEnd_6001769 : Nat := 4983230072969 + 3 ^ 40 * 6001769 * 2
def baseEnd_6001769 : Nat := 3081792274254433784885873

theorem tailTrace_6001769 : CollatzResearch.WordTrace tailWord_6001769 prefixEnd_6001769 3081792274254433784885873 := by
  unfold tailWord_6001769
  simp only [CollatzResearch.WordTrace]
  refine ⟨218902498993623408384256361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145934999329082272256170907 218902498993623408384256361)
  ·
    refine ⟨164176874245217556288192271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218902498993623408384256361 164176874245217556288192271)
    ·
      refine ⟨246265311367826334432288407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164176874245217556288192271 246265311367826334432288407)
      ·
        refine ⟨369397967051739501648432611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246265311367826334432288407 369397967051739501648432611)
        ·
          refine ⟨554096950577609252472648917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369397967051739501648432611 554096950577609252472648917)
          ·
            refine ⟨12986647279162716854827709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 554096950577609252472648917 12986647279162716854827709)
            ·
              refine ⟨4869992729686018820560391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12986647279162716854827709 4869992729686018820560391)
              ·
                refine ⟨7304989094529028230840587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4869992729686018820560391 7304989094529028230840587)
                ·
                  refine ⟨10957483641793542346260881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7304989094529028230840587 10957483641793542346260881)
                  ·
                    refine ⟨8218112731345156759695661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10957483641793542346260881 8218112731345156759695661)
                    ·
                      refine ⟨3081792274254433784885873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8218112731345156759695661 3081792274254433784885873)
                      ·
                        rfl

theorem cell23_6001769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 1, 2, 3].length) (baseStart_6001769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001769 prefixEnd_6001769 := by exact prefixLift 6001769
  have htrace : WordTrace (prefixWord ++ tailWord_6001769) baseStart_6001769 baseEnd_6001769 := by
    simpa [prefixWord, tailWord_6001769, baseEnd_6001769] using wordTrace_append hprefix tailTrace_6001769
  have hstable : (prefixWord ++ tailWord_6001769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001769).length < 2 ^ (prefixWord ++ tailWord_6001769).sum := by decide
  have hdescent : baseEnd_6001769 < baseStart_6001769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001782 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3]
def baseStart_6001782 : Nat := 118140960795 + 6001782 * 2 ^ 59
def prefixEnd_6001782 : Nat := 4983230072969 + 3 ^ 40 * 6001782 * 2
def baseEnd_6001782 : Nat := 3081798949502942234023313

theorem tailTrace_6001782 : CollatzResearch.WordTrace tailWord_6001782 prefixEnd_6001782 3081798949502942234023313 := by
  unfold tailWord_6001782
  simp only [CollatzResearch.WordTrace]
  refine ⟨13681435821411019475279975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145935315428384207736319733 13681435821411019475279975)
  ·
    refine ⟨20522153732116529212919963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13681435821411019475279975 20522153732116529212919963)
    ·
      refine ⟨30783230598174793819379945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20522153732116529212919963 30783230598174793819379945)
      ·
        refine ⟨23087422948631095364534959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30783230598174793819379945 23087422948631095364534959)
        ·
          refine ⟨34631134422946643046802439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23087422948631095364534959 34631134422946643046802439)
          ·
            refine ⟨51946701634419964570203659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34631134422946643046802439 51946701634419964570203659)
            ·
              refine ⟨77920052451629946855305489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51946701634419964570203659 77920052451629946855305489)
              ·
                refine ⟨58440039338722460141479117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77920052451629946855305489 58440039338722460141479117)
                ·
                  refine ⟨21915014752020922553054669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58440039338722460141479117 21915014752020922553054669)
                  ·
                    refine ⟨8218130532007845957395501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21915014752020922553054669 8218130532007845957395501)
                    ·
                      refine ⟨3081798949502942234023313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8218130532007845957395501 3081798949502942234023313)
                      ·
                        rfl

theorem cell23_6001782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_6001782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001782 prefixEnd_6001782 := by exact prefixLift 6001782
  have htrace : WordTrace (prefixWord ++ tailWord_6001782) baseStart_6001782 baseEnd_6001782 := by
    simpa [prefixWord, tailWord_6001782, baseEnd_6001782] using wordTrace_append hprefix tailTrace_6001782
  have hstable : (prefixWord ++ tailWord_6001782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001782).length < 2 ^ (prefixWord ++ tailWord_6001782).sum := by decide
  have hdescent : baseEnd_6001782 < baseStart_6001782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001792 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 3, 3, 2]
def baseStart_6001792 : Nat := 118140960795 + 6001792 * 2 ^ 59
def prefixEnd_6001792 : Nat := 4983230072969 + 3 ^ 40 * 6001792 * 2
def baseEnd_6001792 : Nat := 3081804084309487194898267

theorem tailTrace_6001792 : CollatzResearch.WordTrace tailWord_6001792 prefixEnd_6001792 3081804084309487194898267 := by
  unfold tailWord_6001792
  simp only [CollatzResearch.WordTrace]
  refine ⟨109451668936270041656171815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145935558581693388874895753 109451668936270041656171815)
  ·
    refine ⟨164177503404405062484257723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109451668936270041656171815 164177503404405062484257723)
    ·
      refine ⟨246266255106607593726386585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164177503404405062484257723 246266255106607593726386585)
      ·
        refine ⟨184699691329955695294789939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246266255106607593726386585 184699691329955695294789939)
        ·
          refine ⟨277049536994933542942184909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184699691329955695294789939 277049536994933542942184909)
          ·
            refine ⟨103893576373100078603319341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277049536994933542942184909 103893576373100078603319341)
            ·
              refine ⟨38960091139912529476244753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103893576373100078603319341 38960091139912529476244753)
              ·
                refine ⟨29220068354934397107183565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38960091139912529476244753 29220068354934397107183565)
                ·
                  refine ⟨10957525633100398915193837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29220068354934397107183565 10957525633100398915193837)
                  ·
                    refine ⟨4109072112412649593197689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10957525633100398915193837 4109072112412649593197689)
                    ·
                      refine ⟨3081804084309487194898267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4109072112412649593197689 3081804084309487194898267)
                      ·
                        rfl

theorem cell23_6001792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 3, 3, 2].length) (baseStart_6001792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001792 prefixEnd_6001792 := by exact prefixLift 6001792
  have htrace : WordTrace (prefixWord ++ tailWord_6001792) baseStart_6001792 baseEnd_6001792 := by
    simpa [prefixWord, tailWord_6001792, baseEnd_6001792] using wordTrace_append hprefix tailTrace_6001792
  have hstable : (prefixWord ++ tailWord_6001792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001792).length < 2 ^ (prefixWord ++ tailWord_6001792).sum := by decide
  have hdescent : baseEnd_6001792 < baseStart_6001792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001825 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 1, 3, 5]
def baseStart_6001825 : Nat := 118140960795 + 6001825 * 2 ^ 59
def prefixEnd_6001825 : Nat := 4983230072969 + 3 ^ 40 * 6001825 * 2
def baseEnd_6001825 : Nat := 3081821029171085565785615

theorem tailTrace_6001825 : CollatzResearch.WordTrace tailWord_6001825 prefixEnd_6001825 3081821029171085565785615 := by
  unfold tailWord_6001825
  simp only [CollatzResearch.WordTrace]
  refine ⟨218904541481420529948294929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145936360987613686632196619 218904541481420529948294929)
  ·
    refine ⟨164178406111065397461221197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218904541481420529948294929 164178406111065397461221197)
    ·
      refine ⟨61566902291649524047957949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164178406111065397461221197 61566902291649524047957949)
      ·
        refine ⟨23087588359368571517984231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61566902291649524047957949 23087588359368571517984231)
        ·
          refine ⟨34631382539052857276976347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23087588359368571517984231 34631382539052857276976347)
          ·
            refine ⟨51947073808579285915464521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34631382539052857276976347 51947073808579285915464521)
            ·
              refine ⟨38960305356434464436598391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51947073808579285915464521 38960305356434464436598391)
              ·
                refine ⟨58440458034651696654897587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38960305356434464436598391 58440458034651696654897587)
                ·
                  refine ⟨87660687051977544982346381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58440458034651696654897587 87660687051977544982346381)
                  ·
                    refine ⟨32872757644491579368379893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87660687051977544982346381 32872757644491579368379893)
                    ·
                      refine ⟨3081821029171085565785615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32872757644491579368379893 3081821029171085565785615)
                      ·
                        rfl

theorem cell23_6001825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_6001825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001825 prefixEnd_6001825 := by exact prefixLift 6001825
  have htrace : WordTrace (prefixWord ++ tailWord_6001825) baseStart_6001825 baseEnd_6001825 := by
    simpa [prefixWord, tailWord_6001825, baseEnd_6001825] using wordTrace_append hprefix tailTrace_6001825
  have hstable : (prefixWord ++ tailWord_6001825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001825).length < 2 ^ (prefixWord ++ tailWord_6001825).sum := by decide
  have hdescent : baseEnd_6001825 < baseStart_6001825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001852 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 2, 2, 4]
def baseStart_6001852 : Nat := 118140960795 + 6001852 * 2 ^ 59
def prefixEnd_6001852 : Nat := 4983230072969 + 3 ^ 40 * 6001852 * 2
def baseEnd_6001852 : Nat := 3081834893148756960147991

theorem tailTrace_6001852 : CollatzResearch.WordTrace tailWord_6001852 prefixEnd_6001852 3081834893148756960147991 := by
  unfold tailWord_6001852
  simp only [CollatzResearch.WordTrace]
  refine ⟨109452763126161356779763905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145937017501548475706351873 109452763126161356779763905)
  ·
    refine ⟨82089572344621017584822929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109452763126161356779763905 82089572344621017584822929)
    ·
      refine ⟨61567179258465763188617197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82089572344621017584822929 61567179258465763188617197)
      ·
        refine ⟨23087692221924661195731449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61567179258465763188617197 23087692221924661195731449)
        ·
          refine ⟨17315769166443495896798587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23087692221924661195731449 17315769166443495896798587)
          ·
            refine ⟨25973653749665243845197881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17315769166443495896798587 25973653749665243845197881)
            ·
              refine ⟨19480240312248932883898411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25973653749665243845197881 19480240312248932883898411)
              ·
                refine ⟨29220360468373399325847617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19480240312248932883898411 29220360468373399325847617)
                ·
                  refine ⟨21915270351280049494385713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29220360468373399325847617 21915270351280049494385713)
                  ·
                    refine ⟨16436452763460037120789285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21915270351280049494385713 16436452763460037120789285)
                    ·
                      refine ⟨3081834893148756960147991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16436452763460037120789285 3081834893148756960147991)
                      ·
                        rfl

theorem cell23_6001852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_6001852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001852 prefixEnd_6001852 := by exact prefixLift 6001852
  have htrace : WordTrace (prefixWord ++ tailWord_6001852) baseStart_6001852 baseEnd_6001852 := by
    simpa [prefixWord, tailWord_6001852, baseEnd_6001852] using wordTrace_append hprefix tailTrace_6001852
  have hstable : (prefixWord ++ tailWord_6001852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001852).length < 2 ^ (prefixWord ++ tailWord_6001852).sum := by decide
  have hdescent : baseEnd_6001852 < baseStart_6001852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001856 : List Nat := [2, 1, 1, 2, 6, 2, 1, 1, 1, 4, 2]
def baseStart_6001856 : Nat := 118140960795 + 6001856 * 2 ^ 59
def prefixEnd_6001856 : Nat := 4983230072969 + 3 ^ 40 * 6001856 * 2
def baseEnd_6001856 : Nat := 3081836947071374944497973

theorem tailTrace_6001856 : CollatzResearch.WordTrace tailWord_6001856 prefixEnd_6001856 3081836947071374944497973 := by
  unfold tailWord_6001856
  simp only [CollatzResearch.WordTrace]
  refine ⟨109452836072154111121336711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145937114762872148161782281 109452836072154111121336711)
  ·
    refine ⟨164179254108231166682005067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109452836072154111121336711 164179254108231166682005067)
    ·
      refine ⟨246268881162346750023007601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164179254108231166682005067 246268881162346750023007601)
      ·
        refine ⟨184701660871760062517255701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246268881162346750023007601 184701660871760062517255701)
        ·
          refine ⟨8657890353363752930496361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 184701660871760062517255701 8657890353363752930496361)
          ·
            refine ⟨6493417765022814697872271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8657890353363752930496361 6493417765022814697872271)
            ·
              refine ⟨9740126647534222046808407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6493417765022814697872271 9740126647534222046808407)
              ·
                refine ⟨14610189971301333070212611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9740126647534222046808407 14610189971301333070212611)
                ·
                  refine ⟨21915284956951999605318917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14610189971301333070212611 21915284956951999605318917)
                  ·
                    refine ⟨4109115929428499925997297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21915284956951999605318917 4109115929428499925997297)
                    ·
                      refine ⟨3081836947071374944497973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4109115929428499925997297 3081836947071374944497973)
                      ·
                        rfl

theorem cell23_6001856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 1, 4, 2].length) (baseStart_6001856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001856 prefixEnd_6001856 := by exact prefixLift 6001856
  have htrace : WordTrace (prefixWord ++ tailWord_6001856) baseStart_6001856 baseEnd_6001856 := by
    simpa [prefixWord, tailWord_6001856, baseEnd_6001856] using wordTrace_append hprefix tailTrace_6001856
  have hstable : (prefixWord ++ tailWord_6001856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001856).length < 2 ^ (prefixWord ++ tailWord_6001856).sum := by decide
  have hdescent : baseEnd_6001856 < baseStart_6001856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001882 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2]
def baseStart_6001882 : Nat := 118140960795 + 6001882 * 2 ^ 59
def prefixEnd_6001882 : Nat := 4983230072969 + 3 ^ 40 * 6001882 * 2
def baseEnd_6001882 : Nat := 3081850297568391842772853

theorem tailTrace_6001882 : CollatzResearch.WordTrace tailWord_6001882 prefixEnd_6001882 3081850297568391842772853 := by
  unfold tailWord_6001882
  simp only [CollatzResearch.WordTrace]
  refine ⟨54726655110553507170779975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145937746961476019122079933 54726655110553507170779975)
  ·
    refine ⟨82089982665830260756169963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54726655110553507170779975 82089982665830260756169963)
    ·
      refine ⟨123134973998745391134254945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82089982665830260756169963 123134973998745391134254945)
      ·
        refine ⟨92351230499059043350691209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123134973998745391134254945 92351230499059043350691209)
        ·
          refine ⟨69263422874294282513018407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92351230499059043350691209 69263422874294282513018407)
          ·
            refine ⟨103895134311441423769527611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69263422874294282513018407 103895134311441423769527611)
            ·
              refine ⟨155842701467162135654291417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103895134311441423769527611 155842701467162135654291417)
              ·
                refine ⟨116882026100371601740718563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155842701467162135654291417 116882026100371601740718563)
                ·
                  refine ⟨175323039150557402611077845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116882026100371601740718563 175323039150557402611077845)
                  ·
                    refine ⟨4109133730091189123697137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 175323039150557402611077845 4109133730091189123697137)
                    ·
                      refine ⟨3081850297568391842772853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4109133730091189123697137 3081850297568391842772853)
                      ·
                        rfl

theorem cell23_6001882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2].length) (baseStart_6001882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001882 prefixEnd_6001882 := by exact prefixLift 6001882
  have htrace : WordTrace (prefixWord ++ tailWord_6001882) baseStart_6001882 baseEnd_6001882 := by
    simpa [prefixWord, tailWord_6001882, baseEnd_6001882] using wordTrace_append hprefix tailTrace_6001882
  have hstable : (prefixWord ++ tailWord_6001882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001882).length < 2 ^ (prefixWord ++ tailWord_6001882).sum := by decide
  have hdescent : baseEnd_6001882 < baseStart_6001882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001956 : List Nat := [2, 3, 1, 3, 1, 1, 3, 4, 1, 4]
def baseStart_6001956 : Nat := 118140960795 + 6001956 * 2 ^ 59
def prefixEnd_6001956 : Nat := 4983230072969 + 3 ^ 40 * 6001956 * 2
def baseEnd_6001956 : Nat := 1027296098378941517749171

theorem tailTrace_6001956 : CollatzResearch.WordTrace tailWord_6001956 prefixEnd_6001956 1027296098378941517749171 := by
  unfold tailWord_6001956
  simp only [CollatzResearch.WordTrace]
  refine ⟨109454659721972969660656861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145939546295963959547542481 109454659721972969660656861)
  ·
    refine ⟨41045497395739863622746323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109454659721972969660656861 41045497395739863622746323)
    ·
      refine ⟨61568246093609795434119485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41045497395739863622746323 61568246093609795434119485)
      ·
        refine ⟨23088092285103673287794807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61568246093609795434119485 23088092285103673287794807)
        ·
          refine ⟨34632138427655509931692211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23088092285103673287794807 34632138427655509931692211)
          ·
            refine ⟨51948207641483264897538317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34632138427655509931692211 51948207641483264897538317)
            ·
              refine ⟨19480577865556224336576869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51948207641483264897538317 19480577865556224336576869)
              ·
                refine ⟨3652608349791792063108163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19480577865556224336576869 3652608349791792063108163)
                ·
                  refine ⟨5478912524687688094662245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3652608349791792063108163 5478912524687688094662245)
                  ·
                    refine ⟨1027296098378941517749171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5478912524687688094662245 1027296098378941517749171)
                    ·
                      rfl

theorem cell23_6001956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_6001956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001956 prefixEnd_6001956 := by exact prefixLift 6001956
  have htrace : WordTrace (prefixWord ++ tailWord_6001956) baseStart_6001956 baseEnd_6001956 := by
    simpa [prefixWord, tailWord_6001956, baseEnd_6001956] using wordTrace_append hprefix tailTrace_6001956
  have hstable : (prefixWord ++ tailWord_6001956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001956).length < 2 ^ (prefixWord ++ tailWord_6001956).sum := by decide
  have hdescent : baseEnd_6001956 < baseStart_6001956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6001995 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 2, 10]
def baseStart_6001995 : Nat := 118140960795 + 6001995 * 2 ^ 59
def prefixEnd_6001995 : Nat := 4983230072969 + 3 ^ 40 * 6001995 * 2
def baseEnd_6001995 : Nat := 1027302773627449966886611

theorem tailTrace_6001995 : CollatzResearch.WordTrace tailWord_6001995 prefixEnd_6001995 1027302773627449966886611 := by
  unfold tailWord_6001995
  simp only [CollatzResearch.WordTrace]
  refine ⟨218910741890804648981983439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145940494593869765987988959 218910741890804648981983439)
  ·
    refine ⟨328366112836206973472975159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218910741890804648981983439 328366112836206973472975159)
    ·
      refine ⟨492549169254310460209462739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328366112836206973472975159 492549169254310460209462739)
      ·
        refine ⟨738823753881465690314194109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492549169254310460209462739 738823753881465690314194109)
        ·
          refine ⟨277058907705549633867822791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 738823753881465690314194109 277058907705549633867822791)
          ·
            refine ⟨415588361558324450801734187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277058907705549633867822791 415588361558324450801734187)
            ·
              refine ⟨623382542337486676202601281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415588361558324450801734187 623382542337486676202601281)
              ·
                refine ⟨467536906753115007151950961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 623382542337486676202601281 467536906753115007151950961)
                ·
                  refine ⟨350652680064836255363963221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 467536906753115007151950961 350652680064836255363963221)
                  ·
                    refine ⟨1027302773627449966886611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 350652680064836255363963221 1027302773627449966886611)
                    ·
                      rfl

theorem cell23_6001995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 10].length) (baseStart_6001995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6001995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6001995 prefixEnd_6001995 := by exact prefixLift 6001995
  have htrace : WordTrace (prefixWord ++ tailWord_6001995) baseStart_6001995 baseEnd_6001995 := by
    simpa [prefixWord, tailWord_6001995, baseEnd_6001995] using wordTrace_append hprefix tailTrace_6001995
  have hstable : (prefixWord ++ tailWord_6001995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6001995).length < 2 ^ (prefixWord ++ tailWord_6001995).sum := by decide
  have hdescent : baseEnd_6001995 < baseStart_6001995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6001995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002029 : List Nat := [1, 5, 1, 1, 1, 3, 3, 1, 1, 6]
def baseStart_6002029 : Nat := 118140960795 + 6002029 * 2 ^ 59
def prefixEnd_6002029 : Nat := 4983230072969 + 3 ^ 40 * 6002029 * 2
def baseEnd_6002029 : Nat := 1027308593074867589211559

theorem tailTrace_6002029 : CollatzResearch.WordTrace tailWord_6002029 prefixEnd_6002029 1027308593074867589211559 := by
  unfold tailWord_6002029
  simp only [CollatzResearch.WordTrace]
  refine ⟨218911981972681472788721141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145941321315120981859147427 218911981972681472788721141)
  ·
    refine ⟨20522998309938888073942607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218911981972681472788721141 20522998309938888073942607)
    ·
      refine ⟨30784497464908332110913911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20522998309938888073942607 30784497464908332110913911)
      ·
        refine ⟨46176746197362498166370867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30784497464908332110913911 46176746197362498166370867)
        ·
          refine ⟨69265119296043747249556301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46176746197362498166370867 69265119296043747249556301)
          ·
            refine ⟨25974419736016405218583613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69265119296043747249556301 25974419736016405218583613)
            ·
              refine ⟨9740407401006151956968855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25974419736016405218583613 9740407401006151956968855)
              ·
                refine ⟨14610611101509227935453283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9740407401006151956968855 14610611101509227935453283)
                ·
                  refine ⟨21915916652263841903179925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14610611101509227935453283 21915916652263841903179925)
                  ·
                    refine ⟨1027308593074867589211559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21915916652263841903179925 1027308593074867589211559)
                    ·
                      rfl

theorem cell23_6002029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_6002029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002029 prefixEnd_6002029 := by exact prefixLift 6002029
  have htrace : WordTrace (prefixWord ++ tailWord_6002029) baseStart_6002029 baseEnd_6002029 := by
    simpa [prefixWord, tailWord_6002029, baseEnd_6002029] using wordTrace_append hprefix tailTrace_6002029
  have hstable : (prefixWord ++ tailWord_6002029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002029).length < 2 ^ (prefixWord ++ tailWord_6002029).sum := by decide
  have hdescent : baseEnd_6002029 < baseStart_6002029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002032 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 6]
def baseStart_6002032 : Nat := 118140960795 + 6002032 * 2 ^ 59
def prefixEnd_6002032 : Nat := 4983230072969 + 3 ^ 40 * 6002032 * 2
def baseEnd_6002032 : Nat := 3081927319666566255897163

theorem tailTrace_6002032 : CollatzResearch.WordTrace tailWord_6002032 prefixEnd_6002032 3081927319666566255897163 := by
  unfold tailWord_6002032
  simp only [CollatzResearch.WordTrace]
  refine ⟨109456045695835302150540175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145941394261113736200720233 109456045695835302150540175)
  ·
    refine ⟨164184068543752953225810263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109456045695835302150540175 164184068543752953225810263)
    ·
      refine ⟨246276102815629429838715395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164184068543752953225810263 246276102815629429838715395)
      ·
        refine ⟨369414154223444144758073093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246276102815629429838715395 369414154223444144758073093)
        ·
          refine ⟨69265153916895777142138705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 369414154223444144758073093 69265153916895777142138705)
          ·
            refine ⟨51948865437671832856604029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69265153916895777142138705 51948865437671832856604029)
            ·
              refine ⟨19480824539126937321226511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51948865437671832856604029 19480824539126937321226511)
              ·
                refine ⟨29221236808690405981839767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19480824539126937321226511 29221236808690405981839767)
                ·
                  refine ⟨43831855213035608972759651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29221236808690405981839767 43831855213035608972759651)
                  ·
                    refine ⟨65747782819553413459139477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43831855213035608972759651 65747782819553413459139477)
                    ·
                      refine ⟨3081927319666566255897163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65747782819553413459139477 3081927319666566255897163)
                      ·
                        rfl

theorem cell23_6002032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 6].length) (baseStart_6002032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002032 prefixEnd_6002032 := by exact prefixLift 6002032
  have htrace : WordTrace (prefixWord ++ tailWord_6002032) baseStart_6002032 baseEnd_6002032 := by
    simpa [prefixWord, tailWord_6002032, baseEnd_6002032] using wordTrace_append hprefix tailTrace_6002032
  have hstable : (prefixWord ++ tailWord_6002032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002032).length < 2 ^ (prefixWord ++ tailWord_6002032).sum := by decide
  have hdescent : baseEnd_6002032 < baseStart_6002032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002056 : List Nat := [2, 1, 3, 3, 1, 2, 2, 3, 1, 2, 3]
def baseStart_6002056 : Nat := 118140960795 + 6002056 * 2 ^ 59
def prefixEnd_6002056 : Nat := 4983230072969 + 3 ^ 40 * 6002056 * 2
def baseEnd_6002056 : Nat := 3081939643202274161997053

theorem tailTrace_6002056 : CollatzResearch.WordTrace tailWord_6002056 prefixEnd_6002056 3081939643202274161997053 := by
  unfold tailWord_6002056
  simp only [CollatzResearch.WordTrace]
  refine ⟨109456483371791828199977011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145941977829055770933302681 109456483371791828199977011)
  ·
    refine ⟨164184725057687742299965517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109456483371791828199977011 164184725057687742299965517)
    ·
      refine ⟨61569271896632903362487069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164184725057687742299965517 61569271896632903362487069)
      ·
        refine ⟨23088476961237338760932651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61569271896632903362487069 23088476961237338760932651)
        ·
          refine ⟨34632715441856008141398977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23088476961237338760932651 34632715441856008141398977)
          ·
            refine ⟨25974536581392006106049233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34632715441856008141398977 25974536581392006106049233)
            ·
              refine ⟨19480902436044004579536925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25974536581392006106049233 19480902436044004579536925)
              ·
                refine ⟨7305338413516501717326347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19480902436044004579536925 7305338413516501717326347)
                ·
                  refine ⟨10958007620274752575989521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7305338413516501717326347 10958007620274752575989521)
                  ·
                    refine ⟨8218505715206064431992141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10958007620274752575989521 8218505715206064431992141)
                    ·
                      refine ⟨3081939643202274161997053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8218505715206064431992141 3081939643202274161997053)
                      ·
                        rfl

theorem cell23_6002056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_6002056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002056 prefixEnd_6002056 := by exact prefixLift 6002056
  have htrace : WordTrace (prefixWord ++ tailWord_6002056) baseStart_6002056 baseEnd_6002056 := by
    simpa [prefixWord, tailWord_6002056, baseEnd_6002056] using wordTrace_append hprefix tailTrace_6002056
  have hstable : (prefixWord ++ tailWord_6002056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002056).length < 2 ^ (prefixWord ++ tailWord_6002056).sum := by decide
  have hdescent : baseEnd_6002056 < baseStart_6002056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002076 : List Nat := [2, 2, 3, 4, 1, 1, 2, 8]
def baseStart_6002076 : Nat := 118140960795 + 6002076 * 2 ^ 59
def prefixEnd_6002076 : Nat := 4983230072969 + 3 ^ 40 * 6002076 * 2
def baseEnd_6002076 : Nat := 114146293067235706805443

theorem tailTrace_6002076 : CollatzResearch.WordTrace tailWord_6002076 prefixEnd_6002076 114146293067235706805443 := by
  unfold tailWord_6002076
  simp only [CollatzResearch.WordTrace]
  refine ⟨109456848101755599907841041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145942464135674133210454721 109456848101755599907841041)
  ·
    refine ⟨82092636076316699930880781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109456848101755599907841041 82092636076316699930880781)
    ·
      refine ⟨30784738528618762474080293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82092636076316699930880781 30784738528618762474080293)
      ·
        refine ⟨5772138474116017963890055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30784738528618762474080293 5772138474116017963890055)
        ·
          refine ⟨8658207711174026945835083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5772138474116017963890055 8658207711174026945835083)
          ·
            refine ⟨12987311566761040418752625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8658207711174026945835083 12987311566761040418752625)
            ·
              refine ⟨9740483675070780314064469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12987311566761040418752625 9740483675070780314064469)
              ·
                refine ⟨114146293067235706805443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9740483675070780314064469 114146293067235706805443)
                ·
                  rfl

theorem cell23_6002076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 8].length) (baseStart_6002076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002076 prefixEnd_6002076 := by exact prefixLift 6002076
  have htrace : WordTrace (prefixWord ++ tailWord_6002076) baseStart_6002076 baseEnd_6002076 := by
    simpa [prefixWord, tailWord_6002076, baseEnd_6002076] using wordTrace_append hprefix tailTrace_6002076
  have hstable : (prefixWord ++ tailWord_6002076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002076).length < 2 ^ (prefixWord ++ tailWord_6002076).sum := by decide
  have hdescent : baseEnd_6002076 < baseStart_6002076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002096 : List Nat := [2, 1, 1, 1, 2, 1, 1, 8, 1, 3, 2]
def baseStart_6002096 : Nat := 118140960795 + 6002096 * 2 ^ 59
def prefixEnd_6002096 : Nat := 4983230072969 + 3 ^ 40 * 6002096 * 2
def baseEnd_6002096 : Nat := 3081960182428454005496869

theorem tailTrace_6002096 : CollatzResearch.WordTrace tailWord_6002096 prefixEnd_6002096 3081960182428454005496869 := by
  unfold tailWord_6002096
  simp only [CollatzResearch.WordTrace]
  refine ⟨109457212831719371615705071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145942950442292495487606761 109457212831719371615705071)
  ·
    refine ⟨164185819247579057423557607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109457212831719371615705071 164185819247579057423557607)
    ·
      refine ⟨246278728871368586135336411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164185819247579057423557607 246278728871368586135336411)
      ·
        refine ⟨369418093307052879203004617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246278728871368586135336411 369418093307052879203004617)
        ·
          refine ⟨277063569980289659402253463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369418093307052879203004617 277063569980289659402253463)
          ·
            refine ⟨415595354970434489103380195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277063569980289659402253463 415595354970434489103380195)
            ·
              refine ⟨623393032455651733655070293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415595354970434489103380195 623393032455651733655070293)
              ·
                refine ⟨7305387099089668753770355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 623393032455651733655070293 7305387099089668753770355)
                ·
                  refine ⟨10958080648634503130655533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7305387099089668753770355 10958080648634503130655533)
                  ·
                    refine ⟨4109280243237938673995825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10958080648634503130655533 4109280243237938673995825)
                    ·
                      refine ⟨3081960182428454005496869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4109280243237938673995825 3081960182428454005496869)
                      ·
                        rfl

theorem cell23_6002096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 1, 3, 2].length) (baseStart_6002096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002096 prefixEnd_6002096 := by exact prefixLift 6002096
  have htrace : WordTrace (prefixWord ++ tailWord_6002096) baseStart_6002096 baseEnd_6002096 := by
    simpa [prefixWord, tailWord_6002096, baseEnd_6002096] using wordTrace_append hprefix tailTrace_6002096
  have hstable : (prefixWord ++ tailWord_6002096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002096).length < 2 ^ (prefixWord ++ tailWord_6002096).sum := by decide
  have hdescent : baseEnd_6002096 < baseStart_6002096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002114 : List Nat := [3, 5, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_6002114 : Nat := 118140960795 + 6002114 * 2 ^ 59
def prefixEnd_6002114 : Nat := 4983230072969 + 3 ^ 40 * 6002114 * 2
def baseEnd_6002114 : Nat := 1027323141693411645023929

theorem tailTrace_6002114 : CollatzResearch.WordTrace tailWord_6002114 prefixEnd_6002114 1027323141693411645023929 := by
  unfold tailWord_6002114
  simp only [CollatzResearch.WordTrace]
  refine ⟨54728770544343383076391349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145943388118249021537043597 54728770544343383076391349)
  ·
    refine ⟨5130822238532192163411689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54728770544343383076391349 5130822238532192163411689)
    ·
      refine ⟨3848116678899144122558767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5130822238532192163411689 3848116678899144122558767)
      ·
        refine ⟨5772175018348716183838151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3848116678899144122558767 5772175018348716183838151)
        ·
          refine ⟨8658262527523074275757227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5772175018348716183838151 8658262527523074275757227)
          ·
            refine ⟨12987393791284611413635841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8658262527523074275757227 12987393791284611413635841)
            ·
              refine ⟨9740545343463458560226881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12987393791284611413635841 9740545343463458560226881)
              ·
                refine ⟨7305409007597593920170161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9740545343463458560226881 7305409007597593920170161)
                ·
                  refine ⟨5479056755698195440127621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7305409007597593920170161 5479056755698195440127621)
                  ·
                    refine ⟨1027323141693411645023929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5479056755698195440127621 1027323141693411645023929)
                    ·
                      rfl

theorem cell23_6002114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_6002114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002114 prefixEnd_6002114 := by exact prefixLift 6002114
  have htrace : WordTrace (prefixWord ++ tailWord_6002114) baseStart_6002114 baseEnd_6002114 := by
    simpa [prefixWord, tailWord_6002114, baseEnd_6002114] using wordTrace_append hprefix tailTrace_6002114
  have hstable : (prefixWord ++ tailWord_6002114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002114).length < 2 ^ (prefixWord ++ tailWord_6002114).sum := by decide
  have hdescent : baseEnd_6002114 < baseStart_6002114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002143 : List Nat := [1, 1, 2, 3, 3, 1, 1, 5, 2, 2, 2]
def baseStart_6002143 : Nat := 118140960795 + 6002143 * 2 ^ 59
def prefixEnd_6002143 : Nat := 4983230072969 + 3 ^ 40 * 6002143 * 2
def baseEnd_6002143 : Nat := 3081984316019215321609153

theorem tailTrace_6002143 : CollatzResearch.WordTrace tailWord_6002143 prefixEnd_6002143 3081984316019215321609153 := by
  unfold tailWord_6002143
  simp only [CollatzResearch.WordTrace]
  refine ⟨218916139894268470258371083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145944093262845646838914055 218916139894268470258371083)
  ·
    refine ⟨328374209841402705387556625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218916139894268470258371083 328374209841402705387556625)
    ·
      refine ⟨246280657381052029040667469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328374209841402705387556625 246280657381052029040667469)
      ·
        refine ⟨92355246517894510890250301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246280657381052029040667469 92355246517894510890250301)
        ·
          refine ⟨34633217444210441583843863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92355246517894510890250301 34633217444210441583843863)
          ·
            refine ⟨51949826166315662375765795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34633217444210441583843863 51949826166315662375765795)
            ·
              refine ⟨77924739249473493563648693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51949826166315662375765795 77924739249473493563648693)
              ·
                refine ⟨7305444304638140021592065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77924739249473493563648693 7305444304638140021592065)
                ·
                  refine ⟨5479083228478605016194049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7305444304638140021592065 5479083228478605016194049)
                  ·
                    refine ⟨4109312421358953762145537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5479083228478605016194049 4109312421358953762145537)
                    ·
                      refine ⟨3081984316019215321609153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4109312421358953762145537 3081984316019215321609153)
                      ·
                        rfl

theorem cell23_6002143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 2, 2].length) (baseStart_6002143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002143 prefixEnd_6002143 := by exact prefixLift 6002143
  have htrace : WordTrace (prefixWord ++ tailWord_6002143) baseStart_6002143 baseEnd_6002143 := by
    simpa [prefixWord, tailWord_6002143, baseEnd_6002143] using wordTrace_append hprefix tailTrace_6002143
  have hstable : (prefixWord ++ tailWord_6002143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002143).length < 2 ^ (prefixWord ++ tailWord_6002143).sum := by decide
  have hdescent : baseEnd_6002143 < baseStart_6002143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002149 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 9]
def baseStart_6002149 : Nat := 118140960795 + 6002149 * 2 ^ 59
def prefixEnd_6002149 : Nat := 4983230072969 + 3 ^ 40 * 6002149 * 2
def baseEnd_6002149 : Nat := 342443044100349144237125

theorem tailTrace_6002149 : CollatzResearch.WordTrace tailWord_6002149 prefixEnd_6002149 342443044100349144237125 := by
  unfold tailWord_6002149
  simp only [CollatzResearch.WordTrace]
  refine ⟨218916358732246733283089501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145944239154831155522059667 218916358732246733283089501)
  ·
    refine ⟨82093634524592524981158563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218916358732246733283089501 82093634524592524981158563)
    ·
      refine ⟨123140451786888787471737845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82093634524592524981158563 123140451786888787471737845)
      ·
        refine ⟨11544417355020823825475423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123140451786888787471737845 11544417355020823825475423)
        ·
          refine ⟨17316626032531235738213135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11544417355020823825475423 17316626032531235738213135)
          ·
            refine ⟨25974939048796853607319703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17316626032531235738213135 25974939048796853607319703)
            ·
              refine ⟨38962408573195280410979555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25974939048796853607319703 38962408573195280410979555)
              ·
                refine ⟨58443612859792920616469333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38962408573195280410979555 58443612859792920616469333)
                ·
                  refine ⟨342443044100349144237125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58443612859792920616469333 342443044100349144237125)
                  ·
                    rfl

theorem cell23_6002149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 9].length) (baseStart_6002149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002149 prefixEnd_6002149 := by exact prefixLift 6002149
  have htrace : WordTrace (prefixWord ++ tailWord_6002149) baseStart_6002149 baseEnd_6002149 := by
    simpa [prefixWord, tailWord_6002149, baseEnd_6002149] using wordTrace_append hprefix tailTrace_6002149
  have hstable : (prefixWord ++ tailWord_6002149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002149).length < 2 ^ (prefixWord ++ tailWord_6002149).sum := by decide
  have hdescent : baseEnd_6002149 < baseStart_6002149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002177 : List Nat := [1, 2, 4, 1, 4, 2, 1, 2, 2, 2, 2]
def baseStart_6002177 : Nat := 118140960795 + 6002177 * 2 ^ 59
def prefixEnd_6002177 : Nat := 4983230072969 + 3 ^ 40 * 6002177 * 2
def baseEnd_6002177 : Nat := 3082001774361468188583997

theorem tailTrace_6002177 : CollatzResearch.WordTrace tailWord_6002177 prefixEnd_6002177 3082001774361468188583997 := by
  unfold tailWord_6002177
  simp only [CollatzResearch.WordTrace]
  refine ⟨218917379976145294065108785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145944919984096862710072523 218917379976145294065108785)
  ·
    refine ⟨164188034982108970548831589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218917379976145294065108785 164188034982108970548831589)
    ·
      refine ⟨30785256559145431977905923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164188034982108970548831589 30785256559145431977905923)
      ·
        refine ⟨46177884838718147966858885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30785256559145431977905923 46177884838718147966858885)
        ·
          refine ⟨8658353407259652743786041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46177884838718147966858885 8658353407259652743786041)
          ·
            refine ⟨6493765055444739557839531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8658353407259652743786041 6493765055444739557839531)
            ·
              refine ⟨9740647583167109336759297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6493765055444739557839531 9740647583167109336759297)
              ·
                refine ⟨7305485687375332002569473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9740647583167109336759297 7305485687375332002569473)
                ·
                  refine ⟨5479114265531499001927105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7305485687375332002569473 5479114265531499001927105)
                  ·
                    refine ⟨4109335699148624251445329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5479114265531499001927105 4109335699148624251445329)
                    ·
                      refine ⟨3082001774361468188583997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4109335699148624251445329 3082001774361468188583997)
                      ·
                        rfl

theorem cell23_6002177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_6002177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002177 prefixEnd_6002177 := by exact prefixLift 6002177
  have htrace : WordTrace (prefixWord ++ tailWord_6002177) baseStart_6002177 baseEnd_6002177 := by
    simpa [prefixWord, tailWord_6002177, baseEnd_6002177] using wordTrace_append hprefix tailTrace_6002177
  have hstable : (prefixWord ++ tailWord_6002177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002177).length < 2 ^ (prefixWord ++ tailWord_6002177).sum := by decide
  have hdescent : baseEnd_6002177 < baseStart_6002177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002239 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 8]
def baseStart_6002239 : Nat := 118140960795 + 6002239 * 2 ^ 59
def prefixEnd_6002239 : Nat := 4983230072969 + 3 ^ 40 * 6002239 * 2
def baseEnd_6002239 : Nat := 342448178906894105112079

theorem tailTrace_6002239 : CollatzResearch.WordTrace tailWord_6002239 prefixEnd_6002239 342448178906894105112079 := by
  unfold tailWord_6002239
  simp only [CollatzResearch.WordTrace]
  refine ⟨218919641301920678653865771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145946427534613785769243847 218919641301920678653865771)
  ·
    refine ⟨328379461952881017980798657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218919641301920678653865771 328379461952881017980798657)
    ·
      refine ⟨246284596464660763485598993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328379461952881017980798657 246284596464660763485598993)
      ·
        refine ⟨184713447348495572614199245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246284596464660763485598993 184713447348495572614199245)
        ·
          refine ⟨69267542755685839730324717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184713447348495572614199245 69267542755685839730324717)
          ·
            refine ⟨25975328533382189898871769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69267542755685839730324717 25975328533382189898871769)
            ·
              refine ⟨19481496400036642424153827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25975328533382189898871769 19481496400036642424153827)
              ·
                refine ⟨29222244600054963636230741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19481496400036642424153827 29222244600054963636230741)
                ·
                  refine ⟨342448178906894105112079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29222244600054963636230741 342448178906894105112079)
                  ·
                    rfl

theorem cell23_6002239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 8].length) (baseStart_6002239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002239 prefixEnd_6002239 := by exact prefixLift 6002239
  have htrace : WordTrace (prefixWord ++ tailWord_6002239) baseStart_6002239 baseEnd_6002239 := by
    simpa [prefixWord, tailWord_6002239, baseEnd_6002239] using wordTrace_append hprefix tailTrace_6002239
  have hstable : (prefixWord ++ tailWord_6002239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002239).length < 2 ^ (prefixWord ++ tailWord_6002239).sum := by decide
  have hdescent : baseEnd_6002239 < baseStart_6002239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002294 : List Nat := [5, 1, 1, 2, 2, 3, 2, 2, 1, 4]
def baseStart_6002294 : Nat := 118140960795 + 6002294 * 2 ^ 59
def prefixEnd_6002294 : Nat := 4983230072969 + 3 ^ 40 * 6002294 * 2
def baseEnd_6002294 : Nat := 1027353950532681410273653

theorem tailTrace_6002294 : CollatzResearch.WordTrace tailWord_6002294 prefixEnd_6002294 1027353950532681410273653 := by
  unfold tailWord_6002294
  simp only [CollatzResearch.WordTrace]
  refine ⟨13682602957295088940444871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145947764877814282031411957 13682602957295088940444871)
  ·
    refine ⟨20523904435942633410667307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13682602957295088940444871 20523904435942633410667307)
    ·
      refine ⟨30785856653913950116000961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20523904435942633410667307 30785856653913950116000961)
      ·
        refine ⟨23089392490435462587000721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30785856653913950116000961 23089392490435462587000721)
        ·
          refine ⟨17317044367826596940250541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23089392490435462587000721 17317044367826596940250541)
          ·
            refine ⟨6493891637934973852593953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17317044367826596940250541 6493891637934973852593953)
            ·
              refine ⟨4870418728451230389445465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6493891637934973852593953 4870418728451230389445465)
              ·
                refine ⟨3652814046338422792084099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4870418728451230389445465 3652814046338422792084099)
                ·
                  refine ⟨5479221069507634188126149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3652814046338422792084099 5479221069507634188126149)
                  ·
                    refine ⟨1027353950532681410273653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5479221069507634188126149 1027353950532681410273653)
                    ·
                      rfl

theorem cell23_6002294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_6002294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002294 prefixEnd_6002294 := by exact prefixLift 6002294
  have htrace : WordTrace (prefixWord ++ tailWord_6002294) baseStart_6002294 baseEnd_6002294 := by
    simpa [prefixWord, tailWord_6002294, baseEnd_6002294] using wordTrace_append hprefix tailTrace_6002294
  have hstable : (prefixWord ++ tailWord_6002294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002294).length < 2 ^ (prefixWord ++ tailWord_6002294).sum := by decide
  have hdescent : baseEnd_6002294 < baseStart_6002294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002299 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 3, 6]
def baseStart_6002299 : Nat := 118140960795 + 6002299 * 2 ^ 59
def prefixEnd_6002299 : Nat := 4983230072969 + 3 ^ 40 * 6002299 * 2
def baseEnd_6002299 : Nat := 1027354806333772237086145

theorem tailTrace_6002299 : CollatzResearch.WordTrace tailWord_6002299 prefixEnd_6002299 1027354806333772237086145 := by
  unfold tailWord_6002299
  simp only [CollatzResearch.WordTrace]
  refine ⟨218921829681703308901049951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145947886454468872600699967 218921829681703308901049951)
  ·
    refine ⟨328382744522554963351574927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218921829681703308901049951 328382744522554963351574927)
    ·
      refine ⟨492574116783832445027362391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328382744522554963351574927 492574116783832445027362391)
      ·
        refine ⟨738861175175748667541043587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492574116783832445027362391 738861175175748667541043587)
        ·
          refine ⟨1108291762763623001311565381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738861175175748667541043587 1108291762763623001311565381)
          ·
            refine ⟨207804705518179312745918509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1108291762763623001311565381 207804705518179312745918509)
            ·
              refine ⟨77926764569317242279719441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207804705518179312745918509 77926764569317242279719441)
              ·
                refine ⟨58445073426987931709789581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77926764569317242279719441 58445073426987931709789581)
                ·
                  refine ⟨21916902535120474391171093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58445073426987931709789581 21916902535120474391171093)
                  ·
                    refine ⟨1027354806333772237086145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21916902535120474391171093 1027354806333772237086145)
                    ·
                      rfl

theorem cell23_6002299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 6].length) (baseStart_6002299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002299 prefixEnd_6002299 := by exact prefixLift 6002299
  have htrace : WordTrace (prefixWord ++ tailWord_6002299) baseStart_6002299 baseEnd_6002299 := by
    simpa [prefixWord, tailWord_6002299, baseEnd_6002299] using wordTrace_append hprefix tailTrace_6002299
  have hstable : (prefixWord ++ tailWord_6002299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002299).length < 2 ^ (prefixWord ++ tailWord_6002299).sum := by decide
  have hdescent : baseEnd_6002299 < baseStart_6002299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002316 : List Nat := [2, 2, 1, 2, 1, 1, 6, 1, 1, 6]
def baseStart_6002316 : Nat := 118140960795 + 6002316 * 2 ^ 59
def prefixEnd_6002316 : Nat := 4983230072969 + 3 ^ 40 * 6002316 * 2
def baseEnd_6002316 : Nat := 1027357716057481048248619

theorem tailTrace_6002316 : CollatzResearch.WordTrace tailWord_6002316 prefixEnd_6002316 1027357716057481048248619 := by
  unfold tailWord_6002316
  simp only [CollatzResearch.WordTrace]
  refine ⟨109461224861320860402209401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145948299815094480536279201 109461224861320860402209401)
  ·
    refine ⟨82095918645990645301657051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109461224861320860402209401 82095918645990645301657051)
    ·
      refine ⟨123143877968985967952485577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82095918645990645301657051 123143877968985967952485577)
      ·
        refine ⟨92357908476739475964364183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123143877968985967952485577 92357908476739475964364183)
        ·
          refine ⟨138536862715109213946546275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92357908476739475964364183 138536862715109213946546275)
          ·
            refine ⟨207805294072663820919819413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138536862715109213946546275 207805294072663820919819413)
            ·
              refine ⟨9740873159656116605616535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 207805294072663820919819413 9740873159656116605616535)
              ·
                refine ⟨14611309739484174908424803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9740873159656116605616535 14611309739484174908424803)
                ·
                  refine ⟨21916964609226262362637205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14611309739484174908424803 21916964609226262362637205)
                  ·
                    refine ⟨1027357716057481048248619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21916964609226262362637205 1027357716057481048248619)
                    ·
                      rfl

theorem cell23_6002316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 1, 6].length) (baseStart_6002316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002316 prefixEnd_6002316 := by exact prefixLift 6002316
  have htrace : WordTrace (prefixWord ++ tailWord_6002316) baseStart_6002316 baseEnd_6002316 := by
    simpa [prefixWord, tailWord_6002316, baseEnd_6002316] using wordTrace_append hprefix tailTrace_6002316
  have hstable : (prefixWord ++ tailWord_6002316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002316).length < 2 ^ (prefixWord ++ tailWord_6002316).sum := by decide
  have hdescent : baseEnd_6002316 < baseStart_6002316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002334 : List Nat := [4, 3, 1, 1, 1, 3, 2, 3, 1, 1, 3]
def baseStart_6002334 : Nat := 118140960795 + 6002334 * 2 ^ 59
def prefixEnd_6002334 : Nat := 4983230072969 + 3 ^ 40 * 6002334 * 2
def baseEnd_6002334 : Nat := 3082082390824224074320775

theorem tailTrace_6002334 : CollatzResearch.WordTrace tailWord_6002334 prefixEnd_6002334 3082082390824224074320775 := by
  unfold tailWord_6002334
  simp only [CollatzResearch.WordTrace]
  refine ⟨27365388279572063734821757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145948737491051006585716037 27365388279572063734821757)
  ·
    refine ⟨10262020604839523900558159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27365388279572063734821757 10262020604839523900558159)
    ·
      refine ⟨15393030907259285850837239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10262020604839523900558159 15393030907259285850837239)
      ·
        refine ⟨23089546360888928776255859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15393030907259285850837239 23089546360888928776255859)
        ·
          refine ⟨34634319541333393164383789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23089546360888928776255859 34634319541333393164383789)
          ·
            refine ⟨12987869828000022436643921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34634319541333393164383789 12987869828000022436643921)
            ·
              refine ⟨9740902371000016827482941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12987869828000022436643921 9740902371000016827482941)
              ·
                refine ⟨3652838389125006310306103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9740902371000016827482941 3652838389125006310306103)
                ·
                  refine ⟨5479257583687509465459155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3652838389125006310306103 5479257583687509465459155)
                  ·
                    refine ⟨8218886375531264198188733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5479257583687509465459155 8218886375531264198188733)
                    ·
                      refine ⟨3082082390824224074320775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8218886375531264198188733 3082082390824224074320775)
                      ·
                        rfl

theorem cell23_6002334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_6002334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002334 prefixEnd_6002334 := by exact prefixLift 6002334
  have htrace : WordTrace (prefixWord ++ tailWord_6002334) baseStart_6002334 baseEnd_6002334 := by
    simpa [prefixWord, tailWord_6002334, baseEnd_6002334] using wordTrace_append hprefix tailTrace_6002334
  have hstable : (prefixWord ++ tailWord_6002334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002334).length < 2 ^ (prefixWord ++ tailWord_6002334).sum := by decide
  have hdescent : baseEnd_6002334 < baseStart_6002334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002340 : List Nat := [2, 3, 1, 2, 2, 2, 4, 1, 1, 1, 4]
def baseStart_6002340 : Nat := 118140960795 + 6002340 * 2 ^ 59
def prefixEnd_6002340 : Nat := 4983230072969 + 3 ^ 40 * 6002340 * 2
def baseEnd_6002340 : Nat := 3082085471708151050845747

theorem tailTrace_6002340 : CollatzResearch.WordTrace tailWord_6002340 prefixEnd_6002340 3082085471708151050845747 := by
  unfold tailWord_6002340
  simp only [CollatzResearch.WordTrace]
  refine ⟨109461662537277386451646237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145948883383036515268861649 109461662537277386451646237)
  ·
    refine ⟨41048123451479019919367339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109461662537277386451646237 41048123451479019919367339)
    ·
      refine ⟨61572185177218529879051009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41048123451479019919367339 61572185177218529879051009)
      ·
        refine ⟨46179138882913897409288257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61572185177218529879051009 46179138882913897409288257)
        ·
          refine ⟨34634354162185423056966193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46179138882913897409288257 34634354162185423056966193)
          ·
            refine ⟨25975765621639067292724645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34634354162185423056966193 25975765621639067292724645)
            ·
              refine ⟨4870456054057325117385871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25975765621639067292724645 4870456054057325117385871)
              ·
                refine ⟨7305684081085987676078807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4870456054057325117385871 7305684081085987676078807)
                ·
                  refine ⟨10958526121628981514118211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7305684081085987676078807 10958526121628981514118211)
                  ·
                    refine ⟨16437789182443472271177317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10958526121628981514118211 16437789182443472271177317)
                    ·
                      refine ⟨3082085471708151050845747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16437789182443472271177317 3082085471708151050845747)
                      ·
                        rfl

theorem cell23_6002340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_6002340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002340 prefixEnd_6002340 := by exact prefixLift 6002340
  have htrace : WordTrace (prefixWord ++ tailWord_6002340) baseStart_6002340 baseEnd_6002340 := by
    simpa [prefixWord, tailWord_6002340, baseEnd_6002340] using wordTrace_append hprefix tailTrace_6002340
  have hstable : (prefixWord ++ tailWord_6002340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002340).length < 2 ^ (prefixWord ++ tailWord_6002340).sum := by decide
  have hdescent : baseEnd_6002340 < baseStart_6002340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002374 : List Nat := [6, 1, 2, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_6002374 : Nat := 118140960795 + 6002374 * 2 ^ 59
def prefixEnd_6002374 : Nat := 4983230072969 + 3 ^ 40 * 6002374 * 2
def baseEnd_6002374 : Nat := 3082102930050403917820591

theorem tailTrace_6002374 : CollatzResearch.WordTrace tailWord_6002374 prefixEnd_6002374 3082102930050403917820591 := by
  unfold tailWord_6002374
  simp only [CollatzResearch.WordTrace]
  refine ⟨6841392661138487397188443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 145949710104287731140020117 6841392661138487397188443)
  ·
    refine ⟨10262088991707731095782665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6841392661138487397188443 10262088991707731095782665)
    ·
      refine ⟨7696566743780798321836999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10262088991707731095782665 7696566743780798321836999)
      ·
        refine ⟨11544850115671197482755499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7696566743780798321836999 11544850115671197482755499)
        ·
          refine ⟨17317275173506796224133249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11544850115671197482755499 17317275173506796224133249)
          ·
            refine ⟨12987956380130097168099937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17317275173506796224133249 12987956380130097168099937)
            ·
              refine ⟨9740967285097572876074953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12987956380130097168099937 9740967285097572876074953)
              ·
                refine ⟨7305725463823179657056215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9740967285097572876074953 7305725463823179657056215)
                ·
                  refine ⟨10958588195734769485584323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7305725463823179657056215 10958588195734769485584323)
                  ·
                    refine ⟨16437882293602154228376485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10958588195734769485584323 16437882293602154228376485)
                    ·
                      refine ⟨3082102930050403917820591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16437882293602154228376485 3082102930050403917820591)
                      ·
                        rfl

theorem cell23_6002374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_6002374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002374 prefixEnd_6002374 := by exact prefixLift 6002374
  have htrace : WordTrace (prefixWord ++ tailWord_6002374) baseStart_6002374 baseEnd_6002374 := by
    simpa [prefixWord, tailWord_6002374, baseEnd_6002374] using wordTrace_append hprefix tailTrace_6002374
  have hstable : (prefixWord ++ tailWord_6002374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002374).length < 2 ^ (prefixWord ++ tailWord_6002374).sum := by decide
  have hdescent : baseEnd_6002374 < baseStart_6002374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002380 : List Nat := [2, 2, 1, 5, 2, 2, 2, 7]
def baseStart_6002380 : Nat := 118140960795 + 6002380 * 2 ^ 59
def prefixEnd_6002380 : Nat := 4983230072969 + 3 ^ 40 * 6002380 * 2
def baseEnd_6002380 : Nat := 114152074479049292383169

theorem tailTrace_6002380 : CollatzResearch.WordTrace tailWord_6002380 prefixEnd_6002380 114152074479049292383169 := by
  unfold tailWord_6002380
  simp only [CollatzResearch.WordTrace]
  refine ⟨109462391997204929867374297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145949855996273239823165729 109462391997204929867374297)
  ·
    refine ⟨82096793997903697400530723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109462391997204929867374297 82096793997903697400530723)
    ·
      refine ⟨123145190996855546100796085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82096793997903697400530723 123145190996855546100796085)
      ·
        refine ⟨11544861655955207446949633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123145190996855546100796085 11544861655955207446949633)
        ·
          refine ⟨8658646241966405585212225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11544861655955207446949633 8658646241966405585212225)
          ·
            refine ⟨6493984681474804188909169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8658646241966405585212225 6493984681474804188909169)
            ·
              refine ⟨4870488511106103141681877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6493984681474804188909169 4870488511106103141681877)
              ·
                refine ⟨114152074479049292383169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4870488511106103141681877 114152074479049292383169)
                ·
                  rfl

theorem cell23_6002380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 7].length) (baseStart_6002380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002380 prefixEnd_6002380 := by exact prefixLift 6002380
  have htrace : WordTrace (prefixWord ++ tailWord_6002380) baseStart_6002380 baseEnd_6002380 := by
    simpa [prefixWord, tailWord_6002380, baseEnd_6002380] using wordTrace_append hprefix tailTrace_6002380
  have hstable : (prefixWord ++ tailWord_6002380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002380).length < 2 ^ (prefixWord ++ tailWord_6002380).sum := by decide
  have hdescent : baseEnd_6002380 < baseStart_6002380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002383 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 3, 3, 2]
def baseStart_6002383 : Nat := 118140960795 + 6002383 * 2 ^ 59
def prefixEnd_6002383 : Nat := 4983230072969 + 3 ^ 40 * 6002383 * 2
def baseEnd_6002383 : Nat := 3082107551376294382608049

theorem tailTrace_6002383 : CollatzResearch.WordTrace tailWord_6002383 prefixEnd_6002383 3082107551376294382608049 := by
  unfold tailWord_6002383
  simp only [CollatzResearch.WordTrace]
  refine ⟨218924893413398991247107803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145949928942265994164738535 218924893413398991247107803)
  ·
    refine ⟨328387340120098486870661705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218924893413398991247107803 328387340120098486870661705)
    ·
      refine ⟨246290505090073865152996279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328387340120098486870661705 246290505090073865152996279)
      ·
        refine ⟨369435757635110797729494419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246290505090073865152996279 369435757635110797729494419)
        ·
          refine ⟨554153636452666196594241629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369435757635110797729494419 554153636452666196594241629)
          ·
            refine ⟨207807613669749823722840611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 554153636452666196594241629 207807613669749823722840611)
            ·
              refine ⟨311711420504624735584260917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207807613669749823722840611 311711420504624735584260917)
              ·
                refine ⟨29222945672308568961024461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 311711420504624735584260917 29222945672308568961024461)
                ·
                  refine ⟨10958604627115713360384173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29222945672308568961024461 10958604627115713360384173)
                  ·
                    refine ⟨4109476735168392510144065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10958604627115713360384173 4109476735168392510144065)
                    ·
                      refine ⟨3082107551376294382608049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4109476735168392510144065 3082107551376294382608049)
                      ·
                        rfl

theorem cell23_6002383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 3, 2].length) (baseStart_6002383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002383 prefixEnd_6002383 := by exact prefixLift 6002383
  have htrace : WordTrace (prefixWord ++ tailWord_6002383) baseStart_6002383 baseEnd_6002383 := by
    simpa [prefixWord, tailWord_6002383, baseEnd_6002383] using wordTrace_append hprefix tailTrace_6002383
  have hstable : (prefixWord ++ tailWord_6002383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002383).length < 2 ^ (prefixWord ++ tailWord_6002383).sum := by decide
  have hdescent : baseEnd_6002383 < baseStart_6002383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002400 : List Nat := [2, 1, 1, 3, 1, 2, 4, 3, 1, 3, 2]
def baseStart_6002400 : Nat := 118140960795 + 6002400 * 2 ^ 59
def prefixEnd_6002400 : Nat := 4983230072969 + 3 ^ 40 * 6002400 * 2
def baseEnd_6002400 : Nat := 3082116280547420816095471

theorem tailTrace_6002400 : CollatzResearch.WordTrace tailWord_6002400 prefixEnd_6002400 3082116280547420816095471 := by
  unfold tailWord_6002400
  simp only [CollatzResearch.WordTrace]
  refine ⟨109462756727168701575238327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145950342302891602100317769 109462756727168701575238327)
  ·
    refine ⟨164194135090753052362857491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109462756727168701575238327 164194135090753052362857491)
    ·
      refine ⟨246291202636129578544286237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164194135090753052362857491 246291202636129578544286237)
      ·
        refine ⟨92359200988548591954107339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246291202636129578544286237 92359200988548591954107339)
        ·
          refine ⟨138538801482822887931161009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92359200988548591954107339 138538801482822887931161009)
          ·
            refine ⟨103904101112117165948370757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138538801482822887931161009 103904101112117165948370757)
            ·
              refine ⟨19482018958521968615319517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103904101112117165948370757 19482018958521968615319517)
              ·
                refine ⟨7305757109445738230744819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19482018958521968615319517 7305757109445738230744819)
                ·
                  refine ⟨10958635664168607346117229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7305757109445738230744819 10958635664168607346117229)
                  ·
                    refine ⟨4109488374063227754793961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10958635664168607346117229 4109488374063227754793961)
                    ·
                      refine ⟨3082116280547420816095471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4109488374063227754793961 3082116280547420816095471)
                      ·
                        rfl

theorem cell23_6002400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 1, 3, 2].length) (baseStart_6002400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002400 prefixEnd_6002400 := by exact prefixLift 6002400
  have htrace : WordTrace (prefixWord ++ tailWord_6002400) baseStart_6002400 baseEnd_6002400 := by
    simpa [prefixWord, tailWord_6002400, baseEnd_6002400] using wordTrace_append hprefix tailTrace_6002400
  have hstable : (prefixWord ++ tailWord_6002400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002400).length < 2 ^ (prefixWord ++ tailWord_6002400).sum := by decide
  have hdescent : baseEnd_6002400 < baseStart_6002400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002426 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4]
def baseStart_6002426 : Nat := 118140960795 + 6002426 * 2 ^ 59
def prefixEnd_6002426 : Nat := 4983230072969 + 3 ^ 40 * 6002426 * 2
def baseEnd_6002426 : Nat := 3082129631044437714370351

theorem tailTrace_6002426 : CollatzResearch.WordTrace tailWord_6002426 prefixEnd_6002426 3082129631044437714370351 := by
  unfold tailWord_6002426
  simp only [CollatzResearch.WordTrace]
  refine ⟨54731615438060802397730783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145950974501495473060615421 54731615438060802397730783)
  ·
    refine ⟨82097423157091203596596175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54731615438060802397730783 82097423157091203596596175)
    ·
      refine ⟨123146134735636805394894263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82097423157091203596596175 123146134735636805394894263)
      ·
        refine ⟨184719202103455208092341395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123146134735636805394894263 184719202103455208092341395)
        ·
          refine ⟨277078803155182812138512093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184719202103455208092341395 277078803155182812138512093)
          ·
            refine ⟨103904551183193554551942035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277078803155182812138512093 103904551183193554551942035)
            ·
              refine ⟨155856826774790331827913053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103904551183193554551942035 155856826774790331827913053)
              ·
                refine ⟨58446310040546374435467395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155856826774790331827913053 58446310040546374435467395)
                ·
                  refine ⟨87669465060819561653201093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58446310040546374435467395 87669465060819561653201093)
                  ·
                    refine ⟨16438024698903667809975205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87669465060819561653201093 16438024698903667809975205)
                    ·
                      refine ⟨3082129631044437714370351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16438024698903667809975205 3082129631044437714370351)
                      ·
                        rfl

theorem cell23_6002426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_6002426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002426 prefixEnd_6002426 := by exact prefixLift 6002426
  have htrace : WordTrace (prefixWord ++ tailWord_6002426) baseStart_6002426 baseEnd_6002426 := by
    simpa [prefixWord, tailWord_6002426, baseEnd_6002426] using wordTrace_append hprefix tailTrace_6002426
  have hstable : (prefixWord ++ tailWord_6002426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002426).length < 2 ^ (prefixWord ++ tailWord_6002426).sum := by decide
  have hdescent : baseEnd_6002426 < baseStart_6002426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002450 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_6002450 : Nat := 118140960795 + 6002450 * 2 ^ 59
def prefixEnd_6002450 : Nat := 4983230072969 + 3 ^ 40 * 6002450 * 2
def baseEnd_6002450 : Nat := 3082141954580145620470241

theorem tailTrace_6002450 : CollatzResearch.WordTrace tailWord_6002450 prefixEnd_6002450 3082141954580145620470241 := by
  unfold tailWord_6002450
  simp only [CollatzResearch.WordTrace]
  refine ⟨54731834276039065422449201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145951558069437507793197869 54731834276039065422449201)
  ·
    refine ⟨41048875707029299066836901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54731834276039065422449201 41048875707029299066836901)
    ·
      refine ⟨7696664195067993575031919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41048875707029299066836901 7696664195067993575031919)
      ·
        refine ⟨11544996292601990362547879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7696664195067993575031919 11544996292601990362547879)
        ·
          refine ⟨17317494438902985543821819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11544996292601990362547879 17317494438902985543821819)
          ·
            refine ⟨25976241658354478315732729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17317494438902985543821819 25976241658354478315732729)
            ·
              refine ⟨19482181243765858736799547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25976241658354478315732729 19482181243765858736799547)
              ·
                refine ⟨29223271865648788105199321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19482181243765858736799547 29223271865648788105199321)
                ·
                  refine ⟨21917453899236591078899491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29223271865648788105199321 21917453899236591078899491)
                  ·
                    refine ⟨32876180848854886618349237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21917453899236591078899491 32876180848854886618349237)
                    ·
                      refine ⟨3082141954580145620470241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32876180848854886618349237 3082141954580145620470241)
                      ·
                        rfl

theorem cell23_6002450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_6002450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002450 prefixEnd_6002450 := by exact prefixLift 6002450
  have htrace : WordTrace (prefixWord ++ tailWord_6002450) baseStart_6002450 baseEnd_6002450 := by
    simpa [prefixWord, tailWord_6002450, baseEnd_6002450] using wordTrace_append hprefix tailTrace_6002450
  have hstable : (prefixWord ++ tailWord_6002450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002450).length < 2 ^ (prefixWord ++ tailWord_6002450).sum := by decide
  have hdescent : baseEnd_6002450 < baseStart_6002450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002463 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 3]
def baseStart_6002463 : Nat := 118140960795 + 6002463 * 2 ^ 59
def prefixEnd_6002463 : Nat := 4983230072969 + 3 ^ 40 * 6002463 * 2
def baseEnd_6002463 : Nat := 3082148629828654069607681

theorem tailTrace_6002463 : CollatzResearch.WordTrace tailWord_6002463 prefixEnd_6002463 3082148629828654069607681 := by
  unfold tailWord_6002463
  simp only [CollatzResearch.WordTrace]
  refine ⟨218927811253109164910020043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145951874168739443273346695 218927811253109164910020043)
  ·
    refine ⟨328391716879663747365030065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218927811253109164910020043 328391716879663747365030065)
    ·
      refine ⟨246293787659747810523772549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328391716879663747365030065 246293787659747810523772549)
      ·
        refine ⟨46180085186202714473207353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246293787659747810523772549 46180085186202714473207353)
        ·
          refine ⟨34635063889652035854905515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46180085186202714473207353 34635063889652035854905515)
          ·
            refine ⟨51952595834478053782358273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34635063889652035854905515 51952595834478053782358273)
            ·
              refine ⟨38964446875858540336768705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51952595834478053782358273 38964446875858540336768705)
              ·
                refine ⟨29223335156893905252576529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38964446875858540336768705 29223335156893905252576529)
                ·
                  refine ⟨21917501367670428939432397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29223335156893905252576529 21917501367670428939432397)
                  ·
                    refine ⟨8219063012876410852287149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21917501367670428939432397 8219063012876410852287149)
                    ·
                      refine ⟨3082148629828654069607681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8219063012876410852287149 3082148629828654069607681)
                      ·
                        rfl

theorem cell23_6002463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_6002463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002463 prefixEnd_6002463 := by exact prefixLift 6002463
  have htrace : WordTrace (prefixWord ++ tailWord_6002463) baseStart_6002463 baseEnd_6002463 := by
    simpa [prefixWord, tailWord_6002463, baseEnd_6002463] using wordTrace_append hprefix tailTrace_6002463
  have hstable : (prefixWord ++ tailWord_6002463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002463).length < 2 ^ (prefixWord ++ tailWord_6002463).sum := by decide
  have hdescent : baseEnd_6002463 < baseStart_6002463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002553 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 2, 5, 3]
def baseStart_6002553 : Nat := 118140960795 + 6002553 * 2 ^ 59
def prefixEnd_6002553 : Nat := 4983230072969 + 3 ^ 40 * 6002553 * 2
def baseEnd_6002553 : Nat := 3082194843087558717482267

theorem tailTrace_6002553 : CollatzResearch.WordTrace tailWord_6002553 prefixEnd_6002553 3082194843087558717482267 := by
  unfold tailWord_6002553
  simp only [CollatzResearch.WordTrace]
  refine ⟨218931093822783110280796313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145954062548522073520530875 218931093822783110280796313)
  ·
    refine ⟨164198320367087332710597235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218931093822783110280796313 164198320367087332710597235)
    ·
      refine ⟨246297480550630999065895853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164198320367087332710597235 246297480550630999065895853)
      ·
        refine ⟨92361555206486624649710945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246297480550630999065895853 92361555206486624649710945)
        ·
          refine ⟨69271166404864968487283209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92361555206486624649710945 69271166404864968487283209)
          ·
            refine ⟨51953374803648726365462407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69271166404864968487283209 51953374803648726365462407)
            ·
              refine ⟨77930062205473089548193611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51953374803648726365462407 77930062205473089548193611)
              ·
                refine ⟨116895093308209634322290417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77930062205473089548193611 116895093308209634322290417)
                ·
                  refine ⟨87671319981157225741717813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116895093308209634322290417 87671319981157225741717813)
                  ·
                    refine ⟨8219186248233489913286045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87671319981157225741717813 8219186248233489913286045)
                    ·
                      refine ⟨3082194843087558717482267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8219186248233489913286045 3082194843087558717482267)
                      ·
                        rfl

theorem cell23_6002553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_6002553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002553 prefixEnd_6002553 := by exact prefixLift 6002553
  have htrace : WordTrace (prefixWord ++ tailWord_6002553) baseStart_6002553 baseEnd_6002553 := by
    simpa [prefixWord, tailWord_6002553, baseEnd_6002553] using wordTrace_append hprefix tailTrace_6002553
  have hstable : (prefixWord ++ tailWord_6002553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002553).length < 2 ^ (prefixWord ++ tailWord_6002553).sum := by decide
  have hdescent : baseEnd_6002553 < baseStart_6002553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002574 : List Nat := [4, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3]
def baseStart_6002574 : Nat := 118140960795 + 6002574 * 2 ^ 59
def prefixEnd_6002574 : Nat := 4983230072969 + 3 ^ 40 * 6002574 * 2
def baseEnd_6002574 : Nat := 3082205626181303135319671

theorem tailTrace_6002574 : CollatzResearch.WordTrace tailWord_6002574 prefixEnd_6002574 3082205626181303135319671 := by
  unfold tailWord_6002574
  simp only [CollatzResearch.WordTrace]
  refine ⟨27366482469463378858413847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145954573170471353911540517 27366482469463378858413847)
  ·
    refine ⟨41049723704195068287620771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27366482469463378858413847 41049723704195068287620771)
    ·
      refine ⟨61574585556292602431431157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41049723704195068287620771 61574585556292602431431157)
      ·
        refine ⟨5772617395902431477946671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61574585556292602431431157 5772617395902431477946671)
        ·
          refine ⟨8658926093853647216920007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5772617395902431477946671 8658926093853647216920007)
          ·
            refine ⟨12988389140780470825380011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8658926093853647216920007 12988389140780470825380011)
            ·
              refine ⟨19482583711170706238070017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12988389140780470825380011 19482583711170706238070017)
              ·
                refine ⟨14611937783378029678552513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19482583711170706238070017 14611937783378029678552513)
                ·
                  refine ⟨10958953337533522258914385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14611937783378029678552513 10958953337533522258914385)
                  ·
                    refine ⟨8219215003150141694185789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10958953337533522258914385 8219215003150141694185789)
                    ·
                      refine ⟨3082205626181303135319671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8219215003150141694185789 3082205626181303135319671)
                      ·
                        rfl

theorem cell23_6002574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_6002574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002574 prefixEnd_6002574 := by exact prefixLift 6002574
  have htrace : WordTrace (prefixWord ++ tailWord_6002574) baseStart_6002574 baseEnd_6002574 := by
    simpa [prefixWord, tailWord_6002574, baseEnd_6002574] using wordTrace_append hprefix tailTrace_6002574
  have hstable : (prefixWord ++ tailWord_6002574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002574).length < 2 ^ (prefixWord ++ tailWord_6002574).sum := by decide
  have hdescent : baseEnd_6002574 < baseStart_6002574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002594 : List Nat := [3, 3, 1, 2, 3, 2, 2, 1, 6]
def baseStart_6002594 : Nat := 118140960795 + 6002594 * 2 ^ 59
def prefixEnd_6002594 : Nat := 4983230072969 + 3 ^ 40 * 6002594 * 2
def baseEnd_6002594 : Nat := 342468432866043673007731

theorem tailTrace_6002594 : CollatzResearch.WordTrace tailWord_6002594 prefixEnd_6002594 342468432866043673007731 := by
  unfold tailWord_6002594
  simp only [CollatzResearch.WordTrace]
  refine ⟨54733147303908643570759709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145955059477089716188692557 54733147303908643570759709)
  ·
    refine ⟨20524930238965741339034891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54733147303908643570759709 20524930238965741339034891)
    ·
      refine ⟨30787395358448612008552337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20524930238965741339034891 30787395358448612008552337)
      ·
        refine ⟨23090546518836459006414253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30787395358448612008552337 23090546518836459006414253)
        ·
          refine ⟨8658954944563672127405345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23090546518836459006414253 8658954944563672127405345)
          ·
            refine ⟨6494216208422754095554009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8658954944563672127405345 6494216208422754095554009)
            ·
              refine ⟨4870662156317065571665507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6494216208422754095554009 4870662156317065571665507)
              ·
                refine ⟨7305993234475598357498261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4870662156317065571665507 7305993234475598357498261)
                ·
                  refine ⟨342468432866043673007731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7305993234475598357498261 342468432866043673007731)
                  ·
                    rfl

theorem cell23_6002594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_6002594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002594 prefixEnd_6002594 := by exact prefixLift 6002594
  have htrace : WordTrace (prefixWord ++ tailWord_6002594) baseStart_6002594 baseEnd_6002594 := by
    simpa [prefixWord, tailWord_6002594, baseEnd_6002594] using wordTrace_append hprefix tailTrace_6002594
  have hstable : (prefixWord ++ tailWord_6002594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002594).length < 2 ^ (prefixWord ++ tailWord_6002594).sum := by decide
  have hdescent : baseEnd_6002594 < baseStart_6002594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002610 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2]
def baseStart_6002610 : Nat := 118140960795 + 6002610 * 2 ^ 59
def prefixEnd_6002610 : Nat := 4983230072969 + 3 ^ 40 * 6002610 * 2
def baseEnd_6002610 : Nat := 3082224111484864994469505

theorem tailTrace_6002610 : CollatzResearch.WordTrace tailWord_6002610 prefixEnd_6002610 3082224111484864994469505 := by
  unfold tailWord_6002610
  simp only [CollatzResearch.WordTrace]
  refine ⟨54733293195894152253905321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145955448522384406010414189 54733293195894152253905321)
  ·
    refine ⟨41049969896920614190428991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54733293195894152253905321 41049969896920614190428991)
    ·
      refine ⟨61574954845380921285643487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41049969896920614190428991 61574954845380921285643487)
      ·
        refine ⟨92362432268071381928465231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61574954845380921285643487 92362432268071381928465231)
        ·
          refine ⟨138543648402107072892697847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92362432268071381928465231 138543648402107072892697847)
          ·
            refine ⟨207815472603160609339046771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138543648402107072892697847 207815472603160609339046771)
            ·
              refine ⟨311723208904740914008570157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207815472603160609339046771 311723208904740914008570157)
              ·
                refine ⟨116896203339277842753213809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311723208904740914008570157 116896203339277842753213809)
                ·
                  refine ⟨87672152504458382064910357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116896203339277842753213809 87672152504458382064910357)
                  ·
                    refine ⟨4109632148646486659292673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87672152504458382064910357 4109632148646486659292673)
                    ·
                      refine ⟨3082224111484864994469505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4109632148646486659292673 3082224111484864994469505)
                      ·
                        rfl

theorem cell23_6002610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2].length) (baseStart_6002610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002610 prefixEnd_6002610 := by exact prefixLift 6002610
  have htrace : WordTrace (prefixWord ++ tailWord_6002610) baseStart_6002610 baseEnd_6002610 := by
    simpa [prefixWord, tailWord_6002610, baseEnd_6002610] using wordTrace_append hprefix tailTrace_6002610
  have hstable : (prefixWord ++ tailWord_6002610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002610).length < 2 ^ (prefixWord ++ tailWord_6002610).sum := by decide
  have hdescent : baseEnd_6002610 < baseStart_6002610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002644 : List Nat := [2, 4, 1, 2, 1, 1, 2, 3, 3, 2, 2]
def baseStart_6002644 : Nat := 118140960795 + 6002644 * 2 ^ 59
def prefixEnd_6002644 : Nat := 4983230072969 + 3 ^ 40 * 6002644 * 2
def baseEnd_6002644 : Nat := 3082241569827117861444349

theorem tailTrace_6002644 : CollatzResearch.WordTrace tailWord_6002644 prefixEnd_6002644 3082241569827117861444349 := by
  unfold tailWord_6002644
  simp only [CollatzResearch.WordTrace]
  refine ⟨109467206432726716411179493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145956275243635621881572657 109467206432726716411179493)
  ·
    refine ⟨20525101206136259327096155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109467206432726716411179493 20525101206136259327096155)
    ·
      refine ⟨30787651809204388990644233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20525101206136259327096155 30787651809204388990644233)
      ·
        refine ⟨23090738856903291742983175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30787651809204388990644233 23090738856903291742983175)
        ·
          refine ⟨34636108285354937614474763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23090738856903291742983175 34636108285354937614474763)
          ·
            refine ⟨51954162428032406421712145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34636108285354937614474763 51954162428032406421712145)
            ·
              refine ⟨38965621821024304816284109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51954162428032406421712145 38965621821024304816284109)
              ·
                refine ⟨14612108182884114306106541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38965621821024304816284109 14612108182884114306106541)
                ·
                  refine ⟨5479540568581542864789953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14612108182884114306106541 5479540568581542864789953)
                  ·
                    refine ⟨4109655426436157148592465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5479540568581542864789953 4109655426436157148592465)
                    ·
                      refine ⟨3082241569827117861444349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4109655426436157148592465 3082241569827117861444349)
                      ·
                        rfl

theorem cell23_6002644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_6002644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002644 prefixEnd_6002644 := by exact prefixLift 6002644
  have htrace : WordTrace (prefixWord ++ tailWord_6002644) baseStart_6002644 baseEnd_6002644 := by
    simpa [prefixWord, tailWord_6002644, baseEnd_6002644] using wordTrace_append hprefix tailTrace_6002644
  have hstable : (prefixWord ++ tailWord_6002644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002644).length < 2 ^ (prefixWord ++ tailWord_6002644).sum := by decide
  have hdescent : baseEnd_6002644 < baseStart_6002644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002678 : List Nat := [5, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4]
def baseStart_6002678 : Nat := 118140960795 + 6002678 * 2 ^ 59
def prefixEnd_6002678 : Nat := 4983230072969 + 3 ^ 40 * 6002678 * 2
def baseEnd_6002678 : Nat := 3082259028169370728419193

theorem tailTrace_6002678 : CollatzResearch.WordTrace tailWord_6002678 prefixEnd_6002678 3082259028169370728419193 := by
  unfold tailWord_6002678
  simp only [CollatzResearch.WordTrace]
  refine ⟨13683478309208141039318543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145957101964886837752731125 13683478309208141039318543)
  ·
    refine ⟨20525217463812211558977815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13683478309208141039318543 20525217463812211558977815)
    ·
      refine ⟨30787826195718317338466723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20525217463812211558977815 30787826195718317338466723)
      ·
        refine ⟨46181739293577476007700085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30787826195718317338466723 46181739293577476007700085)
        ·
          refine ⟨4329538058772888375721883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46181739293577476007700085 4329538058772888375721883)
          ·
            refine ⟨6494307088159332563582825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4329538058772888375721883 6494307088159332563582825)
            ·
              refine ⟨4870730316119499422687119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6494307088159332563582825 4870730316119499422687119)
              ·
                refine ⟨7306095474179249134030679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4870730316119499422687119 7306095474179249134030679)
                ·
                  refine ⟨10959143211268873701046019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7306095474179249134030679 10959143211268873701046019)
                  ·
                    refine ⟨16438714816903310551569029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10959143211268873701046019 16438714816903310551569029)
                    ·
                      refine ⟨3082259028169370728419193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16438714816903310551569029 3082259028169370728419193)
                      ·
                        rfl

theorem cell23_6002678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_6002678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002678 prefixEnd_6002678 := by exact prefixLift 6002678
  have htrace : WordTrace (prefixWord ++ tailWord_6002678) baseStart_6002678 baseEnd_6002678 := by
    simpa [prefixWord, tailWord_6002678, baseEnd_6002678] using wordTrace_append hprefix tailTrace_6002678
  have hstable : (prefixWord ++ tailWord_6002678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002678).length < 2 ^ (prefixWord ++ tailWord_6002678).sum := by decide
  have hdescent : baseEnd_6002678 < baseStart_6002678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002708 : List Nat := [2, 4, 3, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_6002708 : Nat := 118140960795 + 6002708 * 2 ^ 59
def prefixEnd_6002708 : Nat := 4983230072969 + 3 ^ 40 * 6002708 * 2
def baseEnd_6002708 : Nat := 3082274432589005611044055

theorem tailTrace_6002708 : CollatzResearch.WordTrace tailWord_6002708 prefixEnd_6002708 3082274432589005611044055 := by
  unfold tailWord_6002708
  simp only [CollatzResearch.WordTrace]
  refine ⟨109468373568610785876344389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145957831424814381168459185 109468373568610785876344389)
  ·
    refine ⟨20525320044114522351814573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109468373568610785876344389 20525320044114522351814573)
    ·
      refine ⟨7696995016542945881930465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20525320044114522351814573 7696995016542945881930465)
      ·
        refine ⟨5772746262407209411447849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7696995016542945881930465 5772746262407209411447849)
        ·
          refine ⟨4329559696805407058585887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5772746262407209411447849 4329559696805407058585887)
          ·
            refine ⟨6494339545208110587878831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4329559696805407058585887 6494339545208110587878831)
            ·
              refine ⟨9741509317812165881818247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6494339545208110587878831 9741509317812165881818247)
              ·
                refine ⟨14612263976718248822727371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9741509317812165881818247 14612263976718248822727371)
                ·
                  refine ⟨21918395965077373234091057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14612263976718248822727371 21918395965077373234091057)
                  ·
                    refine ⟨16438796973808029925568293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21918395965077373234091057 16438796973808029925568293)
                    ·
                      refine ⟨3082274432589005611044055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16438796973808029925568293 3082274432589005611044055)
                      ·
                        rfl

theorem cell23_6002708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_6002708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002708 prefixEnd_6002708 := by exact prefixLift 6002708
  have htrace : WordTrace (prefixWord ++ tailWord_6002708) baseStart_6002708 baseEnd_6002708 := by
    simpa [prefixWord, tailWord_6002708, baseEnd_6002708] using wordTrace_append hprefix tailTrace_6002708
  have hstable : (prefixWord ++ tailWord_6002708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002708).length < 2 ^ (prefixWord ++ tailWord_6002708).sum := by decide
  have hdescent : baseEnd_6002708 < baseStart_6002708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002711 : List Nat := [1, 1, 3, 5, 3, 1, 1, 1, 1, 3, 3]
def baseStart_6002711 : Nat := 118140960795 + 6002711 * 2 ^ 59
def prefixEnd_6002711 : Nat := 4983230072969 + 3 ^ 40 * 6002711 * 2
def baseEnd_6002711 : Nat := 3082275973030969099306541

theorem tailTrace_6002711 : CollatzResearch.WordTrace tailWord_6002711 prefixEnd_6002711 3082275973030969099306541 := by
  unfold tailWord_6002711
  simp only [CollatzResearch.WordTrace]
  refine ⟨218936856556210703265047987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145957904370807135510031991 218936856556210703265047987)
  ·
    refine ⟨328405284834316054897571981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218936856556210703265047987 328405284834316054897571981)
    ·
      refine ⟨123151981812868520586589493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328405284834316054897571981 123151981812868520586589493)
      ·
        refine ⟨11545498294956423804992765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123151981812868520586589493 11545498294956423804992765)
        ·
          refine ⟨4329561860608658926872287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11545498294956423804992765 4329561860608658926872287)
          ·
            refine ⟨6494342790912988390308431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4329561860608658926872287 6494342790912988390308431)
            ·
              refine ⟨9741514186369482585462647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6494342790912988390308431 9741514186369482585462647)
              ·
                refine ⟨14612271279554223878193971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9741514186369482585462647 14612271279554223878193971)
                ·
                  refine ⟨21918406919331335817290957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14612271279554223878193971 21918406919331335817290957)
                  ·
                    refine ⟨8219402594749250931484109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21918406919331335817290957 8219402594749250931484109)
                    ·
                      refine ⟨3082275973030969099306541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8219402594749250931484109 3082275973030969099306541)
                      ·
                        rfl

theorem cell23_6002711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_6002711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002711 prefixEnd_6002711 := by exact prefixLift 6002711
  have htrace : WordTrace (prefixWord ++ tailWord_6002711) baseStart_6002711 baseEnd_6002711 := by
    simpa [prefixWord, tailWord_6002711, baseEnd_6002711] using wordTrace_append hprefix tailTrace_6002711
  have hstable : (prefixWord ++ tailWord_6002711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002711).length < 2 ^ (prefixWord ++ tailWord_6002711).sum := by decide
  have hdescent : baseEnd_6002711 < baseStart_6002711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002721 : List Nat := [1, 2, 3, 2, 4, 1, 2, 2, 1, 3, 2]
def baseStart_6002721 : Nat := 118140960795 + 6002721 * 2 ^ 59
def prefixEnd_6002721 : Nat := 4983230072969 + 3 ^ 40 * 6002721 * 2
def baseEnd_6002721 : Nat := 3082281107837514060181495

theorem tailTrace_6002721 : CollatzResearch.WordTrace tailWord_6002721 prefixEnd_6002721 3082281107837514060181495 := by
  unfold tailWord_6002721
  simp only [CollatzResearch.WordTrace]
  refine ⟨218937221286174474972912017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145958147524116316648608011 218937221286174474972912017)
  ·
    refine ⟨164202915964630856229684013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218937221286174474972912017 164202915964630856229684013)
    ·
      refine ⟨61576093486736571086131505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164202915964630856229684013 61576093486736571086131505)
      ·
        refine ⟨46182070115052428314598629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61576093486736571086131505 46182070115052428314598629)
        ·
          refine ⟨8659138146572330308987243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46182070115052428314598629 8659138146572330308987243)
          ·
            refine ⟨12988707219858495463480865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8659138146572330308987243 12988707219858495463480865)
            ·
              refine ⟨9741530414893871597610649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12988707219858495463480865 9741530414893871597610649)
              ·
                refine ⟨7306147811170403698207987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9741530414893871597610649 7306147811170403698207987)
                ·
                  refine ⟨10959221716755605547311981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7306147811170403698207987 10959221716755605547311981)
                  ·
                    refine ⟨4109708143783352080241993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10959221716755605547311981 4109708143783352080241993)
                    ·
                      refine ⟨3082281107837514060181495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4109708143783352080241993 3082281107837514060181495)
                      ·
                        rfl

theorem cell23_6002721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_6002721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002721 prefixEnd_6002721 := by exact prefixLift 6002721
  have htrace : WordTrace (prefixWord ++ tailWord_6002721) baseStart_6002721 baseEnd_6002721 := by
    simpa [prefixWord, tailWord_6002721, baseEnd_6002721] using wordTrace_append hprefix tailTrace_6002721
  have hstable : (prefixWord ++ tailWord_6002721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002721).length < 2 ^ (prefixWord ++ tailWord_6002721).sum := by decide
  have hdescent : baseEnd_6002721 < baseStart_6002721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002807 : List Nat := [1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 4]
def baseStart_6002807 : Nat := 118140960795 + 6002807 * 2 ^ 59
def prefixEnd_6002807 : Nat := 4983230072969 + 3 ^ 40 * 6002807 * 2
def baseEnd_6002807 : Nat := 3082325267173800723706099

theorem tailTrace_6002807 : CollatzResearch.WordTrace tailWord_6002807 prefixEnd_6002807 3082325267173800723706099 := by
  unfold tailWord_6002807
  simp only [CollatzResearch.WordTrace]
  refine ⟨218940357963862911660542675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145960238642575274440361783 218940357963862911660542675)
  ·
    refine ⟨328410536945794367490814013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218940357963862911660542675 328410536945794367490814013)
    ·
      refine ⟨123153951354672887809055255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328410536945794367490814013 123153951354672887809055255)
      ·
        refine ⟨184730927032009331713582883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123153951354672887809055255 184730927032009331713582883)
        ·
          refine ⟨277096390548013997570374325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184730927032009331713582883 277096390548013997570374325)
          ·
            refine ⟨25977786613876312272222593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 277096390548013997570374325 25977786613876312272222593)
            ·
              refine ⟨19483339960407234204166945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25977786613876312272222593 19483339960407234204166945)
              ·
                refine ⟨14612504970305425653125209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19483339960407234204166945 14612504970305425653125209)
                ·
                  refine ⟨10959378727729069239843907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14612504970305425653125209 10959378727729069239843907)
                  ·
                    refine ⟨16439068091593603859765861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10959378727729069239843907 16439068091593603859765861)
                    ·
                      refine ⟨3082325267173800723706099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16439068091593603859765861 3082325267173800723706099)
                      ·
                        rfl

theorem cell23_6002807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_6002807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002807 prefixEnd_6002807 := by exact prefixLift 6002807
  have htrace : WordTrace (prefixWord ++ tailWord_6002807) baseStart_6002807 baseEnd_6002807 := by
    simpa [prefixWord, tailWord_6002807, baseEnd_6002807] using wordTrace_append hprefix tailTrace_6002807
  have hstable : (prefixWord ++ tailWord_6002807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002807).length < 2 ^ (prefixWord ++ tailWord_6002807).sum := by decide
  have hdescent : baseEnd_6002807 < baseStart_6002807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002824 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 1, 6, 2]
def baseStart_6002824 : Nat := 118140960795 + 6002824 * 2 ^ 59
def prefixEnd_6002824 : Nat := 4983230072969 + 3 ^ 40 * 6002824 * 2
def baseEnd_6002824 : Nat := 3082333996344927157193521

theorem tailTrace_6002824 : CollatzResearch.WordTrace tailWord_6002824 prefixEnd_6002824 3082333996344927157193521 := by
  unfold tailWord_6002824
  simp only [CollatzResearch.WordTrace]
  refine ⟨109470489002400661781955763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145960652003200882375941017 109470489002400661781955763)
  ·
    refine ⟨164205733503600992672933645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109470489002400661781955763 164205733503600992672933645)
    ·
      refine ⟨61577150063850372252350117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164205733503600992672933645 61577150063850372252350117)
      ·
        refine ⟨11545715636971944797315647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61577150063850372252350117 11545715636971944797315647)
        ·
          refine ⟨17318573455457917195973471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11545715636971944797315647 17318573455457917195973471)
          ·
            refine ⟨25977860183186875793960207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17318573455457917195973471 25977860183186875793960207)
            ·
              refine ⟨38966790274780313690940311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25977860183186875793960207 38966790274780313690940311)
              ·
                refine ⟨58450185412170470536410467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38966790274780313690940311 58450185412170470536410467)
                ·
                  refine ⟨87675278118255705804615701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58450185412170470536410467 87675278118255705804615701)
                  ·
                    refine ⟨4109778661793236209591361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87675278118255705804615701 4109778661793236209591361)
                    ·
                      refine ⟨3082333996344927157193521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4109778661793236209591361 3082333996344927157193521)
                      ·
                        rfl

theorem cell23_6002824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_6002824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002824 prefixEnd_6002824 := by exact prefixLift 6002824
  have htrace : WordTrace (prefixWord ++ tailWord_6002824) baseStart_6002824 baseEnd_6002824 := by
    simpa [prefixWord, tailWord_6002824, baseEnd_6002824] using wordTrace_append hprefix tailTrace_6002824
  have hstable : (prefixWord ++ tailWord_6002824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002824).length < 2 ^ (prefixWord ++ tailWord_6002824).sum := by decide
  have hdescent : baseEnd_6002824 < baseStart_6002824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002834 : List Nat := [3, 2, 3, 1, 1, 1, 3, 2, 3, 4]
def baseStart_6002834 : Nat := 118140960795 + 6002834 * 2 ^ 59
def prefixEnd_6002834 : Nat := 4983230072969 + 3 ^ 40 * 6002834 * 2
def baseEnd_6002834 : Nat := 1027446377050490706022825

theorem tailTrace_6002834 : CollatzResearch.WordTrace tailWord_6002834 prefixEnd_6002834 1027446377050490706022825 := by
  unfold tailWord_6002834
  simp only [CollatzResearch.WordTrace]
  refine ⟨54735335683691273817943889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145960895156510063514517037 54735335683691273817943889)
  ·
    refine ⟨41051501762768455363457917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54735335683691273817943889 41051501762768455363457917)
    ·
      refine ⟨15394313161038170761296719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41051501762768455363457917 15394313161038170761296719)
      ·
        refine ⟨23091469741557256141945079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15394313161038170761296719 23091469741557256141945079)
        ·
          refine ⟨34637204612335884212917619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23091469741557256141945079 34637204612335884212917619)
          ·
            refine ⟨51955806918503826319376429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34637204612335884212917619 51955806918503826319376429)
            ·
              refine ⟨19483427594438934869766161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51955806918503826319376429 19483427594438934869766161)
              ·
                refine ⟨14612570695829201152324621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19483427594438934869766161 14612570695829201152324621)
                ·
                  refine ⟨5479714010935950432121733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14612570695829201152324621 5479714010935950432121733)
                  ·
                    refine ⟨1027446377050490706022825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5479714010935950432121733 1027446377050490706022825)
                    ·
                      rfl

theorem cell23_6002834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_6002834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002834 prefixEnd_6002834 := by exact prefixLift 6002834
  have htrace : WordTrace (prefixWord ++ tailWord_6002834) baseStart_6002834 baseEnd_6002834 := by
    simpa [prefixWord, tailWord_6002834, baseEnd_6002834] using wordTrace_append hprefix tailTrace_6002834
  have hstable : (prefixWord ++ tailWord_6002834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002834).length < 2 ^ (prefixWord ++ tailWord_6002834).sum := by decide
  have hdescent : baseEnd_6002834 < baseStart_6002834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002874 : List Nat := [3, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3]
def baseStart_6002874 : Nat := 118140960795 + 6002874 * 2 ^ 59
def prefixEnd_6002874 : Nat := 4983230072969 + 3 ^ 40 * 6002874 * 2
def baseEnd_6002874 : Nat := 3082359670377651961568291

theorem tailTrace_6002874 : CollatzResearch.WordTrace tailWord_6002874 prefixEnd_6002874 3082359670377651961568291 := by
  unfold tailWord_6002874
  simp only [CollatzResearch.WordTrace]
  refine ⟨54735700413655045525807919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145961867769746788068821117 54735700413655045525807919)
  ·
    refine ⟨82103550620482568288711879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54735700413655045525807919 82103550620482568288711879)
    ·
      refine ⟨123155325930723852433067819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82103550620482568288711879 123155325930723852433067819)
      ·
        refine ⟨184732988896085778649601729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123155325930723852433067819 184732988896085778649601729)
        ·
          refine ⟨138549741672064333987201297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184732988896085778649601729 138549741672064333987201297)
          ·
            refine ⟨103912306254048250490400973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138549741672064333987201297 103912306254048250490400973)
            ·
              refine ⟨38967114845268093933900365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103912306254048250490400973 38967114845268093933900365)
              ·
                refine ⟨14612668066975535225212637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38967114845268093933900365 14612668066975535225212637)
                ·
                  refine ⟨5479750525115825709454739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14612668066975535225212637 5479750525115825709454739)
                  ·
                    refine ⟨8219625787673738564182109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5479750525115825709454739 8219625787673738564182109)
                    ·
                      refine ⟨3082359670377651961568291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8219625787673738564182109 3082359670377651961568291)
                      ·
                        rfl

theorem cell23_6002874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3].length) (baseStart_6002874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002874 prefixEnd_6002874 := by exact prefixLift 6002874
  have htrace : WordTrace (prefixWord ++ tailWord_6002874) baseStart_6002874 baseEnd_6002874 := by
    simpa [prefixWord, tailWord_6002874, baseEnd_6002874] using wordTrace_append hprefix tailTrace_6002874
  have hstable : (prefixWord ++ tailWord_6002874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002874).length < 2 ^ (prefixWord ++ tailWord_6002874).sum := by decide
  have hdescent : baseEnd_6002874 < baseStart_6002874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002894 : List Nat := [4, 1, 1, 1, 4, 1, 1, 4, 1, 5]
def baseStart_6002894 : Nat := 118140960795 + 6002894 * 2 ^ 59
def prefixEnd_6002894 : Nat := 4983230072969 + 3 ^ 40 * 6002894 * 2
def baseEnd_6002894 : Nat := 1027456646663580627772733

theorem tailTrace_6002894 : CollatzResearch.WordTrace tailWord_6002894 prefixEnd_6002894 1027456646663580627772733 := by
  unfold tailWord_6002894
  simp only [CollatzResearch.WordTrace]
  refine ⟨27367941389318465689869967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145962354076365150345973157 27367941389318465689869967)
  ·
    refine ⟨41051912083977698534804951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27367941389318465689869967 41051912083977698534804951)
    ·
      refine ⟨61577868125966547802207427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41051912083977698534804951 61577868125966547802207427)
      ·
        refine ⟨92366802188949821703311141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61577868125966547802207427 92366802188949821703311141)
        ·
          refine ⟨17318775410428091569370839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92366802188949821703311141 17318775410428091569370839)
          ·
            refine ⟨25978163115642137354056259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17318775410428091569370839 25978163115642137354056259)
            ·
              refine ⟨38967244673463206031084389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25978163115642137354056259 38967244673463206031084389)
              ·
                refine ⟨7306358376274351130828323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38967244673463206031084389 7306358376274351130828323)
                ·
                  refine ⟨10959537564411526696242485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7306358376274351130828323 10959537564411526696242485)
                  ·
                    refine ⟨1027456646663580627772733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10959537564411526696242485 1027456646663580627772733)
                    ·
                      rfl

theorem cell23_6002894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_6002894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002894 prefixEnd_6002894 := by exact prefixLift 6002894
  have htrace : WordTrace (prefixWord ++ tailWord_6002894) baseStart_6002894 baseEnd_6002894 := by
    simpa [prefixWord, tailWord_6002894, baseEnd_6002894] using wordTrace_append hprefix tailTrace_6002894
  have hstable : (prefixWord ++ tailWord_6002894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002894).length < 2 ^ (prefixWord ++ tailWord_6002894).sum := by decide
  have hdescent : baseEnd_6002894 < baseStart_6002894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002897 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 3, 1, 4]
def baseStart_6002897 : Nat := 118140960795 + 6002897 * 2 ^ 59
def prefixEnd_6002897 : Nat := 4983230072969 + 3 ^ 40 * 6002897 * 2
def baseEnd_6002897 : Nat := 3082371480432705371580685

theorem tailTrace_6002897 : CollatzResearch.WordTrace tailWord_6002897 prefixEnd_6002897 3082371480432705371580685 := by
  unfold tailWord_6002897
  simp only [CollatzResearch.WordTrace]
  refine ⟨218943640533536857031318945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145962427022357904687545963 218943640533536857031318945)
  ·
    refine ⟨164207730400152642773489209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218943640533536857031318945 164207730400152642773489209)
    ·
      refine ⟨123155797800114482080116907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164207730400152642773489209 123155797800114482080116907)
      ·
        refine ⟨184733696700171723120175361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123155797800114482080116907 184733696700171723120175361)
        ·
          refine ⟨138550272525128792340131521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184733696700171723120175361 138550272525128792340131521)
          ·
            refine ⟨103912704393846594255098641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138550272525128792340131521 103912704393846594255098641)
            ·
              refine ⟨77934528295384945691323981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103912704393846594255098641 77934528295384945691323981)
              ·
                refine ⟨29225448110769354634246493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77934528295384945691323981 29225448110769354634246493)
                ·
                  refine ⟨10959543041538507987842435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29225448110769354634246493 10959543041538507987842435)
                  ·
                    refine ⟨16439314562307761981763653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10959543041538507987842435 16439314562307761981763653)
                    ·
                      refine ⟨3082371480432705371580685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16439314562307761981763653 3082371480432705371580685)
                      ·
                        rfl

theorem cell23_6002897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_6002897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002897 prefixEnd_6002897 := by exact prefixLift 6002897
  have htrace : WordTrace (prefixWord ++ tailWord_6002897) baseStart_6002897 baseEnd_6002897 := by
    simpa [prefixWord, tailWord_6002897, baseEnd_6002897] using wordTrace_append hprefix tailTrace_6002897
  have hstable : (prefixWord ++ tailWord_6002897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002897).length < 2 ^ (prefixWord ++ tailWord_6002897).sum := by decide
  have hdescent : baseEnd_6002897 < baseStart_6002897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002907 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 4, 4]
def baseStart_6002907 : Nat := 118140960795 + 6002907 * 2 ^ 59
def prefixEnd_6002907 : Nat := 4983230072969 + 3 ^ 40 * 6002907 * 2
def baseEnd_6002907 : Nat := 1027458871746416777485213

theorem tailTrace_6002907 : CollatzResearch.WordTrace tailWord_6002907 prefixEnd_6002907 1027458871746416777485213 := by
  unfold tailWord_6002907
  simp only [CollatzResearch.WordTrace]
  refine ⟨218944005263500628739182975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145962670175667085826121983 218944005263500628739182975)
  ·
    refine ⟨328416007895250943108774463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218944005263500628739182975 328416007895250943108774463)
    ·
      refine ⟨492624011842876414663161695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328416007895250943108774463 492624011842876414663161695)
      ·
        refine ⟨738936017764314621994742543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492624011842876414663161695 738936017764314621994742543)
        ·
          refine ⟨1108404026646471932992113815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738936017764314621994742543 1108404026646471932992113815)
          ·
            refine ⟨1662606039969707899488170723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1108404026646471932992113815 1662606039969707899488170723)
            ·
              refine ⟨2493909059954561849232256085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1662606039969707899488170723 2493909059954561849232256085)
              ·
                refine ⟨29225496796342521670690501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2493909059954561849232256085 29225496796342521670690501)
                ·
                  refine ⟨5479780649314222813254469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29225496796342521670690501 5479780649314222813254469)
                  ·
                    refine ⟨1027458871746416777485213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5479780649314222813254469 1027458871746416777485213)
                    ·
                      rfl

theorem cell23_6002907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 4].length) (baseStart_6002907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002907 prefixEnd_6002907 := by exact prefixLift 6002907
  have htrace : WordTrace (prefixWord ++ tailWord_6002907) baseStart_6002907 baseEnd_6002907 := by
    simpa [prefixWord, tailWord_6002907, baseEnd_6002907] using wordTrace_append hprefix tailTrace_6002907
  have hstable : (prefixWord ++ tailWord_6002907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002907).length < 2 ^ (prefixWord ++ tailWord_6002907).sum := by decide
  have hdescent : baseEnd_6002907 < baseStart_6002907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002924 : List Nat := [2, 2, 1, 1, 2, 3, 2, 4, 2, 4]
def baseStart_6002924 : Nat := 118140960795 + 6002924 * 2 ^ 59
def prefixEnd_6002924 : Nat := 4983230072969 + 3 ^ 40 * 6002924 * 2
def baseEnd_6002924 : Nat := 1027461781470125588647687

theorem tailTrace_6002924 : CollatzResearch.WordTrace tailWord_6002924 prefixEnd_6002924 1027461781470125588647687 := by
  unfold tailWord_6002924
  simp only [CollatzResearch.WordTrace]
  refine ⟨109472312652219520321275913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145963083536292693761701217 109472312652219520321275913)
  ·
    refine ⟨82104234489164640240956935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109472312652219520321275913 82104234489164640240956935)
    ·
      refine ⟨123156351733746960361435403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82104234489164640240956935 123156351733746960361435403)
      ·
        refine ⟨184734527600620440542153105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123156351733746960361435403 184734527600620440542153105)
        ·
          refine ⟨138550895700465330406614829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184734527600620440542153105 138550895700465330406614829)
          ·
            refine ⟨51956585887674498902480561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138550895700465330406614829 51956585887674498902480561)
            ·
              refine ⟨38967439415755874176860421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51956585887674498902480561 38967439415755874176860421)
              ·
                refine ⟨7306394890454226408161329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38967439415755874176860421 7306394890454226408161329)
                ·
                  refine ⟨5479796167840669806120997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7306394890454226408161329 5479796167840669806120997)
                  ·
                    refine ⟨1027461781470125588647687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5479796167840669806120997 1027461781470125588647687)
                    ·
                      rfl

theorem cell23_6002924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 4].length) (baseStart_6002924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002924 prefixEnd_6002924 := by exact prefixLift 6002924
  have htrace : WordTrace (prefixWord ++ tailWord_6002924) baseStart_6002924 baseEnd_6002924 := by
    simpa [prefixWord, tailWord_6002924, baseEnd_6002924] using wordTrace_append hprefix tailTrace_6002924
  have hstable : (prefixWord ++ tailWord_6002924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002924).length < 2 ^ (prefixWord ++ tailWord_6002924).sum := by decide
  have hdescent : baseEnd_6002924 < baseStart_6002924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002925 : List Nat := [1, 5, 1, 2, 4, 1, 1, 1, 3, 1, 3]
def baseStart_6002925 : Nat := 118140960795 + 6002925 * 2 ^ 59
def prefixEnd_6002925 : Nat := 4983230072969 + 3 ^ 40 * 6002925 * 2
def baseEnd_6002925 : Nat := 3082385857891031262030557

theorem tailTrace_6002925 : CollatzResearch.WordTrace tailWord_6002925 prefixEnd_6002925 3082385857891031262030557 := by
  unfold tailWord_6002925
  simp only [CollatzResearch.WordTrace]
  refine ⟨218944661777435417813338229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145963107851623611875558819 218944661777435417813338229)
  ·
    refine ⟨20526062041634570420000459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218944661777435417813338229 20526062041634570420000459)
    ·
      refine ⟨30789093062451855630000689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20526062041634570420000459 30789093062451855630000689)
      ·
        refine ⟨23091819796838891722500517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30789093062451855630000689 23091819796838891722500517)
        ·
          refine ⟨4329716211907292197968847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23091819796838891722500517 4329716211907292197968847)
          ·
            refine ⟨6494574317860938296953271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4329716211907292197968847 6494574317860938296953271)
            ·
              refine ⟨9741861476791407445429907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6494574317860938296953271 9741861476791407445429907)
              ·
                refine ⟨14612792215187111168144861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9741861476791407445429907 14612792215187111168144861)
                ·
                  refine ⟨5479797080695166688054323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14612792215187111168144861 5479797080695166688054323)
                  ·
                    refine ⟨8219695621042750032081485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5479797080695166688054323 8219695621042750032081485)
                    ·
                      refine ⟨3082385857891031262030557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8219695621042750032081485 3082385857891031262030557)
                      ·
                        rfl

theorem cell23_6002925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_6002925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002925 prefixEnd_6002925 := by exact prefixLift 6002925
  have htrace : WordTrace (prefixWord ++ tailWord_6002925) baseStart_6002925 baseEnd_6002925 := by
    simpa [prefixWord, tailWord_6002925, baseEnd_6002925] using wordTrace_append hprefix tailTrace_6002925
  have hstable : (prefixWord ++ tailWord_6002925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002925).length < 2 ^ (prefixWord ++ tailWord_6002925).sum := by decide
  have hdescent : baseEnd_6002925 < baseStart_6002925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002927 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 6]
def baseStart_6002927 : Nat := 118140960795 + 6002927 * 2 ^ 59
def prefixEnd_6002927 : Nat := 4983230072969 + 3 ^ 40 * 6002927 * 2
def baseEnd_6002927 : Nat := 3082386884852340254205547

theorem tailTrace_6002927 : CollatzResearch.WordTrace tailWord_6002927 prefixEnd_6002927 3082386884852340254205547 := by
  unfold tailWord_6002927
  simp only [CollatzResearch.WordTrace]
  refine ⟨218944734723428172154911035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145963156482285448103274023 218944734723428172154911035)
  ·
    refine ⟨328417102085142258232366553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218944734723428172154911035 328417102085142258232366553)
    ·
      refine ⟨246312826563856693674274915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328417102085142258232366553 246312826563856693674274915)
      ·
        refine ⟨369469239845785040511412373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246312826563856693674274915 369469239845785040511412373)
        ·
          refine ⟨17318870617771173773972455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 369469239845785040511412373 17318870617771173773972455)
          ·
            refine ⟨25978305926656760660958683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17318870617771173773972455 25978305926656760660958683)
            ·
              refine ⟨38967458889985140991438025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25978305926656760660958683 38967458889985140991438025)
              ·
                refine ⟨29225594167488855743578519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38967458889985140991438025 29225594167488855743578519)
                ·
                  refine ⟨43838391251233283615367779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29225594167488855743578519 43838391251233283615367779)
                  ·
                    refine ⟨65757586876849925423051669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43838391251233283615367779 65757586876849925423051669)
                    ·
                      refine ⟨3082386884852340254205547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65757586876849925423051669 3082386884852340254205547)
                      ·
                        rfl

theorem cell23_6002927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 6].length) (baseStart_6002927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002927 prefixEnd_6002927 := by exact prefixLift 6002927
  have htrace : WordTrace (prefixWord ++ tailWord_6002927) baseStart_6002927 baseEnd_6002927 := by
    simpa [prefixWord, tailWord_6002927, baseEnd_6002927] using wordTrace_append hprefix tailTrace_6002927
  have hstable : (prefixWord ++ tailWord_6002927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002927).length < 2 ^ (prefixWord ++ tailWord_6002927).sum := by decide
  have hdescent : baseEnd_6002927 < baseStart_6002927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002934 : List Nat := [5, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_6002934 : Nat := 118140960795 + 6002934 * 2 ^ 59
def prefixEnd_6002934 : Nat := 4983230072969 + 3 ^ 40 * 6002934 * 2
def baseEnd_6002934 : Nat := 3082390479216921726818015

theorem tailTrace_6002934 : CollatzResearch.WordTrace tailWord_6002934 prefixEnd_6002934 3082390479216921726818015 := by
  unfold tailWord_6002934
  simp only [CollatzResearch.WordTrace]
  refine ⟨13684061877150175771900991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145963326689601874900277237 13684061877150175771900991)
  ·
    refine ⟨20526092815725263657851487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13684061877150175771900991 20526092815725263657851487)
    ·
      refine ⟨30789139223587895486777231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20526092815725263657851487 30789139223587895486777231)
      ·
        refine ⟨46183708835381843230165847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30789139223587895486777231 46183708835381843230165847)
        ·
          refine ⟨69275563253072764845248771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46183708835381843230165847 69275563253072764845248771)
          ·
            refine ⟨103913344879609147267873157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69275563253072764845248771 103913344879609147267873157)
            ·
              refine ⟨19483752164926715112726217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103913344879609147267873157 19483752164926715112726217)
              ·
                refine ⟨14612814123695036334544663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19483752164926715112726217 14612814123695036334544663)
                ·
                  refine ⟨21919221185542554501816995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14612814123695036334544663 21919221185542554501816995)
                  ·
                    refine ⟨32878831778313831752725493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21919221185542554501816995 32878831778313831752725493)
                    ·
                      refine ⟨3082390479216921726818015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32878831778313831752725493 3082390479216921726818015)
                      ·
                        rfl

theorem cell23_6002934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_6002934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002934 prefixEnd_6002934 := by exact prefixLift 6002934
  have htrace : WordTrace (prefixWord ++ tailWord_6002934) baseStart_6002934 baseEnd_6002934 := by
    simpa [prefixWord, tailWord_6002934, baseEnd_6002934] using wordTrace_append hprefix tailTrace_6002934
  have hstable : (prefixWord ++ tailWord_6002934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002934).length < 2 ^ (prefixWord ++ tailWord_6002934).sum := by decide
  have hdescent : baseEnd_6002934 < baseStart_6002934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002948 : List Nat := [2, 3, 2, 2, 3, 2, 1, 2, 1, 1, 4]
def baseStart_6002948 : Nat := 118140960795 + 6002948 * 2 ^ 59
def prefixEnd_6002948 : Nat := 4983230072969 + 3 ^ 40 * 6002948 * 2
def baseEnd_6002948 : Nat := 3082397667946084672042951

theorem tailTrace_6002948 : CollatzResearch.WordTrace tailWord_6002948 prefixEnd_6002948 3082397667946084672042951 := by
  unfold tailWord_6002948
  simp only [CollatzResearch.WordTrace]
  refine ⟨109472750328176046370712749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145963667104234728494283665 109472750328176046370712749)
  ·
    refine ⟨41052281373066017389017281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109472750328176046370712749 41052281373066017389017281)
    ·
      refine ⟨30789211029799513041762961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41052281373066017389017281 30789211029799513041762961)
      ·
        refine ⟨23091908272349634781322221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30789211029799513041762961 23091908272349634781322221)
        ·
          refine ⟨8659465602131113042995833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23091908272349634781322221 8659465602131113042995833)
          ·
            refine ⟨6494599201598334782246875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8659465602131113042995833 6494599201598334782246875)
            ·
              refine ⟨9741898802397502173370313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6494599201598334782246875 9741898802397502173370313)
              ·
                refine ⟨7306424101798126630027735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9741898802397502173370313 7306424101798126630027735)
                ·
                  refine ⟨10959636152697189945041603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7306424101798126630027735 10959636152697189945041603)
                  ·
                    refine ⟨16439454229045784917562405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10959636152697189945041603 16439454229045784917562405)
                    ·
                      refine ⟨3082397667946084672042951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16439454229045784917562405 3082397667946084672042951)
                      ·
                        rfl

theorem cell23_6002948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_6002948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002948 prefixEnd_6002948 := by exact prefixLift 6002948
  have htrace : WordTrace (prefixWord ++ tailWord_6002948) baseStart_6002948 baseEnd_6002948 := by
    simpa [prefixWord, tailWord_6002948, baseEnd_6002948] using wordTrace_append hprefix tailTrace_6002948
  have hstable : (prefixWord ++ tailWord_6002948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002948).length < 2 ^ (prefixWord ++ tailWord_6002948).sum := by decide
  have hdescent : baseEnd_6002948 < baseStart_6002948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002977 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 2, 2, 5]
def baseStart_6002977 : Nat := 118140960795 + 6002977 * 2 ^ 59
def prefixEnd_6002977 : Nat := 4983230072969 + 3 ^ 40 * 6002977 * 2
def baseEnd_6002977 : Nat := 3082412558885065058580317

theorem tailTrace_6002977 : CollatzResearch.WordTrace tailWord_6002977 prefixEnd_6002977 3082412558885065058580317 := by
  unfold tailWord_6002977
  simp only [CollatzResearch.WordTrace]
  refine ⟨218946558373247030694231185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145964372248831353796154123 218946558373247030694231185)
  ·
    refine ⟨164209918779935273020673389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218946558373247030694231185 164209918779935273020673389)
    ·
      refine ⟨61578719542475727382752521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164209918779935273020673389 61578719542475727382752521)
      ·
        refine ⟨46184039656856795537064391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61578719542475727382752521 46184039656856795537064391)
        ·
          refine ⟨69276059485285193305596587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46184039656856795537064391 69276059485285193305596587)
          ·
            refine ⟨103914089227927789958394881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69276059485285193305596587 103914089227927789958394881)
            ·
              refine ⟨77935566920945842468796161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103914089227927789958394881 77935566920945842468796161)
              ·
                refine ⟨58451675190709381851597121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77935566920945842468796161 58451675190709381851597121)
                ·
                  refine ⟨43838756393032036388697841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58451675190709381851597121 43838756393032036388697841)
                  ·
                    refine ⟨32879067294774027291523381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43838756393032036388697841 32879067294774027291523381)
                    ·
                      refine ⟨3082412558885065058580317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32879067294774027291523381 3082412558885065058580317)
                      ·
                        rfl

theorem cell23_6002977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_6002977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002977 prefixEnd_6002977 := by exact prefixLift 6002977
  have htrace : WordTrace (prefixWord ++ tailWord_6002977) baseStart_6002977 baseEnd_6002977 := by
    simpa [prefixWord, tailWord_6002977, baseEnd_6002977] using wordTrace_append hprefix tailTrace_6002977
  have hstable : (prefixWord ++ tailWord_6002977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002977).length < 2 ^ (prefixWord ++ tailWord_6002977).sum := by decide
  have hdescent : baseEnd_6002977 < baseStart_6002977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003017 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 3, 4, 4]
def baseStart_6003017 : Nat := 118140960795 + 6003017 * 2 ^ 59
def prefixEnd_6003017 : Nat := 4983230072969 + 3 ^ 40 * 6003017 * 2
def baseEnd_6003017 : Nat := 3082433098111244902080133

theorem tailTrace_6003017 : CollatzResearch.WordTrace tailWord_6003017 prefixEnd_6003017 3082433098111244902080133 := by
  unfold tailWord_6003017
  simp only [CollatzResearch.WordTrace]
  refine ⟨218948017293102117525687305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145965344862068078350458203 218948017293102117525687305)
  ·
    refine ⟨164211012969826588144265479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218948017293102117525687305 164211012969826588144265479)
    ·
      refine ⟨246316519454739882216398219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164211012969826588144265479 246316519454739882216398219)
      ·
        refine ⟨369474779182109823324597329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246316519454739882216398219 369474779182109823324597329)
        ·
          refine ⟨277106084386582367493447997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369474779182109823324597329 277106084386582367493447997)
          ·
            refine ⟨103914781644968387810042999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277106084386582367493447997 103914781644968387810042999)
            ·
              refine ⟨155872172467452581715064499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103914781644968387810042999 155872172467452581715064499)
              ·
                refine ⟨233808258701178872572596749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155872172467452581715064499 233808258701178872572596749)
                ·
                  refine ⟨87678097012942077214723781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233808258701178872572596749 87678097012942077214723781)
                  ·
                    refine ⟨16439643189926639477760709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87678097012942077214723781 16439643189926639477760709)
                    ·
                      refine ⟨3082433098111244902080133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16439643189926639477760709 3082433098111244902080133)
                      ·
                        rfl

theorem cell23_6003017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 4, 4].length) (baseStart_6003017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003017 prefixEnd_6003017 := by exact prefixLift 6003017
  have htrace : WordTrace (prefixWord ++ tailWord_6003017) baseStart_6003017 baseEnd_6003017 := by
    simpa [prefixWord, tailWord_6003017, baseEnd_6003017] using wordTrace_append hprefix tailTrace_6003017
  have hstable : (prefixWord ++ tailWord_6003017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003017).length < 2 ^ (prefixWord ++ tailWord_6003017).sum := by decide
  have hdescent : baseEnd_6003017 < baseStart_6003017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003025 : List Nat := [1, 2, 2, 1, 4, 4, 2, 1, 1, 3, 2]
def baseStart_6003025 : Nat := 118140960795 + 6003025 * 2 ^ 59
def prefixEnd_6003025 : Nat := 4983230072969 + 3 ^ 40 * 6003025 * 2
def baseEnd_6003025 : Nat := 3082437205956480870780097

theorem tailTrace_6003025 : CollatzResearch.WordTrace tailWord_6003025 prefixEnd_6003025 3082437205956480870780097 := by
  unfold tailWord_6003025
  simp only [CollatzResearch.WordTrace]
  refine ⟨218948309077073134891978529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145965539384715423261319019 218948309077073134891978529)
  ·
    refine ⟨164211231807804851168983897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218948309077073134891978529 164211231807804851168983897)
    ·
      refine ⟨123158423855853638376737923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164211231807804851168983897 123158423855853638376737923)
      ·
        refine ⟨184737635783780457565106885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123158423855853638376737923 184737635783780457565106885)
        ·
          refine ⟨34638306709458835793457541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184737635783780457565106885 34638306709458835793457541)
          ·
            refine ⟨6494682508023531711273289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34638306709458835793457541 6494682508023531711273289)
            ·
              refine ⟨4871011881017648783454967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6494682508023531711273289 4871011881017648783454967)
              ·
                refine ⟨7306517821526473175182451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4871011881017648783454967 7306517821526473175182451)
                ·
                  refine ⟨10959776732289709762773677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7306517821526473175182451 10959776732289709762773677)
                  ·
                    refine ⟨4109916274608641161040129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10959776732289709762773677 4109916274608641161040129)
                    ·
                      refine ⟨3082437205956480870780097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4109916274608641161040129 3082437205956480870780097)
                      ·
                        rfl

theorem cell23_6003025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 1, 3, 2].length) (baseStart_6003025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003025 prefixEnd_6003025 := by exact prefixLift 6003025
  have htrace : WordTrace (prefixWord ++ tailWord_6003025) baseStart_6003025 baseEnd_6003025 := by
    simpa [prefixWord, tailWord_6003025, baseEnd_6003025] using wordTrace_append hprefix tailTrace_6003025
  have hstable : (prefixWord ++ tailWord_6003025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003025).length < 2 ^ (prefixWord ++ tailWord_6003025).sum := by decide
  have hdescent : baseEnd_6003025 < baseStart_6003025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003044 : List Nat := [2, 3, 1, 1, 3, 1, 4, 1, 7]
def baseStart_6003044 : Nat := 118140960795 + 6003044 * 2 ^ 59
def prefixEnd_6003044 : Nat := 4983230072969 + 3 ^ 40 * 6003044 * 2
def baseEnd_6003044 : Nat := 342494106898768477382501

theorem tailTrace_6003044 : CollatzResearch.WordTrace tailWord_6003044 prefixEnd_6003044 342494106898768477382501 := by
  unfold tailWord_6003044
  simp only [CollatzResearch.WordTrace]
  refine ⟨109474501032002150568460093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145966001376002867424613457 109474501032002150568460093)
  ·
    refine ⟨41052937887000806463172535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109474501032002150568460093 41052937887000806463172535)
    ·
      refine ⟨61579406830501209694758803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41052937887000806463172535 61579406830501209694758803)
      ·
        refine ⟨92369110245751814542138205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61579406830501209694758803 92369110245751814542138205)
        ·
          refine ⟨34638416342156930453301827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92369110245751814542138205 34638416342156930453301827)
          ·
            refine ⟨51957624513235395679952741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34638416342156930453301827 51957624513235395679952741)
            ·
              refine ⟨9742054596231636689991139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51957624513235395679952741 9742054596231636689991139)
              ·
                refine ⟨14613081894347455034986709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9742054596231636689991139 14613081894347455034986709)
                ·
                  refine ⟨342494106898768477382501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14613081894347455034986709 342494106898768477382501)
                  ·
                    rfl

theorem cell23_6003044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_6003044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003044 prefixEnd_6003044 := by exact prefixLift 6003044
  have htrace : WordTrace (prefixWord ++ tailWord_6003044) baseStart_6003044 baseEnd_6003044 := by
    simpa [prefixWord, tailWord_6003044, baseEnd_6003044] using wordTrace_append hprefix tailTrace_6003044
  have hstable : (prefixWord ++ tailWord_6003044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003044).length < 2 ^ (prefixWord ++ tailWord_6003044).sum := by decide
  have hdescent : baseEnd_6003044 < baseStart_6003044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003101 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 1, 2, 5]
def baseStart_6003101 : Nat := 118140960795 + 6003101 * 2 ^ 59
def prefixEnd_6003101 : Nat := 4983230072969 + 3 ^ 40 * 6003101 * 2
def baseEnd_6003101 : Nat := 3082476230486222573429747

theorem tailTrace_6003101 : CollatzResearch.WordTrace tailWord_6003101 prefixEnd_6003101 3082476230486222573429747 := by
  unfold tailWord_6003101
  simp only [CollatzResearch.WordTrace]
  refine ⟨218951081024797799871745157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145967387349865199914496771 218951081024797799871745157)
  ·
    refine ⟨41053327692149587475952217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218951081024797799871745157 41053327692149587475952217)
    ·
      refine ⟨30789995769112190606964163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41053327692149587475952217 30789995769112190606964163)
      ·
        refine ⟨46184993653668285910446245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30789995769112190606964163 46184993653668285910446245)
        ·
          refine ⟨8659686310062803608208671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46184993653668285910446245 8659686310062803608208671)
          ·
            refine ⟨12989529465094205412313007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8659686310062803608208671 12989529465094205412313007)
            ·
              refine ⟨19484294197641308118469511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12989529465094205412313007 19484294197641308118469511)
              ·
                refine ⟨29226441296461962177704267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19484294197641308118469511 29226441296461962177704267)
                ·
                  refine ⟨43839661944692943266556401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29226441296461962177704267 43839661944692943266556401)
                  ·
                    refine ⟨32879746458519707449917301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43839661944692943266556401 32879746458519707449917301)
                    ·
                      refine ⟨3082476230486222573429747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32879746458519707449917301 3082476230486222573429747)
                      ·
                        rfl

theorem cell23_6003101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_6003101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003101 prefixEnd_6003101 := by exact prefixLift 6003101
  have htrace : WordTrace (prefixWord ++ tailWord_6003101) baseStart_6003101 baseEnd_6003101 := by
    simpa [prefixWord, tailWord_6003101, baseEnd_6003101] using wordTrace_append hprefix tailTrace_6003101
  have hstable : (prefixWord ++ tailWord_6003101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003101).length < 2 ^ (prefixWord ++ tailWord_6003101).sum := by decide
  have hdescent : baseEnd_6003101 < baseStart_6003101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003134 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 10]
def baseStart_6003134 : Nat := 118140960795 + 6003134 * 2 ^ 59
def prefixEnd_6003134 : Nat := 4983230072969 + 3 ^ 40 * 6003134 * 2
def baseEnd_6003134 : Nat := 342499241705313438257455

theorem tailTrace_6003134 : CollatzResearch.WordTrace tailWord_6003134 prefixEnd_6003134 342499241705313438257455 := by
  unfold tailWord_6003134
  simp only [CollatzResearch.WordTrace]
  refine ⟨27369035579209780813462057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145968189755785497671797637 27369035579209780813462057)
  ·
    refine ⟨20526776684407335610096543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27369035579209780813462057 20526776684407335610096543)
    ·
      refine ⟨30790165026611003415144815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20526776684407335610096543 30790165026611003415144815)
      ·
        refine ⟨46185247539916505122717223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30790165026611003415144815 46185247539916505122717223)
        ·
          refine ⟨69277871309874757684075835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46185247539916505122717223 69277871309874757684075835)
          ·
            refine ⟨103916806964812136526113753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69277871309874757684075835 103916806964812136526113753)
            ·
              refine ⟨77937605223609102394585315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103916806964812136526113753 77937605223609102394585315)
              ·
                refine ⟨116906407835413653591877973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77937605223609102394585315 116906407835413653591877973)
                ·
                  refine ⟨342499241705313438257455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 116906407835413653591877973 342499241705313438257455)
                  ·
                    rfl

theorem cell23_6003134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_6003134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003134 prefixEnd_6003134 := by exact prefixLift 6003134
  have htrace : WordTrace (prefixWord ++ tailWord_6003134) baseStart_6003134 baseEnd_6003134 := by
    simpa [prefixWord, tailWord_6003134, baseEnd_6003134] using wordTrace_append hprefix tailTrace_6003134
  have hstable : (prefixWord ++ tailWord_6003134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003134).length < 2 ^ (prefixWord ++ tailWord_6003134).sum := by decide
  have hdescent : baseEnd_6003134 < baseStart_6003134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003178 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 3]
def baseStart_6003178 : Nat := 118140960795 + 6003178 * 2 ^ 59
def prefixEnd_6003178 : Nat := 4983230072969 + 3 ^ 40 * 6003178 * 2
def baseEnd_6003178 : Nat := 3082515768496618772166893

theorem tailTrace_6003178 : CollatzResearch.WordTrace tailWord_6003178 prefixEnd_6003178 3082515768496618772166893 := by
  unfold tailWord_6003178
  simp only [CollatzResearch.WordTrace]
  refine ⟨54738472361379710505574547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145969259630345894681532125 54738472361379710505574547)
  ·
    refine ⟨82107708542069565758361821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54738472361379710505574547 82107708542069565758361821)
    ·
      refine ⟨30790390703276087159385683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82107708542069565758361821 30790390703276087159385683)
      ·
        refine ⟨46185586054914130739078525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30790390703276087159385683 46185586054914130739078525)
        ·
          refine ⟨17319594770592799027154447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46185586054914130739078525 17319594770592799027154447)
          ·
            refine ⟨25979392155889198540731671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17319594770592799027154447 25979392155889198540731671)
            ·
              refine ⟨38969088233833797811097507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25979392155889198540731671 38969088233833797811097507)
              ·
                refine ⟨58453632350750696716646261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38969088233833797811097507 58453632350750696716646261)
                ·
                  refine ⟨5480028032882877817185587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58453632350750696716646261 5480028032882877817185587)
                  ·
                    refine ⟨8220042049324316725778381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5480028032882877817185587 8220042049324316725778381)
                    ·
                      refine ⟨3082515768496618772166893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8220042049324316725778381 3082515768496618772166893)
                      ·
                        rfl

theorem cell23_6003178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_6003178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003178 prefixEnd_6003178 := by exact prefixLift 6003178
  have htrace : WordTrace (prefixWord ++ tailWord_6003178) baseStart_6003178 baseEnd_6003178 := by
    simpa [prefixWord, tailWord_6003178, baseEnd_6003178] using wordTrace_append hprefix tailTrace_6003178
  have hstable : (prefixWord ++ tailWord_6003178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003178).length < 2 ^ (prefixWord ++ tailWord_6003178).sum := by decide
  have hdescent : baseEnd_6003178 < baseStart_6003178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003194 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 3, 6]
def baseStart_6003194 : Nat := 118140960795 + 6003194 * 2 ^ 59
def prefixEnd_6003194 : Nat := 4983230072969 + 3 ^ 40 * 6003194 * 2
def baseEnd_6003194 : Nat := 1027507994729030236522273

theorem tailTrace_6003194 : CollatzResearch.WordTrace tailWord_6003194 prefixEnd_6003194 1027507994729030236522273 := by
  unfold tailWord_6003194
  simp only [CollatzResearch.WordTrace]
  refine ⟨54738618253365219188720159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145969648675640584503253757 54738618253365219188720159)
  ·
    refine ⟨82107927380047828783080239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54738618253365219188720159 82107927380047828783080239)
    ·
      refine ⟨123161891070071743174620359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82107927380047828783080239 123161891070071743174620359)
      ·
        refine ⟨184742836605107614761930539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123161891070071743174620359 184742836605107614761930539)
        ·
          refine ⟨277114254907661422142895809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184742836605107614761930539 277114254907661422142895809)
          ·
            refine ⟨207835691180746066607171857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277114254907661422142895809 207835691180746066607171857)
            ·
              refine ⟨155876768385559549955378893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207835691180746066607171857 155876768385559549955378893)
              ·
                refine ⟨58453788144584831233267085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155876768385559549955378893 58453788144584831233267085)
                ·
                  refine ⟨21920170554219311712475157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58453788144584831233267085 21920170554219311712475157)
                  ·
                    refine ⟨1027507994729030236522273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21920170554219311712475157 1027507994729030236522273)
                    ·
                      rfl

theorem cell23_6003194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_6003194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003194 prefixEnd_6003194 := by exact prefixLift 6003194
  have htrace : WordTrace (prefixWord ++ tailWord_6003194) baseStart_6003194 baseEnd_6003194 := by
    simpa [prefixWord, tailWord_6003194, baseEnd_6003194] using wordTrace_append hprefix tailTrace_6003194
  have hstable : (prefixWord ++ tailWord_6003194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003194).length < 2 ^ (prefixWord ++ tailWord_6003194).sum := by decide
  have hdescent : baseEnd_6003194 < baseStart_6003194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003202 : List Nat := [3, 4, 1, 2, 3, 1, 1, 2, 6]
def baseStart_6003202 : Nat := 118140960795 + 6003202 * 2 ^ 59
def prefixEnd_6003202 : Nat := 4983230072969 + 3 ^ 40 * 6003202 * 2
def baseEnd_6003202 : Nat := 342503121336925186474087

theorem tailTrace_6003202 : CollatzResearch.WordTrace tailWord_6003202 prefixEnd_6003202 342503121336925186474087 := by
  unfold tailWord_6003202
  simp only [CollatzResearch.WordTrace]
  refine ⟨54738691199357973530292965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145969843198287929414114573 54738691199357973530292965)
  ·
    refine ⟨10263504599879620036929931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54738691199357973530292965 10263504599879620036929931)
    ·
      refine ⟨15395256899819430055394897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10263504599879620036929931 15395256899819430055394897)
      ·
        refine ⟨11546442674864572541546173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15395256899819430055394897 11546442674864572541546173)
        ·
          refine ⟨4329916003074214703079815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11546442674864572541546173 4329916003074214703079815)
          ·
            refine ⟨6494874004611322054619723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4329916003074214703079815 6494874004611322054619723)
            ·
              refine ⟨9742311006916983081929585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6494874004611322054619723 9742311006916983081929585)
              ·
                refine ⟨7306733255187737311447189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9742311006916983081929585 7306733255187737311447189)
                ·
                  refine ⟨342503121336925186474087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7306733255187737311447189 342503121336925186474087)
                  ·
                    rfl

theorem cell23_6003202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_6003202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003202 prefixEnd_6003202 := by exact prefixLift 6003202
  have htrace : WordTrace (prefixWord ++ tailWord_6003202) baseStart_6003202 baseEnd_6003202 := by
    simpa [prefixWord, tailWord_6003202, baseEnd_6003202] using wordTrace_append hprefix tailTrace_6003202
  have hstable : (prefixWord ++ tailWord_6003202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003202).length < 2 ^ (prefixWord ++ tailWord_6003202).sum := by decide
  have hdescent : baseEnd_6003202 < baseStart_6003202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003221 : List Nat := [1, 3, 2, 1, 3, 1, 3, 2, 1, 1, 5]
def baseStart_6003221 : Nat := 118140960795 + 6003221 * 2 ^ 59
def prefixEnd_6003221 : Nat := 4983230072969 + 3 ^ 40 * 6003221 * 2
def baseEnd_6003221 : Nat := 3082537848164762103929195

theorem tailTrace_6003221 : CollatzResearch.WordTrace tailWord_6003221 prefixEnd_6003221 3082537848164762103929195 := by
  unfold tailWord_6003221
  simp only [CollatzResearch.WordTrace]
  refine ⟨218955457784363060366113517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145970305189575373577409011 218955457784363060366113517)
  ·
    refine ⟨82108296669136147637292569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218955457784363060366113517 82108296669136147637292569)
    ·
      refine ⟨61581222501852110727969427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82108296669136147637292569 61581222501852110727969427)
      ·
        refine ⟨92371833752778166091954141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61581222501852110727969427 92371833752778166091954141)
        ·
          refine ⟨34639437657291812284482803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92371833752778166091954141 34639437657291812284482803)
          ·
            refine ⟨51959156485937718426724205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34639437657291812284482803 51959156485937718426724205)
            ·
              refine ⟨19484683682226644410021577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51959156485937718426724205 19484683682226644410021577)
              ·
                refine ⟨14613512761669983307516183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19484683682226644410021577 14613512761669983307516183)
                ·
                  refine ⟨21920269142504974961274275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14613512761669983307516183 21920269142504974961274275)
                  ·
                    refine ⟨32880403713757462441911413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21920269142504974961274275 32880403713757462441911413)
                    ·
                      refine ⟨3082537848164762103929195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32880403713757462441911413 3082537848164762103929195)
                      ·
                        rfl

theorem cell23_6003221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_6003221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003221 prefixEnd_6003221 := by exact prefixLift 6003221
  have htrace : WordTrace (prefixWord ++ tailWord_6003221) baseStart_6003221 baseEnd_6003221 := by
    simpa [prefixWord, tailWord_6003221, baseEnd_6003221] using wordTrace_append hprefix tailTrace_6003221
  have hstable : (prefixWord ++ tailWord_6003221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003221).length < 2 ^ (prefixWord ++ tailWord_6003221).sum := by decide
  have hdescent : baseEnd_6003221 < baseStart_6003221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003228 : List Nat := [2, 2, 3, 1, 2, 4, 1, 1, 1, 6]
def baseStart_6003228 : Nat := 118140960795 + 6003228 * 2 ^ 59
def prefixEnd_6003228 : Nat := 4983230072969 + 3 ^ 40 * 6003228 * 2
def baseEnd_6003228 : Nat := 1027513814176447858847221

theorem tailTrace_6003228 : CollatzResearch.WordTrace tailWord_6003228 prefixEnd_6003228 1027513814176447858847221 := by
  unfold tailWord_6003228
  simp only [CollatzResearch.WordTrace]
  refine ⟨109477856547668850280809169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145970475396891800374412225 109477856547668850280809169)
  ·
    refine ⟨82108392410751637710606877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109477856547668850280809169 82108392410751637710606877)
    ·
      refine ⟨30790647154031864141477579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82108392410751637710606877 30790647154031864141477579)
      ·
        refine ⟨46185970731047796212216369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30790647154031864141477579 46185970731047796212216369)
        ·
          refine ⟨34639478048285847159162277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46185970731047796212216369 34639478048285847159162277)
          ·
            refine ⟨6494902134053596342342927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34639478048285847159162277 6494902134053596342342927)
            ·
              refine ⟨9742353201080394513514391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6494902134053596342342927 9742353201080394513514391)
              ·
                refine ⟨14613529801620591770271587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9742353201080394513514391 14613529801620591770271587)
                ·
                  refine ⟨21920294702430887655407381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14613529801620591770271587 21920294702430887655407381)
                  ·
                    refine ⟨1027513814176447858847221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21920294702430887655407381 1027513814176447858847221)
                    ·
                      rfl

theorem cell23_6003228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_6003228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003228 prefixEnd_6003228 := by exact prefixLift 6003228
  have htrace : WordTrace (prefixWord ++ tailWord_6003228) baseStart_6003228 baseEnd_6003228 := by
    simpa [prefixWord, tailWord_6003228, baseEnd_6003228] using wordTrace_append hprefix tailTrace_6003228
  have hstable : (prefixWord ++ tailWord_6003228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003228).length < 2 ^ (prefixWord ++ tailWord_6003228).sum := by decide
  have hdescent : baseEnd_6003228 < baseStart_6003228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003235 : List Nat := [1, 1, 1, 4, 4, 1, 2, 2, 3, 2, 2]
def baseStart_6003235 : Nat := 118140960795 + 6003235 * 2 ^ 59
def prefixEnd_6003235 : Nat := 4983230072969 + 3 ^ 40 * 6003235 * 2
def baseEnd_6003235 : Nat := 3082545036893925049154131

theorem tailTrace_6003235 : CollatzResearch.WordTrace tailWord_6003235 prefixEnd_6003235 3082545036893925049154131 := by
  unfold tailWord_6003235
  simp only [CollatzResearch.WordTrace]
  refine ⟨218955968406312340757123159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145970645604208227171415439 218955968406312340757123159)
  ·
    refine ⟨328433952609468511135684739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218955968406312340757123159 328433952609468511135684739)
    ·
      refine ⟨492650928914202766703527109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328433952609468511135684739 492650928914202766703527109)
      ·
        refine ⟨92372049171413018756911333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 492650928914202766703527109 92372049171413018756911333)
        ·
          refine ⟨17319759219639941016920875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92372049171413018756911333 17319759219639941016920875)
          ·
            refine ⟨25979638829459911525381313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17319759219639941016920875 25979638829459911525381313)
            ·
              refine ⟨19484729122094933644035985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25979638829459911525381313 19484729122094933644035985)
              ·
                refine ⟨14613546841571200233026989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19484729122094933644035985 14613546841571200233026989)
                ·
                  refine ⟨5480080065589200087385121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14613546841571200233026989 5480080065589200087385121)
                  ·
                    refine ⟨4110060049191900065538841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5480080065589200087385121 4110060049191900065538841)
                    ·
                      refine ⟨3082545036893925049154131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4110060049191900065538841 3082545036893925049154131)
                      ·
                        rfl

theorem cell23_6003235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 2, 2].length) (baseStart_6003235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003235 prefixEnd_6003235 := by exact prefixLift 6003235
  have htrace : WordTrace (prefixWord ++ tailWord_6003235) baseStart_6003235 baseEnd_6003235 := by
    simpa [prefixWord, tailWord_6003235, baseEnd_6003235] using wordTrace_append hprefix tailTrace_6003235
  have hstable : (prefixWord ++ tailWord_6003235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003235).length < 2 ^ (prefixWord ++ tailWord_6003235).sum := by decide
  have hdescent : baseEnd_6003235 < baseStart_6003235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003244 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 6]
def baseStart_6003244 : Nat := 118140960795 + 6003244 * 2 ^ 59
def prefixEnd_6003244 : Nat := 4983230072969 + 3 ^ 40 * 6003244 * 2
def baseEnd_6003244 : Nat := 3082549658219815513941589

theorem tailTrace_6003244 : CollatzResearch.WordTrace tailWord_6003244 prefixEnd_6003244 3082549658219815513941589 := by
  unfold tailWord_6003244
  simp only [CollatzResearch.WordTrace]
  refine ⟨109478148331639867647100393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145970864442186490196133857 109478148331639867647100393)
  ·
    refine ⟨82108611248729900735325295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109478148331639867647100393 82108611248729900735325295)
    ·
      refine ⟨123162916873094851102987943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82108611248729900735325295 123162916873094851102987943)
      ·
        refine ⟨184744375309642276654481915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123162916873094851102987943 184744375309642276654481915)
        ·
          refine ⟨277116562964463414981722873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184744375309642276654481915 277116562964463414981722873)
          ·
            refine ⟨207837422223347561236292155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277116562964463414981722873 207837422223347561236292155)
            ·
              refine ⟨311756133335021341854438233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207837422223347561236292155 311756133335021341854438233)
              ·
                refine ⟨233817100001266006390828675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 311756133335021341854438233 233817100001266006390828675)
                ·
                  refine ⟨350725650001899009586243013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233817100001266006390828675 350725650001899009586243013)
                  ·
                    refine ⟨65761059375356064297420565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 350725650001899009586243013 65761059375356064297420565)
                    ·
                      refine ⟨3082549658219815513941589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65761059375356064297420565 3082549658219815513941589)
                      ·
                        rfl

theorem cell23_6003244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_6003244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003244 prefixEnd_6003244 := by exact prefixLift 6003244
  have htrace : WordTrace (prefixWord ++ tailWord_6003244) baseStart_6003244 baseEnd_6003244 := by
    simpa [prefixWord, tailWord_6003244, baseEnd_6003244] using wordTrace_append hprefix tailTrace_6003244
  have hstable : (prefixWord ++ tailWord_6003244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003244).length < 2 ^ (prefixWord ++ tailWord_6003244).sum := by decide
  have hdescent : baseEnd_6003244 < baseStart_6003244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003246 : List Nat := [4, 1, 3, 1, 4, 1, 1, 3, 1, 1, 3]
def baseStart_6003246 : Nat := 118140960795 + 6003246 * 2 ^ 59
def prefixEnd_6003246 : Nat := 4983230072969 + 3 ^ 40 * 6003246 * 2
def baseEnd_6003246 : Nat := 3082550685181124506116581

theorem tailTrace_6003246 : CollatzResearch.WordTrace tailWord_6003246 prefixEnd_6003246 3082550685181124506116581 := by
  unfold tailWord_6003246
  simp only [CollatzResearch.WordTrace]
  refine ⟨27369546201159061204471699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145970913072848326423849061 27369546201159061204471699)
  ·
    refine ⟨41054319301738591806707549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27369546201159061204471699 41054319301738591806707549)
    ·
      refine ⟨15395369738151971927515331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41054319301738591806707549 15395369738151971927515331)
      ·
        refine ⟨23093054607227957891272997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15395369738151971927515331 23093054607227957891272997)
        ·
          refine ⟨4329947738855242104613687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23093054607227957891272997 4329947738855242104613687)
          ·
            refine ⟨6494921608282863156920531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4329947738855242104613687 6494921608282863156920531)
            ·
              refine ⟨9742382412424294735380797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6494921608282863156920531 9742382412424294735380797)
              ·
                refine ⟨3653393404659110525767799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9742382412424294735380797 3653393404659110525767799)
                ·
                  refine ⟨5480090106988665788651699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3653393404659110525767799 5480090106988665788651699)
                  ·
                    refine ⟨8220135160482998682977549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5480090106988665788651699 8220135160482998682977549)
                    ·
                      refine ⟨3082550685181124506116581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8220135160482998682977549 3082550685181124506116581)
                      ·
                        rfl

theorem cell23_6003246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_6003246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003246 prefixEnd_6003246 := by exact prefixLift 6003246
  have htrace : WordTrace (prefixWord ++ tailWord_6003246) baseStart_6003246 baseEnd_6003246 := by
    simpa [prefixWord, tailWord_6003246, baseEnd_6003246] using wordTrace_append hprefix tailTrace_6003246
  have hstable : (prefixWord ++ tailWord_6003246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003246).length < 2 ^ (prefixWord ++ tailWord_6003246).sum := by decide
  have hdescent : baseEnd_6003246 < baseStart_6003246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003251 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 3]
def baseStart_6003251 : Nat := 118140960795 + 6003251 * 2 ^ 59
def prefixEnd_6003251 : Nat := 4983230072969 + 3 ^ 40 * 6003251 * 2
def baseEnd_6003251 : Nat := 3082553252584396986554057

theorem tailTrace_6003251 : CollatzResearch.WordTrace tailWord_6003251 prefixEnd_6003251 3082553252584396986554057 := by
  unfold tailWord_6003251
  simp only [CollatzResearch.WordTrace]
  refine ⟨218956551974254375489705607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145971034649502916993137071 218956551974254375489705607)
  ·
    refine ⟨328434827961381563234558411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218956551974254375489705607 328434827961381563234558411)
    ·
      refine ⟨492652241942072344851837617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328434827961381563234558411 492652241942072344851837617)
      ·
        refine ⟨369489181456554258638878213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 492652241942072344851837617 369489181456554258638878213)
        ·
          refine ⟨69279221523103923494789665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 369489181456554258638878213 69279221523103923494789665)
          ·
            refine ⟨51959416142327942621092249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69279221523103923494789665 51959416142327942621092249)
            ·
              refine ⟨38969562106745956965819187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51959416142327942621092249 38969562106745956965819187)
              ·
                refine ⟨58454343160118935448728781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38969562106745956965819187 58454343160118935448728781)
                ·
                  refine ⟨21920378685044600793273293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58454343160118935448728781 21920378685044600793273293)
                  ·
                    refine ⟨8220142006891725297477485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21920378685044600793273293 8220142006891725297477485)
                    ·
                      refine ⟨3082553252584396986554057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8220142006891725297477485 3082553252584396986554057)
                      ·
                        rfl

theorem cell23_6003251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 3].length) (baseStart_6003251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003251 prefixEnd_6003251 := by exact prefixLift 6003251
  have htrace : WordTrace (prefixWord ++ tailWord_6003251) baseStart_6003251 baseEnd_6003251 := by
    simpa [prefixWord, tailWord_6003251, baseEnd_6003251] using wordTrace_append hprefix tailTrace_6003251
  have hstable : (prefixWord ++ tailWord_6003251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003251).length < 2 ^ (prefixWord ++ tailWord_6003251).sum := by decide
  have hdescent : baseEnd_6003251 < baseStart_6003251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003269 : List Nat := [1, 3, 1, 1, 1, 6, 3, 2, 1, 2, 2]
def baseStart_6003269 : Nat := 118140960795 + 6003269 * 2 ^ 59
def prefixEnd_6003269 : Nat := 4983230072969 + 3 ^ 40 * 6003269 * 2
def baseEnd_6003269 : Nat := 3082562495236177916128975

theorem tailTrace_6003269 : CollatzResearch.WordTrace tailWord_6003269 prefixEnd_6003269 3082562495236177916128975 := by
  unfold tailWord_6003269
  simp only [CollatzResearch.WordTrace]
  refine ⟨218957208488189164563860861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145971472325459443042573907 218957208488189164563860861)
  ·
    refine ⟨82108953183070936711447823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218957208488189164563860861 82108953183070936711447823)
    ·
      refine ⟨123163429774606405067171735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82108953183070936711447823 123163429774606405067171735)
      ·
        refine ⟨184745144661909607600757603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123163429774606405067171735 184745144661909607600757603)
        ·
          refine ⟨277117716992864411401136405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184745144661909607600757603 277117716992864411401136405)
          ·
            refine ⟨12989892984040519284428269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 277117716992864411401136405 12989892984040519284428269)
            ·
              refine ⟨4871209869015194731660601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12989892984040519284428269 4871209869015194731660601)
              ·
                refine ⟨3653407401761396048745451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4871209869015194731660601 3653407401761396048745451)
                ·
                  refine ⟨5480111102642094073118177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3653407401761396048745451 5480111102642094073118177)
                  ·
                    refine ⟨4110083326981570554838633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5480111102642094073118177 4110083326981570554838633)
                    ·
                      refine ⟨3082562495236177916128975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4110083326981570554838633 3082562495236177916128975)
                      ·
                        rfl

theorem cell23_6003269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 1, 2, 2].length) (baseStart_6003269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003269 prefixEnd_6003269 := by exact prefixLift 6003269
  have htrace : WordTrace (prefixWord ++ tailWord_6003269) baseStart_6003269 baseEnd_6003269 := by
    simpa [prefixWord, tailWord_6003269, baseEnd_6003269] using wordTrace_append hprefix tailTrace_6003269
  have hstable : (prefixWord ++ tailWord_6003269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003269).length < 2 ^ (prefixWord ++ tailWord_6003269).sum := by decide
  have hdescent : baseEnd_6003269 < baseStart_6003269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003308 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 3, 4, 2]
def baseStart_6003308 : Nat := 118140960795 + 6003308 * 2 ^ 59
def prefixEnd_6003308 : Nat := 4983230072969 + 3 ^ 40 * 6003308 * 2
def baseEnd_6003308 : Nat := 3082582520981703263541295

theorem tailTrace_6003308 : CollatzResearch.WordTrace tailWord_6003308 prefixEnd_6003308 3082582520981703263541295 := by
  unfold tailWord_6003308
  simp only [CollatzResearch.WordTrace]
  refine ⟨109479315467523937112265289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145972420623365249483020385 109479315467523937112265289)
  ·
    refine ⟨82109486600642952834198967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109479315467523937112265289 82109486600642952834198967)
    ·
      refine ⟨123164229900964429251298451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82109486600642952834198967 123164229900964429251298451)
      ·
        refine ⟨184746344851446643876947677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123164229900964429251298451 184746344851446643876947677)
        ·
          refine ⟨69279879319292491453855379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184746344851446643876947677 69279879319292491453855379)
          ·
            refine ⟨103919818978938737180783069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69279879319292491453855379 103919818978938737180783069)
            ·
              refine ⟨38969932117102026442793651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103919818978938737180783069 38969932117102026442793651)
              ·
                refine ⟨58454898175653039664190477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38969932117102026442793651 58454898175653039664190477)
                ·
                  refine ⟨21920586815869889874071429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58454898175653039664190477 21920586815869889874071429)
                  ·
                    refine ⟨4110110027975604351388393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21920586815869889874071429 4110110027975604351388393)
                    ·
                      refine ⟨3082582520981703263541295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4110110027975604351388393 3082582520981703263541295)
                      ·
                        rfl

theorem cell23_6003308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 4, 2].length) (baseStart_6003308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003308 prefixEnd_6003308 := by exact prefixLift 6003308
  have htrace : WordTrace (prefixWord ++ tailWord_6003308) baseStart_6003308 baseEnd_6003308 := by
    simpa [prefixWord, tailWord_6003308, baseEnd_6003308] using wordTrace_append hprefix tailTrace_6003308
  have hstable : (prefixWord ++ tailWord_6003308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003308).length < 2 ^ (prefixWord ++ tailWord_6003308).sum := by decide
  have hdescent : baseEnd_6003308 < baseStart_6003308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003311 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 5]
def baseStart_6003311 : Nat := 118140960795 + 6003311 * 2 ^ 59
def prefixEnd_6003311 : Nat := 4983230072969 + 3 ^ 40 * 6003311 * 2
def baseEnd_6003311 : Nat := 3082584061423666751803781

theorem tailTrace_6003311 : CollatzResearch.WordTrace tailWord_6003311 prefixEnd_6003311 3082584061423666751803781 := by
  unfold tailWord_6003311
  simp only [CollatzResearch.WordTrace]
  refine ⟨218958740354037005736889787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145972493569358003824593191 218958740354037005736889787)
  ·
    refine ⟨328438110531055508605334681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218958740354037005736889787 328438110531055508605334681)
    ·
      refine ⟨246328582898291631454001011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328438110531055508605334681 246328582898291631454001011)
      ·
        refine ⟨369492874347437447181001517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246328582898291631454001011 369492874347437447181001517)
        ·
          refine ⟨138559827880289042692875569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 369492874347437447181001517 138559827880289042692875569)
          ·
            refine ⟨103919870910216782019656677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138559827880289042692875569 103919870910216782019656677)
            ·
              refine ⟨19484975795665646628685627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103919870910216782019656677 19484975795665646628685627)
              ·
                refine ⟨29227463693498469943028441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19484975795665646628685627 29227463693498469943028441)
                ·
                  refine ⟨21920597770123852457271331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29227463693498469943028441 21920597770123852457271331)
                  ·
                    refine ⟨32880896655185778685906997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21920597770123852457271331 32880896655185778685906997)
                    ·
                      refine ⟨3082584061423666751803781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32880896655185778685906997 3082584061423666751803781)
                      ·
                        rfl

theorem cell23_6003311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 5].length) (baseStart_6003311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003311 prefixEnd_6003311 := by exact prefixLift 6003311
  have htrace : WordTrace (prefixWord ++ tailWord_6003311) baseStart_6003311 baseEnd_6003311 := by
    simpa [prefixWord, tailWord_6003311, baseEnd_6003311] using wordTrace_append hprefix tailTrace_6003311
  have hstable : (prefixWord ++ tailWord_6003311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003311).length < 2 ^ (prefixWord ++ tailWord_6003311).sum := by decide
  have hdescent : baseEnd_6003311 < baseStart_6003311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003342 : List Nat := [4, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2]
def baseStart_6003342 : Nat := 118140960795 + 6003342 * 2 ^ 59
def prefixEnd_6003342 : Nat := 4983230072969 + 3 ^ 40 * 6003342 * 2
def baseEnd_6003342 : Nat := 3082599979323956130516139

theorem tailTrace_6003342 : CollatzResearch.WordTrace tailWord_6003342 prefixEnd_6003342 3082599979323956130516139 := by
  unfold tailWord_6003342
  simp only [CollatzResearch.WordTrace]
  refine ⟨27369983877115587253908535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145973247344616465354178853 27369983877115587253908535)
  ·
    refine ⟨41054975815673380880862803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27369983877115587253908535 41054975815673380880862803)
    ·
      refine ⟨61582463723510071321294205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41054975815673380880862803 61582463723510071321294205)
      ·
        refine ⟨23093423896316276745485327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61582463723510071321294205 23093423896316276745485327)
        ·
          refine ⟨34640135844474415118227991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23093423896316276745485327 34640135844474415118227991)
          ·
            refine ⟨51960203766711622677341987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34640135844474415118227991 51960203766711622677341987)
            ·
              refine ⟨77940305650067434016012981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51960203766711622677341987 77940305650067434016012981)
              ·
                refine ⟨7306903654693821939001217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77940305650067434016012981 7306903654693821939001217)
                ·
                  refine ⟨5480177741020366454250913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7306903654693821939001217 5480177741020366454250913)
                  ·
                    refine ⟨4110133305765274840688185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5480177741020366454250913 4110133305765274840688185)
                    ·
                      refine ⟨3082599979323956130516139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4110133305765274840688185 3082599979323956130516139)
                      ·
                        rfl

theorem cell23_6003342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_6003342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003342 prefixEnd_6003342 := by exact prefixLift 6003342
  have htrace : WordTrace (prefixWord ++ tailWord_6003342) baseStart_6003342 baseEnd_6003342 := by
    simpa [prefixWord, tailWord_6003342, baseEnd_6003342] using wordTrace_append hprefix tailTrace_6003342
  have hstable : (prefixWord ++ tailWord_6003342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003342).length < 2 ^ (prefixWord ++ tailWord_6003342).sum := by decide
  have hdescent : baseEnd_6003342 < baseStart_6003342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003348 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 9]
def baseStart_6003348 : Nat := 118140960795 + 6003348 * 2 ^ 59
def prefixEnd_6003348 : Nat := 4983230072969 + 3 ^ 40 * 6003348 * 2
def baseEnd_6003348 : Nat := 342511451134209234115679

theorem tailTrace_6003348 : CollatzResearch.WordTrace tailWord_6003348 prefixEnd_6003348 342511451134209234115679 := by
  unfold tailWord_6003348
  simp only [CollatzResearch.WordTrace]
  refine ⟨109480044927451480527993349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145973393236601974037324465 109480044927451480527993349)
  ·
    refine ⟨20527508423897152598998753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109480044927451480527993349 20527508423897152598998753)
    ·
      refine ⟨15395631317922864449249065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20527508423897152598998753 15395631317922864449249065)
      ·
        refine ⟨11546723488442148336936799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15395631317922864449249065 11546723488442148336936799)
        ·
          refine ⟨17320085232663222505405199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11546723488442148336936799 17320085232663222505405199)
          ·
            refine ⟨25980127848994833758107799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17320085232663222505405199 25980127848994833758107799)
            ·
              refine ⟨38970191773492250637161699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25980127848994833758107799 38970191773492250637161699)
              ·
                refine ⟨58455287660238375955742549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38970191773492250637161699 58455287660238375955742549)
                ·
                  refine ⟨342511451134209234115679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58455287660238375955742549 342511451134209234115679)
                  ·
                    rfl

theorem cell23_6003348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_6003348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003348 prefixEnd_6003348 := by exact prefixLift 6003348
  have htrace : WordTrace (prefixWord ++ tailWord_6003348) baseStart_6003348 baseEnd_6003348 := by
    simpa [prefixWord, tailWord_6003348, baseEnd_6003348] using wordTrace_append hprefix tailTrace_6003348
  have hstable : (prefixWord ++ tailWord_6003348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003348).length < 2 ^ (prefixWord ++ tailWord_6003348).sum := by decide
  have hdescent : baseEnd_6003348 < baseStart_6003348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003382 : List Nat := [5, 1, 3, 1, 2, 1, 2, 1, 7]
def baseStart_6003382 : Nat := 118140960795 + 6003382 * 2 ^ 59
def prefixEnd_6003382 : Nat := 4983230072969 + 3 ^ 40 * 6003382 * 2
def baseEnd_6003382 : Nat := 342513390950015108223995

theorem tailTrace_6003382 : CollatzResearch.WordTrace tailWord_6003382 prefixEnd_6003382 342513390950015108223995 := by
  unfold tailWord_6003382
  simp only [CollatzResearch.WordTrace]
  refine ⟨13685083121048736553920275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145974219957853189908482933 13685083121048736553920275)
  ·
    refine ⟨20527624681573104830880413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13685083121048736553920275 20527624681573104830880413)
    ·
      refine ⟨7697859255589914311580155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20527624681573104830880413 7697859255589914311580155)
      ·
        refine ⟨11546788883384871467370233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7697859255589914311580155 11546788883384871467370233)
        ·
          refine ⟨8660091662538653600527675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11546788883384871467370233 8660091662538653600527675)
          ·
            refine ⟨12990137493807980400791513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8660091662538653600527675 12990137493807980400791513)
            ·
              refine ⟨9742603120355985300593635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12990137493807980400791513 9742603120355985300593635)
              ·
                refine ⟨14613904680533977950890453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9742603120355985300593635 14613904680533977950890453)
                ·
                  refine ⟨342513390950015108223995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14613904680533977950890453 342513390950015108223995)
                  ·
                    rfl

theorem cell23_6003382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_6003382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003382 prefixEnd_6003382 := by exact prefixLift 6003382
  have htrace : WordTrace (prefixWord ++ tailWord_6003382) baseStart_6003382 baseEnd_6003382 := by
    simpa [prefixWord, tailWord_6003382, baseEnd_6003382] using wordTrace_append hprefix tailTrace_6003382
  have hstable : (prefixWord ++ tailWord_6003382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003382).length < 2 ^ (prefixWord ++ tailWord_6003382).sum := by decide
  have hdescent : baseEnd_6003382 < baseStart_6003382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003393 : List Nat := [1, 2, 6, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_6003393 : Nat := 118140960795 + 6003393 * 2 ^ 59
def prefixEnd_6003393 : Nat := 4983230072969 + 3 ^ 40 * 6003393 * 2
def baseEnd_6003393 : Nat := 3082626166837335430978405

theorem tailTrace_6003393 : CollatzResearch.WordTrace tailWord_6003393 prefixEnd_6003393 3082626166837335430978405 := by
  unfold tailWord_6003393
  simp only [CollatzResearch.WordTrace]
  refine ⟨218961731139739933741374833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145974487426493289160916555 218961731139739933741374833)
  ·
    refine ⟨164221298354804950306031125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218961731139739933741374833 164221298354804950306031125)
    ·
      refine ⟨7697873360381482045595209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 164221298354804950306031125 7697873360381482045595209)
      ·
        refine ⟨5773405020286111534196407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7697873360381482045595209 5773405020286111534196407)
        ·
          refine ⟨8660107530429167301294611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5773405020286111534196407 8660107530429167301294611)
          ·
            refine ⟨12990161295643750951941917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8660107530429167301294611 12990161295643750951941917)
            ·
              refine ⟨4871310485866406606978219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12990161295643750951941917 4871310485866406606978219)
              ·
                refine ⟨7306965728799609910467329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4871310485866406606978219 7306965728799609910467329)
                ·
                  refine ⟨5480224296599707432850497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7306965728799609910467329 5480224296599707432850497)
                  ·
                    refine ⟨4110168222449780574637873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5480224296599707432850497 4110168222449780574637873)
                    ·
                      refine ⟨3082626166837335430978405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4110168222449780574637873 3082626166837335430978405)
                      ·
                        rfl

theorem cell23_6003393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_6003393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003393 prefixEnd_6003393 := by exact prefixLift 6003393
  have htrace : WordTrace (prefixWord ++ tailWord_6003393) baseStart_6003393 baseEnd_6003393 := by
    simpa [prefixWord, tailWord_6003393, baseEnd_6003393] using wordTrace_append hprefix tailTrace_6003393
  have hstable : (prefixWord ++ tailWord_6003393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003393).length < 2 ^ (prefixWord ++ tailWord_6003393).sum := by decide
  have hdescent : baseEnd_6003393 < baseStart_6003393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003418 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3]
def baseStart_6003418 : Nat := 118140960795 + 6003418 * 2 ^ 59
def prefixEnd_6003418 : Nat := 4983230072969 + 3 ^ 40 * 6003418 * 2
def baseEnd_6003418 : Nat := 3082639003853697833165789

theorem tailTrace_6003418 : CollatzResearch.WordTrace tailWord_6003418 prefixEnd_6003418 3082639003853697833165789 := by
  unfold tailWord_6003418
  simp only [CollatzResearch.WordTrace]
  refine ⟨54740660741162340752758727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145975095309766242007356605 54740660741162340752758727)
  ·
    refine ⟨82110991111743511129138091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54740660741162340752758727 82110991111743511129138091)
    ·
      refine ⟨123166486667615266693707137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82110991111743511129138091 123166486667615266693707137)
      ·
        refine ⟨92374865000711450020280353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123166486667615266693707137 92374865000711450020280353)
        ·
          refine ⟨69281148750533587515210265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92374865000711450020280353 69281148750533587515210265)
          ·
            refine ⟨51960861562900190636407699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69281148750533587515210265 51960861562900190636407699)
            ·
              refine ⟨77941292344350285954611549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51960861562900190636407699 77941292344350285954611549)
              ·
                refine ⟨29227984629131357232979331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77941292344350285954611549 29227984629131357232979331)
                ·
                  refine ⟨43841976943697035849468997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29227984629131357232979331 43841976943697035849468997)
                  ·
                    refine ⟨8220370676943194221775437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43841976943697035849468997 8220370676943194221775437)
                    ·
                      refine ⟨3082639003853697833165789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8220370676943194221775437 3082639003853697833165789)
                      ·
                        rfl

theorem cell23_6003418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_6003418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003418 prefixEnd_6003418 := by exact prefixLift 6003418
  have htrace : WordTrace (prefixWord ++ tailWord_6003418) baseStart_6003418 baseEnd_6003418 := by
    simpa [prefixWord, tailWord_6003418, baseEnd_6003418] using wordTrace_append hprefix tailTrace_6003418
  have hstable : (prefixWord ++ tailWord_6003418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003418).length < 2 ^ (prefixWord ++ tailWord_6003418).sum := by decide
  have hdescent : baseEnd_6003418 < baseStart_6003418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003438 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 8]
def baseStart_6003438 : Nat := 118140960795 + 6003438 * 2 ^ 59
def prefixEnd_6003438 : Nat := 4983230072969 + 3 ^ 40 * 6003438 * 2
def baseEnd_6003438 : Nat := 342516585940754194990633

theorem tailTrace_6003438 : CollatzResearch.WordTrace tailWord_6003438 prefixEnd_6003438 342516585940754194990633 := by
  unfold tailWord_6003438
  simp only [CollatzResearch.WordTrace]
  refine ⟨27370421553072113303345371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145975581616384604284508645 27370421553072113303345371)
  ·
    refine ⟨41055632329608169955018057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27370421553072113303345371 41055632329608169955018057)
    ·
      refine ⟨30791724247206127466263543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41055632329608169955018057 30791724247206127466263543)
      ·
        refine ⟨46187586370809191199395315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30791724247206127466263543 46187586370809191199395315)
        ·
          refine ⟨69281379556213786799092973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46187586370809191199395315 69281379556213786799092973)
          ·
            refine ⟨25980517333580170049659865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69281379556213786799092973 25980517333580170049659865)
            ·
              refine ⟨19485388000185127537244899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25980517333580170049659865 19485388000185127537244899)
              ·
                refine ⟨29228082000277691305867349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19485388000185127537244899 29228082000277691305867349)
                ·
                  refine ⟨342516585940754194990633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29228082000277691305867349 342516585940754194990633)
                  ·
                    rfl

theorem cell23_6003438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_6003438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003438 prefixEnd_6003438 := by exact prefixLift 6003438
  have htrace : WordTrace (prefixWord ++ tailWord_6003438) baseStart_6003438 baseEnd_6003438 := by
    simpa [prefixWord, tailWord_6003438, baseEnd_6003438] using wordTrace_append hprefix tailTrace_6003438
  have hstable : (prefixWord ++ tailWord_6003438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003438).length < 2 ^ (prefixWord ++ tailWord_6003438).sum := by decide
  have hdescent : baseEnd_6003438 < baseStart_6003438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003442 : List Nat := [3, 2, 1, 3, 1, 4, 1, 1, 3, 4]
def baseStart_6003442 : Nat := 118140960795 + 6003442 * 2 ^ 59
def prefixEnd_6003442 : Nat := 4983230072969 + 3 ^ 40 * 6003442 * 2
def baseEnd_6003442 : Nat := 1027550442463135246421893

theorem tailTrace_6003442 : CollatzResearch.WordTrace tailWord_6003442 prefixEnd_6003442 1027550442463135246421893 := by
  unfold tailWord_6003442
  simp only [CollatzResearch.WordTrace]
  refine ⟨54740879579140603777477145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145975678877708276739939053 54740879579140603777477145)
  ·
    refine ⟨41055659684355452833107859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54740879579140603777477145 41055659684355452833107859)
    ·
      refine ⟨61583489526533179249661789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41055659684355452833107859 61583489526533179249661789)
      ·
        refine ⟨23093808572449942218623171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61583489526533179249661789 23093808572449942218623171)
        ·
          refine ⟨34640712858674913327934757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23093808572449942218623171 34640712858674913327934757)
          ·
            refine ⟨6495133661001546248987767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34640712858674913327934757 6495133661001546248987767)
            ·
              refine ⟨9742700491502319373481651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6495133661001546248987767 9742700491502319373481651)
              ·
                refine ⟨14614050737253479060222477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9742700491502319373481651 14614050737253479060222477)
                ·
                  refine ⟨5480269026470054647583429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14614050737253479060222477 5480269026470054647583429)
                  ·
                    refine ⟨1027550442463135246421893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5480269026470054647583429 1027550442463135246421893)
                    ·
                      rfl

theorem cell23_6003442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_6003442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003442 prefixEnd_6003442 := by exact prefixLift 6003442
  have htrace : WordTrace (prefixWord ++ tailWord_6003442) baseStart_6003442 baseEnd_6003442 := by
    simpa [prefixWord, tailWord_6003442, baseEnd_6003442] using wordTrace_append hprefix tailTrace_6003442
  have hstable : (prefixWord ++ tailWord_6003442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003442).length < 2 ^ (prefixWord ++ tailWord_6003442).sum := by decide
  have hdescent : baseEnd_6003442 < baseStart_6003442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003465 : List Nat := [1, 2, 1, 1, 3, 2, 2, 4, 3, 1, 3]
def baseStart_6003465 : Nat := 118140960795 + 6003465 * 2 ^ 59
def prefixEnd_6003465 : Nat := 4983230072969 + 3 ^ 40 * 6003465 * 2
def baseEnd_6003465 : Nat := 3082663137444459149278073

theorem tailTrace_6003465 : CollatzResearch.WordTrace tailWord_6003465 prefixEnd_6003465 3082663137444459149278073 := by
  unfold tailWord_6003465
  simp only [CollatzResearch.WordTrace]
  refine ⟨218964357195479090037995849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145976238130319393358663899 218964357195479090037995849)
  ·
    refine ⟨164223267896609317528496887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218964357195479090037995849 164223267896609317528496887)
    ·
      refine ⟨246334901844913976292745331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164223267896609317528496887 246334901844913976292745331)
      ·
        refine ⟨369502352767370964439117997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246334901844913976292745331 369502352767370964439117997)
        ·
          refine ⟨138563382287764111664669249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 369502352767370964439117997 138563382287764111664669249)
          ·
            refine ⟨103922536715823083748501937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138563382287764111664669249 103922536715823083748501937)
            ·
              refine ⟨77941902536867312811376453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103922536715823083748501937 77941902536867312811376453)
              ·
                refine ⟨14614106725662621152133085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77941902536867312811376453 14614106725662621152133085)
                ·
                  refine ⟨5480290022123482932049907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14614106725662621152133085 5480290022123482932049907)
                  ·
                    refine ⟨8220435033185224398074861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5480290022123482932049907 8220435033185224398074861)
                    ·
                      refine ⟨3082663137444459149278073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8220435033185224398074861 3082663137444459149278073)
                      ·
                        rfl

theorem cell23_6003465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 1, 3].length) (baseStart_6003465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003465 prefixEnd_6003465 := by exact prefixLift 6003465
  have htrace : WordTrace (prefixWord ++ tailWord_6003465) baseStart_6003465 baseEnd_6003465 := by
    simpa [prefixWord, tailWord_6003465, baseEnd_6003465] using wordTrace_append hprefix tailTrace_6003465
  have hstable : (prefixWord ++ tailWord_6003465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003465).length < 2 ^ (prefixWord ++ tailWord_6003465).sum := by decide
  have hdescent : baseEnd_6003465 < baseStart_6003465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003526 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2]
def baseStart_6003526 : Nat := 118140960795 + 6003526 * 2 ^ 59
def prefixEnd_6003526 : Nat := 4983230072969 + 3 ^ 40 * 6003526 * 2
def baseEnd_6003526 : Nat := 3082694459764383410615293

theorem tailTrace_6003526 : CollatzResearch.WordTrace tailWord_6003526 prefixEnd_6003526 3082694459764383410615293 := by
  unfold tailWord_6003526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6842705689008065545498951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 145977721365505398303977621 6842705689008065545498951)
  ·
    refine ⟨10264058533512098318248427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6842705689008065545498951 10264058533512098318248427)
    ·
      refine ⟨15396087800268147477372641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10264058533512098318248427 15396087800268147477372641)
      ·
        refine ⟨11547065850201110608029481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15396087800268147477372641 11547065850201110608029481)
        ·
          refine ⟨8660299387650832956022111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11547065850201110608029481 8660299387650832956022111)
          ·
            refine ⟨12990449081476249434033167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8660299387650832956022111 12990449081476249434033167)
            ·
              refine ⟨19485673622214374151049751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12990449081476249434033167 19485673622214374151049751)
              ·
                refine ⟨29228510433321561226574627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19485673622214374151049751 29228510433321561226574627)
                ·
                  refine ⟨43842765649982341839861941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29228510433321561226574627 43842765649982341839861941)
                  ·
                    refine ⟨4110259279685844547487057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43842765649982341839861941 4110259279685844547487057)
                    ·
                      refine ⟨3082694459764383410615293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4110259279685844547487057 3082694459764383410615293)
                      ·
                        rfl

theorem cell23_6003526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_6003526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003526 prefixEnd_6003526 := by exact prefixLift 6003526
  have htrace : WordTrace (prefixWord ++ tailWord_6003526) baseStart_6003526 baseEnd_6003526 := by
    simpa [prefixWord, tailWord_6003526, baseEnd_6003526] using wordTrace_append hprefix tailTrace_6003526
  have hstable : (prefixWord ++ tailWord_6003526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003526).length < 2 ^ (prefixWord ++ tailWord_6003526).sum := by decide
  have hdescent : baseEnd_6003526 < baseStart_6003526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003533 : List Nat := [1, 6, 1, 2, 2, 1, 2, 3, 1, 1, 3]
def baseStart_6003533 : Nat := 118140960795 + 6003533 * 2 ^ 59
def prefixEnd_6003533 : Nat := 4983230072969 + 3 ^ 40 * 6003533 * 2
def baseEnd_6003533 : Nat := 3082698054128964883227761

theorem tailTrace_6003533 : CollatzResearch.WordTrace tailWord_6003533 prefixEnd_6003533 3082698054128964883227761 := by
  unfold tailWord_6003533
  simp only [CollatzResearch.WordTrace]
  refine ⟨218966837359232737651471253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145977891572821825100980835 218966837359232737651471253)
  ·
    refine ⟨10264070501214034577412715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 218966837359232737651471253 10264070501214034577412715)
    ·
      refine ⟨15396105751821051866119073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10264070501214034577412715 15396105751821051866119073)
      ·
        refine ⟨11547079313865788899589305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15396105751821051866119073 11547079313865788899589305)
        ·
          refine ⟨8660309485399341674691979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11547079313865788899589305 8660309485399341674691979)
          ·
            refine ⟨12990464228099012512037969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8660309485399341674691979 12990464228099012512037969)
            ·
              refine ⟨9742848171074259384028477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12990464228099012512037969 9742848171074259384028477)
              ·
                refine ⟨3653568064152847269010679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9742848171074259384028477 3653568064152847269010679)
                ·
                  refine ⟨5480352096229270903516019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3653568064152847269010679 5480352096229270903516019)
                  ·
                    refine ⟨8220528144343906355274029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5480352096229270903516019 8220528144343906355274029)
                    ·
                      refine ⟨3082698054128964883227761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8220528144343906355274029 3082698054128964883227761)
                      ·
                        rfl

theorem cell23_6003533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_6003533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003533 prefixEnd_6003533 := by exact prefixLift 6003533
  have htrace : WordTrace (prefixWord ++ tailWord_6003533) baseStart_6003533 baseEnd_6003533 := by
    simpa [prefixWord, tailWord_6003533, baseEnd_6003533] using wordTrace_append hprefix tailTrace_6003533
  have hstable : (prefixWord ++ tailWord_6003533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003533).length < 2 ^ (prefixWord ++ tailWord_6003533).sum := by decide
  have hdescent : baseEnd_6003533 < baseStart_6003533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003556 : List Nat := [2, 3, 1, 1, 4, 1, 2, 4, 1, 2, 2]
def baseStart_6003556 : Nat := 118140960795 + 6003556 * 2 ^ 59
def prefixEnd_6003556 : Nat := 4983230072969 + 3 ^ 40 * 6003556 * 2
def baseEnd_6003556 : Nat := 3082709864184018293240155

theorem tailTrace_6003556 : CollatzResearch.WordTrace tailWord_6003556 prefixEnd_6003556 3082709864184018293240155 := by
  unfold tailWord_6003556
  simp only [CollatzResearch.WordTrace]
  refine ⟨109483838119074706289779261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145978450825432941719705681 109483838119074706289779261)
  ·
    refine ⟨41056439294653014858667223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109483838119074706289779261 41056439294653014858667223)
    ·
      refine ⟨61584658941979522288000835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41056439294653014858667223 61584658941979522288000835)
      ·
        refine ⟨92376988412969283432001253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61584658941979522288000835 92376988412969283432001253)
        ·
          refine ⟨17320685327431740643500235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92376988412969283432001253 17320685327431740643500235)
          ·
            refine ⟨25981027991147610965250353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17320685327431740643500235 25981027991147610965250353)
            ·
              refine ⟨19485770993360708223937765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25981027991147610965250353 19485770993360708223937765)
              ·
                refine ⟨3653582061255132791988331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19485770993360708223937765 3653582061255132791988331)
                ·
                  refine ⟨5480373091882699187982497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3653582061255132791988331 5480373091882699187982497)
                  ·
                    refine ⟨4110279818912024390986873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5480373091882699187982497 4110279818912024390986873)
                    ·
                      refine ⟨3082709864184018293240155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4110279818912024390986873 3082709864184018293240155)
                      ·
                        rfl

theorem cell23_6003556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 1, 2, 2].length) (baseStart_6003556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003556 prefixEnd_6003556 := by exact prefixLift 6003556
  have htrace : WordTrace (prefixWord ++ tailWord_6003556) baseStart_6003556 baseEnd_6003556 := by
    simpa [prefixWord, tailWord_6003556, baseEnd_6003556] using wordTrace_append hprefix tailTrace_6003556
  have hstable : (prefixWord ++ tailWord_6003556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003556).length < 2 ^ (prefixWord ++ tailWord_6003556).sum := by decide
  have hdescent : baseEnd_6003556 < baseStart_6003556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003566 : List Nat := [4, 1, 2, 3, 2, 1, 3, 1, 2, 4]
def baseStart_6003566 : Nat := 118140960795 + 6003566 * 2 ^ 59
def prefixEnd_6003566 : Nat := 4983230072969 + 3 ^ 40 * 6003566 * 2
def baseEnd_6003566 : Nat := 1027571666330187751371703

theorem tailTrace_6003566 : CollatzResearch.WordTrace tailWord_6003566 prefixEnd_6003566 1027571666330187751371703 := by
  unfold tailWord_6003566
  simp only [CollatzResearch.WordTrace]
  refine ⟨27371005121014148035927819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145978693978742122858281701 27371005121014148035927819)
  ·
    refine ⟨41056507681521222053891729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27371005121014148035927819 41056507681521222053891729)
    ·
      refine ⟨30792380761140916540418797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41056507681521222053891729 30792380761140916540418797)
      ·
        refine ⟨11547142785427843702657049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30792380761140916540418797 11547142785427843702657049)
        ·
          refine ⟨8660357089070882776992787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11547142785427843702657049 8660357089070882776992787)
          ·
            refine ⟨12990535633606324165489181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8660357089070882776992787 12990535633606324165489181)
            ·
              refine ⟨4871450862602371562058443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12990535633606324165489181 4871450862602371562058443)
              ·
                refine ⟨7307176293903557343087665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4871450862602371562058443 7307176293903557343087665)
                ·
                  refine ⟨5480382220427668007315749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7307176293903557343087665 5480382220427668007315749)
                  ·
                    refine ⟨1027571666330187751371703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5480382220427668007315749 1027571666330187751371703)
                    ·
                      rfl

theorem cell23_6003566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_6003566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003566 prefixEnd_6003566 := by exact prefixLift 6003566
  have htrace : WordTrace (prefixWord ++ tailWord_6003566) baseStart_6003566 baseEnd_6003566 := by
    simpa [prefixWord, tailWord_6003566, baseEnd_6003566] using wordTrace_append hprefix tailTrace_6003566
  have hstable : (prefixWord ++ tailWord_6003566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003566).length < 2 ^ (prefixWord ++ tailWord_6003566).sum := by decide
  have hdescent : baseEnd_6003566 < baseStart_6003566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003623 : List Nat := [1, 1, 6, 1, 3, 2, 2, 1, 2, 1, 3]
def baseStart_6003623 : Nat := 118140960795 + 6003623 * 2 ^ 59
def prefixEnd_6003623 : Nat := 4983230072969 + 3 ^ 40 * 6003623 * 2
def baseEnd_6003623 : Nat := 3082744267387869531102347

theorem tailTrace_6003623 : CollatzResearch.WordTrace tailWord_6003623 prefixEnd_6003623 3082744267387869531102347 := by
  unfold tailWord_6003623
  simp only [CollatzResearch.WordTrace]
  refine ⟨218970119928906683022247523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145980079952604455348165015 218970119928906683022247523)
  ·
    refine ⟨328455179893360024533371285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218970119928906683022247523 328455179893360024533371285)
    ·
      refine ⟨15396336557501251150001779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 328455179893360024533371285 15396336557501251150001779)
      ·
        refine ⟨23094504836251876725002669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15396336557501251150001779 23094504836251876725002669)
        ·
          refine ⟨8660439313594453771876001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23094504836251876725002669 8660439313594453771876001)
          ·
            refine ⟨6495329485195840328907001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8660439313594453771876001 6495329485195840328907001)
            ·
              refine ⟨4871497113896880246680251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6495329485195840328907001 4871497113896880246680251)
              ·
                refine ⟨7307245670845320370020377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4871497113896880246680251 7307245670845320370020377)
                ·
                  refine ⟨5480434253133990277515283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7307245670845320370020377 5480434253133990277515283)
                  ·
                    refine ⟨8220651379700985416272925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5480434253133990277515283 8220651379700985416272925)
                    ·
                      refine ⟨3082744267387869531102347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8220651379700985416272925 3082744267387869531102347)
                      ·
                        rfl

theorem cell23_6003623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_6003623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003623 prefixEnd_6003623 := by exact prefixLift 6003623
  have htrace : WordTrace (prefixWord ++ tailWord_6003623) baseStart_6003623 baseEnd_6003623 := by
    simpa [prefixWord, tailWord_6003623, baseEnd_6003623] using wordTrace_append hprefix tailTrace_6003623
  have hstable : (prefixWord ++ tailWord_6003623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003623).length < 2 ^ (prefixWord ++ tailWord_6003623).sum := by decide
  have hdescent : baseEnd_6003623 < baseStart_6003623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003628 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 9]
def baseStart_6003628 : Nat := 118140960795 + 6003628 * 2 ^ 59
def prefixEnd_6003628 : Nat := 4983230072969 + 3 ^ 40 * 6003628 * 2
def baseEnd_6003628 : Nat := 3082746834791142011539823

theorem tailTrace_6003628 : CollatzResearch.WordTrace tailWord_6003628 prefixEnd_6003628 3082746834791142011539823 := by
  unfold tailWord_6003628
  simp only [CollatzResearch.WordTrace]
  refine ⟨109485151146944284438089769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145980201529259045917453025 109485151146944284438089769)
  ·
    refine ⟨82113863360208213328567327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109485151146944284438089769 82113863360208213328567327)
    ·
      refine ⟨123170795040312319992850991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82113863360208213328567327 123170795040312319992850991)
      ·
        refine ⟨184756192560468479989276487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123170795040312319992850991 184756192560468479989276487)
        ·
          refine ⟨277134288840702719983914731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184756192560468479989276487 277134288840702719983914731)
          ·
            refine ⟨415701433261054079975872097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277134288840702719983914731 415701433261054079975872097)
            ·
              refine ⟨311776074945790559981904073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415701433261054079975872097 311776074945790559981904073)
              ·
                refine ⟨233832056209342919986428055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 311776074945790559981904073 233832056209342919986428055)
                ·
                  refine ⟨350748084314014379979642083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233832056209342919986428055 350748084314014379979642083)
                  ·
                    refine ⟨526122126471021569969463125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 350748084314014379979642083 526122126471021569969463125)
                    ·
                      refine ⟨3082746834791142011539823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 526122126471021569969463125 3082746834791142011539823)
                      ·
                        rfl

theorem cell23_6003628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_6003628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003628 prefixEnd_6003628 := by exact prefixLift 6003628
  have htrace : WordTrace (prefixWord ++ tailWord_6003628) baseStart_6003628 baseEnd_6003628 := by
    simpa [prefixWord, tailWord_6003628, baseEnd_6003628] using wordTrace_append hprefix tailTrace_6003628
  have hstable : (prefixWord ++ tailWord_6003628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003628).length < 2 ^ (prefixWord ++ tailWord_6003628).sum := by decide
  have hdescent : baseEnd_6003628 < baseStart_6003628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003633 : List Nat := [1, 2, 2, 4, 4, 1, 1, 2, 1, 3, 2]
def baseStart_6003633 : Nat := 118140960795 + 6003633 * 2 ^ 59
def prefixEnd_6003633 : Nat := 4983230072969 + 3 ^ 40 * 6003633 * 2
def baseEnd_6003633 : Nat := 3082749402194414491977301

theorem tailTrace_6003633 : CollatzResearch.WordTrace tailWord_6003633 prefixEnd_6003633 3082749402194414491977301 := by
  unfold tailWord_6003633
  simp only [CollatzResearch.WordTrace]
  refine ⟨218970484658870454730111553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145980323105913636486741035 218970484658870454730111553)
  ·
    refine ⟨164227863494152841047583665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218970484658870454730111553 164227863494152841047583665)
    ·
      refine ⟨123170897620614630785687749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164227863494152841047583665 123170897620614630785687749)
      ·
        refine ⟨23094543303865243272316453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123170897620614630785687749 23094543303865243272316453)
        ·
          refine ⟨4330226869474733113559335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23094543303865243272316453 4330226869474733113559335)
          ·
            refine ⟨6495340304212099670339003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4330226869474733113559335 6495340304212099670339003)
            ·
              refine ⟨9743010456318149505508505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6495340304212099670339003 9743010456318149505508505)
              ·
                refine ⟨7307257842238612129131379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9743010456318149505508505 7307257842238612129131379)
                ·
                  refine ⟨10960886763357918193697069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7307257842238612129131379 10960886763357918193697069)
                  ·
                    refine ⟨4110332536259219322636401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10960886763357918193697069 4110332536259219322636401)
                    ·
                      refine ⟨3082749402194414491977301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4110332536259219322636401 3082749402194414491977301)
                      ·
                        rfl

theorem cell23_6003633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_6003633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003633 prefixEnd_6003633 := by exact prefixLift 6003633
  have htrace : WordTrace (prefixWord ++ tailWord_6003633) baseStart_6003633 baseEnd_6003633 := by
    simpa [prefixWord, tailWord_6003633, baseEnd_6003633] using wordTrace_append hprefix tailTrace_6003633
  have hstable : (prefixWord ++ tailWord_6003633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003633).length < 2 ^ (prefixWord ++ tailWord_6003633).sum := by decide
  have hdescent : baseEnd_6003633 < baseStart_6003633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003665 : List Nat := [1, 2, 2, 1, 2, 1, 3, 4, 2, 5]
def baseStart_6003665 : Nat := 118140960795 + 6003665 * 2 ^ 59
def prefixEnd_6003665 : Nat := 4983230072969 + 3 ^ 40 * 6003665 * 2
def baseEnd_6003665 : Nat := 1027588611191786122259051

theorem tailTrace_6003665 : CollatzResearch.WordTrace tailWord_6003665 prefixEnd_6003665 1027588611191786122259051 := by
  unfold tailWord_6003665
  simp only [CollatzResearch.WordTrace]
  refine ⟨218971651794754524195276449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145981101196503016130184299 218971651794754524195276449)
  ·
    refine ⟨164228738846065893146457337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218971651794754524195276449 164228738846065893146457337)
    ·
      refine ⟨123171554134549419859843003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164228738846065893146457337 123171554134549419859843003)
      ·
        refine ⟨184757331201824129789764505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123171554134549419859843003 184757331201824129789764505)
        ·
          refine ⟨138567998401368097342323379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184757331201824129789764505 138567998401368097342323379)
          ·
            refine ⟨207851997602052146013485069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138567998401368097342323379 207851997602052146013485069)
            ·
              refine ⟨77944499100769554755056901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207851997602052146013485069 77944499100769554755056901)
              ·
                refine ⟨14614593581394291516573169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77944499100769554755056901 14614593581394291516573169)
                ·
                  refine ⟨10960945186045718637429877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14614593581394291516573169 10960945186045718637429877)
                  ·
                    refine ⟨1027588611191786122259051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10960945186045718637429877 1027588611191786122259051)
                    ·
                      rfl

theorem cell23_6003665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_6003665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003665 prefixEnd_6003665 := by exact prefixLift 6003665
  have htrace : WordTrace (prefixWord ++ tailWord_6003665) baseStart_6003665 baseEnd_6003665 := by
    simpa [prefixWord, tailWord_6003665, baseEnd_6003665] using wordTrace_append hprefix tailTrace_6003665
  have hstable : (prefixWord ++ tailWord_6003665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003665).length < 2 ^ (prefixWord ++ tailWord_6003665).sum := by decide
  have hdescent : baseEnd_6003665 < baseStart_6003665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003669 : List Nat := [1, 3, 2, 3, 3, 1, 1, 4, 5]
def baseStart_6003669 : Nat := 118140960795 + 6003669 * 2 ^ 59
def prefixEnd_6003669 : Nat := 4983230072969 + 3 ^ 40 * 6003669 * 2
def baseEnd_6003669 : Nat := 342529765277552927903015

theorem tailTrace_6003669 : CollatzResearch.WordTrace tailWord_6003669 prefixEnd_6003669 342529765277552927903015 := by
  unfold tailWord_6003669
  simp only [CollatzResearch.WordTrace]
  refine ⟨218971797686740032878422061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145981198457826688585614707 218971797686740032878422061)
  ·
    refine ⟨82114424132527512329408273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218971797686740032878422061 82114424132527512329408273)
    ·
      refine ⟨61585818099395634247056205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82114424132527512329408273 61585818099395634247056205)
      ·
        refine ⟨23094681787273362842646077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61585818099395634247056205 23094681787273362842646077)
        ·
          refine ⟨8660505670227511065992279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23094681787273362842646077 8660505670227511065992279)
          ·
            refine ⟨12990758505341266598988419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8660505670227511065992279 12990758505341266598988419)
            ·
              refine ⟨19486137758011899898482629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12990758505341266598988419 19486137758011899898482629)
              ·
                refine ⟨3653650829627231230965493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19486137758011899898482629 3653650829627231230965493)
                ·
                  refine ⟨342529765277552927903015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3653650829627231230965493 342529765277552927903015)
                  ·
                    rfl

theorem cell23_6003669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 5].length) (baseStart_6003669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003669 prefixEnd_6003669 := by exact prefixLift 6003669
  have htrace : WordTrace (prefixWord ++ tailWord_6003669) baseStart_6003669 baseEnd_6003669 := by
    simpa [prefixWord, tailWord_6003669, baseEnd_6003669] using wordTrace_append hprefix tailTrace_6003669
  have hstable : (prefixWord ++ tailWord_6003669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003669).length < 2 ^ (prefixWord ++ tailWord_6003669).sum := by decide
  have hdescent : baseEnd_6003669 < baseStart_6003669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003672 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 2, 5, 2]
def baseStart_6003672 : Nat := 118140960795 + 6003672 * 2 ^ 59
def prefixEnd_6003672 : Nat := 4983230072969 + 3 ^ 40 * 6003672 * 2
def baseEnd_6003672 : Nat := 3082769427939939839389621

theorem tailTrace_6003672 : CollatzResearch.WordTrace tailWord_6003672 prefixEnd_6003672 3082769427939939839389621 := by
  unfold tailWord_6003672
  simp only [CollatzResearch.WordTrace]
  refine ⟨109485953552864582195390635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145981271403819442927187513 109485953552864582195390635)
  ·
    refine ⟨164228930329296873293085953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109485953552864582195390635 164228930329296873293085953)
    ·
      refine ⟨123171697746972654969814465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164228930329296873293085953 123171697746972654969814465)
      ·
        refine ⟨92378773310229491227360849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123171697746972654969814465 92378773310229491227360849)
        ·
          refine ⟨69284079982672118420520637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92378773310229491227360849 69284079982672118420520637)
          ·
            refine ⟨25981529993502044407695239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69284079982672118420520637 25981529993502044407695239)
            ·
              refine ⟨38972294990253066611542859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25981529993502044407695239 38972294990253066611542859)
              ·
                refine ⟨58458442485379599917314289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38972294990253066611542859 58458442485379599917314289)
                ·
                  refine ⟨43843831864034699937985717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58458442485379599917314289 43843831864034699937985717)
                  ·
                    refine ⟨4110359237253253119186161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43843831864034699937985717 4110359237253253119186161)
                    ·
                      refine ⟨3082769427939939839389621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4110359237253253119186161 3082769427939939839389621)
                      ·
                        rfl

theorem cell23_6003672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 2, 5, 2].length) (baseStart_6003672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003672 prefixEnd_6003672 := by exact prefixLift 6003672
  have htrace : WordTrace (prefixWord ++ tailWord_6003672) baseStart_6003672 baseEnd_6003672 := by
    simpa [prefixWord, tailWord_6003672, baseEnd_6003672] using wordTrace_append hprefix tailTrace_6003672
  have hstable : (prefixWord ++ tailWord_6003672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003672).length < 2 ^ (prefixWord ++ tailWord_6003672).sum := by decide
  have hdescent : baseEnd_6003672 < baseStart_6003672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003779 : List Nat := [1, 1, 1, 3, 1, 2, 5, 2, 2, 3, 2]
def baseStart_6003779 : Nat := 118140960795 + 6003779 * 2 ^ 59
def prefixEnd_6003779 : Nat := 4983230072969 + 3 ^ 40 * 6003779 * 2
def baseEnd_6003779 : Nat := 3082824370369970920751629

theorem tailTrace_6003779 : CollatzResearch.WordTrace tailWord_6003779 prefixEnd_6003779 3082824370369970920751629 := by
  unfold tailWord_6003779
  simp only [CollatzResearch.WordTrace]
  refine ⟨218975809716341521664926391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145983873144227681109950927 218975809716341521664926391)
  ·
    refine ⟨328463714574512282497389587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218975809716341521664926391 328463714574512282497389587)
    ·
      refine ⟨492695571861768423746084381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328463714574512282497389587 492695571861768423746084381)
      ·
        refine ⟨184760839448163158904781643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 492695571861768423746084381 184760839448163158904781643)
        ·
          refine ⟨277141259172244738357172465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184760839448163158904781643 277141259172244738357172465)
          ·
            refine ⟨207855944379183553767879349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277141259172244738357172465 207855944379183553767879349)
            ·
              refine ⟨19486494785548458165738689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 207855944379183553767879349 19486494785548458165738689)
              ·
                refine ⟨14614871089161343624304017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19486494785548458165738689 14614871089161343624304017)
                ·
                  refine ⟨10961153316871007718228013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14614871089161343624304017 10961153316871007718228013)
                  ·
                    refine ⟨4110432493826627894335505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10961153316871007718228013 4110432493826627894335505)
                    ·
                      refine ⟨3082824370369970920751629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4110432493826627894335505 3082824370369970920751629)
                      ·
                        rfl

theorem cell23_6003779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 3, 2].length) (baseStart_6003779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003779 prefixEnd_6003779 := by exact prefixLift 6003779
  have htrace : WordTrace (prefixWord ++ tailWord_6003779) baseStart_6003779 baseEnd_6003779 := by
    simpa [prefixWord, tailWord_6003779, baseEnd_6003779] using wordTrace_append hprefix tailTrace_6003779
  have hstable : (prefixWord ++ tailWord_6003779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003779).length < 2 ^ (prefixWord ++ tailWord_6003779).sum := by decide
  have hdescent : baseEnd_6003779 < baseStart_6003779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003785 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 5, 6]
def baseStart_6003785 : Nat := 118140960795 + 6003785 * 2 ^ 59
def prefixEnd_6003785 : Nat := 4983230072969 + 3 ^ 40 * 6003785 * 2
def baseEnd_6003785 : Nat := 1027609150417965965758867

theorem tailTrace_6003785 : CollatzResearch.WordTrace tailWord_6003785 prefixEnd_6003785 1027609150417965965758867 := by
  unfold tailWord_6003785
  simp only [CollatzResearch.WordTrace]
  refine ⟨218976028554319784689644809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145984019036213189793096539 218976028554319784689644809)
  ·
    refine ⟨164232021415739838517233607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218976028554319784689644809 164232021415739838517233607)
    ·
      refine ⟨246348032123609757775850411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164232021415739838517233607 246348032123609757775850411)
      ·
        refine ⟨369522048185414636663775617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246348032123609757775850411 369522048185414636663775617)
        ·
          refine ⟨277141536139060977497831713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369522048185414636663775617 277141536139060977497831713)
          ·
            refine ⟨207856152104295733123373785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277141536139060977497831713 207856152104295733123373785)
            ·
              refine ⟨155892114078221799842530339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207856152104295733123373785 155892114078221799842530339)
              ·
                refine ⟨233838171117332699763795509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155892114078221799842530339 233838171117332699763795509)
                ·
                  refine ⟨21922328542249940602855829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 233838171117332699763795509 21922328542249940602855829)
                  ·
                    refine ⟨1027609150417965965758867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21922328542249940602855829 1027609150417965965758867)
                    ·
                      rfl

theorem cell23_6003785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 6].length) (baseStart_6003785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003785 prefixEnd_6003785 := by exact prefixLift 6003785
  have htrace : WordTrace (prefixWord ++ tailWord_6003785) baseStart_6003785 baseEnd_6003785 := by
    simpa [prefixWord, tailWord_6003785, baseEnd_6003785] using wordTrace_append hprefix tailTrace_6003785
  have hstable : (prefixWord ++ tailWord_6003785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003785).length < 2 ^ (prefixWord ++ tailWord_6003785).sum := by decide
  have hdescent : baseEnd_6003785 < baseStart_6003785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003786 : List Nat := [3, 1, 2, 1, 1, 2, 2, 6, 1, 1, 3]
def baseStart_6003786 : Nat := 118140960795 + 6003786 * 2 ^ 59
def prefixEnd_6003786 : Nat := 4983230072969 + 3 ^ 40 * 6003786 * 2
def baseEnd_6003786 : Nat := 3082827964734552393364097

theorem tailTrace_6003786 : CollatzResearch.WordTrace tailWord_6003786 prefixEnd_6003786 3082827964734552393364097 := by
  unfold tailWord_6003786
  simp only [CollatzResearch.WordTrace]
  refine ⟨54744016256829040465107803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145984043351544107906954141 54744016256829040465107803)
  ·
    refine ⟨82116024385243560697661705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54744016256829040465107803 82116024385243560697661705)
    ·
      refine ⟨61587018288932670523246279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82116024385243560697661705 61587018288932670523246279)
      ·
        refine ⟨92380527433399005784869419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61587018288932670523246279 92380527433399005784869419)
        ·
          refine ⟨138570791150098508677304129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92380527433399005784869419 138570791150098508677304129)
          ·
            refine ⟨103928093362573881507978097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138570791150098508677304129 103928093362573881507978097)
            ·
              refine ⟨77946070021930411130983573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103928093362573881507978097 77946070021930411130983573)
              ·
                refine ⟨3653722032277988021764855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77946070021930411130983573 3653722032277988021764855)
                ·
                  refine ⟨5480583048416982032647283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3653722032277988021764855 5480583048416982032647283)
                  ·
                    refine ⟨8220874572625473048970925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5480583048416982032647283 8220874572625473048970925)
                    ·
                      refine ⟨3082827964734552393364097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8220874572625473048970925 3082827964734552393364097)
                      ·
                        rfl

theorem cell23_6003786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 1, 1, 3].length) (baseStart_6003786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003786 prefixEnd_6003786 := by exact prefixLift 6003786
  have htrace : WordTrace (prefixWord ++ tailWord_6003786) baseStart_6003786 baseEnd_6003786 := by
    simpa [prefixWord, tailWord_6003786, baseEnd_6003786] using wordTrace_append hprefix tailTrace_6003786
  have hstable : (prefixWord ++ tailWord_6003786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003786).length < 2 ^ (prefixWord ++ tailWord_6003786).sum := by decide
  have hdescent : baseEnd_6003786 < baseStart_6003786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003802 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 6, 4]
def baseStart_6003802 : Nat := 118140960795 + 6003802 * 2 ^ 59
def prefixEnd_6003802 : Nat := 4983230072969 + 3 ^ 40 * 6003802 * 2
def baseEnd_6003802 : Nat := 1027612060141674776921341

theorem tailTrace_6003802 : CollatzResearch.WordTrace tailWord_6003802 prefixEnd_6003802 1027612060141674776921341 := by
  unfold tailWord_6003802
  simp only [CollatzResearch.WordTrace]
  refine ⟨54744162148814549148253415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145984432396838797728675773 54744162148814549148253415)
  ·
    refine ⟨82116243223221823722380123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54744162148814549148253415 82116243223221823722380123)
    ·
      refine ⟨123174364834832735583570185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82116243223221823722380123 123174364834832735583570185)
      ·
        refine ⟨92380773626124551687677639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123174364834832735583570185 92380773626124551687677639)
        ·
          refine ⟨138571160439186827531516459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92380773626124551687677639 138571160439186827531516459)
          ·
            refine ⟨207856740658780241297274689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138571160439186827531516459 207856740658780241297274689)
            ·
              refine ⟨155892555494085180972956017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207856740658780241297274689 155892555494085180972956017)
              ·
                refine ⟨116919416620563885729717013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155892555494085180972956017 116919416620563885729717013)
                ·
                  refine ⟨5480597654088932143580485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116919416620563885729717013 5480597654088932143580485)
                  ·
                    refine ⟨1027612060141674776921341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5480597654088932143580485 1027612060141674776921341)
                    ·
                      rfl

theorem cell23_6003802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 6, 4].length) (baseStart_6003802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003802 prefixEnd_6003802 := by exact prefixLift 6003802
  have htrace : WordTrace (prefixWord ++ tailWord_6003802) baseStart_6003802 baseEnd_6003802 := by
    simpa [prefixWord, tailWord_6003802, baseEnd_6003802] using wordTrace_append hprefix tailTrace_6003802
  have hstable : (prefixWord ++ tailWord_6003802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003802).length < 2 ^ (prefixWord ++ tailWord_6003802).sum := by decide
  have hdescent : baseEnd_6003802 < baseStart_6003802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003809 : List Nat := [1, 2, 3, 1, 1, 2, 5, 2, 1, 1, 4]
def baseStart_6003809 : Nat := 118140960795 + 6003809 * 2 ^ 59
def prefixEnd_6003809 : Nat := 4983230072969 + 3 ^ 40 * 6003809 * 2
def baseEnd_6003809 : Nat := 3082839774789605803376491

theorem tailTrace_6003809 : CollatzResearch.WordTrace tailWord_6003809 prefixEnd_6003809 3082839774789605803376491 := by
  unfold tailWord_6003809
  simp only [CollatzResearch.WordTrace]
  refine ⟨218976903906232836788518481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145984602604155224525678987 218976903906232836788518481)
  ·
    refine ⟨164232677929674627591388861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218976903906232836788518481 164232677929674627591388861)
    ·
      refine ⟨61587254223627985346770823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164232677929674627591388861 61587254223627985346770823)
      ·
        refine ⟨92380881335441978020156235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61587254223627985346770823 92380881335441978020156235)
        ·
          refine ⟨138571322003162967030234353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92380881335441978020156235 138571322003162967030234353)
          ·
            refine ⟨103928491502372225272675765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138571322003162967030234353 103928491502372225272675765)
            ·
              refine ⟨9743296078347396119313353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103928491502372225272675765 9743296078347396119313353)
              ·
                refine ⟨7307472058760547089485015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9743296078347396119313353 7307472058760547089485015)
                ·
                  refine ⟨10961208088140820634227523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7307472058760547089485015 10961208088140820634227523)
                  ·
                    refine ⟨16441812132211230951341285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10961208088140820634227523 16441812132211230951341285)
                    ·
                      refine ⟨3082839774789605803376491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16441812132211230951341285 3082839774789605803376491)
                      ·
                        rfl

theorem cell23_6003809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_6003809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003809 prefixEnd_6003809 := by exact prefixLift 6003809
  have htrace : WordTrace (prefixWord ++ tailWord_6003809) baseStart_6003809 baseEnd_6003809 := by
    simpa [prefixWord, tailWord_6003809, baseEnd_6003809] using wordTrace_append hprefix tailTrace_6003809
  have hstable : (prefixWord ++ tailWord_6003809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003809).length < 2 ^ (prefixWord ++ tailWord_6003809).sum := by decide
  have hdescent : baseEnd_6003809 < baseStart_6003809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003826 : List Nat := [3, 2, 1, 2, 2, 1, 5, 1, 1, 1, 4]
def baseStart_6003826 : Nat := 118140960795 + 6003826 * 2 ^ 59
def prefixEnd_6003826 : Nat := 4983230072969 + 3 ^ 40 * 6003826 * 2
def baseEnd_6003826 : Nat := 3082848503960732236863913

theorem tailTrace_6003826 : CollatzResearch.WordTrace tailWord_6003826 prefixEnd_6003826 3082848503960732236863913 := by
  unfold tailWord_6003826
  simp only [CollatzResearch.WordTrace]
  refine ⟨54744380986792812172971833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145985015964780832461258221 54744380986792812172971833)
  ·
    refine ⟨41058285740094609129728875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54744380986792812172971833 41058285740094609129728875)
    ·
      refine ⟨61587428610141913694593313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41058285740094609129728875 61587428610141913694593313)
      ·
        refine ⟨46190571457606435270944985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61587428610141913694593313 46190571457606435270944985)
        ·
          refine ⟨34642928593204826453208739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46190571457606435270944985 34642928593204826453208739)
          ·
            refine ⟨51964392889807239679813109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34642928593204826453208739 51964392889807239679813109)
            ·
              refine ⟨4871661833419428719982479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51964392889807239679813109 4871661833419428719982479)
              ·
                refine ⟨7307492750129143079973719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4871661833419428719982479 7307492750129143079973719)
                ·
                  refine ⟨10961239125193714619960579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7307492750129143079973719 10961239125193714619960579)
                  ·
                    refine ⟨16441858687790571929940869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10961239125193714619960579 16441858687790571929940869)
                    ·
                      refine ⟨3082848503960732236863913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16441858687790571929940869 3082848503960732236863913)
                      ·
                        rfl

theorem cell23_6003826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_6003826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003826 prefixEnd_6003826 := by exact prefixLift 6003826
  have htrace : WordTrace (prefixWord ++ tailWord_6003826) baseStart_6003826 baseEnd_6003826 := by
    simpa [prefixWord, tailWord_6003826, baseEnd_6003826] using wordTrace_append hprefix tailTrace_6003826
  have hstable : (prefixWord ++ tailWord_6003826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003826).length < 2 ^ (prefixWord ++ tailWord_6003826).sum := by decide
  have hdescent : baseEnd_6003826 < baseStart_6003826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003843 : List Nat := [1, 1, 1, 3, 3, 2, 3, 4, 1, 2, 2]
def baseStart_6003843 : Nat := 118140960795 + 6003843 * 2 ^ 59
def prefixEnd_6003843 : Nat := 4983230072969 + 3 ^ 40 * 6003843 * 2
def baseEnd_6003843 : Nat := 3082857233131858670351335

theorem tailTrace_6003843 : CollatzResearch.WordTrace tailWord_6003843 prefixEnd_6003843 3082857233131858670351335 := by
  unfold tailWord_6003843
  simp only [CollatzResearch.WordTrace]
  refine ⟨218978143988109660595256183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145985429325406440396837455 218978143988109660595256183)
  ·
    refine ⟨328467215982164490892884275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218978143988109660595256183 328467215982164490892884275)
    ·
      refine ⟨492700823973246736339326413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328467215982164490892884275 492700823973246736339326413)
      ·
        refine ⟨184762808989967526127247405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 492700823973246736339326413 184762808989967526127247405)
        ·
          refine ⟨69286053371237822297717777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184762808989967526127247405 69286053371237822297717777)
          ·
            refine ⟨51964540028428366723288333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69286053371237822297717777 51964540028428366723288333)
            ·
              refine ⟨19486702510660637521233125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51964540028428366723288333 19486702510660637521233125)
              ·
                refine ⟨3653756720748869535231211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19486702510660637521233125 3653756720748869535231211)
                ·
                  refine ⟨5480635081123304302846817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3653756720748869535231211 5480635081123304302846817)
                  ·
                    refine ⟨4110476310842478227135113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5480635081123304302846817 4110476310842478227135113)
                    ·
                      refine ⟨3082857233131858670351335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4110476310842478227135113 3082857233131858670351335)
                      ·
                        rfl

theorem cell23_6003843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 1, 2, 2].length) (baseStart_6003843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003843 prefixEnd_6003843 := by exact prefixLift 6003843
  have htrace : WordTrace (prefixWord ++ tailWord_6003843) baseStart_6003843 baseEnd_6003843 := by
    simpa [prefixWord, tailWord_6003843, baseEnd_6003843] using wordTrace_append hprefix tailTrace_6003843
  have hstable : (prefixWord ++ tailWord_6003843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003843).length < 2 ^ (prefixWord ++ tailWord_6003843).sum := by decide
  have hdescent : baseEnd_6003843 < baseStart_6003843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003872 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 5]
def baseStart_6003872 : Nat := 118140960795 + 6003872 * 2 ^ 59
def prefixEnd_6003872 : Nat := 4983230072969 + 3 ^ 40 * 6003872 * 2
def baseEnd_6003872 : Nat := 3082872124070839056888701

theorem tailTrace_6003872 : CollatzResearch.WordTrace tailWord_6003872 prefixEnd_6003872 3082872124070839056888701 := by
  unfold tailWord_6003872
  simp only [CollatzResearch.WordTrace]
  refine ⟨109489600852502299274030935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145986134470003065698707913 109489600852502299274030935)
  ·
    refine ⟨164234401278753448911046403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109489600852502299274030935 164234401278753448911046403)
    ·
      refine ⟨246351601918130173366569605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164234401278753448911046403 246351601918130173366569605)
      ·
        refine ⟨46190925359649407506231801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246351601918130173366569605 46190925359649407506231801)
        ·
          refine ⟨34643194019737055629673851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46190925359649407506231801 34643194019737055629673851)
          ·
            refine ⟨51964791029605583444510777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34643194019737055629673851 51964791029605583444510777)
            ·
              refine ⟨38973593272204187583383083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51964791029605583444510777 38973593272204187583383083)
              ·
                refine ⟨58460389908306281375074625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38973593272204187583383083 58460389908306281375074625)
                ·
                  refine ⟨43845292431229711031305969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58460389908306281375074625 43845292431229711031305969)
                  ·
                    refine ⟨32883969323422283273479477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43845292431229711031305969 32883969323422283273479477)
                    ·
                      refine ⟨3082872124070839056888701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32883969323422283273479477 3082872124070839056888701)
                      ·
                        rfl

theorem cell23_6003872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_6003872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003872 prefixEnd_6003872 := by exact prefixLift 6003872
  have htrace : WordTrace (prefixWord ++ tailWord_6003872) baseStart_6003872 baseEnd_6003872 := by
    simpa [prefixWord, tailWord_6003872, baseEnd_6003872] using wordTrace_append hprefix tailTrace_6003872
  have hstable : (prefixWord ++ tailWord_6003872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003872).length < 2 ^ (prefixWord ++ tailWord_6003872).sum := by decide
  have hdescent : baseEnd_6003872 < baseStart_6003872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6003959 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 1, 7, 2]
def baseStart_6003959 : Nat := 118140960795 + 6003959 * 2 ^ 59
def prefixEnd_6003959 : Nat := 4983230072969 + 3 ^ 40 * 6003959 * 2
def baseEnd_6003959 : Nat := 3082916796887780216500801

theorem tailTrace_6003959 : CollatzResearch.WordTrace tailWord_6003959 prefixEnd_6003959 3082916796887780216500801 := by
  unfold tailWord_6003959
  simp only [CollatzResearch.WordTrace]
  refine ⟨218982374855689412406478931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145988249903792941604319287 218982374855689412406478931)
  ·
    refine ⟨328473562283534118609718397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218982374855689412406478931 328473562283534118609718397)
    ·
      refine ⟨123177585856325294478644399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328473562283534118609718397 123177585856325294478644399)
      ·
        refine ⟨184766378784487941717966599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123177585856325294478644399 184766378784487941717966599)
        ·
          refine ⟨277149568176731912576949899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184766378784487941717966599 277149568176731912576949899)
          ·
            refine ⟨415724352265097868865424849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277149568176731912576949899 415724352265097868865424849)
            ·
              refine ⟨311793264198823401649068637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415724352265097868865424849 311793264198823401649068637)
              ·
                refine ⟨116922474074558775618400739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311793264198823401649068637 116922474074558775618400739)
                ·
                  refine ⟨175383711111838163427601109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116922474074558775618400739 175383711111838163427601109)
                  ·
                    refine ⟨4110555729183706955334401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 175383711111838163427601109 4110555729183706955334401)
                    ·
                      refine ⟨3082916796887780216500801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4110555729183706955334401 3082916796887780216500801)
                      ·
                        rfl

theorem cell23_6003959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 7, 2].length) (baseStart_6003959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6003959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6003959 prefixEnd_6003959 := by exact prefixLift 6003959
  have htrace : WordTrace (prefixWord ++ tailWord_6003959) baseStart_6003959 baseEnd_6003959 := by
    simpa [prefixWord, tailWord_6003959, baseEnd_6003959] using wordTrace_append hprefix tailTrace_6003959
  have hstable : (prefixWord ++ tailWord_6003959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6003959).length < 2 ^ (prefixWord ++ tailWord_6003959).sum := by decide
  have hdescent : baseEnd_6003959 < baseStart_6003959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6003959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
