import V185TrunkScan23Chunk0262

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1556196 : List Nat := [2, 3, 1, 1, 1, 3, 1, 6, 1, 4]
def baseStart_1556196 : Nat := 118140960795 + 1556196 * 2 ^ 59
def prefixEnd_1556196 : Nat := 4983230072969 + 3 ^ 40 * 1556196 * 2
def baseEnd_1556196 : Nat := 266358846868099536564397

theorem tailTrace_1556196 : CollatzResearch.WordTrace tailWord_1556196 prefixEnd_1556196 266358846868099536564397 := by
  unfold tailWord_1556196
  simp only [CollatzResearch.WordTrace]
  refine ⟨28379565535087571981156221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37839420713450095974874961 28379565535087571981156221)
  ·
    refine ⟨10642337075657839492933583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28379565535087571981156221 10642337075657839492933583)
    ·
      refine ⟨15963505613486759239400375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10642337075657839492933583 15963505613486759239400375)
      ·
        refine ⟨23945258420230138859100563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15963505613486759239400375 23945258420230138859100563)
        ·
          refine ⟨35917887630345208288650845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23945258420230138859100563 35917887630345208288650845)
          ·
            refine ⟨13469207861379453108244067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35917887630345208288650845 13469207861379453108244067)
            ·
              refine ⟨20203811792069179662366101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13469207861379453108244067 20203811792069179662366101)
              ·
                refine ⟨947053677753242796673411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20203811792069179662366101 947053677753242796673411)
                ·
                  refine ⟨1420580516629864195010117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 947053677753242796673411 1420580516629864195010117)
                  ·
                    refine ⟨266358846868099536564397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1420580516629864195010117 266358846868099536564397)
                    ·
                      rfl

theorem cell23_1556196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_1556196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556196 prefixEnd_1556196 := by exact prefixLift 1556196
  have htrace : WordTrace (prefixWord ++ tailWord_1556196) baseStart_1556196 baseEnd_1556196 := by
    simpa [prefixWord, tailWord_1556196, baseEnd_1556196] using wordTrace_append hprefix tailTrace_1556196
  have hstable : (prefixWord ++ tailWord_1556196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556196).length < 2 ^ (prefixWord ++ tailWord_1556196).sum := by decide
  have hdescent : baseEnd_1556196 < baseStart_1556196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556219 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 5, 1, 3]
def baseStart_1556219 : Nat := 118140960795 + 1556219 * 2 ^ 59
def prefixEnd_1556219 : Nat := 4983230072969 + 3 ^ 40 * 1556219 * 2
def baseEnd_1556219 : Nat := 799088350659352019705585

theorem tailTrace_1556219 : CollatzResearch.WordTrace tailWord_1556219 prefixEnd_1556219 799088350659352019705585 := by
  unfold tailWord_1556219
  simp only [CollatzResearch.WordTrace]
  refine ⟨56759969949091818890399711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37839979966061212593599807 56759969949091818890399711)
  ·
    refine ⟨85139954923637728335599567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56759969949091818890399711 85139954923637728335599567)
    ·
      refine ⟨127709932385456592503399351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85139954923637728335599567 127709932385456592503399351)
      ·
        refine ⟨191564898578184888755099027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127709932385456592503399351 191564898578184888755099027)
        ·
          refine ⟨287347347867277333132648541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191564898578184888755099027 287347347867277333132648541)
          ·
            refine ⟨107755255450228999924743203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287347347867277333132648541 107755255450228999924743203)
            ·
              refine ⟨161632883175343499887114805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107755255450228999924743203 161632883175343499887114805)
              ·
                refine ⟨15153082797688453114417013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161632883175343499887114805 15153082797688453114417013)
                ·
                  refine ⟨1420601512283292479476595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15153082797688453114417013 1420601512283292479476595)
                  ·
                    refine ⟨2130902268424938719214893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1420601512283292479476595 2130902268424938719214893)
                    ·
                      refine ⟨799088350659352019705585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2130902268424938719214893 799088350659352019705585)
                      ·
                        rfl

theorem cell23_1556219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 1, 3].length) (baseStart_1556219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556219 prefixEnd_1556219 := by exact prefixLift 1556219
  have htrace : WordTrace (prefixWord ++ tailWord_1556219) baseStart_1556219 baseEnd_1556219 := by
    simpa [prefixWord, tailWord_1556219, baseEnd_1556219] using wordTrace_append hprefix tailTrace_1556219
  have hstable : (prefixWord ++ tailWord_1556219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556219).length < 2 ^ (prefixWord ++ tailWord_1556219).sum := by decide
  have hdescent : baseEnd_1556219 < baseStart_1556219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556237 : List Nat := [1, 7, 2, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_1556237 : Nat := 118140960795 + 1556237 * 2 ^ 59
def prefixEnd_1556237 : Nat := 4983230072969 + 3 ^ 40 * 1556237 * 2
def baseEnd_1556237 : Nat := 799097593311132949280503

theorem tailTrace_1556237 : CollatzResearch.WordTrace tailWord_1556237 prefixEnd_1556237 799097593311132949280503 := by
  unfold tailWord_1556237
  simp only [CollatzResearch.WordTrace]
  refine ⟨56760626463026607964554965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37840417642017738643036643 56760626463026607964554965)
  ·
    refine ⟨1330327182727186124169257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 56760626463026607964554965 1330327182727186124169257)
    ·
      refine ⟨997745387045389593126943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1330327182727186124169257 997745387045389593126943)
      ·
        refine ⟨1496618080568084389690415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 997745387045389593126943 1496618080568084389690415)
        ·
          refine ⟨2244927120852126584535623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1496618080568084389690415 2244927120852126584535623)
          ·
            refine ⟨3367390681278189876803435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2244927120852126584535623 3367390681278189876803435)
            ·
              refine ⟨5051086021917284815205153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3367390681278189876803435 5051086021917284815205153)
              ·
                refine ⟨3788314516437963611403865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5051086021917284815205153 3788314516437963611403865)
                ·
                  refine ⟨2841235887328472708552899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3788314516437963611403865 2841235887328472708552899)
                  ·
                    refine ⟨4261853830992709062829349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2841235887328472708552899 4261853830992709062829349)
                    ·
                      refine ⟨799097593311132949280503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4261853830992709062829349 799097593311132949280503)
                      ·
                        rfl

theorem cell23_1556237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_1556237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556237 prefixEnd_1556237 := by exact prefixLift 1556237
  have htrace : WordTrace (prefixWord ++ tailWord_1556237) baseStart_1556237 baseEnd_1556237 := by
    simpa [prefixWord, tailWord_1556237, baseEnd_1556237] using wordTrace_append hprefix tailTrace_1556237
  have hstable : (prefixWord ++ tailWord_1556237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556237).length < 2 ^ (prefixWord ++ tailWord_1556237).sum := by decide
  have hdescent : baseEnd_1556237 < baseStart_1556237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556286 : List Nat := [4, 2, 1, 2, 2, 2, 1, 2, 1, 6]
def baseStart_1556286 : Nat := 118140960795 + 1556286 * 2 ^ 59
def prefixEnd_1556286 : Nat := 4983230072969 + 3 ^ 40 * 1556286 * 2
def baseEnd_1556286 : Nat := 266374251287734419189259

theorem tailTrace_1556286 : CollatzResearch.WordTrace tailWord_1556286 prefixEnd_1556286 266374251287734419189259 := by
  unfold tailWord_1556286
  simp only [CollatzResearch.WordTrace]
  refine ⟨7095301704981136166636089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37841609093232726222059141 7095301704981136166636089)
  ·
    refine ⟨5321476278735852124977067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7095301704981136166636089 5321476278735852124977067)
    ·
      refine ⟨7982214418103778187465601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5321476278735852124977067 7982214418103778187465601)
      ·
        refine ⟨5986660813577833640599201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7982214418103778187465601 5986660813577833640599201)
        ·
          refine ⟨4489995610183375230449401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5986660813577833640599201 4489995610183375230449401)
          ·
            refine ⟨3367496707637531422837051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4489995610183375230449401 3367496707637531422837051)
            ·
              refine ⟨5051245061456297134255577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3367496707637531422837051 5051245061456297134255577)
              ·
                refine ⟨3788433796092222850691683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5051245061456297134255577 3788433796092222850691683)
                ·
                  refine ⟨5682650694138334276037525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3788433796092222850691683 5682650694138334276037525)
                  ·
                    refine ⟨266374251287734419189259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5682650694138334276037525 266374251287734419189259)
                    ·
                      rfl

theorem cell23_1556286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_1556286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556286 prefixEnd_1556286 := by exact prefixLift 1556286
  have htrace : WordTrace (prefixWord ++ tailWord_1556286) baseStart_1556286 baseEnd_1556286 := by
    simpa [prefixWord, tailWord_1556286, baseEnd_1556286] using wordTrace_append hprefix tailTrace_1556286
  have hstable : (prefixWord ++ tailWord_1556286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556286).length < 2 ^ (prefixWord ++ tailWord_1556286).sum := by decide
  have hdescent : baseEnd_1556286 < baseStart_1556286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556296 : List Nat := [2, 1, 3, 1, 1, 6, 1, 1, 1, 1, 5]
def baseStart_1556296 : Nat := 118140960795 + 1556296 * 2 ^ 59
def prefixEnd_1556296 : Nat := 4983230072969 + 3 ^ 40 * 1556296 * 2
def baseEnd_1556296 : Nat := 799127888669748218442731

theorem tailTrace_1556296 : CollatzResearch.WordTrace tailWord_1556296 prefixEnd_1556296 799127888669748218442731 := by
  unfold tailWord_1556296
  simp only [CollatzResearch.WordTrace]
  refine ⟨28381389184906430520476371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37841852246541907360635161 28381389184906430520476371)
  ·
    refine ⟨42572083777359645780714557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28381389184906430520476371 42572083777359645780714557)
    ·
      refine ⟨15964531416509867167767959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42572083777359645780714557 15964531416509867167767959)
      ·
        refine ⟨23946797124764800751651939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15964531416509867167767959 23946797124764800751651939)
        ·
          refine ⟨35920195687147201127477909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23946797124764800751651939 35920195687147201127477909)
          ·
            refine ⟨1683759172835025052850527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35920195687147201127477909 1683759172835025052850527)
            ·
              refine ⟨2525638759252537579275791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1683759172835025052850527 2525638759252537579275791)
              ·
                refine ⟨3788458138878806368913687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2525638759252537579275791 3788458138878806368913687)
                ·
                  refine ⟨5682687208318209553370531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3788458138878806368913687 5682687208318209553370531)
                  ·
                    refine ⟨8524030812477314330055797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5682687208318209553370531 8524030812477314330055797)
                    ·
                      refine ⟨799127888669748218442731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8524030812477314330055797 799127888669748218442731)
                      ·
                        rfl

theorem cell23_1556296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_1556296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556296 prefixEnd_1556296 := by exact prefixLift 1556296
  have htrace : WordTrace (prefixWord ++ tailWord_1556296) baseStart_1556296 baseEnd_1556296 := by
    simpa [prefixWord, tailWord_1556296, baseEnd_1556296] using wordTrace_append hprefix tailTrace_1556296
  have hstable : (prefixWord ++ tailWord_1556296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556296).length < 2 ^ (prefixWord ++ tailWord_1556296).sum := by decide
  have hdescent : baseEnd_1556296 < baseStart_1556296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556369 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 3]
def baseStart_1556369 : Nat := 118140960795 + 1556369 * 2 ^ 59
def prefixEnd_1556369 : Nat := 4983230072969 + 3 ^ 40 * 1556369 * 2
def baseEnd_1556369 : Nat := 799165372757526432829895

theorem tailTrace_1556369 : CollatzResearch.WordTrace tailWord_1556369 prefixEnd_1556369 799165372757526432829895 := by
  unfold tailWord_1556369
  simp only [CollatzResearch.WordTrace]
  refine ⟨56765440898548394508360161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37843627265698929672240107 56765440898548394508360161)
  ·
    refine ⟨42574080673911295881270121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56765440898548394508360161 42574080673911295881270121)
    ·
      refine ⟨31930560505433471910952591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42574080673911295881270121 31930560505433471910952591)
      ·
        refine ⟨47895840758150207866428887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31930560505433471910952591 47895840758150207866428887)
        ·
          refine ⟨71843761137225311799643331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47895840758150207866428887 71843761137225311799643331)
          ·
            refine ⟨107765641705837967699464997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71843761137225311799643331 107765641705837967699464997)
            ·
              refine ⟨20206057819844618943649687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107765641705837967699464997 20206057819844618943649687)
              ·
                refine ⟨30309086729766928415474531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20206057819844618943649687 30309086729766928415474531)
                ·
                  refine ⟨45463630094650392623211797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30309086729766928415474531 45463630094650392623211797)
                  ·
                    refine ⟨2131107660686737154213053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45463630094650392623211797 2131107660686737154213053)
                    ·
                      refine ⟨799165372757526432829895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2131107660686737154213053 799165372757526432829895)
                      ·
                        rfl

theorem cell23_1556369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 3].length) (baseStart_1556369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556369 prefixEnd_1556369 := by exact prefixLift 1556369
  have htrace : WordTrace (prefixWord ++ tailWord_1556369) baseStart_1556369 baseEnd_1556369 := by
    simpa [prefixWord, tailWord_1556369, baseEnd_1556369] using wordTrace_append hprefix tailTrace_1556369
  have hstable : (prefixWord ++ tailWord_1556369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556369).length < 2 ^ (prefixWord ++ tailWord_1556369).sum := by decide
  have hdescent : baseEnd_1556369 < baseStart_1556369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556374 : List Nat := [5, 3, 1, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_1556374 : Nat := 118140960795 + 1556374 * 2 ^ 59
def prefixEnd_1556374 : Nat := 4983230072969 + 3 ^ 40 * 1556374 * 2
def baseEnd_1556374 : Nat := 799167940160798913267373

theorem tailTrace_1556374 : CollatzResearch.WordTrace tailWord_1556374 prefixEnd_1556374 799167940160798913267373 := by
  unfold tailWord_1556374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3547851453970642522643261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37843748842353520241528117 3547851453970642522643261)
  ·
    refine ⟨1330444295238990945991223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3547851453970642522643261 1330444295238990945991223)
    ·
      refine ⟨1995666442858486418986835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1330444295238990945991223 1995666442858486418986835)
      ·
        refine ⟨2993499664287729628480253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1995666442858486418986835 2993499664287729628480253)
        ·
          refine ⟨1122562374107898610680095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2993499664287729628480253 1122562374107898610680095)
          ·
            refine ⟨1683843561161847916020143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1122562374107898610680095 1683843561161847916020143)
            ·
              refine ⟨2525765341742771874030215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1683843561161847916020143 2525765341742771874030215)
              ·
                refine ⟨3788648012614157811045323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2525765341742771874030215 3788648012614157811045323)
                ·
                  refine ⟨5682972018921236716567985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3788648012614157811045323 5682972018921236716567985)
                  ·
                    refine ⟨4262229014190927537425989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5682972018921236716567985 4262229014190927537425989)
                    ·
                      refine ⟨799167940160798913267373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4262229014190927537425989 799167940160798913267373)
                      ·
                        rfl

theorem cell23_1556374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_1556374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556374 prefixEnd_1556374 := by exact prefixLift 1556374
  have htrace : WordTrace (prefixWord ++ tailWord_1556374) baseStart_1556374 baseEnd_1556374 := by
    simpa [prefixWord, tailWord_1556374, baseEnd_1556374] using wordTrace_append hprefix tailTrace_1556374
  have hstable : (prefixWord ++ tailWord_1556374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556374).length < 2 ^ (prefixWord ++ tailWord_1556374).sum := by decide
  have hdescent : baseEnd_1556374 < baseStart_1556374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556436 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 4, 5]
def baseStart_1556436 : Nat := 118140960795 + 1556436 * 2 ^ 59
def prefixEnd_1556436 : Nat := 4983230072969 + 3 ^ 40 * 1556436 * 2
def baseEnd_1556436 : Nat := 266399925320459223564029

theorem tailTrace_1556436 : CollatzResearch.WordTrace tailWord_1556436 prefixEnd_1556436 266399925320459223564029 := by
  unfold tailWord_1556436
  simp only [CollatzResearch.WordTrace]
  refine ⟨28383942294652832475524581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37845256392870443300699441 28383942294652832475524581)
  ·
    refine ⟨5321989180247406089160859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28383942294652832475524581 5321989180247406089160859)
    ·
      refine ⟨7982983770371109133741289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5321989180247406089160859 7982983770371109133741289)
      ·
        refine ⟨5987237827778331850305967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7982983770371109133741289 5987237827778331850305967)
        ·
          refine ⟨8980856741667497775458951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5987237827778331850305967 8980856741667497775458951)
          ·
            refine ⟨13471285112501246663188427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8980856741667497775458951 13471285112501246663188427)
            ·
              refine ⟨20206927668751869994782641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13471285112501246663188427 20206927668751869994782641)
              ·
                refine ⟨15155195751563902496086981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20206927668751869994782641 15155195751563902496086981)
                ·
                  refine ⟨2841599203418231718016309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15155195751563902496086981 2841599203418231718016309)
                  ·
                    refine ⟨266399925320459223564029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2841599203418231718016309 266399925320459223564029)
                    ·
                      rfl

theorem cell23_1556436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_1556436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556436 prefixEnd_1556436 := by exact prefixLift 1556436
  have htrace : WordTrace (prefixWord ++ tailWord_1556436) baseStart_1556436 baseEnd_1556436 := by
    simpa [prefixWord, tailWord_1556436, baseEnd_1556436] using wordTrace_append hprefix tailTrace_1556436
  have hstable : (prefixWord ++ tailWord_1556436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556436).length < 2 ^ (prefixWord ++ tailWord_1556436).sum := by decide
  have hdescent : baseEnd_1556436 < baseStart_1556436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556449 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 2, 8]
def baseStart_1556449 : Nat := 118140960795 + 1556449 * 2 ^ 59
def prefixEnd_1556449 : Nat := 4983230072969 + 3 ^ 40 * 1556449 * 2
def baseEnd_1556449 : Nat := 266402150403295373276509

theorem tailTrace_1556449 : CollatzResearch.WordTrace tailWord_1556449 prefixEnd_1556449 266402150403295373276509 := by
  unfold tailWord_1556449
  simp only [CollatzResearch.WordTrace]
  refine ⟨56768358738258568171272401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37845572492172378780848267 56768358738258568171272401)
  ·
    refine ⟨42576269053693926128454301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56768358738258568171272401 42576269053693926128454301)
    ·
      refine ⟨15966100895135222298170363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42576269053693926128454301 15966100895135222298170363)
      ·
        refine ⟨23949151342702833447255545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15966100895135222298170363 23949151342702833447255545)
        ·
          refine ⟨17961863507027125085441659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23949151342702833447255545 17961863507027125085441659)
          ·
            refine ⟨26942795260540687628162489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17961863507027125085441659 26942795260540687628162489)
            ·
              refine ⟨20207096445405515721121867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26942795260540687628162489 20207096445405515721121867)
              ·
                refine ⟨30310644668108273581682801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20207096445405515721121867 30310644668108273581682801)
                ·
                  refine ⟨22732983501081205186262101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30310644668108273581682801 22732983501081205186262101)
                  ·
                    refine ⟨266402150403295373276509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22732983501081205186262101 266402150403295373276509)
                    ·
                      rfl

theorem cell23_1556449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_1556449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556449 prefixEnd_1556449 := by exact prefixLift 1556449
  have htrace : WordTrace (prefixWord ++ tailWord_1556449) baseStart_1556449 baseEnd_1556449 := by
    simpa [prefixWord, tailWord_1556449, baseEnd_1556449] using wordTrace_append hprefix tailTrace_1556449
  have hstable : (prefixWord ++ tailWord_1556449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556449).length < 2 ^ (prefixWord ++ tailWord_1556449).sum := by decide
  have hdescent : baseEnd_1556449 < baseStart_1556449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556479 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 8]
def baseStart_1556479 : Nat := 118140960795 + 1556479 * 2 ^ 59
def prefixEnd_1556479 : Nat := 4983230072969 + 3 ^ 40 * 1556479 * 2
def baseEnd_1556479 : Nat := 88802428403280111383821

theorem tailTrace_1556479 : CollatzResearch.WordTrace tailWord_1556479 prefixEnd_1556479 88802428403280111383821 := by
  unfold tailWord_1556479
  simp only [CollatzResearch.WordTrace]
  refine ⟨56769452928149883294864491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37846301952099922196576327 56769452928149883294864491)
  ·
    refine ⟨85154179392224824942296737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56769452928149883294864491 85154179392224824942296737)
    ·
      refine ⟨63865634544168618706722553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85154179392224824942296737 63865634544168618706722553)
      ·
        refine ⟨47899225908126464030041915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63865634544168618706722553 47899225908126464030041915)
        ·
          refine ⟨71848838862189696045062873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47899225908126464030041915 71848838862189696045062873)
          ·
            refine ⟨53886629146642272033797155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71848838862189696045062873 53886629146642272033797155)
            ·
              refine ⟨80829943719963408050695733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53886629146642272033797155 80829943719963408050695733)
              ·
                refine ⟨7577807223746569504752725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80829943719963408050695733 7577807223746569504752725)
                ·
                  refine ⟨88802428403280111383821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7577807223746569504752725 88802428403280111383821)
                  ·
                    rfl

theorem cell23_1556479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 8].length) (baseStart_1556479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556479 prefixEnd_1556479 := by exact prefixLift 1556479
  have htrace : WordTrace (prefixWord ++ tailWord_1556479) baseStart_1556479 baseEnd_1556479 := by
    simpa [prefixWord, tailWord_1556479, baseEnd_1556479] using wordTrace_append hprefix tailTrace_1556479
  have hstable : (prefixWord ++ tailWord_1556479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556479).length < 2 ^ (prefixWord ++ tailWord_1556479).sum := by decide
  have hdescent : baseEnd_1556479 < baseStart_1556479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556490 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 2, 4, 2]
def baseStart_1556490 : Nat := 118140960795 + 1556490 * 2 ^ 59
def prefixEnd_1556490 : Nat := 4983230072969 + 3 ^ 40 * 1556490 * 2
def baseEnd_1556490 : Nat := 799227503916720459416839

theorem tailTrace_1556490 : CollatzResearch.WordTrace tailWord_1556490 prefixEnd_1556490 799227503916720459416839 := by
  unfold tailWord_1556490
  simp only [CollatzResearch.WordTrace]
  refine ⟨14192463532777508043378731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37846569420740021449009949 14192463532777508043378731)
  ·
    refine ⟨21288695299166262065068097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14192463532777508043378731 21288695299166262065068097)
    ·
      refine ⟨15966521474374696548801073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21288695299166262065068097 15966521474374696548801073)
      ·
        refine ⟨11974891105781022411600805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15966521474374696548801073 11974891105781022411600805)
        ·
          refine ⟨2245292082333941702175151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11974891105781022411600805 2245292082333941702175151)
          ·
            refine ⟨3367938123500912553262727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2245292082333941702175151 3367938123500912553262727)
            ·
              refine ⟨5051907185251368829894091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3367938123500912553262727 5051907185251368829894091)
              ·
                refine ⟨7577860777877053244841137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5051907185251368829894091 7577860777877053244841137)
                ·
                  refine ⟨5683395583407789933630853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7577860777877053244841137 5683395583407789933630853)
                  ·
                    refine ⟨1065636671888960612555785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5683395583407789933630853 1065636671888960612555785)
                    ·
                      refine ⟨799227503916720459416839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1065636671888960612555785 799227503916720459416839)
                      ·
                        rfl

theorem cell23_1556490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_1556490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556490 prefixEnd_1556490 := by exact prefixLift 1556490
  have htrace : WordTrace (prefixWord ++ tailWord_1556490) baseStart_1556490 baseEnd_1556490 := by
    simpa [prefixWord, tailWord_1556490, baseEnd_1556490] using wordTrace_append hprefix tailTrace_1556490
  have hstable : (prefixWord ++ tailWord_1556490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556490).length < 2 ^ (prefixWord ++ tailWord_1556490).sum := by decide
  have hdescent : baseEnd_1556490 < baseStart_1556490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556540 : List Nat := [2, 2, 2, 2, 2, 1, 4, 1, 3, 1, 3]
def baseStart_1556540 : Nat := 118140960795 + 1556540 * 2 ^ 59
def prefixEnd_1556540 : Nat := 4983230072969 + 3 ^ 40 * 1556540 * 2
def baseEnd_1556540 : Nat := 799253177949445263791609

theorem tailTrace_1556540 : CollatzResearch.WordTrace tailWord_1556540 prefixEnd_1556540 799253177949445263791609 := by
  unfold tailWord_1556540
  simp only [CollatzResearch.WordTrace]
  refine ⟨28385838890464445356417537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37847785187285927141890049 28385838890464445356417537)
  ·
    refine ⟨21289379167848334017313153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28385838890464445356417537 21289379167848334017313153)
    ·
      refine ⟨15967034375886250512984865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21289379167848334017313153 15967034375886250512984865)
      ·
        refine ⟨11975275781914687884738649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15967034375886250512984865 11975275781914687884738649)
        ·
          refine ⟨8981456836436015913553987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11975275781914687884738649 8981456836436015913553987)
          ·
            refine ⟨13472185254654023870330981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8981456836436015913553987 13472185254654023870330981)
            ·
              refine ⟨2526034735247629475687059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13472185254654023870330981 2526034735247629475687059)
              ·
                refine ⟨3789052102871444213530589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2526034735247629475687059 3789052102871444213530589)
                ·
                  refine ⟨1420894538576791580073971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3789052102871444213530589 1420894538576791580073971)
                  ·
                    refine ⟨2131341807865187370110957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1420894538576791580073971 2131341807865187370110957)
                    ·
                      refine ⟨799253177949445263791609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2131341807865187370110957 799253177949445263791609)
                      ·
                        rfl

theorem cell23_1556540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_1556540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556540 prefixEnd_1556540 := by exact prefixLift 1556540
  have htrace : WordTrace (prefixWord ++ tailWord_1556540) baseStart_1556540 baseEnd_1556540 := by
    simpa [prefixWord, tailWord_1556540, baseEnd_1556540] using wordTrace_append hprefix tailTrace_1556540
  have hstable : (prefixWord ++ tailWord_1556540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556540).length < 2 ^ (prefixWord ++ tailWord_1556540).sum := by decide
  have hdescent : baseEnd_1556540 < baseStart_1556540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556580 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 5, 2, 2]
def baseStart_1556580 : Nat := 118140960795 + 1556580 * 2 ^ 59
def prefixEnd_1556580 : Nat := 4983230072969 + 3 ^ 40 * 1556580 * 2
def baseEnd_1556580 : Nat := 799273717175625107291425

theorem tailTrace_1556580 : CollatzResearch.WordTrace tailWord_1556580 prefixEnd_1556580 799273717175625107291425 := by
  unfold tailWord_1556580
  simp only [CollatzResearch.WordTrace]
  refine ⟨28386568350391988772145597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37848757800522651696194129 28386568350391988772145597)
  ·
    refine ⟨10644963131396995789554599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28386568350391988772145597 10644963131396995789554599)
    ·
      refine ⟨15967444697095493684331899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10644963131396995789554599 15967444697095493684331899)
      ·
        refine ⟨23951167045643240526497849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15967444697095493684331899 23951167045643240526497849)
        ·
          refine ⟨17963375284232430394873387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23951167045643240526497849 17963375284232430394873387)
          ·
            refine ⟨26945062926348645592310081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17963375284232430394873387 26945062926348645592310081)
            ·
              refine ⟨20208797194761484194232561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26945062926348645592310081 20208797194761484194232561)
              ·
                refine ⟨15156597896071113145674421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20208797194761484194232561 15156597896071113145674421)
                ·
                  refine ⟨1420931052756666857406977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15156597896071113145674421 1420931052756666857406977)
                  ·
                    refine ⟨1065698289567500143055233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1420931052756666857406977 1065698289567500143055233)
                    ·
                      refine ⟨799273717175625107291425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1065698289567500143055233 799273717175625107291425)
                      ·
                        rfl

theorem cell23_1556580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 5, 2, 2].length) (baseStart_1556580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556580 prefixEnd_1556580 := by exact prefixLift 1556580
  have htrace : WordTrace (prefixWord ++ tailWord_1556580) baseStart_1556580 baseEnd_1556580 := by
    simpa [prefixWord, tailWord_1556580, baseEnd_1556580] using wordTrace_append hprefix tailTrace_1556580
  have hstable : (prefixWord ++ tailWord_1556580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556580).length < 2 ^ (prefixWord ++ tailWord_1556580).sum := by decide
  have hdescent : baseEnd_1556580 < baseStart_1556580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556583 : List Nat := [1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 5]
def baseStart_1556583 : Nat := 118140960795 + 1556583 * 2 ^ 59
def prefixEnd_1556583 : Nat := 4983230072969 + 3 ^ 40 * 1556583 * 2
def baseEnd_1556583 : Nat := 799275257617588595553911

theorem tailTrace_1556583 : CollatzResearch.WordTrace tailWord_1556583 prefixEnd_1556583 799275257617588595553911 := by
  unfold tailWord_1556583
  simp only [CollatzResearch.WordTrace]
  refine ⟨56773246119773109056650403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37848830746515406037766935 56773246119773109056650403)
  ·
    refine ⟨85159869179659663584975605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56773246119773109056650403 85159869179659663584975605)
    ·
      refine ⟨7983737735593093461091463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85159869179659663584975605 7983737735593093461091463)
      ·
        refine ⟨11975606603389640191637195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7983737735593093461091463 11975606603389640191637195)
        ·
          refine ⟨17963409905084460287455793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11975606603389640191637195 17963409905084460287455793)
          ·
            refine ⟨13472557428813345215591845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17963409905084460287455793 13472557428813345215591845)
            ·
              refine ⟨2526104517902502227923471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13472557428813345215591845 2526104517902502227923471)
              ·
                refine ⟨3789156776853753341885207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2526104517902502227923471 3789156776853753341885207)
                ·
                  refine ⟨5683735165280630012827811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3789156776853753341885207 5683735165280630012827811)
                  ·
                    refine ⟨8525602747920945019241717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5683735165280630012827811 8525602747920945019241717)
                    ·
                      refine ⟨799275257617588595553911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8525602747920945019241717 799275257617588595553911)
                      ·
                        rfl

theorem cell23_1556583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_1556583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556583 prefixEnd_1556583 := by exact prefixLift 1556583
  have htrace : WordTrace (prefixWord ++ tailWord_1556583) baseStart_1556583 baseEnd_1556583 := by
    simpa [prefixWord, tailWord_1556583, baseEnd_1556583] using wordTrace_append hprefix tailTrace_1556583
  have hstable : (prefixWord ++ tailWord_1556583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556583).length < 2 ^ (prefixWord ++ tailWord_1556583).sum := by decide
  have hdescent : baseEnd_1556583 < baseStart_1556583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556590 : List Nat := [4, 1, 2, 2, 1, 1, 2, 4, 2, 4]
def baseStart_1556590 : Nat := 118140960795 + 1556590 * 2 ^ 59
def prefixEnd_1556590 : Nat := 4983230072969 + 3 ^ 40 * 1556590 * 2
def baseEnd_1556590 : Nat := 266426283994056689388793

theorem tailTrace_1556590 : CollatzResearch.WordTrace tailWord_1556590 prefixEnd_1556590 266426283994056689388793 := by
  unfold tailWord_1556590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7096687678843468656519403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37849000953831832834770149 7096687678843468656519403)
  ·
    refine ⟨10645031518265202984779105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7096687678843468656519403 10645031518265202984779105)
    ·
      refine ⟨7983773638698902238584329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10645031518265202984779105 7983773638698902238584329)
      ·
        refine ⟨5987830229024176678938247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7983773638698902238584329 5987830229024176678938247)
        ·
          refine ⟨8981745343536265018407371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5987830229024176678938247 8981745343536265018407371)
          ·
            refine ⟨13472618015304397527611057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8981745343536265018407371 13472618015304397527611057)
            ·
              refine ⟨10104463511478298145708293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13472618015304397527611057 10104463511478298145708293)
              ·
                refine ⟨1894586908402180902320305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10104463511478298145708293 1894586908402180902320305)
                ·
                  refine ⟨1420940181301635676740229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1894586908402180902320305 1420940181301635676740229)
                  ·
                    refine ⟨266426283994056689388793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1420940181301635676740229 266426283994056689388793)
                    ·
                      rfl

theorem cell23_1556590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_1556590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556590 prefixEnd_1556590 := by exact prefixLift 1556590
  have htrace : WordTrace (prefixWord ++ tailWord_1556590) baseStart_1556590 baseEnd_1556590 := by
    simpa [prefixWord, tailWord_1556590, baseEnd_1556590] using wordTrace_append hprefix tailTrace_1556590
  have hstable : (prefixWord ++ tailWord_1556590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556590).length < 2 ^ (prefixWord ++ tailWord_1556590).sum := by decide
  have hdescent : baseEnd_1556590 < baseStart_1556590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556634 : List Nat := [3, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3]
def baseStart_1556634 : Nat := 118140960795 + 1556634 * 2 ^ 59
def prefixEnd_1556634 : Nat := 4983230072969 + 3 ^ 40 * 1556634 * 2
def baseEnd_1556634 : Nat := 799301445130967896016177

theorem tailTrace_1556634 : CollatzResearch.WordTrace tailWord_1556634 prefixEnd_1556634 799301445130967896016177 := by
  unfold tailWord_1556634
  simp only [CollatzResearch.WordTrace]
  refine ⟨14193776560647086191689239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37850070828392229844504637 14193776560647086191689239)
  ·
    refine ⟨21290664840970629287533859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14193776560647086191689239 21290664840970629287533859)
    ·
      refine ⟨31935997261455943931300789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21290664840970629287533859 31935997261455943931300789)
      ·
        refine ⟨2993999743261494743559449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31935997261455943931300789 2993999743261494743559449)
        ·
          refine ⟨2245499807446121057669587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2993999743261494743559449 2245499807446121057669587)
          ·
            refine ⟨3368249711169181586504381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2245499807446121057669587 3368249711169181586504381)
            ·
              refine ⟨1263093641688443094939143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3368249711169181586504381 1263093641688443094939143)
              ·
                refine ⟨1894640462532664642408715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1263093641688443094939143 1894640462532664642408715)
                ·
                  refine ⟨2841960693798996963613073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1894640462532664642408715 2841960693798996963613073)
                  ·
                    refine ⟨2131470520349247722709805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2841960693798996963613073 2131470520349247722709805)
                    ·
                      refine ⟨799301445130967896016177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2131470520349247722709805 799301445130967896016177)
                      ·
                        rfl

theorem cell23_1556634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_1556634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556634 prefixEnd_1556634 := by exact prefixLift 1556634
  have htrace : WordTrace (prefixWord ++ tailWord_1556634) baseStart_1556634 baseEnd_1556634 := by
    simpa [prefixWord, tailWord_1556634, baseEnd_1556634] using wordTrace_append hprefix tailTrace_1556634
  have hstable : (prefixWord ++ tailWord_1556634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556634).length < 2 ^ (prefixWord ++ tailWord_1556634).sum := by decide
  have hdescent : baseEnd_1556634 < baseStart_1556634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556654 : List Nat := [4, 1, 4, 2, 2, 1, 1, 8]
def baseStart_1556654 : Nat := 118140960795 + 1556654 * 2 ^ 59
def prefixEnd_1556654 : Nat := 4983230072969 + 3 ^ 40 * 1556654 * 2
def baseEnd_1556654 : Nat := 29604137583113252509855

theorem tailTrace_1556654 : CollatzResearch.WordTrace tailWord_1556654 prefixEnd_1556654 29604137583113252509855 := by
  unfold tailWord_1556654
  simp only [CollatzResearch.WordTrace]
  refine ⟨7096979462814486022810627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37850557135010592121656677 7096979462814486022810627)
  ·
    refine ⟨10645469194221729034215941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7096979462814486022810627 10645469194221729034215941)
    ·
      refine ⟨1996025473916574193915489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10645469194221729034215941 1996025473916574193915489)
      ·
        refine ⟨1497019105437430645436617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1996025473916574193915489 1497019105437430645436617)
        ·
          refine ⟨1122764329078072984077463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1497019105437430645436617 1122764329078072984077463)
          ·
            refine ⟨1684146493617109476116195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1122764329078072984077463 1684146493617109476116195)
            ·
              refine ⟨2526219740425664214174293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1684146493617109476116195 2526219740425664214174293)
              ·
                refine ⟨29604137583113252509855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2526219740425664214174293 29604137583113252509855)
                ·
                  rfl

theorem cell23_1556654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 8].length) (baseStart_1556654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556654 prefixEnd_1556654 := by exact prefixLift 1556654
  have htrace : WordTrace (prefixWord ++ tailWord_1556654) baseStart_1556654 baseEnd_1556654 := by
    simpa [prefixWord, tailWord_1556654, baseEnd_1556654] using wordTrace_append hprefix tailTrace_1556654
  have hstable : (prefixWord ++ tailWord_1556654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556654).length < 2 ^ (prefixWord ++ tailWord_1556654).sum := by decide
  have hdescent : baseEnd_1556654 < baseStart_1556654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556663 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 2, 6]
def baseStart_1556663 : Nat := 118140960795 + 1556663 * 2 ^ 59
def prefixEnd_1556663 : Nat := 4983230072969 + 3 ^ 40 * 1556663 * 2
def baseEnd_1556663 : Nat := 266438778689982760851181

theorem tailTrace_1556663 : CollatzResearch.WordTrace tailWord_1556663 prefixEnd_1556663 266438778689982760851181 := by
  unfold tailWord_1556663
  simp only [CollatzResearch.WordTrace]
  refine ⟨56776163959483282719562643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37850775972988855146375095 56776163959483282719562643)
  ·
    refine ⟨85164245939224924079343965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56776163959483282719562643 85164245939224924079343965)
    ·
      refine ⟨31936592227209346529753987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85164245939224924079343965 31936592227209346529753987)
      ·
        refine ⟨47904888340814019794630981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31936592227209346529753987 47904888340814019794630981)
        ·
          refine ⟨8982166563902628711493309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47904888340814019794630981 8982166563902628711493309)
          ·
            refine ⟨3368312461463485766809991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8982166563902628711493309 3368312461463485766809991)
            ·
              refine ⟨5052468692195228650214987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3368312461463485766809991 5052468692195228650214987)
              ·
                refine ⟨7578703038292842975322481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5052468692195228650214987 7578703038292842975322481)
                ·
                  refine ⟨5684027278719632231491861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7578703038292842975322481 5684027278719632231491861)
                  ·
                    refine ⟨266438778689982760851181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5684027278719632231491861 266438778689982760851181)
                    ·
                      rfl

theorem cell23_1556663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_1556663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556663 prefixEnd_1556663 := by exact prefixLift 1556663
  have htrace : WordTrace (prefixWord ++ tailWord_1556663) baseStart_1556663 baseEnd_1556663 := by
    simpa [prefixWord, tailWord_1556663, baseEnd_1556663] using wordTrace_append hprefix tailTrace_1556663
  have hstable : (prefixWord ++ tailWord_1556663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556663).length < 2 ^ (prefixWord ++ tailWord_1556663).sum := by decide
  have hdescent : baseEnd_1556663 < baseStart_1556663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556760 : List Nat := [2, 1, 2, 3, 1, 2, 3, 2, 2, 1, 4]
def baseStart_1556760 : Nat := 118140960795 + 1556760 * 2 ^ 59
def prefixEnd_1556760 : Nat := 4983230072969 + 3 ^ 40 * 1556760 * 2
def baseEnd_1556760 : Nat := 799366143693434403040597

theorem tailTrace_1556760 : CollatzResearch.WordTrace tailWord_1556760 prefixEnd_1556760 799366143693434403040597 := by
  unfold tailWord_1556760
  simp only [CollatzResearch.WordTrace]
  refine ⟨28389850920065934142921867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37853134560087912190562489 28389850920065934142921867)
  ·
    refine ⟨42584776380098901214382801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28389850920065934142921867 42584776380098901214382801)
    ·
      refine ⟨31938582285074175910787101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42584776380098901214382801 31938582285074175910787101)
      ·
        refine ⟨11976968356902815966545163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31938582285074175910787101 11976968356902815966545163)
        ·
          refine ⟨17965452535354223949817745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11976968356902815966545163 17965452535354223949817745)
          ·
            refine ⟨13474089401515667962363309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17965452535354223949817745 13474089401515667962363309)
            ·
              refine ⟨5052783525568375485886241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13474089401515667962363309 5052783525568375485886241)
              ·
                refine ⟨3789587644176281614414681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5052783525568375485886241 3789587644176281614414681)
                ·
                  refine ⟨2842190733132211210811011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3789587644176281614414681 2842190733132211210811011)
                  ·
                    refine ⟨4263286099698316816216517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2842190733132211210811011 4263286099698316816216517)
                    ·
                      refine ⟨799366143693434403040597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4263286099698316816216517 799366143693434403040597)
                      ·
                        rfl

theorem cell23_1556760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_1556760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556760 prefixEnd_1556760 := by exact prefixLift 1556760
  have htrace : WordTrace (prefixWord ++ tailWord_1556760) baseStart_1556760 baseEnd_1556760 := by
    simpa [prefixWord, tailWord_1556760, baseEnd_1556760] using wordTrace_append hprefix tailTrace_1556760
  have hstable : (prefixWord ++ tailWord_1556760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556760).length < 2 ^ (prefixWord ++ tailWord_1556760).sum := by decide
  have hdescent : baseEnd_1556760 < baseStart_1556760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556843 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 5, 6]
def baseStart_1556843 : Nat := 118140960795 + 1556843 * 2 ^ 59
def prefixEnd_1556843 : Nat := 4983230072969 + 3 ^ 40 * 1556843 * 2
def baseEnd_1556843 : Nat := 266469587529252526100905

theorem tailTrace_1556843 : CollatzResearch.WordTrace tailWord_1556843 prefixEnd_1556843 266469587529252526100905 := by
  unfold tailWord_1556843
  simp only [CollatzResearch.WordTrace]
  refine ⟨56782729098831173461115183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37855152732554115640743455 56782729098831173461115183)
  ·
    refine ⟨85174093648246760191672775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56782729098831173461115183 85174093648246760191672775)
    ·
      refine ⟨127761140472370140287509163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85174093648246760191672775 127761140472370140287509163)
      ·
        refine ⟨191641710708555210431263745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127761140472370140287509163 191641710708555210431263745)
        ·
          refine ⟨143731283031416407823447809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191641710708555210431263745 143731283031416407823447809)
          ·
            refine ⟨107798462273562305867585857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143731283031416407823447809 107798462273562305867585857)
            ·
              refine ⟨80848846705171729400689393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107798462273562305867585857 80848846705171729400689393)
              ·
                refine ⟨60636635028878797050517045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80848846705171729400689393 60636635028878797050517045)
                ·
                  refine ⟨5684684533957387223485973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60636635028878797050517045 5684684533957387223485973)
                  ·
                    refine ⟨266469587529252526100905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5684684533957387223485973 266469587529252526100905)
                    ·
                      rfl

theorem cell23_1556843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 6].length) (baseStart_1556843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556843 prefixEnd_1556843 := by exact prefixLift 1556843
  have htrace : WordTrace (prefixWord ++ tailWord_1556843) baseStart_1556843 baseEnd_1556843 := by
    simpa [prefixWord, tailWord_1556843, baseEnd_1556843] using wordTrace_append hprefix tailTrace_1556843
  have hstable : (prefixWord ++ tailWord_1556843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556843).length < 2 ^ (prefixWord ++ tailWord_1556843).sum := by decide
  have hdescent : baseEnd_1556843 < baseStart_1556843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556844 : List Nat := [2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 3]
def baseStart_1556844 : Nat := 118140960795 + 1556844 * 2 ^ 59
def prefixEnd_1556844 : Nat := 4983230072969 + 3 ^ 40 * 1556844 * 2
def baseEnd_1556844 : Nat := 799409276068412074390211

theorem tailTrace_1556844 : CollatzResearch.WordTrace tailWord_1556844 prefixEnd_1556844 799409276068412074390211 := by
  unfold tailWord_1556844
  simp only [CollatzResearch.WordTrace]
  refine ⟨28391382785913775315950793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37855177047885033754601057 28391382785913775315950793)
  ·
    refine ⟨21293537089435331486963095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28391382785913775315950793 21293537089435331486963095)
    ·
      refine ⟨31940305634152997230444643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21293537089435331486963095 31940305634152997230444643)
      ·
        refine ⟨47910458451229495845666965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31940305634152997230444643 47910458451229495845666965)
        ·
          refine ⟨2245802739901382617765639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47910458451229495845666965 2245802739901382617765639)
          ·
            refine ⟨3368704109852073926648459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2245802739901382617765639 3368704109852073926648459)
            ·
              refine ⟨5053056164778110889972689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3368704109852073926648459 5053056164778110889972689)
              ·
                refine ⟨3789792123583583167479517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5053056164778110889972689 3789792123583583167479517)
                ·
                  refine ⟨1421172046343843687804819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3789792123583583167479517 1421172046343843687804819)
                  ·
                    refine ⟨2131758069515765531707229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1421172046343843687804819 2131758069515765531707229)
                    ·
                      refine ⟨799409276068412074390211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2131758069515765531707229 799409276068412074390211)
                      ·
                        rfl

theorem cell23_1556844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 3].length) (baseStart_1556844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556844 prefixEnd_1556844 := by exact prefixLift 1556844
  have htrace : WordTrace (prefixWord ++ tailWord_1556844) baseStart_1556844 baseEnd_1556844 := by
    simpa [prefixWord, tailWord_1556844, baseEnd_1556844] using wordTrace_append hprefix tailTrace_1556844
  have hstable : (prefixWord ++ tailWord_1556844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556844).length < 2 ^ (prefixWord ++ tailWord_1556844).sum := by decide
  have hdescent : baseEnd_1556844 < baseStart_1556844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556861 : List Nat := [1, 4, 1, 1, 2, 4, 2, 3, 1, 1, 3]
def baseStart_1556861 : Nat := 118140960795 + 1556861 * 2 ^ 59
def prefixEnd_1556861 : Nat := 4983230072969 + 3 ^ 40 * 1556861 * 2
def baseEnd_1556861 : Nat := 799418005239538507877633

theorem tailTrace_1556861 : CollatzResearch.WordTrace tailWord_1556861 prefixEnd_1556861 799418005239538507877633 := by
  unfold tailWord_1556861
  simp only [CollatzResearch.WordTrace]
  refine ⟨56783385612765962535270437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37855590408510641690180291 56783385612765962535270437)
  ·
    refine ⟨10646884802393617975363207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56783385612765962535270437 10646884802393617975363207)
    ·
      refine ⟨15970327203590426963044811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10646884802393617975363207 15970327203590426963044811)
      ·
        refine ⟨23955490805385640444567217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15970327203590426963044811 23955490805385640444567217)
        ·
          refine ⟨17966618104039230333425413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23955490805385640444567217 17966618104039230333425413)
          ·
            refine ⟨3368740894507355687517265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17966618104039230333425413 3368740894507355687517265)
            ·
              refine ⟨2526555670880516765637949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3368740894507355687517265 2526555670880516765637949)
              ·
                refine ⟨947458376580193787114231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2526555670880516765637949 947458376580193787114231)
                ·
                  refine ⟨1421187564870290680671347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 947458376580193787114231 1421187564870290680671347)
                  ·
                    refine ⟨2131781347305436021007021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1421187564870290680671347 2131781347305436021007021)
                    ·
                      refine ⟨799418005239538507877633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2131781347305436021007021 799418005239538507877633)
                      ·
                        rfl

theorem cell23_1556861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 1, 1, 3].length) (baseStart_1556861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556861 prefixEnd_1556861 := by exact prefixLift 1556861
  have htrace : WordTrace (prefixWord ++ tailWord_1556861) baseStart_1556861 baseEnd_1556861 := by
    simpa [prefixWord, tailWord_1556861, baseEnd_1556861] using wordTrace_append hprefix tailTrace_1556861
  have hstable : (prefixWord ++ tailWord_1556861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556861).length < 2 ^ (prefixWord ++ tailWord_1556861).sum := by decide
  have hdescent : baseEnd_1556861 < baseStart_1556861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556894 : List Nat := [4, 3, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_1556894 : Nat := 118140960795 + 1556894 * 2 ^ 59
def prefixEnd_1556894 : Nat := 4983230072969 + 3 ^ 40 * 1556894 * 2
def baseEnd_1556894 : Nat := 266478316700378959588327

theorem tailTrace_1556894 : CollatzResearch.WordTrace tailWord_1556894 prefixEnd_1556894 266478316700378959588327 := by
  unfold tailWord_1556894
  simp only [CollatzResearch.WordTrace]
  refine ⟨7098073652705801146402717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37856392814430939447481157 7098073652705801146402717)
  ·
    refine ⟨2661777619764675429901019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7098073652705801146402717 2661777619764675429901019)
    ·
      refine ⟨3992666429647013144851529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2661777619764675429901019 3992666429647013144851529)
      ·
        refine ⟨2994499822235259858638647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3992666429647013144851529 2994499822235259858638647)
        ·
          refine ⟨4491749733352889787957971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2994499822235259858638647 4491749733352889787957971)
          ·
            refine ⟨6737624600029334681936957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4491749733352889787957971 6737624600029334681936957)
            ·
              refine ⟨2526609225011000505726359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6737624600029334681936957 2526609225011000505726359)
              ·
                refine ⟨3789913837516500758589539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2526609225011000505726359 3789913837516500758589539)
                ·
                  refine ⟨5684870756274751137884309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3789913837516500758589539 5684870756274751137884309)
                  ·
                    refine ⟨266478316700378959588327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5684870756274751137884309 266478316700378959588327)
                    ·
                      rfl

theorem cell23_1556894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_1556894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556894 prefixEnd_1556894 := by exact prefixLift 1556894
  have htrace : WordTrace (prefixWord ++ tailWord_1556894) baseStart_1556894 baseEnd_1556894 := by
    simpa [prefixWord, tailWord_1556894, baseEnd_1556894] using wordTrace_append hprefix tailTrace_1556894
  have hstable : (prefixWord ++ tailWord_1556894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556894).length < 2 ^ (prefixWord ++ tailWord_1556894).sum := by decide
  have hdescent : baseEnd_1556894 < baseStart_1556894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556927 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 7, 3, 2]
def baseStart_1556927 : Nat := 118140960795 + 1556927 * 2 ^ 59
def prefixEnd_1556927 : Nat := 4983230072969 + 3 ^ 40 * 1556927 * 2
def baseEnd_1556927 : Nat := 799451894962735249652329

theorem tailTrace_1556927 : CollatzResearch.WordTrace tailWord_1556927 prefixEnd_1556927 799451894962735249652329 := by
  unfold tailWord_1556927
  simp only [CollatzResearch.WordTrace]
  refine ⟨56785792830526855807173035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37857195220351237204782023 56785792830526855807173035)
  ·
    refine ⟨85178689245790283710759553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56785792830526855807173035 85178689245790283710759553)
    ·
      refine ⟨63884016934342712783069665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85178689245790283710759553 63884016934342712783069665)
      ·
        refine ⟨47913012700757034587302249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63884016934342712783069665 47913012700757034587302249)
        ·
          refine ⟨35934759525567775940476687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47913012700757034587302249 35934759525567775940476687)
          ·
            refine ⟨53902139288351663910715031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35934759525567775940476687 53902139288351663910715031)
            ·
              refine ⟨80853208932527495866072547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53902139288351663910715031 80853208932527495866072547)
              ·
                refine ⟨121279813398791243799108821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80853208932527495866072547 121279813398791243799108821)
                ·
                  refine ⟨2842495626534169776541613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 121279813398791243799108821 2842495626534169776541613)
                  ·
                    refine ⟨1065935859950313666203105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2842495626534169776541613 1065935859950313666203105)
                    ·
                      refine ⟨799451894962735249652329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1065935859950313666203105 799451894962735249652329)
                      ·
                        rfl

theorem cell23_1556927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 3, 2].length) (baseStart_1556927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556927 prefixEnd_1556927 := by exact prefixLift 1556927
  have htrace : WordTrace (prefixWord ++ tailWord_1556927) baseStart_1556927 baseEnd_1556927 := by
    simpa [prefixWord, tailWord_1556927, baseEnd_1556927] using wordTrace_append hprefix tailTrace_1556927
  have hstable : (prefixWord ++ tailWord_1556927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556927).length < 2 ^ (prefixWord ++ tailWord_1556927).sum := by decide
  have hdescent : baseEnd_1556927 < baseStart_1556927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556960 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 5]
def baseStart_1556960 : Nat := 118140960795 + 1556960 * 2 ^ 59
def prefixEnd_1556960 : Nat := 4983230072969 + 3 ^ 40 * 1556960 * 2
def baseEnd_1556960 : Nat := 799468839824333620539677

theorem tailTrace_1556960 : CollatzResearch.WordTrace tailWord_1556960 prefixEnd_1556960 799468839824333620539677 := by
  unfold tailWord_1556960
  simp only [CollatzResearch.WordTrace]
  refine ⟨28393498219703651221562167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37857997626271534962082889 28393498219703651221562167)
  ·
    refine ⟨42590247329555476832343251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28393498219703651221562167 42590247329555476832343251)
    ·
      refine ⟨63885370994333215248514877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42590247329555476832343251 63885370994333215248514877)
      ·
        refine ⟨23957014122874955718193079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63885370994333215248514877 23957014122874955718193079)
        ·
          refine ⟨35935521184312433577289619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23957014122874955718193079 35935521184312433577289619)
          ·
            refine ⟨53903281776468650365934429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35935521184312433577289619 53903281776468650365934429)
            ·
              refine ⟨20213730666175743887225411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53903281776468650365934429 20213730666175743887225411)
              ·
                refine ⟨30320595999263615830838117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20213730666175743887225411 30320595999263615830838117)
                ·
                  refine ⟨5685111749861927968282147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30320595999263615830838117 5685111749861927968282147)
                  ·
                    refine ⟨8527667624792891952423221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5685111749861927968282147 8527667624792891952423221)
                    ·
                      refine ⟨799468839824333620539677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8527667624792891952423221 799468839824333620539677)
                      ·
                        rfl

theorem cell23_1556960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_1556960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556960 prefixEnd_1556960 := by exact prefixLift 1556960
  have htrace : WordTrace (prefixWord ++ tailWord_1556960) baseStart_1556960 baseEnd_1556960 := by
    simpa [prefixWord, tailWord_1556960, baseEnd_1556960] using wordTrace_append hprefix tailTrace_1556960
  have hstable : (prefixWord ++ tailWord_1556960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556960).length < 2 ^ (prefixWord ++ tailWord_1556960).sum := by decide
  have hdescent : baseEnd_1556960 < baseStart_1556960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556974 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 3, 4, 2]
def baseStart_1556974 : Nat := 118140960795 + 1556974 * 2 ^ 59
def prefixEnd_1556974 : Nat := 4983230072969 + 3 ^ 40 * 1556974 * 2
def baseEnd_1556974 : Nat := 799476028553496565764613

theorem tailTrace_1556974 : CollatzResearch.WordTrace tailWord_1556974 prefixEnd_1556974 799476028553496565764613 := by
  unfold tailWord_1556974
  simp only [CollatzResearch.WordTrace]
  refine ⟨7098438382669572854266747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37858338040904388556089317 7098438382669572854266747)
  ·
    refine ⟨10647657574004359281400121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7098438382669572854266747 10647657574004359281400121)
    ·
      refine ⟨7985743180503269461050091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10647657574004359281400121 7985743180503269461050091)
      ·
        refine ⟨11978614770754904191575137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7985743180503269461050091 11978614770754904191575137)
        ·
          refine ⟨8983961078066178143681353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11978614770754904191575137 8983961078066178143681353)
          ·
            refine ⟨6737970808549633607761015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8983961078066178143681353 6737970808549633607761015)
            ·
              refine ⟨10106956212824450411641523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6737970808549633607761015 10106956212824450411641523)
              ·
                refine ⟨15160434319236675617462285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10106956212824450411641523 15160434319236675617462285)
                ·
                  refine ⟨5685162869713753356548357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15160434319236675617462285 5685162869713753356548357)
                  ·
                    refine ⟨1065968038071328754352817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5685162869713753356548357 1065968038071328754352817)
                    ·
                      refine ⟨799476028553496565764613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1065968038071328754352817 799476028553496565764613)
                      ·
                        rfl

theorem cell23_1556974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_1556974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556974 prefixEnd_1556974 := by exact prefixLift 1556974
  have htrace : WordTrace (prefixWord ++ tailWord_1556974) baseStart_1556974 baseEnd_1556974 := by
    simpa [prefixWord, tailWord_1556974, baseEnd_1556974] using wordTrace_append hprefix tailTrace_1556974
  have hstable : (prefixWord ++ tailWord_1556974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556974).length < 2 ^ (prefixWord ++ tailWord_1556974).sum := by decide
  have hdescent : baseEnd_1556974 < baseStart_1556974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556991 : List Nat := [1, 1, 2, 2, 1, 2, 6, 2, 2, 2, 2]
def baseStart_1556991 : Nat := 118140960795 + 1556991 * 2 ^ 59
def prefixEnd_1556991 : Nat := 4983230072969 + 3 ^ 40 * 1556991 * 2
def baseEnd_1556991 : Nat := 799484757724622999252035

theorem tailTrace_1556991 : CollatzResearch.WordTrace tailWord_1556991 prefixEnd_1556991 799484757724622999252035 := by
  unfold tailWord_1556991
  simp only [CollatzResearch.WordTrace]
  refine ⟨56788127102294994737502827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37858751401529996491668551 56788127102294994737502827)
  ·
    refine ⟨85182190653442492106254241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56788127102294994737502827 85182190653442492106254241)
    ·
      refine ⟨63886642990081869079690681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85182190653442492106254241 63886642990081869079690681)
      ·
        refine ⟨47914982242561401809768011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63886642990081869079690681 47914982242561401809768011)
        ·
          refine ⟨71872473363842102714652017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47914982242561401809768011 71872473363842102714652017)
          ·
            refine ⟨53904355022881577035989013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71872473363842102714652017 53904355022881577035989013)
            ·
              refine ⟨2526766641697573923561985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53904355022881577035989013 2526766641697573923561985)
              ·
                refine ⟨1895074981273180442671489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2526766641697573923561985 1895074981273180442671489)
                ·
                  refine ⟨1421306235954885332003617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1895074981273180442671489 1421306235954885332003617)
                  ·
                    refine ⟨1065979676966163999002713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1421306235954885332003617 1065979676966163999002713)
                    ·
                      refine ⟨799484757724622999252035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1065979676966163999002713 799484757724622999252035)
                      ·
                        rfl

theorem cell23_1556991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 2, 2].length) (baseStart_1556991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556991 prefixEnd_1556991 := by exact prefixLift 1556991
  have htrace : WordTrace (prefixWord ++ tailWord_1556991) baseStart_1556991 baseEnd_1556991 := by
    simpa [prefixWord, tailWord_1556991, baseEnd_1556991] using wordTrace_append hprefix tailTrace_1556991
  have hstable : (prefixWord ++ tailWord_1556991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556991).length < 2 ^ (prefixWord ++ tailWord_1556991).sum := by decide
  have hdescent : baseEnd_1556991 < baseStart_1556991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557000 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 2, 1, 8]
def baseStart_1557000 : Nat := 118140960795 + 1557000 * 2 ^ 59
def prefixEnd_1557000 : Nat := 4983230072969 + 3 ^ 40 * 1557000 * 2
def baseEnd_1557000 : Nat := 799489379050513464039493

theorem tailTrace_1557000 : CollatzResearch.WordTrace tailWord_1557000 prefixEnd_1557000 799489379050513464039493 := by
  unfold tailWord_1557000
  simp only [CollatzResearch.WordTrace]
  refine ⟨28394227679631194637290227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37858970239508259516386969 28394227679631194637290227)
  ·
    refine ⟨42591341519446791955935341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28394227679631194637290227 42591341519446791955935341)
    ·
      refine ⟨15971753069792546983475753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42591341519446791955935341 15971753069792546983475753)
      ·
        refine ⟨11978814802344410237606815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15971753069792546983475753 11978814802344410237606815)
        ·
          refine ⟨17968222203516615356410223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11978814802344410237606815 17968222203516615356410223)
          ·
            refine ⟨26952333305274923034615335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17968222203516615356410223 26952333305274923034615335)
            ·
              refine ⟨40428499957912384551923003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26952333305274923034615335 40428499957912384551923003)
              ·
                refine ⟨60642749936868576827884505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40428499957912384551923003 60642749936868576827884505)
                ·
                  refine ⟨45482062452651432620913379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60642749936868576827884505 45482062452651432620913379)
                  ·
                    refine ⟨68223093678977148931370069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45482062452651432620913379 68223093678977148931370069)
                    ·
                      refine ⟨799489379050513464039493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 68223093678977148931370069 799489379050513464039493)
                      ·
                        rfl

theorem cell23_1557000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_1557000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557000 prefixEnd_1557000 := by exact prefixLift 1557000
  have htrace : WordTrace (prefixWord ++ tailWord_1557000) baseStart_1557000 baseEnd_1557000 := by
    simpa [prefixWord, tailWord_1557000, baseEnd_1557000] using wordTrace_append hprefix tailTrace_1557000
  have hstable : (prefixWord ++ tailWord_1557000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557000).length < 2 ^ (prefixWord ++ tailWord_1557000).sum := by decide
  have hdescent : baseEnd_1557000 < baseStart_1557000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557027 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 1, 7]
def baseStart_1557027 : Nat := 118140960795 + 1557027 * 2 ^ 59
def prefixEnd_1557027 : Nat := 4983230072969 + 3 ^ 40 * 1557027 * 2
def baseEnd_1557027 : Nat := 266501081009394952800623

theorem tailTrace_1557027 : CollatzResearch.WordTrace tailWord_1557027 prefixEnd_1557027 266501081009394952800623 := by
  unfold tailWord_1557027
  simp only [CollatzResearch.WordTrace]
  refine ⟨56789440130164572885813335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37859626753443048590542223 56789440130164572885813335)
  ·
    refine ⟨85184160195246859328720003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56789440130164572885813335 85184160195246859328720003)
    ·
      refine ⟨127776240292870288993080005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85184160195246859328720003 127776240292870288993080005)
      ·
        refine ⟨23958045054913179186202501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127776240292870288993080005 23958045054913179186202501)
        ·
          refine ⟨4492133447796221097412969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23958045054913179186202501 4492133447796221097412969)
          ·
            refine ⟨3369100085847165823059727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4492133447796221097412969 3369100085847165823059727)
            ·
              refine ⟨5053650128770748734589591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3369100085847165823059727 5053650128770748734589591)
              ·
                refine ⟨7580475193156123101884387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5053650128770748734589591 7580475193156123101884387)
                ·
                  refine ⟨11370712789734184652826581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7580475193156123101884387 11370712789734184652826581)
                  ·
                    refine ⟨266501081009394952800623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11370712789734184652826581 266501081009394952800623)
                    ·
                      rfl

theorem cell23_1557027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 7].length) (baseStart_1557027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557027 prefixEnd_1557027 := by exact prefixLift 1557027
  have htrace : WordTrace (prefixWord ++ tailWord_1557027) baseStart_1557027 baseEnd_1557027 := by
    simpa [prefixWord, tailWord_1557027, baseEnd_1557027] using wordTrace_append hprefix tailTrace_1557027
  have hstable : (prefixWord ++ tailWord_1557027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557027).length < 2 ^ (prefixWord ++ tailWord_1557027).sum := by decide
  have hdescent : baseEnd_1557027 < baseStart_1557027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557047 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 4]
def baseStart_1557047 : Nat := 118140960795 + 1557047 * 2 ^ 59
def prefixEnd_1557047 : Nat := 4983230072969 + 3 ^ 40 * 1557047 * 2
def baseEnd_1557047 : Nat := 799513512641274780151777

theorem tailTrace_1557047 : CollatzResearch.WordTrace tailWord_1557047 prefixEnd_1557047 799513512641274780151777 := by
  unfold tailWord_1557047
  simp only [CollatzResearch.WordTrace]
  refine ⟨56790169590092116301541395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37860113060061410867694263 56790169590092116301541395)
  ·
    refine ⟨85185254385138174452312093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56790169590092116301541395 85185254385138174452312093)
    ·
      refine ⟨31944470394426815419617035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85185254385138174452312093 31944470394426815419617035)
      ·
        refine ⟨47916705591640223129425553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31944470394426815419617035 47916705591640223129425553)
        ·
          refine ⟨35937529193730167347069165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47916705591640223129425553 35937529193730167347069165)
          ·
            refine ⟨13476573447648812755150937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35937529193730167347069165 13476573447648812755150937)
            ·
              refine ⟨10107430085736609566363203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13476573447648812755150937 10107430085736609566363203)
              ·
                refine ⟨15161145128604914349544805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10107430085736609566363203 15161145128604914349544805)
                ·
                  refine ⟨2842714711613421440539651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15161145128604914349544805 2842714711613421440539651)
                  ·
                    refine ⟨4264072067420132160809477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2842714711613421440539651 4264072067420132160809477)
                    ·
                      refine ⟨799513512641274780151777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4264072067420132160809477 799513512641274780151777)
                      ·
                        rfl

theorem cell23_1557047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_1557047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557047 prefixEnd_1557047 := by exact prefixLift 1557047
  have htrace : WordTrace (prefixWord ++ tailWord_1557047) baseStart_1557047 baseEnd_1557047 := by
    simpa [prefixWord, tailWord_1557047, baseEnd_1557047] using wordTrace_append hprefix tailTrace_1557047
  have hstable : (prefixWord ++ tailWord_1557047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557047).length < 2 ^ (prefixWord ++ tailWord_1557047).sum := by decide
  have hdescent : baseEnd_1557047 < baseStart_1557047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557067 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 3]
def baseStart_1557067 : Nat := 118140960795 + 1557067 * 2 ^ 59
def prefixEnd_1557067 : Nat := 4983230072969 + 3 ^ 40 * 1557067 * 2
def baseEnd_1557067 : Nat := 799523782254364701901685

theorem tailTrace_1557067 : CollatzResearch.WordTrace tailWord_1557067 prefixEnd_1557067 799523782254364701901685 := by
  unfold tailWord_1557067
  simp only [CollatzResearch.WordTrace]
  refine ⟨56790899050019659717269455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37860599366679773144846303 56790899050019659717269455)
  ·
    refine ⟨85186348575029489575904183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56790899050019659717269455 85186348575029489575904183)
    ·
      refine ⟨127779522862544234363856275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85186348575029489575904183 127779522862544234363856275)
      ·
        refine ⟨191669284293816351545784413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127779522862544234363856275 191669284293816351545784413)
        ·
          refine ⟨71875981610181131829669155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191669284293816351545784413 71875981610181131829669155)
          ·
            refine ⟨107813972415271697744503733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71875981610181131829669155 107813972415271697744503733)
            ·
              refine ⟨10107559913931721663547225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107813972415271697744503733 10107559913931721663547225)
              ·
                refine ⟨7580669935448791247660419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10107559913931721663547225 7580669935448791247660419)
                ·
                  refine ⟨11371004903173186871490629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7580669935448791247660419 11371004903173186871490629)
                  ·
                    refine ⟨2132063419344972538404493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11371004903173186871490629 2132063419344972538404493)
                    ·
                      refine ⟨799523782254364701901685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2132063419344972538404493 799523782254364701901685)
                      ·
                        rfl

theorem cell23_1557067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 3].length) (baseStart_1557067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557067 prefixEnd_1557067 := by exact prefixLift 1557067
  have htrace : WordTrace (prefixWord ++ tailWord_1557067) baseStart_1557067 baseEnd_1557067 := by
    simpa [prefixWord, tailWord_1557067, baseEnd_1557067] using wordTrace_append hprefix tailTrace_1557067
  have hstable : (prefixWord ++ tailWord_1557067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557067).length < 2 ^ (prefixWord ++ tailWord_1557067).sum := by decide
  have hdescent : baseEnd_1557067 < baseStart_1557067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557074 : List Nat := [3, 2, 2, 1, 2, 1, 1, 4, 3, 4]
def baseStart_1557074 : Nat := 118140960795 + 1557074 * 2 ^ 59
def prefixEnd_1557074 : Nat := 4983230072969 + 3 ^ 40 * 1557074 * 2
def baseEnd_1557074 : Nat := 266509125539648724838051

theorem tailTrace_1557074 : CollatzResearch.WordTrace tailWord_1557074 prefixEnd_1557074 266509125539648724838051 := by
  unfold tailWord_1557074
  simp only [CollatzResearch.WordTrace]
  refine ⟨14197788590248574978193569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37860769573996199941849517 14197788590248574978193569)
  ·
    refine ⟨10648341442686431233645177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14197788590248574978193569 10648341442686431233645177)
    ·
      refine ⟨7986256082014823425233883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10648341442686431233645177 7986256082014823425233883)
      ·
        refine ⟨11979384123022235137850825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7986256082014823425233883 11979384123022235137850825)
        ·
          refine ⟨8984538092266676353388119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11979384123022235137850825 8984538092266676353388119)
          ·
            refine ⟨13476807138400014530082179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8984538092266676353388119 13476807138400014530082179)
            ·
              refine ⟨20215210707600021795123269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13476807138400014530082179 20215210707600021795123269)
              ·
                refine ⟨3790352007675004086585613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20215210707600021795123269 3790352007675004086585613)
                ·
                  refine ⟨1421382002878126532469605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3790352007675004086585613 1421382002878126532469605)
                  ·
                    refine ⟨266509125539648724838051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1421382002878126532469605 266509125539648724838051)
                    ·
                      rfl

theorem cell23_1557074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_1557074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557074 prefixEnd_1557074 := by exact prefixLift 1557074
  have htrace : WordTrace (prefixWord ++ tailWord_1557074) baseStart_1557074 baseEnd_1557074 := by
    simpa [prefixWord, tailWord_1557074, baseEnd_1557074] using wordTrace_append hprefix tailTrace_1557074
  have hstable : (prefixWord ++ tailWord_1557074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557074).length < 2 ^ (prefixWord ++ tailWord_1557074).sum := by decide
  have hdescent : baseEnd_1557074 < baseStart_1557074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557101 : List Nat := [1, 5, 1, 1, 3, 2, 1, 2, 2, 2, 3]
def baseStart_1557101 : Nat := 118140960795 + 1557101 * 2 ^ 59
def prefixEnd_1557101 : Nat := 4983230072969 + 3 ^ 40 * 1557101 * 2
def baseEnd_1557101 : Nat := 799541240596617568876529

theorem tailTrace_1557101 : CollatzResearch.WordTrace tailWord_1557101 prefixEnd_1557101 799541240596617568876529 := by
  unfold tailWord_1557101
  simp only [CollatzResearch.WordTrace]
  refine ⟨56792139131896483524007157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37861426087930989016004771 56792139131896483524007157)
  ·
    refine ⟨5324263043615295330375671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56792139131896483524007157 5324263043615295330375671)
    ·
      refine ⟨7986394565422942995563507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5324263043615295330375671 7986394565422942995563507)
      ·
        refine ⟨11979591848134414493345261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7986394565422942995563507 11979591848134414493345261)
        ·
          refine ⟨4492346943050405435004473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11979591848134414493345261 4492346943050405435004473)
          ·
            refine ⟨3369260207287804076253355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4492346943050405435004473 3369260207287804076253355)
            ·
              refine ⟨5053890310931706114380033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3369260207287804076253355 5053890310931706114380033)
              ·
                refine ⟨3790417733198779585785025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5053890310931706114380033 3790417733198779585785025)
                ·
                  refine ⟨2842813299899084689338769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3790417733198779585785025 2842813299899084689338769)
                  ·
                    refine ⟨2132109974924313517004077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2842813299899084689338769 2132109974924313517004077)
                    ·
                      refine ⟨799541240596617568876529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2132109974924313517004077 799541240596617568876529)
                      ·
                        rfl

theorem cell23_1557101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_1557101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557101 prefixEnd_1557101 := by exact prefixLift 1557101
  have htrace : WordTrace (prefixWord ++ tailWord_1557101) baseStart_1557101 baseEnd_1557101 := by
    simpa [prefixWord, tailWord_1557101, baseEnd_1557101] using wordTrace_append hprefix tailTrace_1557101
  have hstable : (prefixWord ++ tailWord_1557101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557101).length < 2 ^ (prefixWord ++ tailWord_1557101).sum := by decide
  have hdescent : baseEnd_1557101 < baseStart_1557101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557134 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 3, 5]
def baseStart_1557134 : Nat := 118140960795 + 1557134 * 2 ^ 59
def prefixEnd_1557134 : Nat := 4983230072969 + 3 ^ 40 * 1557134 * 2
def baseEnd_1557134 : Nat := 266519395152738646587959

theorem tailTrace_1557134 : CollatzResearch.WordTrace tailWord_1557134 prefixEnd_1557134 266519395152738646587959 := by
  unfold tailWord_1557134
  simp only [CollatzResearch.WordTrace]
  refine ⟨7099167842597116269994807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37862228493851286773305637 7099167842597116269994807)
  ·
    refine ⟨10648751763895674404992211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7099167842597116269994807 10648751763895674404992211)
    ·
      refine ⟨15973127645843511607488317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10648751763895674404992211 15973127645843511607488317)
      ·
        refine ⟨5989922867191316852808119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15973127645843511607488317 5989922867191316852808119)
        ·
          refine ⟨8984884300786975279212179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5989922867191316852808119 8984884300786975279212179)
          ·
            refine ⟨13477326451180462918818269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8984884300786975279212179 13477326451180462918818269)
            ·
              refine ⟨5053997419192673594556851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13477326451180462918818269 5053997419192673594556851)
              ·
                refine ⟨7580996128789010391835277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5053997419192673594556851 7580996128789010391835277)
                ·
                  refine ⟨2842873548295878896938229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7580996128789010391835277 2842873548295878896938229)
                  ·
                    refine ⟨266519395152738646587959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2842873548295878896938229 266519395152738646587959)
                    ·
                      rfl

theorem cell23_1557134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_1557134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557134 prefixEnd_1557134 := by exact prefixLift 1557134
  have htrace : WordTrace (prefixWord ++ tailWord_1557134) baseStart_1557134 baseEnd_1557134 := by
    simpa [prefixWord, tailWord_1557134, baseEnd_1557134] using wordTrace_append hprefix tailTrace_1557134
  have hstable : (prefixWord ++ tailWord_1557134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557134).length < 2 ^ (prefixWord ++ tailWord_1557134).sum := by decide
  have hdescent : baseEnd_1557134 < baseStart_1557134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557159 : List Nat := [1, 1, 6, 3, 2, 1, 2, 2, 1, 4]
def baseStart_1557159 : Nat := 118140960795 + 1557159 * 2 ^ 59
def prefixEnd_1557159 : Nat := 4983230072969 + 3 ^ 40 * 1557159 * 2
def baseEnd_1557159 : Nat := 266523674158192780650421

theorem tailTrace_1557159 : CollatzResearch.WordTrace tailWord_1557159 prefixEnd_1557159 266523674158192780650421 := by
  unfold tailWord_1557159
  simp only [CollatzResearch.WordTrace]
  refine ⟨56794254565686359429618531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37862836377124239619745687 56794254565686359429618531)
  ·
    refine ⟨85191381848529539144427797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56794254565686359429618531 85191381848529539144427797)
    ·
      refine ⟨3993346024149822147395053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 85191381848529539144427797 3993346024149822147395053)
      ·
        refine ⟨1497504759056183305273145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3993346024149822147395053 1497504759056183305273145)
        ·
          refine ⟨1123128569292137478954859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1497504759056183305273145 1123128569292137478954859)
          ·
            refine ⟨1684692853938206218432289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123128569292137478954859 1684692853938206218432289)
            ·
              refine ⟨1263519640453654663824217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1684692853938206218432289 1263519640453654663824217)
              ·
                refine ⟨947639730340240997868163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1263519640453654663824217 947639730340240997868163)
                ·
                  refine ⟨1421459595510361496802245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 947639730340240997868163 1421459595510361496802245)
                  ·
                    refine ⟨266523674158192780650421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1421459595510361496802245 266523674158192780650421)
                    ·
                      rfl

theorem cell23_1557159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_1557159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557159 prefixEnd_1557159 := by exact prefixLift 1557159
  have htrace : WordTrace (prefixWord ++ tailWord_1557159) baseStart_1557159 baseEnd_1557159 := by
    simpa [prefixWord, tailWord_1557159, baseEnd_1557159] using wordTrace_append hprefix tailTrace_1557159
  have hstable : (prefixWord ++ tailWord_1557159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557159).length < 2 ^ (prefixWord ++ tailWord_1557159).sum := by decide
  have hdescent : baseEnd_1557159 < baseStart_1557159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557165 : List Nat := [1, 5, 2, 1, 1, 3, 1, 4, 1, 1, 3]
def baseStart_1557165 : Nat := 118140960795 + 1557165 * 2 ^ 59
def prefixEnd_1557165 : Nat := 4983230072969 + 3 ^ 40 * 1557165 * 2
def baseEnd_1557165 : Nat := 799574103358505318476235

theorem tailTrace_1557165 : CollatzResearch.WordTrace tailWord_1557165 prefixEnd_1557165 799574103358505318476235 := by
  unfold tailWord_1557165
  simp only [CollatzResearch.WordTrace]
  refine ⟨56794473403664622454336949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37862982269109748302891299 56794473403664622454336949)
  ·
    refine ⟨5324481881593558355094089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56794473403664622454336949 5324481881593558355094089)
    ·
      refine ⟨3993361411195168766320567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5324481881593558355094089 3993361411195168766320567)
      ·
        refine ⟨5990042116792753149480851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3993361411195168766320567 5990042116792753149480851)
        ·
          refine ⟨8985063175189129724221277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5990042116792753149480851 8985063175189129724221277)
          ·
            refine ⟨3369398690695923646582979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8985063175189129724221277 3369398690695923646582979)
            ·
              refine ⟨5054098036043885469874469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3369398690695923646582979 5054098036043885469874469)
              ·
                refine ⟨947643381758228525601463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5054098036043885469874469 947643381758228525601463)
                ·
                  refine ⟨1421465072637342788402195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 947643381758228525601463 1421465072637342788402195)
                  ·
                    refine ⟨2132197608956014182603293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1421465072637342788402195 2132197608956014182603293)
                    ·
                      refine ⟨799574103358505318476235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2132197608956014182603293 799574103358505318476235)
                      ·
                        rfl

theorem cell23_1557165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_1557165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557165 prefixEnd_1557165 := by exact prefixLift 1557165
  have htrace : WordTrace (prefixWord ++ tailWord_1557165) baseStart_1557165 baseEnd_1557165 := by
    simpa [prefixWord, tailWord_1557165, baseEnd_1557165] using wordTrace_append hprefix tailTrace_1557165
  have hstable : (prefixWord ++ tailWord_1557165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557165).length < 2 ^ (prefixWord ++ tailWord_1557165).sum := by decide
  have hdescent : baseEnd_1557165 < baseStart_1557165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557181 : List Nat := [1, 4, 1, 2, 1, 3, 2, 3, 2, 4]
def baseStart_1557181 : Nat := 118140960795 + 1557181 * 2 ^ 59
def prefixEnd_1557181 : Nat := 4983230072969 + 3 ^ 40 * 1557181 * 2
def baseEnd_1557181 : Nat := 266527439682992418625387

theorem tailTrace_1557181 : CollatzResearch.WordTrace tailWord_1557181 prefixEnd_1557181 266527439682992418625387 := by
  unfold tailWord_1557181
  simp only [CollatzResearch.WordTrace]
  refine ⟨56795056971606657186919397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37863371314404438124612931 56795056971606657186919397)
  ·
    refine ⟨10649073182176248222547387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56795056971606657186919397 10649073182176248222547387)
    ·
      refine ⟨15973609773264372333821081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10649073182176248222547387 15973609773264372333821081)
      ·
        refine ⟨11980207329948279250365811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15973609773264372333821081 11980207329948279250365811)
        ·
          refine ⟨17970310994922418875548717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11980207329948279250365811 17970310994922418875548717)
          ·
            refine ⟨6738866623095907078330769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17970310994922418875548717 6738866623095907078330769)
            ·
              refine ⟨5054149967321930308748077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6738866623095907078330769 5054149967321930308748077)
              ·
                refine ⟨1895306237745723865780529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5054149967321930308748077 1895306237745723865780529)
                ·
                  refine ⟨1421479678309292899335397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1895306237745723865780529 1421479678309292899335397)
                  ·
                    refine ⟨266527439682992418625387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1421479678309292899335397 266527439682992418625387)
                    ·
                      rfl

theorem cell23_1557181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_1557181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557181 prefixEnd_1557181 := by exact prefixLift 1557181
  have htrace : WordTrace (prefixWord ++ tailWord_1557181) baseStart_1557181 baseEnd_1557181 := by
    simpa [prefixWord, tailWord_1557181, baseEnd_1557181] using wordTrace_append hprefix tailTrace_1557181
  have hstable : (prefixWord ++ tailWord_1557181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557181).length < 2 ^ (prefixWord ++ tailWord_1557181).sum := by decide
  have hdescent : baseEnd_1557181 < baseStart_1557181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557184 : List Nat := [2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 4]
def baseStart_1557184 : Nat := 118140960795 + 1557184 * 2 ^ 59
def prefixEnd_1557184 : Nat := 4983230072969 + 3 ^ 40 * 1557184 * 2
def baseEnd_1557184 : Nat := 799583859490940744138647

theorem tailTrace_1557184 : CollatzResearch.WordTrace tailWord_1557184 prefixEnd_1557184 799583859490940744138647 := by
  unfold tailWord_1557184
  simp only [CollatzResearch.WordTrace]
  refine ⟨28397583195297894349639303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37863444260397192466185737 28397583195297894349639303)
  ·
    refine ⟨42596374792946841524458955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28397583195297894349639303 42596374792946841524458955)
    ·
      refine ⟨63894562189420262286688433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42596374792946841524458955 63894562189420262286688433)
      ·
        refine ⟨47920921642065196715016325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63894562189420262286688433 47920921642065196715016325)
        ·
          refine ⟨8985172807887224384065561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47920921642065196715016325 8985172807887224384065561)
          ·
            refine ⟨6738879605915418288049171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8985172807887224384065561 6738879605915418288049171)
            ·
              refine ⟨10108319408873127432073757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6738879605915418288049171 10108319408873127432073757)
              ·
                refine ⟨3790619778327422787027659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10108319408873127432073757 3790619778327422787027659)
                ·
                  refine ⟨5685929667491134180541489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3790619778327422787027659 5685929667491134180541489)
                  ·
                    refine ⟨4264447250618350635406117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5685929667491134180541489 4264447250618350635406117)
                    ·
                      refine ⟨799583859490940744138647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4264447250618350635406117 799583859490940744138647)
                      ·
                        rfl

theorem cell23_1557184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_1557184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557184 prefixEnd_1557184 := by exact prefixLift 1557184
  have htrace : WordTrace (prefixWord ++ tailWord_1557184) baseStart_1557184 baseEnd_1557184 := by
    simpa [prefixWord, tailWord_1557184, baseEnd_1557184] using wordTrace_append hprefix tailTrace_1557184
  have hstable : (prefixWord ++ tailWord_1557184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557184).length < 2 ^ (prefixWord ++ tailWord_1557184).sum := by decide
  have hdescent : baseEnd_1557184 < baseStart_1557184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557188 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 5, 2, 2]
def baseStart_1557188 : Nat := 118140960795 + 1557188 * 2 ^ 59
def prefixEnd_1557188 : Nat := 4983230072969 + 3 ^ 40 * 1557188 * 2
def baseEnd_1557188 : Nat := 799585913413558728488629

theorem tailTrace_1557188 : CollatzResearch.WordTrace tailWord_1557188 prefixEnd_1557188 799585913413558728488629 := by
  unfold tailWord_1557188
  simp only [CollatzResearch.WordTrace]
  refine ⟨28397656141290648691212109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37863541521720864921616145 28397656141290648691212109)
  ·
    refine ⟨10649121052983993259204541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28397656141290648691212109 10649121052983993259204541)
    ·
      refine ⟨3993420394868997472201703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10649121052983993259204541 3993420394868997472201703)
      ·
        refine ⟨5990130592303496208302555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3993420394868997472201703 5990130592303496208302555)
        ·
          refine ⟨8985195888455244312453833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5990130592303496208302555 8985195888455244312453833)
          ·
            refine ⟨6738896916341433234340375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8985195888455244312453833 6738896916341433234340375)
            ·
              refine ⟨10108345374512149851510563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6738896916341433234340375 10108345374512149851510563)
              ·
                refine ⟨15162518061768224777265845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10108345374512149851510563 15162518061768224777265845)
                ·
                  refine ⟨1421486068290771072868673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15162518061768224777265845 1421486068290771072868673)
                  ·
                    refine ⟨1066114551218078304651505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1421486068290771072868673 1066114551218078304651505)
                    ·
                      refine ⟨799585913413558728488629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1066114551218078304651505 799585913413558728488629)
                      ·
                        rfl

theorem cell23_1557188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_1557188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557188 prefixEnd_1557188 := by exact prefixLift 1557188
  have htrace : WordTrace (prefixWord ++ tailWord_1557188) baseStart_1557188 baseEnd_1557188 := by
    simpa [prefixWord, tailWord_1557188, baseEnd_1557188] using wordTrace_append hprefix tailTrace_1557188
  have hstable : (prefixWord ++ tailWord_1557188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557188).length < 2 ^ (prefixWord ++ tailWord_1557188).sum := by decide
  have hdescent : baseEnd_1557188 < baseStart_1557188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557208 : List Nat := [2, 1, 2, 2, 3, 2, 4, 1, 1, 2, 3]
def baseStart_1557208 : Nat := 118140960795 + 1557208 * 2 ^ 59
def prefixEnd_1557208 : Nat := 4983230072969 + 3 ^ 40 * 1557208 * 2
def baseEnd_1557208 : Nat := 799596183026648650238537

theorem tailTrace_1557208 : CollatzResearch.WordTrace tailWord_1557208 prefixEnd_1557208 799596183026648650238537 := by
  unfold tailWord_1557208
  simp only [CollatzResearch.WordTrace]
  refine ⟨28398020871254420399076139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37864027828339227198768185 28398020871254420399076139)
  ·
    refine ⟨42597031306881630598614209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28398020871254420399076139 42597031306881630598614209)
    ·
      refine ⟨31947773480161222948960657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42597031306881630598614209 31947773480161222948960657)
      ·
        refine ⟨23960830110120917211720493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31947773480161222948960657 23960830110120917211720493)
        ·
          refine ⟨8985311291295343954395185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23960830110120917211720493 8985311291295343954395185)
          ·
            refine ⟨6738983468471507965796389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8985311291295343954395185 6738983468471507965796389)
            ·
              refine ⟨1263559400338407743586823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6738983468471507965796389 1263559400338407743586823)
              ·
                refine ⟨1895339100507611615380235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1263559400338407743586823 1895339100507611615380235)
                ·
                  refine ⟨2843008650761417423070353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1895339100507611615380235 2843008650761417423070353)
                  ·
                    refine ⟨2132256488071063067302765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2843008650761417423070353 2132256488071063067302765)
                    ·
                      refine ⟨799596183026648650238537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2132256488071063067302765 799596183026648650238537)
                      ·
                        rfl

theorem cell23_1557208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 1, 2, 3].length) (baseStart_1557208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557208 prefixEnd_1557208 := by exact prefixLift 1557208
  have htrace : WordTrace (prefixWord ++ tailWord_1557208) baseStart_1557208 baseEnd_1557208 := by
    simpa [prefixWord, tailWord_1557208, baseEnd_1557208] using wordTrace_append hprefix tailTrace_1557208
  have hstable : (prefixWord ++ tailWord_1557208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557208).length < 2 ^ (prefixWord ++ tailWord_1557208).sum := by decide
  have hdescent : baseEnd_1557208 < baseStart_1557208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557335 : List Nat := [1, 1, 3, 2, 4, 3, 2, 2, 5]
def baseStart_1557335 : Nat := 118140960795 + 1557335 * 2 ^ 59
def prefixEnd_1557335 : Nat := 4983230072969 + 3 ^ 40 * 1557335 * 2
def baseEnd_1557335 : Nat := 88851266118863294816717

theorem tailTrace_1557335 : CollatzResearch.WordTrace tailWord_1557335 prefixEnd_1557335 88851266118863294816717 := by
  unfold tailWord_1557335
  simp only [CollatzResearch.WordTrace]
  refine ⟨56800673813048741488025459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37867115875365827658683639 56800673813048741488025459)
  ·
    refine ⟨85201010719573112232038189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56800673813048741488025459 85201010719573112232038189)
    ·
      refine ⟨31950379019839917087014321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85201010719573112232038189 31950379019839917087014321)
      ·
        refine ⟨23962784264879937815260741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31950379019839917087014321 23962784264879937815260741)
        ·
          refine ⟨4493022049664988340361389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23962784264879937815260741 4493022049664988340361389)
          ·
            refine ⟨1684883268624370627635521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4493022049664988340361389 1684883268624370627635521)
            ·
              refine ⟨1263662451468277970726641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1684883268624370627635521 1263662451468277970726641)
              ·
                refine ⟨947746838601208478044981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1263662451468277970726641 947746838601208478044981)
                ·
                  refine ⟨88851266118863294816717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 947746838601208478044981 88851266118863294816717)
                  ·
                    rfl

theorem cell23_1557335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 5].length) (baseStart_1557335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557335 prefixEnd_1557335 := by exact prefixLift 1557335
  have htrace : WordTrace (prefixWord ++ tailWord_1557335) baseStart_1557335 baseEnd_1557335 := by
    simpa [prefixWord, tailWord_1557335, baseEnd_1557335] using wordTrace_append hprefix tailTrace_1557335
  have hstable : (prefixWord ++ tailWord_1557335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557335).length < 2 ^ (prefixWord ++ tailWord_1557335).sum := by decide
  have hdescent : baseEnd_1557335 < baseStart_1557335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557361 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 5, 4]
def baseStart_1557361 : Nat := 118140960795 + 1557361 * 2 ^ 59
def prefixEnd_1557361 : Nat := 4983230072969 + 3 ^ 40 * 1557361 * 2
def baseEnd_1557361 : Nat := 266558248522262183875111

theorem tailTrace_1557361 : CollatzResearch.WordTrace tailWord_1557361 prefixEnd_1557361 266558248522262183875111 := by
  unfold tailWord_1557361
  simp only [CollatzResearch.WordTrace]
  refine ⟨56801622110954547928471937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37867748073969698618981291 56801622110954547928471937)
  ·
    refine ⟨42601216583215910946353953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56801622110954547928471937 42601216583215910946353953)
    ·
      refine ⟨31950912437411933209765465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42601216583215910946353953 31950912437411933209765465)
      ·
        refine ⟨23963184328058949907324099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31950912437411933209765465 23963184328058949907324099)
        ·
          refine ⟨35944776492088424860986149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23963184328058949907324099 35944776492088424860986149)
          ·
            refine ⟨6739645592266579661434903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35944776492088424860986149 6739645592266579661434903)
            ·
              refine ⟨10109468388399869492152355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6739645592266579661434903 10109468388399869492152355)
              ·
                refine ⟨15164202582599804238228533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10109468388399869492152355 15164202582599804238228533)
                ·
                  refine ⟨1421643992118731647333925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15164202582599804238228533 1421643992118731647333925)
                  ·
                    refine ⟨266558248522262183875111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1421643992118731647333925 266558248522262183875111)
                    ·
                      rfl

theorem cell23_1557361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 4].length) (baseStart_1557361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557361 prefixEnd_1557361 := by exact prefixLift 1557361
  have htrace : WordTrace (prefixWord ++ tailWord_1557361) baseStart_1557361 baseEnd_1557361 := by
    simpa [prefixWord, tailWord_1557361, baseEnd_1557361] using wordTrace_append hprefix tailTrace_1557361
  have hstable : (prefixWord ++ tailWord_1557361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557361).length < 2 ^ (prefixWord ++ tailWord_1557361).sum := by decide
  have hdescent : baseEnd_1557361 < baseStart_1557361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557438 : List Nat := [4, 2, 1, 1, 1, 2, 1, 5, 1, 5]
def baseStart_1557438 : Nat := 118140960795 + 1557438 * 2 ^ 59
def prefixEnd_1557438 : Nat := 4983230072969 + 3 ^ 40 * 1557438 * 2
def baseEnd_1557438 : Nat := 266571427859060916787493

theorem tailTrace_1557438 : CollatzResearch.WordTrace tailWord_1557438 prefixEnd_1557438 266571427859060916787493 := by
  unfold tailWord_1557438
  simp only [CollatzResearch.WordTrace]
  refine ⟨7100553816459448759878121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37869620354450393386016645 7100553816459448759878121)
  ·
    refine ⟨5325415362344586569908591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7100553816459448759878121 5325415362344586569908591)
    ·
      refine ⟨7988123043516879854862887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5325415362344586569908591 7988123043516879854862887)
      ·
        refine ⟨11982184565275319782294331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7988123043516879854862887 11982184565275319782294331)
        ·
          refine ⟨17973276847912979673441497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11982184565275319782294331 17973276847912979673441497)
          ·
            refine ⟨13479957635934734755081123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17973276847912979673441497 13479957635934734755081123)
            ·
              refine ⟨20219936453902102132621685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13479957635934734755081123 20219936453902102132621685)
              ·
                refine ⟨1895619042553322074933283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20219936453902102132621685 1895619042553322074933283)
                ·
                  refine ⟨2843428563829983112399925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1895619042553322074933283 2843428563829983112399925)
                  ·
                    refine ⟨266571427859060916787493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2843428563829983112399925 266571427859060916787493)
                    ·
                      rfl

theorem cell23_1557438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_1557438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557438 prefixEnd_1557438 := by exact prefixLift 1557438
  have htrace : WordTrace (prefixWord ++ tailWord_1557438) baseStart_1557438 baseEnd_1557438 := by
    simpa [prefixWord, tailWord_1557438, baseEnd_1557438] using wordTrace_append hprefix tailTrace_1557438
  have hstable : (prefixWord ++ tailWord_1557438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557438).length < 2 ^ (prefixWord ++ tailWord_1557438).sum := by decide
  have hdescent : baseEnd_1557438 < baseStart_1557438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557475 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 5, 2, 2]
def baseStart_1557475 : Nat := 118140960795 + 1557475 * 2 ^ 59
def prefixEnd_1557475 : Nat := 4983230072969 + 3 ^ 40 * 1557475 * 2
def baseEnd_1557475 : Nat := 799733282361399105599809

theorem tailTrace_1557475 : CollatzResearch.WordTrace tailWord_1557475 prefixEnd_1557475 799733282361399105599809 := by
  unfold tailWord_1557475
  simp only [CollatzResearch.WordTrace]
  refine ⟨56805780032541545398121879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37870520021694363598747919 56805780032541545398121879)
  ·
    refine ⟨85208670048812318097182819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56805780032541545398121879 85208670048812318097182819)
    ·
      refine ⟨127813005073218477145774229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85208670048812318097182819 127813005073218477145774229)
      ·
        refine ⟨5991234612807116116208167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 127813005073218477145774229 5991234612807116116208167)
        ·
          refine ⟨8986851919210674174312251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5991234612807116116208167 8986851919210674174312251)
          ·
            refine ⟨13480277878816011261468377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8986851919210674174312251 13480277878816011261468377)
            ·
              refine ⟨10110208409112008446101283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13480277878816011261468377 10110208409112008446101283)
              ·
                refine ⟨15165312613668012669151925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10110208409112008446101283 15165312613668012669151925)
                ·
                  refine ⟨1421748057531376187732993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15165312613668012669151925 1421748057531376187732993)
                  ·
                    refine ⟨1066311043148532140799745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1421748057531376187732993 1066311043148532140799745)
                    ·
                      refine ⟨799733282361399105599809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1066311043148532140799745 799733282361399105599809)
                      ·
                        rfl

theorem cell23_1557475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_1557475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557475 prefixEnd_1557475 := by exact prefixLift 1557475
  have htrace : WordTrace (prefixWord ++ tailWord_1557475) baseStart_1557475 baseEnd_1557475 := by
    simpa [prefixWord, tailWord_1557475, baseEnd_1557475] using wordTrace_append hprefix tailTrace_1557475
  have hstable : (prefixWord ++ tailWord_1557475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557475).length < 2 ^ (prefixWord ++ tailWord_1557475).sum := by decide
  have hdescent : baseEnd_1557475 < baseStart_1557475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557511 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 1, 9]
def baseStart_1557511 : Nat := 118140960795 + 1557511 * 2 ^ 59
def prefixEnd_1557511 : Nat := 4983230072969 + 3 ^ 40 * 1557511 * 2
def baseEnd_1557511 : Nat := 266583922554986988249881

theorem tailTrace_1557511 : CollatzResearch.WordTrace tailWord_1557511 prefixEnd_1557511 266583922554986988249881 := by
  unfold tailWord_1557511
  simp only [CollatzResearch.WordTrace]
  refine ⟨56807093060411123546432387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37871395373607415697621591 56807093060411123546432387)
  ·
    refine ⟨85210639590616685319648581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56807093060411123546432387 85210639590616685319648581)
    ·
      refine ⟨15976994923240628497434109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85210639590616685319648581 15976994923240628497434109)
      ·
        refine ⟨5991373096215235686537791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15976994923240628497434109 5991373096215235686537791)
        ·
          refine ⟨8987059644322853529806687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5991373096215235686537791 8987059644322853529806687)
          ·
            refine ⟨13480589466484280294710031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8987059644322853529806687 13480589466484280294710031)
            ·
              refine ⟨20220884199726420442065047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13480589466484280294710031 20220884199726420442065047)
              ·
                refine ⟨30331326299589630663097571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20220884199726420442065047 30331326299589630663097571)
                ·
                  refine ⟨45496989449384445994646357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30331326299589630663097571 45496989449384445994646357)
                  ·
                    refine ⟨266583922554986988249881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 45496989449384445994646357 266583922554986988249881)
                    ·
                      rfl

theorem cell23_1557511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_1557511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557511 prefixEnd_1557511 := by exact prefixLift 1557511
  have htrace : WordTrace (prefixWord ++ tailWord_1557511) baseStart_1557511 baseEnd_1557511 := by
    simpa [prefixWord, tailWord_1557511, baseEnd_1557511] using wordTrace_append hprefix tailTrace_1557511
  have hstable : (prefixWord ++ tailWord_1557511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557511).length < 2 ^ (prefixWord ++ tailWord_1557511).sum := by decide
  have hdescent : baseEnd_1557511 < baseStart_1557511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557525 : List Nat := [1, 3, 2, 1, 4, 2, 2, 1, 1, 3, 3]
def baseStart_1557525 : Nat := 118140960795 + 1557525 * 2 ^ 59
def prefixEnd_1557525 : Nat := 4983230072969 + 3 ^ 40 * 1557525 * 2
def baseEnd_1557525 : Nat := 799758956394123909974579

theorem tailTrace_1557525 : CollatzResearch.WordTrace tailWord_1557525 prefixEnd_1557525 799758956394123909974579 := by
  unfold tailWord_1557525
  simp only [CollatzResearch.WordTrace]
  refine ⟨56807603682360403937442029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37871735788240269291628019 56807603682360403937442029)
  ·
    refine ⟨21302851380885151476540761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56807603682360403937442029 21302851380885151476540761)
    ·
      refine ⟨15977138535663863607405571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21302851380885151476540761 15977138535663863607405571)
      ·
        refine ⟨23965707803495795411108357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15977138535663863607405571 23965707803495795411108357)
        ·
          refine ⟨4493570213155461639582817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23965707803495795411108357 4493570213155461639582817)
          ·
            refine ⟨3370177659866596229687113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4493570213155461639582817 3370177659866596229687113)
            ·
              refine ⟨2527633244899947172265335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3370177659866596229687113 2527633244899947172265335)
              ·
                refine ⟨3791449867349920758398003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2527633244899947172265335 3791449867349920758398003)
                ·
                  refine ⟨5687174801024881137597005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3791449867349920758398003 5687174801024881137597005)
                  ·
                    refine ⟨2132690550384330426598877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5687174801024881137597005 2132690550384330426598877)
                    ·
                      refine ⟨799758956394123909974579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2132690550384330426598877 799758956394123909974579)
                      ·
                        rfl

theorem cell23_1557525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_1557525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557525 prefixEnd_1557525 := by exact prefixLift 1557525
  have htrace : WordTrace (prefixWord ++ tailWord_1557525) baseStart_1557525 baseEnd_1557525 := by
    simpa [prefixWord, tailWord_1557525, baseEnd_1557525] using wordTrace_append hprefix tailTrace_1557525
  have hstable : (prefixWord ++ tailWord_1557525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557525).length < 2 ^ (prefixWord ++ tailWord_1557525).sum := by decide
  have hdescent : baseEnd_1557525 < baseStart_1557525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557535 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 3, 3, 2]
def baseStart_1557535 : Nat := 118140960795 + 1557535 * 2 ^ 59
def prefixEnd_1557535 : Nat := 4983230072969 + 3 ^ 40 * 1557535 * 2
def baseEnd_1557535 : Nat := 799764091200668870849533

theorem tailTrace_1557535 : CollatzResearch.WordTrace tailWord_1557535 prefixEnd_1557535 799764091200668870849533 := by
  unfold tailWord_1557535
  simp only [CollatzResearch.WordTrace]
  refine ⟨56807968412324175645306059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37871978941549450430204039 56807968412324175645306059)
  ·
    refine ⟨85211952618486263467959089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56807968412324175645306059 85211952618486263467959089)
    ·
      refine ⟨63908964463864697600969317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85211952618486263467959089 63908964463864697600969317)
      ·
        refine ⟨11982930836974630800181747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63908964463864697600969317 11982930836974630800181747)
        ·
          refine ⟨17974396255461946200272621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11982930836974630800181747 17974396255461946200272621)
          ·
            refine ⟨6740398595798229825102233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17974396255461946200272621 6740398595798229825102233)
            ·
              refine ⟨5055298946848672368826675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6740398595798229825102233 5055298946848672368826675)
              ·
                refine ⟨7582948420273008553240013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5055298946848672368826675 7582948420273008553240013)
                ·
                  refine ⟨2843605657602378207465005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7582948420273008553240013 2843605657602378207465005)
                  ·
                    refine ⟨1066352121600891827799377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2843605657602378207465005 1066352121600891827799377)
                    ·
                      refine ⟨799764091200668870849533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1066352121600891827799377 799764091200668870849533)
                      ·
                        rfl

theorem cell23_1557535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_1557535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557535 prefixEnd_1557535 := by exact prefixLift 1557535
  have htrace : WordTrace (prefixWord ++ tailWord_1557535) baseStart_1557535 baseEnd_1557535 := by
    simpa [prefixWord, tailWord_1557535, baseEnd_1557535] using wordTrace_append hprefix tailTrace_1557535
  have hstable : (prefixWord ++ tailWord_1557535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557535).length < 2 ^ (prefixWord ++ tailWord_1557535).sum := by decide
  have hdescent : baseEnd_1557535 < baseStart_1557535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557541 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 1, 8]
def baseStart_1557541 : Nat := 118140960795 + 1557541 * 2 ^ 59
def prefixEnd_1557541 : Nat := 4983230072969 + 3 ^ 40 * 1557541 * 2
def baseEnd_1557541 : Nat := 266589057361531949124835

theorem tailTrace_1557541 : CollatzResearch.WordTrace tailWord_1557541 prefixEnd_1557541 266589057361531949124835 := by
  unfold tailWord_1557541
  simp only [CollatzResearch.WordTrace]
  refine ⟨56808187250302438670024477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37872124833534959113349651 56808187250302438670024477)
  ·
    refine ⟨21303070218863414501259179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56808187250302438670024477 21303070218863414501259179)
    ·
      refine ⟨31954605328295121751888769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21303070218863414501259179 31954605328295121751888769)
      ·
        refine ⟨23965953996221341313916577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31954605328295121751888769 23965953996221341313916577)
        ·
          refine ⟨17974465497166005985437433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23965953996221341313916577 17974465497166005985437433)
          ·
            refine ⟨13480849122874504489078075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17974465497166005985437433 13480849122874504489078075)
            ·
              refine ⟨20221273684311756733617113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13480849122874504489078075 20221273684311756733617113)
              ·
                refine ⟨15165955263233817550212835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20221273684311756733617113 15165955263233817550212835)
                ·
                  refine ⟨22748932894850726325319253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15165955263233817550212835 22748932894850726325319253)
                  ·
                    refine ⟨266589057361531949124835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22748932894850726325319253 266589057361531949124835)
                    ·
                      rfl

theorem cell23_1557541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_1557541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557541 prefixEnd_1557541 := by exact prefixLift 1557541
  have htrace : WordTrace (prefixWord ++ tailWord_1557541) baseStart_1557541 baseEnd_1557541 := by
    simpa [prefixWord, tailWord_1557541, baseEnd_1557541] using wordTrace_append hprefix tailTrace_1557541
  have hstable : (prefixWord ++ tailWord_1557541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557541).length < 2 ^ (prefixWord ++ tailWord_1557541).sum := by decide
  have hdescent : baseEnd_1557541 < baseStart_1557541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557546 : List Nat := [3, 1, 4, 1, 4, 1, 2, 1, 1, 2, 3]
def baseStart_1557546 : Nat := 118140960795 + 1557546 * 2 ^ 59
def prefixEnd_1557546 : Nat := 4983230072969 + 3 ^ 40 * 1557546 * 2
def baseEnd_1557546 : Nat := 799769739487868327811983

theorem tailTrace_1557546 : CollatzResearch.WordTrace tailWord_1557546 prefixEnd_1557546 799769739487868327811983 := by
  unfold tailWord_1557546
  simp only [CollatzResearch.WordTrace]
  refine ⟨14202092403821081130989123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37872246410189549682637661 14202092403821081130989123)
  ·
    refine ⟨21303138605731621696483685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14202092403821081130989123 21303138605731621696483685)
    ·
      refine ⟨3994338488574679068090691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21303138605731621696483685 3994338488574679068090691)
      ·
        refine ⟨5991507732862018602136037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3994338488574679068090691 5991507732862018602136037)
        ·
          refine ⟨1123407699911628487900507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5991507732862018602136037 1123407699911628487900507)
          ·
            refine ⟨1685111549867442731850761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123407699911628487900507 1685111549867442731850761)
            ·
              refine ⟨1263833662400582048888071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1685111549867442731850761 1263833662400582048888071)
              ·
                refine ⟨1895750493600873073332107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1263833662400582048888071 1895750493600873073332107)
                ·
                  refine ⟨2843625740401309609998161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1895750493600873073332107 2843625740401309609998161)
                  ·
                    refine ⟨2132719305300982207498621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2843625740401309609998161 2132719305300982207498621)
                    ·
                      refine ⟨799769739487868327811983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2132719305300982207498621 799769739487868327811983)
                      ·
                        rfl

theorem cell23_1557546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_1557546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557546 prefixEnd_1557546 := by exact prefixLift 1557546
  have htrace : WordTrace (prefixWord ++ tailWord_1557546) baseStart_1557546 baseEnd_1557546 := by
    simpa [prefixWord, tailWord_1557546, baseEnd_1557546] using wordTrace_append hprefix tailTrace_1557546
  have hstable : (prefixWord ++ tailWord_1557546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557546).length < 2 ^ (prefixWord ++ tailWord_1557546).sum := by decide
  have hdescent : baseEnd_1557546 < baseStart_1557546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557551 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 5]
def baseStart_1557551 : Nat := 118140960795 + 1557551 * 2 ^ 59
def prefixEnd_1557551 : Nat := 4983230072969 + 3 ^ 40 * 1557551 * 2
def baseEnd_1557551 : Nat := 799772306891140808249459

theorem tailTrace_1557551 : CollatzResearch.WordTrace tailWord_1557551 prefixEnd_1557551 799772306891140808249459 := by
  unfold tailWord_1557551
  simp only [CollatzResearch.WordTrace]
  refine ⟨56808551980266210377888507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37872367986844140251925671 56808551980266210377888507)
  ·
    refine ⟨85212827970399315566832761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56808551980266210377888507 85212827970399315566832761)
    ·
      refine ⟨63909620977799486675124571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85212827970399315566832761 63909620977799486675124571)
      ·
        refine ⟨95864431466699230012686857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63909620977799486675124571 95864431466699230012686857)
        ·
          refine ⟨71898323600024422509515143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95864431466699230012686857 71898323600024422509515143)
          ·
            refine ⟨107847485400036633764272715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71898323600024422509515143 107847485400036633764272715)
            ·
              refine ⟨161771228100054950646409073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107847485400036633764272715 161771228100054950646409073)
              ·
                refine ⟨121328421075041212984806805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161771228100054950646409073 121328421075041212984806805)
                ·
                  refine ⟨5687269737892556858662819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121328421075041212984806805 5687269737892556858662819)
                  ·
                    refine ⟨8530904606838835287994229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5687269737892556858662819 8530904606838835287994229)
                    ·
                      refine ⟨799772306891140808249459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8530904606838835287994229 799772306891140808249459)
                      ·
                        rfl

theorem cell23_1557551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 5].length) (baseStart_1557551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557551 prefixEnd_1557551 := by exact prefixLift 1557551
  have htrace : WordTrace (prefixWord ++ tailWord_1557551) baseStart_1557551 baseEnd_1557551 := by
    simpa [prefixWord, tailWord_1557551, baseEnd_1557551] using wordTrace_append hprefix tailTrace_1557551
  have hstable : (prefixWord ++ tailWord_1557551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557551).length < 2 ^ (prefixWord ++ tailWord_1557551).sum := by decide
  have hdescent : baseEnd_1557551 < baseStart_1557551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557578 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 2, 2, 4]
def baseStart_1557578 : Nat := 118140960795 + 1557578 * 2 ^ 59
def prefixEnd_1557578 : Nat := 4983230072969 + 3 ^ 40 * 1557578 * 2
def baseEnd_1557578 : Nat := 799786170868812202611835

theorem tailTrace_1557578 : CollatzResearch.WordTrace tailWord_1557578 prefixEnd_1557578 799786170868812202611835 := by
  unfold tailWord_1557578
  simp only [CollatzResearch.WordTrace]
  refine ⟨14202384187792098497280347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37873024500778929326080925 14202384187792098497280347)
  ·
    refine ⟨21303576281688147745920521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14202384187792098497280347 21303576281688147745920521)
    ·
      refine ⟨15977682211266110809440391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21303576281688147745920521 15977682211266110809440391)
      ·
        refine ⟨23966523316899166214160587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15977682211266110809440391 23966523316899166214160587)
        ·
          refine ⟨35949784975348749321240881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23966523316899166214160587 35949784975348749321240881)
          ·
            refine ⟨26962338731511561990930661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35949784975348749321240881 26962338731511561990930661)
            ·
              refine ⟨5055438512158417873299499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26962338731511561990930661 5055438512158417873299499)
              ·
                refine ⟨7583157768237626809949249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5055438512158417873299499 7583157768237626809949249)
                ·
                  refine ⟨5687368326178220107461937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7583157768237626809949249 5687368326178220107461937)
                  ·
                    refine ⟨4265526244633665080596453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5687368326178220107461937 4265526244633665080596453)
                    ·
                      refine ⟨799786170868812202611835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4265526244633665080596453 799786170868812202611835)
                      ·
                        rfl

theorem cell23_1557578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_1557578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557578 prefixEnd_1557578 := by exact prefixLift 1557578
  have htrace : WordTrace (prefixWord ++ tailWord_1557578) baseStart_1557578 baseEnd_1557578 := by
    simpa [prefixWord, tailWord_1557578, baseEnd_1557578] using wordTrace_append hprefix tailTrace_1557578
  have hstable : (prefixWord ++ tailWord_1557578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557578).length < 2 ^ (prefixWord ++ tailWord_1557578).sum := by decide
  have hdescent : baseEnd_1557578 < baseStart_1557578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557588 : List Nat := [2, 4, 1, 1, 1, 1, 4, 2, 7]
def baseStart_1557588 : Nat := 118140960795 + 1557588 * 2 ^ 59
def prefixEnd_1557588 : Nat := 4983230072969 + 3 ^ 40 * 1557588 * 2
def baseEnd_1557588 : Nat := 88865700630595240387421

theorem tailTrace_1557588 : CollatzResearch.WordTrace tailWord_1557588 prefixEnd_1557588 88865700630595240387421 := by
  unfold tailWord_1557588
  simp only [CollatzResearch.WordTrace]
  refine ⟨28404950740566082848492709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37873267654088110464656945 28404950740566082848492709)
  ·
    refine ⟨5325928263856140534092383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28404950740566082848492709 5325928263856140534092383)
    ·
      refine ⟨7988892395784210801138575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5325928263856140534092383 7988892395784210801138575)
      ·
        refine ⟨11983338593676316201707863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7988892395784210801138575 11983338593676316201707863)
        ·
          refine ⟨17975007890514474302561795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11983338593676316201707863 17975007890514474302561795)
          ·
            refine ⟨26962511835771711453842693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17975007890514474302561795 26962511835771711453842693)
            ·
              refine ⟨5055470969207195897595505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26962511835771711453842693 5055470969207195897595505)
              ·
                refine ⟨3791603226905396923196629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5055470969207195897595505 3791603226905396923196629)
                ·
                  refine ⟨88865700630595240387421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3791603226905396923196629 88865700630595240387421)
                  ·
                    rfl

theorem cell23_1557588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_1557588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557588 prefixEnd_1557588 := by exact prefixLift 1557588
  have htrace : WordTrace (prefixWord ++ tailWord_1557588) baseStart_1557588 baseEnd_1557588 := by
    simpa [prefixWord, tailWord_1557588, baseEnd_1557588] using wordTrace_append hprefix tailTrace_1557588
  have hstable : (prefixWord ++ tailWord_1557588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557588).length < 2 ^ (prefixWord ++ tailWord_1557588).sum := by decide
  have hdescent : baseEnd_1557588 < baseStart_1557588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557611 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 7]
def baseStart_1557611 : Nat := 118140960795 + 1557611 * 2 ^ 59
def prefixEnd_1557611 : Nat := 4983230072969 + 3 ^ 40 * 1557611 * 2
def baseEnd_1557611 : Nat := 799803115730410573499183

theorem tailTrace_1557611 : CollatzResearch.WordTrace tailWord_1557611 prefixEnd_1557611 799803115730410573499183 := by
  unfold tailWord_1557611
  simp only [CollatzResearch.WordTrace]
  refine ⟨56810740360048840625072687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37873826906699227083381791 56810740360048840625072687)
  ·
    refine ⟨85216110540073260937609031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56810740360048840625072687 85216110540073260937609031)
    ·
      refine ⟨127824165810109891406413547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85216110540073260937609031 127824165810109891406413547)
      ·
        refine ⟨191736248715164837109620321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127824165810109891406413547 191736248715164837109620321)
        ·
          refine ⟨143802186536373627832215241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191736248715164837109620321 143802186536373627832215241)
          ·
            refine ⟨107851639902280220874161431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143802186536373627832215241 107851639902280220874161431)
            ·
              refine ⟨161777459853420331311242147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107851639902280220874161431 161777459853420331311242147)
              ·
                refine ⟨242666189780130496966863221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161777459853420331311242147 242666189780130496966863221)
                ·
                  refine ⟨22749955291887234090643427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 242666189780130496966863221 22749955291887234090643427)
                  ·
                    refine ⟨34124932937830851135965141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22749955291887234090643427 34124932937830851135965141)
                    ·
                      refine ⟨799803115730410573499183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34124932937830851135965141 799803115730410573499183)
                      ·
                        rfl

theorem cell23_1557611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 7].length) (baseStart_1557611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557611 prefixEnd_1557611 := by exact prefixLift 1557611
  have htrace : WordTrace (prefixWord ++ tailWord_1557611) baseStart_1557611 baseEnd_1557611 := by
    simpa [prefixWord, tailWord_1557611, baseEnd_1557611] using wordTrace_append hprefix tailTrace_1557611
  have hstable : (prefixWord ++ tailWord_1557611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557611).length < 2 ^ (prefixWord ++ tailWord_1557611).sum := by decide
  have hdescent : baseEnd_1557611 < baseStart_1557611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557628 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 1, 2, 5]
def baseStart_1557628 : Nat := 118140960795 + 1557628 * 2 ^ 59
def prefixEnd_1557628 : Nat := 4983230072969 + 3 ^ 40 * 1557628 * 2
def baseEnd_1557628 : Nat := 799811844901537006986605

theorem tailTrace_1557628 : CollatzResearch.WordTrace tailWord_1557628 prefixEnd_1557628 799811844901537006986605 := by
  unfold tailWord_1557628
  simp only [CollatzResearch.WordTrace]
  refine ⟨28405680200493626264220769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37874240267324835018961025 28405680200493626264220769)
  ·
    refine ⟨21304260150370219698165577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28405680200493626264220769 21304260150370219698165577)
    ·
      refine ⟨15978195112777664773624183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21304260150370219698165577 15978195112777664773624183)
      ·
        refine ⟨23967292669166497160436275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15978195112777664773624183 23967292669166497160436275)
        ·
          refine ⟨35950939003749745740654413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23967292669166497160436275 35950939003749745740654413)
          ·
            refine ⟨13481602126406154652745405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35950939003749745740654413 13481602126406154652745405)
            ·
              refine ⟨5055600797402307994779527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13481602126406154652745405 5055600797402307994779527)
              ·
                refine ⟨7583401196103461992169291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5055600797402307994779527 7583401196103461992169291)
                ·
                  refine ⟨11375101794155192988253937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7583401196103461992169291 11375101794155192988253937)
                  ·
                    refine ⟨8531326345616394741190453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11375101794155192988253937 8531326345616394741190453)
                    ·
                      refine ⟨799811844901537006986605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8531326345616394741190453 799811844901537006986605)
                      ·
                        rfl

theorem cell23_1557628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_1557628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557628 prefixEnd_1557628 := by exact prefixLift 1557628
  have htrace : WordTrace (prefixWord ++ tailWord_1557628) baseStart_1557628 baseEnd_1557628 := by
    simpa [prefixWord, tailWord_1557628, baseEnd_1557628] using wordTrace_append hprefix tailTrace_1557628
  have hstable : (prefixWord ++ tailWord_1557628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557628).length < 2 ^ (prefixWord ++ tailWord_1557628).sum := by decide
  have hdescent : baseEnd_1557628 < baseStart_1557628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557655 : List Nat := [1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 4]
def baseStart_1557655 : Nat := 118140960795 + 1557655 * 2 ^ 59
def prefixEnd_1557655 : Nat := 4983230072969 + 3 ^ 40 * 1557655 * 2
def baseEnd_1557655 : Nat := 799825708879208401348981

theorem tailTrace_1557655 : CollatzResearch.WordTrace tailWord_1557655 prefixEnd_1557655 799825708879208401348981 := by
  unfold tailWord_1557655
  simp only [CollatzResearch.WordTrace]
  refine ⟨56812345171889436139674419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37874896781259624093116279 56812345171889436139674419)
  ·
    refine ⟨85218517757834154209511629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56812345171889436139674419 85218517757834154209511629)
    ·
      refine ⟨31956944159187807828566861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85218517757834154209511629 31956944159187807828566861)
      ·
        refine ⟨11983854059695427935712573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31956944159187807828566861 11983854059695427935712573)
        ·
          refine ⟨4493945272385785475892215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11983854059695427935712573 4493945272385785475892215)
          ·
            refine ⟨6740917908578678213838323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4493945272385785475892215 6740917908578678213838323)
            ·
              refine ⟨10111376862868017320757485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6740917908578678213838323 10111376862868017320757485)
              ·
                refine ⟨3791766323575506495284057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10111376862868017320757485 3791766323575506495284057)
                ·
                  refine ⟨2843824742681629871463043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3791766323575506495284057 2843824742681629871463043)
                  ·
                    refine ⟨4265737114022444807194565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2843824742681629871463043 4265737114022444807194565)
                    ·
                      refine ⟨799825708879208401348981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4265737114022444807194565 799825708879208401348981)
                      ·
                        rfl

theorem cell23_1557655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_1557655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557655 prefixEnd_1557655 := by exact prefixLift 1557655
  have htrace : WordTrace (prefixWord ++ tailWord_1557655) baseStart_1557655 baseEnd_1557655 := by
    simpa [prefixWord, tailWord_1557655, baseEnd_1557655] using wordTrace_append hprefix tailTrace_1557655
  have hstable : (prefixWord ++ tailWord_1557655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557655).length < 2 ^ (prefixWord ++ tailWord_1557655).sum := by decide
  have hdescent : baseEnd_1557655 < baseStart_1557655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557715 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 1, 5, 2]
def baseStart_1557715 : Nat := 118140960795 + 1557715 * 2 ^ 59
def prefixEnd_1557715 : Nat := 4983230072969 + 3 ^ 40 * 1557715 * 2
def baseEnd_1557715 : Nat := 799856517718478166598705

theorem tailTrace_1557715 : CollatzResearch.WordTrace tailWord_1557715 prefixEnd_1557715 799856517718478166598705 := by
  unfold tailWord_1557715
  simp only [CollatzResearch.WordTrace]
  refine ⟨56814533551672066386858599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37876355701114710924572399 56814533551672066386858599)
  ·
    refine ⟨85221800327508099580287899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56814533551672066386858599 85221800327508099580287899)
    ·
      refine ⟨127832700491262149370431849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85221800327508099580287899 127832700491262149370431849)
      ·
        refine ⟨95874525368446612027823887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127832700491262149370431849 95874525368446612027823887)
        ·
          refine ⟨143811788052669918041735831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95874525368446612027823887 143811788052669918041735831)
          ·
            refine ⟨215717682079004877062603747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143811788052669918041735831 215717682079004877062603747)
            ·
              refine ⟨323576523118507315593905621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215717682079004877062603747 323576523118507315593905621)
              ·
                refine ⟨7583824760590015209232163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 323576523118507315593905621 7583824760590015209232163)
                ·
                  refine ⟨11375737140885022813848245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7583824760590015209232163 11375737140885022813848245)
                  ·
                    refine ⟨1066475356957970888798273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11375737140885022813848245 1066475356957970888798273)
                    ·
                      refine ⟨799856517718478166598705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1066475356957970888798273 799856517718478166598705)
                      ·
                        rfl

theorem cell23_1557715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 5, 2].length) (baseStart_1557715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557715 prefixEnd_1557715 := by exact prefixLift 1557715
  have htrace : WordTrace (prefixWord ++ tailWord_1557715) baseStart_1557715 baseEnd_1557715 := by
    simpa [prefixWord, tailWord_1557715, baseEnd_1557715] using wordTrace_append hprefix tailTrace_1557715
  have hstable : (prefixWord ++ tailWord_1557715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557715).length < 2 ^ (prefixWord ++ tailWord_1557715).sum := by decide
  have hdescent : baseEnd_1557715 < baseStart_1557715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557732 : List Nat := [2, 3, 1, 1, 1, 2, 2, 4, 2, 3, 2]
def baseStart_1557732 : Nat := 118140960795 + 1557732 * 2 ^ 59
def prefixEnd_1557732 : Nat := 4983230072969 + 3 ^ 40 * 1557732 * 2
def baseEnd_1557732 : Nat := 799865246889604600086127

theorem tailTrace_1557732 : CollatzResearch.WordTrace tailWord_1557732 prefixEnd_1557732 799865246889604600086127 := by
  unfold tailWord_1557732
  simp only [CollatzResearch.WordTrace]
  refine ⟨28407576796305239145113725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37876769061740318860151633 28407576796305239145113725)
  ·
    refine ⟨10652841298614464679417647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28407576796305239145113725 10652841298614464679417647)
    ·
      refine ⟨15979261947921697019126471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10652841298614464679417647 15979261947921697019126471)
      ·
        refine ⟨23968892921882545528689707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15979261947921697019126471 23968892921882545528689707)
        ·
          refine ⟨35953339382823818293034561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23968892921882545528689707 35953339382823818293034561)
          ·
            refine ⟨26965004537117863719775921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35953339382823818293034561 26965004537117863719775921)
            ·
              refine ⟨20223753402838397789831941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26965004537117863719775921 20223753402838397789831941)
              ·
                refine ⟨3791953763032199585593489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20223753402838397789831941 3791953763032199585593489)
                ·
                  refine ⟨2843965322274149689195117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3791953763032199585593489 2843965322274149689195117)
                  ·
                    refine ⟨1066486995852806133448169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2843965322274149689195117 1066486995852806133448169)
                    ·
                      refine ⟨799865246889604600086127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1066486995852806133448169 799865246889604600086127)
                      ·
                        rfl

theorem cell23_1557732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 2, 3, 2].length) (baseStart_1557732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557732 prefixEnd_1557732 := by exact prefixLift 1557732
  have htrace : WordTrace (prefixWord ++ tailWord_1557732) baseStart_1557732 baseEnd_1557732 := by
    simpa [prefixWord, tailWord_1557732, baseEnd_1557732] using wordTrace_append hprefix tailTrace_1557732
  have hstable : (prefixWord ++ tailWord_1557732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557732).length < 2 ^ (prefixWord ++ tailWord_1557732).sum := by decide
  have hdescent : baseEnd_1557732 < baseStart_1557732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557739 : List Nat := [1, 1, 1, 1, 2, 6, 2, 4, 1, 1, 3]
def baseStart_1557739 : Nat := 118140960795 + 1557739 * 2 ^ 59
def prefixEnd_1557739 : Nat := 4983230072969 + 3 ^ 40 * 1557739 * 2
def baseEnd_1557739 : Nat := 799868841254186072698595

theorem tailTrace_1557739 : CollatzResearch.WordTrace tailWord_1557739 prefixEnd_1557739 799868841254186072698595 := by
  unfold tailWord_1557739
  simp only [CollatzResearch.WordTrace]
  refine ⟨56815408903585118485732271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37876939269056745657154847 56815408903585118485732271)
  ·
    refine ⟨85223113355377677728598407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56815408903585118485732271 85223113355377677728598407)
    ·
      refine ⟨127834670033066516592897611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85223113355377677728598407 127834670033066516592897611)
      ·
        refine ⟨191752005049599774889346417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127834670033066516592897611 191752005049599774889346417)
        ·
          refine ⟨143814003787199831167009813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191752005049599774889346417 143814003787199831167009813)
          ·
            refine ⟨6741281427524992085953585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 143814003787199831167009813 6741281427524992085953585)
            ·
              refine ⟨5055961070643744064465189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6741281427524992085953585 5055961070643744064465189)
              ·
                refine ⟨947992700745702012087223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5055961070643744064465189 947992700745702012087223)
                ·
                  refine ⟨1421989051118553018130835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 947992700745702012087223 1421989051118553018130835)
                  ·
                    refine ⟨2132983576677829527196253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1421989051118553018130835 2132983576677829527196253)
                    ·
                      refine ⟨799868841254186072698595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2132983576677829527196253 799868841254186072698595)
                      ·
                        rfl

theorem cell23_1557739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 1, 1, 3].length) (baseStart_1557739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557739 prefixEnd_1557739 := by exact prefixLift 1557739
  have htrace : WordTrace (prefixWord ++ tailWord_1557739) baseStart_1557739 baseEnd_1557739 := by
    simpa [prefixWord, tailWord_1557739, baseEnd_1557739] using wordTrace_append hprefix tailTrace_1557739
  have hstable : (prefixWord ++ tailWord_1557739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557739).length < 2 ^ (prefixWord ++ tailWord_1557739).sum := by decide
  have hdescent : baseEnd_1557739 < baseStart_1557739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557790 : List Nat := [4, 3, 2, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_1557790 : Nat := 118140960795 + 1557790 * 2 ^ 59
def prefixEnd_1557790 : Nat := 4983230072969 + 3 ^ 40 * 1557790 * 2
def baseEnd_1557790 : Nat := 799895028767565373160861

theorem tailTrace_1557790 : CollatzResearch.WordTrace tailWord_1557790 prefixEnd_1557790 799895028767565373160861 := by
  unfold tailWord_1557790
  simp only [CollatzResearch.WordTrace]
  refine ⟨7102158628300044274479853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37878179350933569463892549 7102158628300044274479853)
  ·
    refine ⟨2663309485612516602929945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7102158628300044274479853 2663309485612516602929945)
    ·
      refine ⟨1997482114209387452197459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2663309485612516602929945 1997482114209387452197459)
      ·
        refine ⟨2996223171314081178296189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1997482114209387452197459 2996223171314081178296189)
        ·
          refine ⟨1123583689242780441861071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2996223171314081178296189 1123583689242780441861071)
          ·
            refine ⟨1685375533864170662791607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123583689242780441861071 1685375533864170662791607)
            ·
              refine ⟨2528063300796255994187411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1685375533864170662791607 2528063300796255994187411)
              ·
                refine ⟨3792094951194383991281117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2528063300796255994187411 3792094951194383991281117)
                ·
                  refine ⟨1422035606697893996730419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3792094951194383991281117 1422035606697893996730419)
                  ·
                    refine ⟨2133053410046840995095629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1422035606697893996730419 2133053410046840995095629)
                    ·
                      refine ⟨799895028767565373160861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2133053410046840995095629 799895028767565373160861)
                      ·
                        rfl

theorem cell23_1557790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_1557790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557790 prefixEnd_1557790 := by exact prefixLift 1557790
  have htrace : WordTrace (prefixWord ++ tailWord_1557790) baseStart_1557790 baseEnd_1557790 := by
    simpa [prefixWord, tailWord_1557790, baseEnd_1557790] using wordTrace_append hprefix tailTrace_1557790
  have hstable : (prefixWord ++ tailWord_1557790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557790).length < 2 ^ (prefixWord ++ tailWord_1557790).sum := by decide
  have hdescent : baseEnd_1557790 < baseStart_1557790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557802 : List Nat := [3, 1, 4, 2, 1, 2, 2, 8]
def baseStart_1557802 : Nat := 118140960795 + 1557802 * 2 ^ 59
def prefixEnd_1557802 : Nat := 4983230072969 + 3 ^ 40 * 1557802 * 2
def baseEnd_1557802 : Nat := 29625970019830345415215

theorem tailTrace_1557802 : CollatzResearch.WordTrace tailWord_1557802 prefixEnd_1557802 29625970019830345415215 := by
  unfold tailWord_1557802
  simp only [CollatzResearch.WordTrace]
  refine ⟨14204426675589220061318915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37878471134904586830183773 14204426675589220061318915)
  ·
    refine ⟨21306640013383830091978373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14204426675589220061318915 21306640013383830091978373)
    ·
      refine ⟨3994995002509468142245945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21306640013383830091978373 3994995002509468142245945)
      ·
        refine ⟨2996246251882101106684459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3994995002509468142245945 2996246251882101106684459)
        ·
          refine ⟨4494369377823151660026689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2996246251882101106684459 4494369377823151660026689)
          ·
            refine ⟨3370777033367363745020017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4494369377823151660026689 3370777033367363745020017)
            ·
              refine ⟨2528082775025522808765013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3370777033367363745020017 2528082775025522808765013)
              ·
                refine ⟨29625970019830345415215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2528082775025522808765013 29625970019830345415215)
                ·
                  rfl

theorem cell23_1557802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 8].length) (baseStart_1557802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557802 prefixEnd_1557802 := by exact prefixLift 1557802
  have htrace : WordTrace (prefixWord ++ tailWord_1557802) baseStart_1557802 baseEnd_1557802 := by
    simpa [prefixWord, tailWord_1557802, baseEnd_1557802] using wordTrace_append hprefix tailTrace_1557802
  have hstable : (prefixWord ++ tailWord_1557802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557802).length < 2 ^ (prefixWord ++ tailWord_1557802).sum := by decide
  have hdescent : baseEnd_1557802 < baseStart_1557802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557830 : List Nat := [6, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4]
def baseStart_1557830 : Nat := 118140960795 + 1557830 * 2 ^ 59
def prefixEnd_1557830 : Nat := 4983230072969 + 3 ^ 40 * 1557830 * 2
def baseEnd_1557830 : Nat := 799915567993745216660677

theorem tailTrace_1557830 : CollatzResearch.WordTrace tailWord_1557830 prefixEnd_1557830 799915567993745216660677 := by
  unfold tailWord_1557830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1775585248320482532102967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37879151964170294018196629 1775585248320482532102967)
  ·
    refine ⟨2663377872480723798154451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1775585248320482532102967 2663377872480723798154451)
    ·
      refine ⟨3995066808721085697231677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2663377872480723798154451 3995066808721085697231677)
      ·
        refine ⟨1498150053270407136461879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3995066808721085697231677 1498150053270407136461879)
        ·
          refine ⟨2247225079905610704692819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1498150053270407136461879 2247225079905610704692819)
          ·
            refine ⟨3370837619858416057039229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2247225079905610704692819 3370837619858416057039229)
            ·
              refine ⟨1264064107446906021389711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3370837619858416057039229 1264064107446906021389711)
              ·
                refine ⟨1896096161170359032084567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1264064107446906021389711 1896096161170359032084567)
                ·
                  refine ⟨2844144241755538548126851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1896096161170359032084567 2844144241755538548126851)
                  ·
                    refine ⟨4266216362633307822190277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2844144241755538548126851 4266216362633307822190277)
                    ·
                      refine ⟨799915567993745216660677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4266216362633307822190277 799915567993745216660677)
                      ·
                        rfl

theorem cell23_1557830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_1557830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557830 prefixEnd_1557830 := by exact prefixLift 1557830
  have htrace : WordTrace (prefixWord ++ tailWord_1557830) baseStart_1557830 baseEnd_1557830 := by
    simpa [prefixWord, tailWord_1557830, baseEnd_1557830] using wordTrace_append hprefix tailTrace_1557830
  have hstable : (prefixWord ++ tailWord_1557830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557830).length < 2 ^ (prefixWord ++ tailWord_1557830).sum := by decide
  have hdescent : baseEnd_1557830 < baseStart_1557830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557853 : List Nat := [1, 4, 5, 1, 2, 1, 1, 8]
def baseStart_1557853 : Nat := 118140960795 + 1557853 * 2 ^ 59
def prefixEnd_1557853 : Nat := 4983230072969 + 3 ^ 40 * 1557853 * 2
def baseEnd_1557853 : Nat := 29626939927733282469373

theorem tailTrace_1557853 : CollatzResearch.WordTrace tailWord_1557853 prefixEnd_1557853 29626939927733282469373 := by
  unfold tailWord_1557853
  simp only [CollatzResearch.WordTrace]
  refine ⟨56819566825172115955382213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37879711216781410636921475 56819566825172115955382213)
  ·
    refine ⟨10653668779719771741634165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56819566825172115955382213 10653668779719771741634165)
    ·
      refine ⟨998781448098728600778203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10653668779719771741634165 998781448098728600778203)
      ·
        refine ⟨1498172172148092901167305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 998781448098728600778203 1498172172148092901167305)
        ·
          refine ⟨1123629129111069675875479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1498172172148092901167305 1123629129111069675875479)
          ·
            refine ⟨1685443693666604513813219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123629129111069675875479 1685443693666604513813219)
            ·
              refine ⟨2528165540499906770719829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1685443693666604513813219 2528165540499906770719829)
              ·
                refine ⟨29626939927733282469373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2528165540499906770719829 29626939927733282469373)
                ·
                  rfl

theorem cell23_1557853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 8].length) (baseStart_1557853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557853 prefixEnd_1557853 := by exact prefixLift 1557853
  have htrace : WordTrace (prefixWord ++ tailWord_1557853) baseStart_1557853 baseEnd_1557853 := by
    simpa [prefixWord, tailWord_1557853, baseEnd_1557853] using wordTrace_append hprefix tailTrace_1557853
  have hstable : (prefixWord ++ tailWord_1557853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557853).length < 2 ^ (prefixWord ++ tailWord_1557853).sum := by decide
  have hdescent : baseEnd_1557853 < baseStart_1557853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557869 : List Nat := [1, 5, 1, 1, 1, 3, 1, 3, 1, 4, 2]
def baseStart_1557869 : Nat := 118140960795 + 1557869 * 2 ^ 59
def prefixEnd_1557869 : Nat := 4983230072969 + 3 ^ 40 * 1557869 * 2
def baseEnd_1557869 : Nat := 799935593739270564072997

theorem tailTrace_1557869 : CollatzResearch.WordTrace tailWord_1557869 prefixEnd_1557869 799935593739270564072997 := by
  unfold tailWord_1557869
  simp only [CollatzResearch.WordTrace]
  refine ⟨56820150393114150687964661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37880100262076100458643107 56820150393114150687964661)
  ·
    refine ⟨5326889099354451626996687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56820150393114150687964661 5326889099354451626996687)
    ·
      refine ⟨7990333649031677440495031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5326889099354451626996687 7990333649031677440495031)
      ·
        refine ⟨11985500473547516160742547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7990333649031677440495031 11985500473547516160742547)
        ·
          refine ⟨17978250710321274241113821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11985500473547516160742547 17978250710321274241113821)
          ·
            refine ⟨6741844016370477840417683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17978250710321274241113821 6741844016370477840417683)
            ·
              refine ⟨10112766024555716760626525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6741844016370477840417683 10112766024555716760626525)
              ·
                refine ⟨3792287259208393785234947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10112766024555716760626525 3792287259208393785234947)
                ·
                  refine ⟨5688430888812590677852421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3792287259208393785234947 5688430888812590677852421)
                  ·
                    refine ⟨1066580791652360752097329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5688430888812590677852421 1066580791652360752097329)
                    ·
                      refine ⟨799935593739270564072997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1066580791652360752097329 799935593739270564072997)
                      ·
                        rfl

theorem cell23_1557869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_1557869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557869 prefixEnd_1557869 := by exact prefixLift 1557869
  have htrace : WordTrace (prefixWord ++ tailWord_1557869) baseStart_1557869 baseEnd_1557869 := by
    simpa [prefixWord, tailWord_1557869, baseEnd_1557869] using wordTrace_append hprefix tailTrace_1557869
  have hstable : (prefixWord ++ tailWord_1557869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557869).length < 2 ^ (prefixWord ++ tailWord_1557869).sum := by decide
  have hdescent : baseEnd_1557869 < baseStart_1557869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557890 : List Nat := [3, 4, 2, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_1557890 : Nat := 118140960795 + 1557890 * 2 ^ 59
def prefixEnd_1557890 : Nat := 4983230072969 + 3 ^ 40 * 1557890 * 2
def baseEnd_1557890 : Nat := 799946376833014981910401

theorem tailTrace_1557890 : CollatzResearch.WordTrace tailWord_1557890 prefixEnd_1557890 799946376833014981910401 := by
  unfold tailWord_1557890
  simp only [CollatzResearch.WordTrace]
  refine ⟨14205229081509517818619781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37880610884025380849652749 14205229081509517818619781)
  ·
    refine ⟨2663480452783034590991209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14205229081509517818619781 2663480452783034590991209)
    ·
      refine ⟨1997610339587275943243407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2663480452783034590991209 1997610339587275943243407)
      ·
        refine ⟨2996415509380913914865111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1997610339587275943243407 2996415509380913914865111)
        ·
          refine ⟨4494623264071370872297667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2996415509380913914865111 4494623264071370872297667)
          ·
            refine ⟨6741934896107056308446501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4494623264071370872297667 6741934896107056308446501)
            ·
              refine ⟨1264112793020073057833719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6741934896107056308446501 1264112793020073057833719)
              ·
                refine ⟨1896169189530109586750579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1264112793020073057833719 1896169189530109586750579)
                ·
                  refine ⟨2844253784295164380125869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1896169189530109586750579 2844253784295164380125869)
                  ·
                    refine ⟨1066595169110686642547201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2844253784295164380125869 1066595169110686642547201)
                    ·
                      refine ⟨799946376833014981910401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1066595169110686642547201 799946376833014981910401)
                      ·
                        rfl

theorem cell23_1557890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_1557890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557890 prefixEnd_1557890 := by exact prefixLift 1557890
  have htrace : WordTrace (prefixWord ++ tailWord_1557890) baseStart_1557890 baseEnd_1557890 := by
    simpa [prefixWord, tailWord_1557890, baseEnd_1557890] using wordTrace_append hprefix tailTrace_1557890
  have hstable : (prefixWord ++ tailWord_1557890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557890).length < 2 ^ (prefixWord ++ tailWord_1557890).sum := by decide
  have hdescent : baseEnd_1557890 < baseStart_1557890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557922 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 1, 7]
def baseStart_1557922 : Nat := 118140960795 + 1557922 * 2 ^ 59
def prefixEnd_1557922 : Nat := 4983230072969 + 3 ^ 40 * 1557922 * 2
def baseEnd_1557922 : Nat := 266654269404652952236751

theorem tailTrace_1557922 : CollatzResearch.WordTrace tailWord_1557922 prefixEnd_1557922 266654269404652952236751 := by
  unfold tailWord_1557922
  simp only [CollatzResearch.WordTrace]
  refine ⟨14205520865480535184911005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37881388974614760493096013 14205520865480535184911005)
  ·
    refine ⟨5327070324555200694341627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14205520865480535184911005 5327070324555200694341627)
    ·
      refine ⟨7990605486832801041512441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5327070324555200694341627 7990605486832801041512441)
      ·
        refine ⟨5992954115124600781134331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7990605486832801041512441 5992954115124600781134331)
        ·
          refine ⟨8989431172686901171701497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5992954115124600781134331 8989431172686901171701497)
          ·
            refine ⟨6742073379515175878776123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8989431172686901171701497 6742073379515175878776123)
            ·
              refine ⟨10113110069272763818164185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6742073379515175878776123 10113110069272763818164185)
              ·
                refine ⟨7584832551954572863623139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10113110069272763818164185 7584832551954572863623139)
                ·
                  refine ⟨11377248827931859295434709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7584832551954572863623139 11377248827931859295434709)
                  ·
                    refine ⟨266654269404652952236751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11377248827931859295434709 266654269404652952236751)
                    ·
                      rfl

theorem cell23_1557922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_1557922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557922 prefixEnd_1557922 := by exact prefixLift 1557922
  have htrace : WordTrace (prefixWord ++ tailWord_1557922) baseStart_1557922 baseEnd_1557922 := by
    simpa [prefixWord, tailWord_1557922, baseEnd_1557922] using wordTrace_append hprefix tailTrace_1557922
  have hstable : (prefixWord ++ tailWord_1557922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557922).length < 2 ^ (prefixWord ++ tailWord_1557922).sum := by decide
  have hdescent : baseEnd_1557922 < baseStart_1557922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557952 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 5, 4]
def baseStart_1557952 : Nat := 118140960795 + 1557952 * 2 ^ 59
def prefixEnd_1557952 : Nat := 4983230072969 + 3 ^ 40 * 1557952 * 2
def baseEnd_1557952 : Nat := 266659404211197913111705

theorem tailTrace_1557952 : CollatzResearch.WordTrace tailWord_1557952 prefixEnd_1557952 266659404211197913111705 := by
  unfold tailWord_1557952
  simp only [CollatzResearch.WordTrace]
  refine ⟨28411588825906727931618055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37882118434542303908824073 28411588825906727931618055)
  ·
    refine ⟨42617383238860091897427083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28411588825906727931618055 42617383238860091897427083)
    ·
      refine ⟨63926074858290137846140625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42617383238860091897427083 63926074858290137846140625)
      ·
        refine ⟨47944556143717603384605469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63926074858290137846140625 47944556143717603384605469)
        ·
          refine ⟨17979208553894101269227051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47944556143717603384605469 17979208553894101269227051)
          ·
            refine ⟨26968812830841151903840577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17979208553894101269227051 26968812830841151903840577)
            ·
              refine ⟨20226609623130863927880433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26968812830841151903840577 20226609623130863927880433)
              ·
                refine ⟨15169957217348147945910325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20226609623130863927880433 15169957217348147945910325)
                ·
                  refine ⟨1422183489126388869929093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15169957217348147945910325 1422183489126388869929093)
                  ·
                    refine ⟨266659404211197913111705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1422183489126388869929093 266659404211197913111705)
                    ·
                      rfl

theorem cell23_1557952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 5, 4].length) (baseStart_1557952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557952 prefixEnd_1557952 := by exact prefixLift 1557952
  have htrace : WordTrace (prefixWord ++ tailWord_1557952) baseStart_1557952 baseEnd_1557952 := by
    simpa [prefixWord, tailWord_1557952, baseEnd_1557952] using wordTrace_append hprefix tailTrace_1557952
  have hstable : (prefixWord ++ tailWord_1557952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557952).length < 2 ^ (prefixWord ++ tailWord_1557952).sum := by decide
  have hdescent : baseEnd_1557952 < baseStart_1557952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1557955 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 6]
def baseStart_1557955 : Nat := 118140960795 + 1557955 * 2 ^ 59
def prefixEnd_1557955 : Nat := 4983230072969 + 3 ^ 40 * 1557955 * 2
def baseEnd_1557955 : Nat := 799979753075557227597601

theorem tailTrace_1557955 : CollatzResearch.WordTrace tailWord_1557955 prefixEnd_1557955 799979753075557227597601 := by
  unfold tailWord_1557955
  simp only [CollatzResearch.WordTrace]
  refine ⟨56823287070802587375595319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37882191380535058250396879 56823287070802587375595319)
  ·
    refine ⟨85234930606203881063392979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56823287070802587375595319 85234930606203881063392979)
    ·
      refine ⟨127852395909305821595089469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85234930606203881063392979 127852395909305821595089469)
      ·
        refine ⟨47944648465989683098158551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127852395909305821595089469 47944648465989683098158551)
        ·
          refine ⟨71916972698984524647237827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47944648465989683098158551 71916972698984524647237827)
          ·
            refine ⟨107875459048476786970856741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71916972698984524647237827 107875459048476786970856741)
            ·
              refine ⟨20226648571589397557035639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107875459048476786970856741 20226648571589397557035639)
              ·
                refine ⟨30339972857384096335553459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20226648571589397557035639 30339972857384096335553459)
                ·
                  refine ⟨45509959286076144503330189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30339972857384096335553459 45509959286076144503330189)
                  ·
                    refine ⟨17066234732278554188748821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45509959286076144503330189 17066234732278554188748821)
                    ·
                      refine ⟨799979753075557227597601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17066234732278554188748821 799979753075557227597601)
                      ·
                        rfl

theorem cell23_1557955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_1557955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1557955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1557955 prefixEnd_1557955 := by exact prefixLift 1557955
  have htrace : WordTrace (prefixWord ++ tailWord_1557955) baseStart_1557955 baseEnd_1557955 := by
    simpa [prefixWord, tailWord_1557955, baseEnd_1557955] using wordTrace_append hprefix tailTrace_1557955
  have hstable : (prefixWord ++ tailWord_1557955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1557955).length < 2 ^ (prefixWord ++ tailWord_1557955).sum := by decide
  have hdescent : baseEnd_1557955 < baseStart_1557955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1557955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558019 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 4, 3, 2]
def baseStart_1558019 : Nat := 118140960795 + 1558019 * 2 ^ 59
def prefixEnd_1558019 : Nat := 4983230072969 + 3 ^ 40 * 1558019 * 2
def baseEnd_1558019 : Nat := 800012615837444977197307

theorem tailTrace_1558019 : CollatzResearch.WordTrace tailWord_1558019 prefixEnd_1558019 800012615837444977197307 := by
  unfold tailWord_1558019
  simp only [CollatzResearch.WordTrace]
  refine ⟨56825621342570726305925111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37883747561713817537283407 56825621342570726305925111)
  ·
    refine ⟨85238432013856089458887667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56825621342570726305925111 85238432013856089458887667)
    ·
      refine ⟨127857648020784134188331501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85238432013856089458887667 127857648020784134188331501)
      ·
        refine ⟨47946618007794050320624313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127857648020784134188331501 47946618007794050320624313)
        ·
          refine ⟨35959963505845537740468235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47946618007794050320624313 35959963505845537740468235)
          ·
            refine ⟨53939945258768306610702353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35959963505845537740468235 53939945258768306610702353)
            ·
              refine ⟨40454958944076229958026765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53939945258768306610702353 40454958944076229958026765)
              ·
                refine ⟨15170609604028586234260037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40454958944076229958026765 15170609604028586234260037)
                ·
                  refine ⟨2844489300755359918923757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15170609604028586234260037 2844489300755359918923757)
                  ·
                    refine ⟨1066683487783259969596409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2844489300755359918923757 1066683487783259969596409)
                    ·
                      refine ⟨800012615837444977197307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1066683487783259969596409 800012615837444977197307)
                      ·
                        rfl

theorem cell23_1558019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 3, 2].length) (baseStart_1558019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558019 prefixEnd_1558019 := by exact prefixLift 1558019
  have htrace : WordTrace (prefixWord ++ tailWord_1558019) baseStart_1558019 baseEnd_1558019 := by
    simpa [prefixWord, tailWord_1558019, baseEnd_1558019] using wordTrace_append hprefix tailTrace_1558019
  have hstable : (prefixWord ++ tailWord_1558019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558019).length < 2 ^ (prefixWord ++ tailWord_1558019).sum := by decide
  have hdescent : baseEnd_1558019 < baseStart_1558019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558049 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 3, 1, 4]
def baseStart_1558049 : Nat := 118140960795 + 1558049 * 2 ^ 59
def prefixEnd_1558049 : Nat := 4983230072969 + 3 ^ 40 * 1558049 * 2
def baseEnd_1558049 : Nat := 800028020257079859822169

theorem tailTrace_1558049 : CollatzResearch.WordTrace tailWord_1558049 prefixEnd_1558049 800028020257079859822169 := by
  unfold tailWord_1558049
  simp only [CollatzResearch.WordTrace]
  refine ⟨56826715532462041429517201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37884477021641360953011467 56826715532462041429517201)
  ·
    refine ⟨42620036649346531072137901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56826715532462041429517201 42620036649346531072137901)
    ·
      refine ⟨15982513743504949152051713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42620036649346531072137901 15982513743504949152051713)
      ·
        refine ⟨11986885307628711864038785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15982513743504949152051713 11986885307628711864038785)
        ·
          refine ⟨8990163980721533898029089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11986885307628711864038785 8990163980721533898029089)
          ·
            refine ⟨6742622985541150423521817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8990163980721533898029089 6742622985541150423521817)
            ·
              refine ⟨5056967239155862817641363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6742622985541150423521817 5056967239155862817641363)
              ·
                refine ⟨7585450858733794226462045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5056967239155862817641363 7585450858733794226462045)
                ·
                  refine ⟨2844544072025172834923267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7585450858733794226462045 2844544072025172834923267)
                  ·
                    refine ⟨4266816108037759252384901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2844544072025172834923267 4266816108037759252384901)
                    ·
                      refine ⟨800028020257079859822169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4266816108037759252384901 800028020257079859822169)
                      ·
                        rfl

theorem cell23_1558049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_1558049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558049 prefixEnd_1558049 := by exact prefixLift 1558049
  have htrace : WordTrace (prefixWord ++ tailWord_1558049) baseStart_1558049 baseEnd_1558049 := by
    simpa [prefixWord, tailWord_1558049, baseEnd_1558049] using wordTrace_append hprefix tailTrace_1558049
  have hstable : (prefixWord ++ tailWord_1558049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558049).length < 2 ^ (prefixWord ++ tailWord_1558049).sum := by decide
  have hdescent : baseEnd_1558049 < baseStart_1558049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558066 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2]
def baseStart_1558066 : Nat := 118140960795 + 1558066 * 2 ^ 59
def prefixEnd_1558066 : Nat := 4983230072969 + 3 ^ 40 * 1558066 * 2
def baseEnd_1558066 : Nat := 800036749428206293309591

theorem tailTrace_1558066 : CollatzResearch.WordTrace tailWord_1558066 prefixEnd_1558066 800036749428206293309591 := by
  unfold tailWord_1558066
  simp only [CollatzResearch.WordTrace]
  refine ⟨14206833893350113333221513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37884890382266968888590701 14206833893350113333221513)
  ·
    refine ⟨10655125420012584999916135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14206833893350113333221513 10655125420012584999916135)
    ·
      refine ⟨15982688130018877499874203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10655125420012584999916135 15982688130018877499874203)
      ·
        refine ⟨23974032195028316249811305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15982688130018877499874203 23974032195028316249811305)
        ·
          refine ⟨17980524146271237187358479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23974032195028316249811305 17980524146271237187358479)
          ·
            refine ⟨26970786219406855781037719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17980524146271237187358479 26970786219406855781037719)
            ·
              refine ⟨40456179329110283671556579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26970786219406855781037719 40456179329110283671556579)
              ·
                refine ⟨60684268993665425507334869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40456179329110283671556579 60684268993665425507334869)
                ·
                  refine ⟨1422287554539033410328161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 60684268993665425507334869 1422287554539033410328161)
                  ·
                    refine ⟨1066715665904275057746121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1422287554539033410328161 1066715665904275057746121)
                    ·
                      refine ⟨800036749428206293309591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1066715665904275057746121 800036749428206293309591)
                      ·
                        rfl

theorem cell23_1558066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2].length) (baseStart_1558066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558066 prefixEnd_1558066 := by exact prefixLift 1558066
  have htrace : WordTrace (prefixWord ++ tailWord_1558066) baseStart_1558066 baseEnd_1558066 := by
    simpa [prefixWord, tailWord_1558066, baseEnd_1558066] using wordTrace_append hprefix tailTrace_1558066
  have hstable : (prefixWord ++ tailWord_1558066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558066).length < 2 ^ (prefixWord ++ tailWord_1558066).sum := by decide
  have hdescent : baseEnd_1558066 < baseStart_1558066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558072 : List Nat := [2, 1, 2, 1, 4, 3, 10]
def baseStart_1558072 : Nat := 118140960795 + 1558072 * 2 ^ 59
def prefixEnd_1558072 : Nat := 4983230072969 + 3 ^ 40 * 1558072 * 2
def baseEnd_1558072 : Nat := 9877034942125102096723

theorem tailTrace_1558072 : CollatzResearch.WordTrace tailWord_1558072 prefixEnd_1558072 9877034942125102096723 := by
  unfold tailWord_1558072
  simp only [CollatzResearch.WordTrace]
  refine ⟨28413777205689358178802235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37885036274252477571736313 28413777205689358178802235)
  ·
    refine ⟨42620665808534037268203353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28413777205689358178802235 42620665808534037268203353)
    ·
      refine ⟨31965499356400527951152515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42620665808534037268203353 31965499356400527951152515)
      ·
        refine ⟨47948249034600791926728773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31965499356400527951152515 47948249034600791926728773)
        ·
          refine ⟨8990296693987648486261645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47948249034600791926728773 8990296693987648486261645)
          ·
            refine ⟨3371361260245368182348117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8990296693987648486261645 3371361260245368182348117)
            ·
              refine ⟨9877034942125102096723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3371361260245368182348117 9877034942125102096723)
              ·
                rfl

theorem cell23_1558072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 10].length) (baseStart_1558072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558072 prefixEnd_1558072 := by exact prefixLift 1558072
  have htrace : WordTrace (prefixWord ++ tailWord_1558072) baseStart_1558072 baseEnd_1558072 := by
    simpa [prefixWord, tailWord_1558072, baseEnd_1558072] using wordTrace_append hprefix tailTrace_1558072
  have hstable : (prefixWord ++ tailWord_1558072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558072).length < 2 ^ (prefixWord ++ tailWord_1558072).sum := by decide
  have hdescent : baseEnd_1558072 < baseStart_1558072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558076 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 4, 4]
def baseStart_1558076 : Nat := 118140960795 + 1558076 * 2 ^ 59
def prefixEnd_1558076 : Nat := 4983230072969 + 3 ^ 40 * 1558076 * 2
def baseEnd_1558076 : Nat := 266680628078250418061515

theorem tailTrace_1558076 : CollatzResearch.WordTrace tailWord_1558076 prefixEnd_1558076 266680628078250418061515 := by
  unfold tailWord_1558076
  simp only [CollatzResearch.WordTrace]
  refine ⟨28413850151682112520375041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37885133535576150027166721 28413850151682112520375041)
  ·
    refine ⟨21310387613761584390281281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28413850151682112520375041 21310387613761584390281281)
    ·
      refine ⟨15982790710321188292710961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21310387613761584390281281 15982790710321188292710961)
      ·
        refine ⟨11987093032740891219533221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15982790710321188292710961 11987093032740891219533221)
        ·
          refine ⟨2247579943638917103662479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11987093032740891219533221 2247579943638917103662479)
          ·
            refine ⟨3371369915458375655493719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2247579943638917103662479 3371369915458375655493719)
            ·
              refine ⟨5057054873187563483240579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3371369915458375655493719 5057054873187563483240579)
              ·
                refine ⟨7585582309781345224860869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5057054873187563483240579 7585582309781345224860869)
                ·
                  refine ⟨1422296683084002229661413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7585582309781345224860869 1422296683084002229661413)
                  ·
                    refine ⟨266680628078250418061515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1422296683084002229661413 266680628078250418061515)
                    ·
                      rfl

theorem cell23_1558076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_1558076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558076 prefixEnd_1558076 := by exact prefixLift 1558076
  have htrace : WordTrace (prefixWord ++ tailWord_1558076) baseStart_1558076 baseEnd_1558076 := by
    simpa [prefixWord, tailWord_1558076, baseEnd_1558076] using wordTrace_append hprefix tailTrace_1558076
  have hstable : (prefixWord ++ tailWord_1558076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558076).length < 2 ^ (prefixWord ++ tailWord_1558076).sum := by decide
  have hdescent : baseEnd_1558076 < baseStart_1558076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558093 : List Nat := [1, 6, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_1558093 : Nat := 118140960795 + 1558093 * 2 ^ 59
def prefixEnd_1558093 : Nat := 4983230072969 + 3 ^ 40 * 1558093 * 2
def baseEnd_1558093 : Nat := 266683537801959229223989

theorem tailTrace_1558093 : CollatzResearch.WordTrace tailWord_1558093 prefixEnd_1558093 266683537801959229223989 := by
  unfold tailWord_1558093
  simp only [CollatzResearch.WordTrace]
  refine ⟨56828320344302636944118933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37885546896201757962745955 56828320344302636944118933)
  ·
    refine ⟨2663827516139186106755575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56828320344302636944118933 2663827516139186106755575)
    ·
      refine ⟨3995741274208779160133363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2663827516139186106755575 3995741274208779160133363)
      ·
        refine ⟨5993611911313168740200045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3995741274208779160133363 5993611911313168740200045)
        ·
          refine ⟨2247604466742438277575017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5993611911313168740200045 2247604466742438277575017)
          ·
            refine ⟨1685703350056828708181263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2247604466742438277575017 1685703350056828708181263)
            ·
              refine ⟨2528555025085243062271895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1685703350056828708181263 2528555025085243062271895)
              ·
                refine ⟨3792832537627864593407843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2528555025085243062271895 3792832537627864593407843)
                ·
                  refine ⟨5689248806441796890111765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3792832537627864593407843 5689248806441796890111765)
                  ·
                    refine ⟨266683537801959229223989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5689248806441796890111765 266683537801959229223989)
                    ·
                      rfl

theorem cell23_1558093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_1558093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558093 prefixEnd_1558093 := by exact prefixLift 1558093
  have htrace : WordTrace (prefixWord ++ tailWord_1558093) baseStart_1558093 baseEnd_1558093 := by
    simpa [prefixWord, tailWord_1558093, baseEnd_1558093] using wordTrace_append hprefix tailTrace_1558093
  have hstable : (prefixWord ++ tailWord_1558093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558093).length < 2 ^ (prefixWord ++ tailWord_1558093).sum := by decide
  have hdescent : baseEnd_1558093 < baseStart_1558093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558116 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 4, 1, 3]
def baseStart_1558116 : Nat := 118140960795 + 1558116 * 2 ^ 59
def prefixEnd_1558116 : Nat := 4983230072969 + 3 ^ 40 * 1558116 * 2
def baseEnd_1558116 : Nat := 800062423460931097684361

theorem tailTrace_1558116 : CollatzResearch.WordTrace tailWord_1558116 prefixEnd_1558116 800062423460931097684361 := by
  unfold tailWord_1558116
  simp only [CollatzResearch.WordTrace]
  refine ⟨28414579611609655936103101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37886106148812874581470801 28414579611609655936103101)
  ·
    refine ⟨10655467354353620976038663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28414579611609655936103101 10655467354353620976038663)
    ·
      refine ⟨15983201031530431464057995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10655467354353620976038663 15983201031530431464057995)
      ·
        refine ⟨23974801547295647196086993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15983201031530431464057995 23974801547295647196086993)
        ·
          refine ⟨17981101160471735397065245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23974801547295647196086993 17981101160471735397065245)
          ·
            refine ⟨6742912935176900773899467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17981101160471735397065245 6742912935176900773899467)
            ·
              refine ⟨10114369402765351160849201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6742912935176900773899467 10114369402765351160849201)
              ·
                refine ⟨7585777052074013370636901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10114369402765351160849201 7585777052074013370636901)
                ·
                  refine ⟨1422333197263877506994419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7585777052074013370636901 1422333197263877506994419)
                  ·
                    refine ⟨2133499795895816260491629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1422333197263877506994419 2133499795895816260491629)
                    ·
                      refine ⟨800062423460931097684361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2133499795895816260491629 800062423460931097684361)
                      ·
                        rfl

theorem cell23_1558116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_1558116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558116 prefixEnd_1558116 := by exact prefixLift 1558116
  have htrace : WordTrace (prefixWord ++ tailWord_1558116) baseStart_1558116 baseEnd_1558116 := by
    simpa [prefixWord, tailWord_1558116, baseEnd_1558116] using wordTrace_append hprefix tailTrace_1558116
  have hstable : (prefixWord ++ tailWord_1558116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558116).length < 2 ^ (prefixWord ++ tailWord_1558116).sum := by decide
  have hdescent : baseEnd_1558116 < baseStart_1558116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558117 : List Nat := [1, 3, 1, 3, 3, 3, 1, 3, 1, 2, 2]
def baseStart_1558117 : Nat := 118140960795 + 1558117 * 2 ^ 59
def prefixEnd_1558117 : Nat := 4983230072969 + 3 ^ 40 * 1558117 * 2
def baseEnd_1558117 : Nat := 800062936941585593771857

theorem tailTrace_1558117 : CollatzResearch.WordTrace tailWord_1558117 prefixEnd_1558117 800062936941585593771857 := by
  unfold tailWord_1558117
  simp only [CollatzResearch.WordTrace]
  refine ⟨56829195696215689042992605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37886130464143792695328403 56829195696215689042992605)
  ·
    refine ⟨21310948386080883391122227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56829195696215689042992605 21310948386080883391122227)
    ·
      refine ⟨31966422579121325086683341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21310948386080883391122227 31966422579121325086683341)
      ·
        refine ⟨11987408467170496907506253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31966422579121325086683341 11987408467170496907506253)
        ·
          refine ⟨4495278175188936340314845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11987408467170496907506253 4495278175188936340314845)
          ·
            refine ⟨1685729315695851127618067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4495278175188936340314845 1685729315695851127618067)
            ·
              refine ⟨2528593973543776691427101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1685729315695851127618067 2528593973543776691427101)
              ·
                refine ⟨948222740078916259285163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2528593973543776691427101 948222740078916259285163)
                ·
                  refine ⟨1422334110118374388927745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 948222740078916259285163 1422334110118374388927745)
                  ·
                    refine ⟨1066750582588780791695809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1422334110118374388927745 1066750582588780791695809)
                    ·
                      refine ⟨800062936941585593771857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1066750582588780791695809 800062936941585593771857)
                      ·
                        rfl

theorem cell23_1558117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_1558117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558117 prefixEnd_1558117 := by exact prefixLift 1558117
  have htrace : WordTrace (prefixWord ++ tailWord_1558117) baseStart_1558117 baseEnd_1558117 := by
    simpa [prefixWord, tailWord_1558117, baseEnd_1558117] using wordTrace_append hprefix tailTrace_1558117
  have hstable : (prefixWord ++ tailWord_1558117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558117).length < 2 ^ (prefixWord ++ tailWord_1558117).sum := by decide
  have hdescent : baseEnd_1558117 < baseStart_1558117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558133 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_1558133 : Nat := 118140960795 + 1558133 * 2 ^ 59
def prefixEnd_1558133 : Nat := 4983230072969 + 3 ^ 40 * 1558133 * 2
def baseEnd_1558133 : Nat := 800071152632057531171783

theorem tailTrace_1558133 : CollatzResearch.WordTrace tailWord_1558133 prefixEnd_1558133 800071152632057531171783 := by
  unfold tailWord_1558133
  simp only [CollatzResearch.WordTrace]
  refine ⟨56829779264157723775575053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37886519509438482517050035 56829779264157723775575053)
  ·
    refine ⟨21311167224059146415840645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56829779264157723775575053 21311167224059146415840645)
    ·
      refine ⟨3995843854511089952970121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21311167224059146415840645 3995843854511089952970121)
      ·
        refine ⟨2996882890883317464727591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3995843854511089952970121 2996882890883317464727591)
        ·
          refine ⟨4495324336324976197091387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2996882890883317464727591 4495324336324976197091387)
          ·
            refine ⟨6742986504487464295637081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4495324336324976197091387 6742986504487464295637081)
            ·
              refine ⟨5057239878365598221727811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6742986504487464295637081 5057239878365598221727811)
              ·
                refine ⟨7585859817548397332591717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5057239878365598221727811 7585859817548397332591717)
                ·
                  refine ⟨1422348715790324499860947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7585859817548397332591717 1422348715790324499860947)
                  ·
                    refine ⟨2133523073685486749791421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1422348715790324499860947 2133523073685486749791421)
                    ·
                      refine ⟨800071152632057531171783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2133523073685486749791421 800071152632057531171783)
                      ·
                        rfl

theorem cell23_1558133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_1558133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558133 prefixEnd_1558133 := by exact prefixLift 1558133
  have htrace : WordTrace (prefixWord ++ tailWord_1558133) baseStart_1558133 baseEnd_1558133 := by
    simpa [prefixWord, tailWord_1558133, baseEnd_1558133] using wordTrace_append hprefix tailTrace_1558133
  have hstable : (prefixWord ++ tailWord_1558133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558133).length < 2 ^ (prefixWord ++ tailWord_1558133).sum := by decide
  have hdescent : baseEnd_1558133 < baseStart_1558133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558134 : List Nat := [5, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2]
def baseStart_1558134 : Nat := 118140960795 + 1558134 * 2 ^ 59
def prefixEnd_1558134 : Nat := 4983230072969 + 3 ^ 40 * 1558134 * 2
def baseEnd_1558134 : Nat := 800071666112712027259279

theorem tailTrace_1558134 : CollatzResearch.WordTrace tailWord_1558134 prefixEnd_1558134 800071666112712027259279 := by
  unfold tailWord_1558134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3551863483572131309147591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37886543824769400630907637 3551863483572131309147591)
  ·
    refine ⟨5327795225358196963721387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3551863483572131309147591 5327795225358196963721387)
    ·
      refine ⟨7991692838037295445582081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5327795225358196963721387 7991692838037295445582081)
      ·
        refine ⟨5993769628527971584186561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7991692838037295445582081 5993769628527971584186561)
        ·
          refine ⟨4495327221395978688139921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5993769628527971584186561 4495327221395978688139921)
          ·
            refine ⟨3371495416046984016104941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4495327221395978688139921 3371495416046984016104941)
            ·
              refine ⟨1264310781017619006039353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3371495416046984016104941 1264310781017619006039353)
              ·
                refine ⟨948233085763214254529515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1264310781017619006039353 948233085763214254529515)
                ·
                  refine ⟨1422349628644821381794273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 948233085763214254529515 1422349628644821381794273)
                  ·
                    refine ⟨1066762221483616036345705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1422349628644821381794273 1066762221483616036345705)
                    ·
                      refine ⟨800071666112712027259279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1066762221483616036345705 800071666112712027259279)
                      ·
                        rfl

theorem cell23_1558134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_1558134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558134 prefixEnd_1558134 := by exact prefixLift 1558134
  have htrace : WordTrace (prefixWord ++ tailWord_1558134) baseStart_1558134 baseEnd_1558134 := by
    simpa [prefixWord, tailWord_1558134, baseEnd_1558134] using wordTrace_append hprefix tailTrace_1558134
  have hstable : (prefixWord ++ tailWord_1558134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558134).length < 2 ^ (prefixWord ++ tailWord_1558134).sum := by decide
  have hdescent : baseEnd_1558134 < baseStart_1558134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558156 : List Nat := [2, 2, 1, 2, 1, 1, 4, 3, 1, 4, 2]
def baseStart_1558156 : Nat := 118140960795 + 1558156 * 2 ^ 59
def prefixEnd_1558156 : Nat := 4983230072969 + 3 ^ 40 * 1558156 * 2
def baseEnd_1558156 : Nat := 800082962687110941184177

theorem tailTrace_1558156 : CollatzResearch.WordTrace tailWord_1558156 prefixEnd_1558156 800082962687110941184177 := by
  unfold tailWord_1558156
  simp only [CollatzResearch.WordTrace]
  refine ⟨28415309071537199351831161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37887078762049599135774881 28415309071537199351831161)
  ·
    refine ⟨21311481803652899513873371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28415309071537199351831161 21311481803652899513873371)
    ·
      refine ⟨31967222705479349270810057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21311481803652899513873371 31967222705479349270810057)
      ·
        refine ⟨23975417029109511953107543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31967222705479349270810057 23975417029109511953107543)
        ·
          refine ⟨35963125543664267929661315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23975417029109511953107543 35963125543664267929661315)
          ·
            refine ⟨53944688315496401894491973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35963125543664267929661315 53944688315496401894491973)
            ·
              refine ⟨10114629059155575355217245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53944688315496401894491973 10114629059155575355217245)
              ·
                refine ⟨3792985897183340758206467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10114629059155575355217245 3792985897183340758206467)
                ·
                  refine ⟨5689478845775011137309701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3792985897183340758206467 5689478845775011137309701)
                  ·
                    refine ⟨1066777283582814588245569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5689478845775011137309701 1066777283582814588245569)
                    ·
                      refine ⟨800082962687110941184177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1066777283582814588245569 800082962687110941184177)
                      ·
                        rfl

theorem cell23_1558156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 1, 4, 2].length) (baseStart_1558156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558156 prefixEnd_1558156 := by exact prefixLift 1558156
  have htrace : WordTrace (prefixWord ++ tailWord_1558156) baseStart_1558156 baseEnd_1558156 := by
    simpa [prefixWord, tailWord_1558156, baseEnd_1558156] using wordTrace_append hprefix tailTrace_1558156
  have hstable : (prefixWord ++ tailWord_1558156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558156).length < 2 ^ (prefixWord ++ tailWord_1558156).sum := by decide
  have hdescent : baseEnd_1558156 < baseStart_1558156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558184 : List Nat := [2, 1, 7, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_1558184 : Nat := 118140960795 + 1558184 * 2 ^ 59
def prefixEnd_1558184 : Nat := 4983230072969 + 3 ^ 40 * 1558184 * 2
def baseEnd_1558184 : Nat := 800097340145436831634049

theorem tailTrace_1558184 : CollatzResearch.WordTrace tailWord_1558184 prefixEnd_1558184 800097340145436831634049 := by
  unfold tailWord_1558184
  simp only [CollatzResearch.WordTrace]
  refine ⟨28415819693486479742840803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37887759591315306323787737 28415819693486479742840803)
  ·
    refine ⟨42623729540229719614261205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28415819693486479742840803 42623729540229719614261205)
    ·
      refine ⟨998993661099134053459247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 42623729540229719614261205 998993661099134053459247)
      ·
        refine ⟨1498490491648701080188871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 998993661099134053459247 1498490491648701080188871)
        ·
          refine ⟨2247735737473051620283307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1498490491648701080188871 2247735737473051620283307)
          ·
            refine ⟨3371603606209577430424961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2247735737473051620283307 3371603606209577430424961)
            ·
              refine ⟨2528702704657183072818721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3371603606209577430424961 2528702704657183072818721)
              ·
                refine ⟨1896527028492887304614041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2528702704657183072818721 1896527028492887304614041)
                ·
                  refine ⟨1422395271369665478460531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1896527028492887304614041 1422395271369665478460531)
                  ·
                    refine ⟨2133592907054498217690797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1422395271369665478460531 2133592907054498217690797)
                    ·
                      refine ⟨800097340145436831634049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2133592907054498217690797 800097340145436831634049)
                      ·
                        rfl

theorem cell23_1558184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_1558184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558184 prefixEnd_1558184 := by exact prefixLift 1558184
  have htrace : WordTrace (prefixWord ++ tailWord_1558184) baseStart_1558184 baseEnd_1558184 := by
    simpa [prefixWord, tailWord_1558184, baseEnd_1558184] using wordTrace_append hprefix tailTrace_1558184
  have hstable : (prefixWord ++ tailWord_1558184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558184).length < 2 ^ (prefixWord ++ tailWord_1558184).sum := by decide
  have hdescent : baseEnd_1558184 < baseStart_1558184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558206 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3]
def baseStart_1558206 : Nat := 118140960795 + 1558206 * 2 ^ 59
def prefixEnd_1558206 : Nat := 4983230072969 + 3 ^ 40 * 1558206 * 2
def baseEnd_1558206 : Nat := 800108636719835745558947

theorem tailTrace_1558206 : CollatzResearch.WordTrace tailWord_1558206 prefixEnd_1558206 800108636719835745558947 := by
  unfold tailWord_1558206
  simp only [CollatzResearch.WordTrace]
  refine ⟨7104055224111657155372809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37888294528595504828654981 7104055224111657155372809)
  ·
    refine ⟨5328041418083742866529607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7104055224111657155372809 5328041418083742866529607)
    ·
      refine ⟨7992062127125614299794411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5328041418083742866529607 7992062127125614299794411)
      ·
        refine ⟨11988093190688421449691617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7992062127125614299794411 11988093190688421449691617)
        ·
          refine ⟨8991069893016316087268713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11988093190688421449691617 8991069893016316087268713)
          ·
            refine ⟨6743302419762237065451535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8991069893016316087268713 6743302419762237065451535)
            ·
              refine ⟨10114953629643355598177303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6743302419762237065451535 10114953629643355598177303)
              ·
                refine ⟨15172430444465033397265955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10114953629643355598177303 15172430444465033397265955)
                ·
                  refine ⟨22758645666697550095898933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15172430444465033397265955 22758645666697550095898933)
                  ·
                    refine ⟨2133623031252895321490525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22758645666697550095898933 2133623031252895321490525)
                    ·
                      refine ⟨800108636719835745558947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2133623031252895321490525 800108636719835745558947)
                      ·
                        rfl

theorem cell23_1558206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_1558206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558206 prefixEnd_1558206 := by exact prefixLift 1558206
  have htrace : WordTrace (prefixWord ++ tailWord_1558206) baseStart_1558206 baseEnd_1558206 := by
    simpa [prefixWord, tailWord_1558206, baseEnd_1558206] using wordTrace_append hprefix tailTrace_1558206
  have hstable : (prefixWord ++ tailWord_1558206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558206).length < 2 ^ (prefixWord ++ tailWord_1558206).sum := by decide
  have hdescent : baseEnd_1558206 < baseStart_1558206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558216 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 2, 5, 2]
def baseStart_1558216 : Nat := 118140960795 + 1558216 * 2 ^ 59
def prefixEnd_1558216 : Nat := 4983230072969 + 3 ^ 40 * 1558216 * 2
def baseEnd_1558216 : Nat := 800113771526380706433901

theorem tailTrace_1558216 : CollatzResearch.WordTrace tailWord_1558216 prefixEnd_1558216 800113771526380706433901 := by
  unfold tailWord_1558216
  simp only [CollatzResearch.WordTrace]
  refine ⟨28416403261428514475423251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37888537681904685967231001 28416403261428514475423251)
  ·
    refine ⟨42624604892142771713134877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28416403261428514475423251 42624604892142771713134877)
    ·
      refine ⟨15984226834553539392425579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42624604892142771713134877 15984226834553539392425579)
      ·
        refine ⟨23976340251830309088638369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15984226834553539392425579 23976340251830309088638369)
        ·
          refine ⟨17982255188872731816478777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23976340251830309088638369 17982255188872731816478777)
          ·
            refine ⟨13486691391654548862359083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17982255188872731816478777 13486691391654548862359083)
            ·
              refine ⟨20230037087481823293538625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13486691391654548862359083 20230037087481823293538625)
              ·
                refine ⟨15172527815611367470153969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20230037087481823293538625 15172527815611367470153969)
                ·
                  refine ⟨11379395861708525602615477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15172527815611367470153969 11379395861708525602615477)
                  ·
                    refine ⟨1066818362035174275245201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11379395861708525602615477 1066818362035174275245201)
                    ·
                      refine ⟨800113771526380706433901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1066818362035174275245201 800113771526380706433901)
                      ·
                        rfl

theorem cell23_1558216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 2, 5, 2].length) (baseStart_1558216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558216 prefixEnd_1558216 := by exact prefixLift 1558216
  have htrace : WordTrace (prefixWord ++ tailWord_1558216) baseStart_1558216 baseEnd_1558216 := by
    simpa [prefixWord, tailWord_1558216, baseEnd_1558216] using wordTrace_append hprefix tailTrace_1558216
  have hstable : (prefixWord ++ tailWord_1558216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558216).length < 2 ^ (prefixWord ++ tailWord_1558216).sum := by decide
  have hdescent : baseEnd_1558216 < baseStart_1558216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558226 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 1, 7]
def baseStart_1558226 : Nat := 118140960795 + 1558226 * 2 ^ 59
def prefixEnd_1558226 : Nat := 4983230072969 + 3 ^ 40 * 1558226 * 2
def baseEnd_1558226 : Nat := 266706302110975222436285

theorem tailTrace_1558226 : CollatzResearch.WordTrace tailWord_1558226 prefixEnd_1558226 266706302110975222436285 := by
  unfold tailWord_1558226
  simp only [CollatzResearch.WordTrace]
  refine ⟨14208292813205200164677633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37888780835213867105807021 14208292813205200164677633)
  ·
    refine ⟨10656219609903900123508225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14208292813205200164677633 10656219609903900123508225)
    ·
      refine ⟨7992164707427925092631169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10656219609903900123508225 7992164707427925092631169)
      ·
        refine ⟨5994123530570943819473377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7992164707427925092631169 5994123530570943819473377)
        ·
          refine ⟨4495592647928207864605033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5994123530570943819473377 4495592647928207864605033)
          ·
            refine ⟨3371694485946155898453775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4495592647928207864605033 3371694485946155898453775)
            ·
              refine ⟨5057541728919233847680663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3371694485946155898453775 5057541728919233847680663)
              ·
                refine ⟨7586312593378850771520995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5057541728919233847680663 7586312593378850771520995)
                ·
                  refine ⟨11379468890068276157281493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7586312593378850771520995 11379468890068276157281493)
                  ·
                    refine ⟨266706302110975222436285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11379468890068276157281493 266706302110975222436285)
                    ·
                      rfl

theorem cell23_1558226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_1558226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558226 prefixEnd_1558226 := by exact prefixLift 1558226
  have htrace : WordTrace (prefixWord ++ tailWord_1558226) baseStart_1558226 baseEnd_1558226 := by
    simpa [prefixWord, tailWord_1558226, baseEnd_1558226] using wordTrace_append hprefix tailTrace_1558226
  have hstable : (prefixWord ++ tailWord_1558226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558226).length < 2 ^ (prefixWord ++ tailWord_1558226).sum := by decide
  have hdescent : baseEnd_1558226 < baseStart_1558226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558333 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 3, 5]
def baseStart_1558333 : Nat := 118140960795 + 1558333 * 2 ^ 59
def prefixEnd_1558333 : Nat := 4983230072969 + 3 ^ 40 * 1558333 * 2
def baseEnd_1558333 : Nat := 266724616254318916223621

theorem tailTrace_1558333 : CollatzResearch.WordTrace tailWord_1558333 prefixEnd_1558333 266724616254318916223621 := by
  unfold tailWord_1558333
  simp only [CollatzResearch.WordTrace]
  refine ⟨56837073863433157932855653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37891382575622105288570435 56837073863433157932855653)
  ·
    refine ⟨10656951349393717112410435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56837073863433157932855653 10656951349393717112410435)
    ·
      refine ⟨15985427024090575668615653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10656951349393717112410435 15985427024090575668615653)
      ·
        refine ⟨2997267567016982937865435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15985427024090575668615653 2997267567016982937865435)
        ·
          refine ⟨4495901350525474406798153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2997267567016982937865435 4495901350525474406798153)
          ·
            refine ⟨3371926012894105805098615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4495901350525474406798153 3371926012894105805098615)
            ·
              refine ⟨5057889019341158707647923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3371926012894105805098615 5057889019341158707647923)
              ·
                refine ⟨7586833529011738061471885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5057889019341158707647923 7586833529011738061471885)
                ·
                  refine ⟨2845062573379401773051957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7586833529011738061471885 2845062573379401773051957)
                  ·
                    refine ⟨266724616254318916223621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2845062573379401773051957 266724616254318916223621)
                    ·
                      rfl

theorem cell23_1558333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_1558333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558333 prefixEnd_1558333 := by exact prefixLift 1558333
  have htrace : WordTrace (prefixWord ++ tailWord_1558333) baseStart_1558333 baseEnd_1558333 := by
    simpa [prefixWord, tailWord_1558333, baseEnd_1558333] using wordTrace_append hprefix tailTrace_1558333
  have hstable : (prefixWord ++ tailWord_1558333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558333).length < 2 ^ (prefixWord ++ tailWord_1558333).sum := by decide
  have hdescent : baseEnd_1558333 < baseStart_1558333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558346 : List Nat := [3, 1, 2, 1, 1, 1, 5, 2, 1, 6]
def baseStart_1558346 : Nat := 118140960795 + 1558346 * 2 ^ 59
def prefixEnd_1558346 : Nat := 4983230072969 + 3 ^ 40 * 1558346 * 2
def baseEnd_1558346 : Nat := 266726841337155065936101

theorem tailTrace_1558346 : CollatzResearch.WordTrace tailWord_1558346 prefixEnd_1558346 266726841337155065936101 := by
  unfold tailWord_1558346
  simp only [CollatzResearch.WordTrace]
  refine ⟨14209387003096515288269723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37891698674924040768719261 14209387003096515288269723)
  ·
    refine ⟨21314080504644772932404585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14209387003096515288269723 21314080504644772932404585)
    ·
      refine ⟨15985560378483579699303439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21314080504644772932404585 15985560378483579699303439)
      ·
        refine ⟨23978340567725369548955159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15985560378483579699303439 23978340567725369548955159)
        ·
          refine ⟨35967510851588054323432739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23978340567725369548955159 35967510851588054323432739)
          ·
            refine ⟨53951266277382081485149109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35967510851588054323432739 53951266277382081485149109)
            ·
              refine ⟨5057931213504570139232729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53951266277382081485149109 5057931213504570139232729)
              ·
                refine ⟨3793448410128427604424547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5057931213504570139232729 3793448410128427604424547)
                ·
                  refine ⟨5690172615192641406636821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3793448410128427604424547 5690172615192641406636821)
                  ·
                    refine ⟨266726841337155065936101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5690172615192641406636821 266726841337155065936101)
                    ·
                      rfl

theorem cell23_1558346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_1558346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558346 prefixEnd_1558346 := by exact prefixLift 1558346
  have htrace : WordTrace (prefixWord ++ tailWord_1558346) baseStart_1558346 baseEnd_1558346 := by
    simpa [prefixWord, tailWord_1558346, baseEnd_1558346] using wordTrace_append hprefix tailTrace_1558346
  have hstable : (prefixWord ++ tailWord_1558346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558346).length < 2 ^ (prefixWord ++ tailWord_1558346).sum := by decide
  have hdescent : baseEnd_1558346 < baseStart_1558346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558359 : List Nat := [1, 1, 3, 2, 16]
def baseStart_1558359 : Nat := 118140960795 + 1558359 * 2 ^ 59
def prefixEnd_1558359 : Nat := 4983230072969 + 3 ^ 40 * 1558359 * 2
def baseEnd_1558359 : Nat := 1097650479094614056167

theorem tailTrace_1558359 : CollatzResearch.WordTrace tailWord_1558359 prefixEnd_1558359 1097650479094614056167 := by
  unfold tailWord_1558359
  simp only [CollatzResearch.WordTrace]
  refine ⟨56838022161338964373302131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37892014774225976248868087 56838022161338964373302131)
  ·
    refine ⟨85257033242008446559953197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56838022161338964373302131 85257033242008446559953197)
    ·
      refine ⟨31971387465753167459982449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85257033242008446559953197 31971387465753167459982449)
      ·
        refine ⟨23978540599314875594986837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31971387465753167459982449 23978540599314875594986837)
        ·
          refine ⟨1097650479094614056167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 23978540599314875594986837 1097650479094614056167)
          ·
            rfl

theorem cell23_1558359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 16].length) (baseStart_1558359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558359 prefixEnd_1558359 := by exact prefixLift 1558359
  have htrace : WordTrace (prefixWord ++ tailWord_1558359) baseStart_1558359 baseEnd_1558359 := by
    simpa [prefixWord, tailWord_1558359, baseEnd_1558359] using wordTrace_append hprefix tailTrace_1558359
  have hstable : (prefixWord ++ tailWord_1558359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558359).length < 2 ^ (prefixWord ++ tailWord_1558359).sum := by decide
  have hdescent : baseEnd_1558359 < baseStart_1558359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558364 : List Nat := [2, 2, 4, 2, 2, 1, 1, 4, 1, 1, 3]
def baseStart_1558364 : Nat := 118140960795 + 1558364 * 2 ^ 59
def prefixEnd_1558364 : Nat := 4983230072969 + 3 ^ 40 * 1558364 * 2
def baseEnd_1558364 : Nat := 800189766663246127383221

theorem tailTrace_1558364 : CollatzResearch.WordTrace tailWord_1558364 prefixEnd_1558364 800189766663246127383221 := by
  unfold tailWord_1558364
  simp only [CollatzResearch.WordTrace]
  refine ⟨28419102263160425113617073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37892136350880566818156097 28419102263160425113617073)
  ·
    refine ⟨21314326697370318835212805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28419102263160425113617073 21314326697370318835212805)
    ·
      refine ⟨3996436255756934781602401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21314326697370318835212805 3996436255756934781602401)
      ·
        refine ⟨2997327191817701086201801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3996436255756934781602401 2997327191817701086201801)
        ·
          refine ⟨2247995393863275814651351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2997327191817701086201801 2247995393863275814651351)
          ·
            refine ⟨3371993090794913721977027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2247995393863275814651351 3371993090794913721977027)
            ·
              refine ⟨5057989636192370582965541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3371993090794913721977027 5057989636192370582965541)
              ·
                refine ⟨948373056786069484306039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5057989636192370582965541 948373056786069484306039)
                ·
                  refine ⟨1422559585179104226459059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 948373056786069484306039 1422559585179104226459059)
                  ·
                    refine ⟨2133839377768656339688589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1422559585179104226459059 2133839377768656339688589)
                    ·
                      refine ⟨800189766663246127383221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2133839377768656339688589 800189766663246127383221)
                      ·
                        rfl

theorem cell23_1558364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_1558364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558364 prefixEnd_1558364 := by exact prefixLift 1558364
  have htrace : WordTrace (prefixWord ++ tailWord_1558364) baseStart_1558364 baseEnd_1558364 := by
    simpa [prefixWord, tailWord_1558364, baseEnd_1558364] using wordTrace_append hprefix tailTrace_1558364
  have hstable : (prefixWord ++ tailWord_1558364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558364).length < 2 ^ (prefixWord ++ tailWord_1558364).sum := by decide
  have hdescent : baseEnd_1558364 < baseStart_1558364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558403 : List Nat := [1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 3]
def baseStart_1558403 : Nat := 118140960795 + 1558403 * 2 ^ 59
def prefixEnd_1558403 : Nat := 4983230072969 + 3 ^ 40 * 1558403 * 2
def baseEnd_1558403 : Nat := 800209792408771474795541

theorem tailTrace_1558403 : CollatzResearch.WordTrace tailWord_1558403 prefixEnd_1558403 800209792408771474795541 := by
  unfold tailWord_1558403
  simp only [CollatzResearch.WordTrace]
  refine ⟨56839626973179559887903863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37893084648786373258602575 56839626973179559887903863)
  ·
    refine ⟨85259440459769339831855795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56839626973179559887903863 85259440459769339831855795)
    ·
      refine ⟨127889160689654009747783693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85259440459769339831855795 127889160689654009747783693)
      ·
        refine ⟨47958435258620253655418885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127889160689654009747783693 47958435258620253655418885)
        ·
          refine ⟨8992206610991297560391041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47958435258620253655418885 8992206610991297560391041)
          ·
            refine ⟨6744154958243473170293281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8992206610991297560391041 6744154958243473170293281)
            ·
              refine ⟨5058116218682604877719961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6744154958243473170293281 5058116218682604877719961)
              ·
                refine ⟨3793587164011953658289971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5058116218682604877719961 3793587164011953658289971)
                ·
                  refine ⟨5690380746017930487434957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3793587164011953658289971 5690380746017930487434957)
                  ·
                    refine ⟨2133892779756723932788109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5690380746017930487434957 2133892779756723932788109)
                    ·
                      refine ⟨800209792408771474795541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2133892779756723932788109 800209792408771474795541)
                      ·
                        rfl

theorem cell23_1558403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 3].length) (baseStart_1558403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558403 prefixEnd_1558403 := by exact prefixLift 1558403
  have htrace : WordTrace (prefixWord ++ tailWord_1558403) baseStart_1558403 baseEnd_1558403 := by
    simpa [prefixWord, tailWord_1558403, baseEnd_1558403] using wordTrace_append hprefix tailTrace_1558403
  have hstable : (prefixWord ++ tailWord_1558403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558403).length < 2 ^ (prefixWord ++ tailWord_1558403).sum := by decide
  have hdescent : baseEnd_1558403 < baseStart_1558403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558414 : List Nat := [4, 1, 1, 5, 1, 2, 1, 2, 2, 4]
def baseStart_1558414 : Nat := 118140960795 + 1558414 * 2 ^ 59
def prefixEnd_1558414 : Nat := 4983230072969 + 3 ^ 40 * 1558414 * 2
def baseEnd_1558414 : Nat := 266738480231990310585997

theorem tailTrace_1558414 : CollatzResearch.WordTrace tailWord_1558414 prefixEnd_1558414 266738480231990310585997 := by
  unfold tailWord_1558414
  simp only [CollatzResearch.WordTrace]
  refine ⟨7105003522017463595819287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37893352117426472511036197 7105003522017463595819287)
  ·
    refine ⟨10657505283026195393728931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7105003522017463595819287 10657505283026195393728931)
    ·
      refine ⟨15986257924539293090593397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10657505283026195393728931 15986257924539293090593397)
      ·
        refine ⟨1498711680425558727243131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15986257924539293090593397 1498711680425558727243131)
        ·
          refine ⟨2248067520638338090864697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1498711680425558727243131 2248067520638338090864697)
          ·
            refine ⟨1686050640478753568148523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2248067520638338090864697 1686050640478753568148523)
            ·
              refine ⟨2529075960718130352222785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1686050640478753568148523 2529075960718130352222785)
              ·
                refine ⟨1896806970538597764167089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2529075960718130352222785 1896806970538597764167089)
                ·
                  refine ⟨1422605227903948323125317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1896806970538597764167089 1422605227903948323125317)
                  ·
                    refine ⟨266738480231990310585997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1422605227903948323125317 266738480231990310585997)
                    ·
                      rfl

theorem cell23_1558414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_1558414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558414 prefixEnd_1558414 := by exact prefixLift 1558414
  have htrace : WordTrace (prefixWord ++ tailWord_1558414) baseStart_1558414 baseEnd_1558414 := by
    simpa [prefixWord, tailWord_1558414, baseEnd_1558414] using wordTrace_append hprefix tailTrace_1558414
  have hstable : (prefixWord ++ tailWord_1558414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558414).length < 2 ^ (prefixWord ++ tailWord_1558414).sum := by decide
  have hdescent : baseEnd_1558414 < baseStart_1558414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558496 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 3, 7]
def baseStart_1558496 : Nat := 118140960795 + 1558496 * 2 ^ 59
def prefixEnd_1558496 : Nat := 4983230072969 + 3 ^ 40 * 1558496 * 2
def baseEnd_1558496 : Nat := 266752515369879870310871

theorem tailTrace_1558496 : CollatzResearch.WordTrace tailWord_1558496 prefixEnd_1558496 266752515369879870310871 := by
  unfold tailWord_1558496
  simp only [CollatzResearch.WordTrace]
  refine ⟨28421509480921318385519671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37895345974561757847359561 28421509480921318385519671)
  ·
    refine ⟨42632264221381977578279507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28421509480921318385519671 42632264221381977578279507)
    ·
      refine ⟨63948396332072966367419261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42632264221381977578279507 63948396332072966367419261)
      ·
        refine ⟨23980648624527362387782223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63948396332072966367419261 23980648624527362387782223)
        ·
          refine ⟨35970972936791043581673335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23980648624527362387782223 35970972936791043581673335)
          ·
            refine ⟨53956459405186565372510003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35970972936791043581673335 53956459405186565372510003)
            ·
              refine ⟨80934689107779848058765005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53956459405186565372510003 80934689107779848058765005)
              ·
                refine ⟨30350508415417443022036877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80934689107779848058765005 30350508415417443022036877)
                ·
                  refine ⟨11381440655781541133263829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30350508415417443022036877 11381440655781541133263829)
                  ·
                    refine ⟨266752515369879870310871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11381440655781541133263829 266752515369879870310871)
                    ·
                      rfl

theorem cell23_1558496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 3, 7].length) (baseStart_1558496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558496 prefixEnd_1558496 := by exact prefixLift 1558496
  have htrace : WordTrace (prefixWord ++ tailWord_1558496) baseStart_1558496 baseEnd_1558496 := by
    simpa [prefixWord, tailWord_1558496, baseEnd_1558496] using wordTrace_append hprefix tailTrace_1558496
  have hstable : (prefixWord ++ tailWord_1558496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558496).length < 2 ^ (prefixWord ++ tailWord_1558496).sum := by decide
  have hdescent : baseEnd_1558496 < baseStart_1558496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558498 : List Nat := [3, 3, 3, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_1558498 : Nat := 118140960795 + 1558498 * 2 ^ 59
def prefixEnd_1558498 : Nat := 4983230072969 + 3 ^ 40 * 1558498 * 2
def baseEnd_1558498 : Nat := 800258573070948603107605

theorem tailTrace_1558498 : CollatzResearch.WordTrace tailWord_1558498 prefixEnd_1558498 800258573070948603107605 := by
  unfold tailWord_1558498
  simp only [CollatzResearch.WordTrace]
  refine ⟨14210772976958847778153037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37895394605223594075074765 14210772976958847778153037)
  ·
    refine ⟨5329039866359567916807389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14210772976958847778153037 5329039866359567916807389)
    ·
      refine ⟨1998389949884837968802771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5329039866359567916807389 1998389949884837968802771)
      ·
        refine ⟨2997584924827256953204157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1998389949884837968802771 2997584924827256953204157)
        ·
          refine ⟨1124094346810221357451559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2997584924827256953204157 1124094346810221357451559)
          ·
            refine ⟨1686141520215332036177339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1124094346810221357451559 1686141520215332036177339)
            ·
              refine ⟨2529212280322998054266009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1686141520215332036177339 2529212280322998054266009)
              ·
                refine ⟨1896909210242248540699507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2529212280322998054266009 1896909210242248540699507)
                ·
                  refine ⟨2845363815363372811049261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1896909210242248540699507 2845363815363372811049261)
                  ·
                    refine ⟨1067011430761264804143473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2845363815363372811049261 1067011430761264804143473)
                    ·
                      refine ⟨800258573070948603107605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1067011430761264804143473 800258573070948603107605)
                      ·
                        rfl

theorem cell23_1558498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_1558498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558498 prefixEnd_1558498 := by exact prefixLift 1558498
  have htrace : WordTrace (prefixWord ++ tailWord_1558498) baseStart_1558498 baseEnd_1558498 := by
    simpa [prefixWord, tailWord_1558498, baseEnd_1558498] using wordTrace_append hprefix tailTrace_1558498
  have hstable : (prefixWord ++ tailWord_1558498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558498).length < 2 ^ (prefixWord ++ tailWord_1558498).sum := by decide
  have hdescent : baseEnd_1558498 < baseStart_1558498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558553 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 1, 4, 3]
def baseStart_1558553 : Nat := 118140960795 + 1558553 * 2 ^ 59
def prefixEnd_1558553 : Nat := 4983230072969 + 3 ^ 40 * 1558553 * 2
def baseEnd_1558553 : Nat := 800286814506945887919851

theorem tailTrace_1558553 : CollatzResearch.WordTrace tailWord_1558553 prefixEnd_1558553 800286814506945887919851 := by
  unfold tailWord_1558553
  simp only [CollatzResearch.WordTrace]
  refine ⟨56845097922636135505864313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37896731948424090337242875 56845097922636135505864313)
  ·
    refine ⟨42633823441977101629398235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56845097922636135505864313 42633823441977101629398235)
    ·
      refine ⟨63950735162965652444097353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42633823441977101629398235 63950735162965652444097353)
      ·
        refine ⟨47963051372224239333073015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63950735162965652444097353 47963051372224239333073015)
        ·
          refine ⟨71944577058336358999609523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47963051372224239333073015 71944577058336358999609523)
          ·
            refine ⟨107916865587504538499414285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71944577058336358999609523 107916865587504538499414285)
            ·
              refine ⟨40468824595314201937280357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107916865587504538499414285 40468824595314201937280357)
              ·
                refine ⟨7587904611621412863240067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40468824595314201937280357 7587904611621412863240067)
                ·
                  refine ⟨11381856917432119294860101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7587904611621412863240067 11381856917432119294860101)
                  ·
                    refine ⟨2134098172018522367786269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11381856917432119294860101 2134098172018522367786269)
                    ·
                      refine ⟨800286814506945887919851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2134098172018522367786269 800286814506945887919851)
                      ·
                        rfl

theorem cell23_1558553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 4, 3].length) (baseStart_1558553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558553 prefixEnd_1558553 := by exact prefixLift 1558553
  have htrace : WordTrace (prefixWord ++ tailWord_1558553) baseStart_1558553 baseEnd_1558553 := by
    simpa [prefixWord, tailWord_1558553, baseEnd_1558553] using wordTrace_append hprefix tailTrace_1558553
  have hstable : (prefixWord ++ tailWord_1558553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558553).length < 2 ^ (prefixWord ++ tailWord_1558553).sum := by decide
  have hdescent : baseEnd_1558553 < baseStart_1558553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558564 : List Nat := [2, 3, 1, 4, 3, 1, 1, 1, 2, 5]
def baseStart_1558564 : Nat := 118140960795 + 1558564 * 2 ^ 59
def prefixEnd_1558564 : Nat := 4983230072969 + 3 ^ 40 * 1558564 * 2
def baseEnd_1558564 : Nat := 266764154264715114960767

theorem tailTrace_1558564 : CollatzResearch.WordTrace tailWord_1558564 prefixEnd_1558564 266764154264715114960767 := by
  unfold tailWord_1558564
  simp only [CollatzResearch.WordTrace]
  refine ⟨28422749562798142192257373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37896999417064189589676497 28422749562798142192257373)
  ·
    refine ⟨10658531086049303322096515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28422749562798142192257373 10658531086049303322096515)
    ·
      refine ⟨15987796629073954983144773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10658531086049303322096515 15987796629073954983144773)
      ·
        refine ⟨2997711867951366559339645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15987796629073954983144773 2997711867951366559339645)
        ·
          refine ⟨1124141950481762459752367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2997711867951366559339645 1124141950481762459752367)
          ·
            refine ⟨1686212925722643689628551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1124141950481762459752367 1686212925722643689628551)
            ·
              refine ⟨2529319388583965534442827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1686212925722643689628551 2529319388583965534442827)
              ·
                refine ⟨3793979082875948301664241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2529319388583965534442827 3793979082875948301664241)
                ·
                  refine ⟨2845484312156961226248181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3793979082875948301664241 2845484312156961226248181)
                  ·
                    refine ⟨266764154264715114960767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2845484312156961226248181 266764154264715114960767)
                    ·
                      rfl

theorem cell23_1558564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_1558564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558564 prefixEnd_1558564 := by exact prefixLift 1558564
  have htrace : WordTrace (prefixWord ++ tailWord_1558564) baseStart_1558564 baseEnd_1558564 := by
    simpa [prefixWord, tailWord_1558564, baseEnd_1558564] using wordTrace_append hprefix tailTrace_1558564
  have hstable : (prefixWord ++ tailWord_1558564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558564).length < 2 ^ (prefixWord ++ tailWord_1558564).sum := by decide
  have hdescent : baseEnd_1558564 < baseStart_1558564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558567 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_1558567 : Nat := 118140960795 + 1558567 * 2 ^ 59
def prefixEnd_1558567 : Nat := 4983230072969 + 3 ^ 40 * 1558567 * 2
def baseEnd_1558567 : Nat := 800294003236108833144787

theorem tailTrace_1558567 : CollatzResearch.WordTrace tailWord_1558567 prefixEnd_1558567 800294003236108833144787 := by
  unfold tailWord_1558567
  simp only [CollatzResearch.WordTrace]
  refine ⟨56845608544585415896873955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37897072363056943931249303 56845608544585415896873955)
  ·
    refine ⟨85268412816878123845310933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56845608544585415896873955 85268412816878123845310933)
    ·
      refine ⟨1998478425395581027624475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 85268412816878123845310933 1998478425395581027624475)
      ·
        refine ⟨2997717638093371541436713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1998478425395581027624475 2997717638093371541436713)
        ·
          refine ⟨2248288228570028656077535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2997717638093371541436713 2248288228570028656077535)
          ·
            refine ⟨3372432342855042984116303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2248288228570028656077535 3372432342855042984116303)
            ·
              refine ⟨5058648514282564476174455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3372432342855042984116303 5058648514282564476174455)
              ·
                refine ⟨7587972771423846714261683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5058648514282564476174455 7587972771423846714261683)
                ·
                  refine ⟨11381959157135770071392525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7587972771423846714261683 11381959157135770071392525)
                  ·
                    refine ⟨4268234683925913776772197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11381959157135770071392525 4268234683925913776772197)
                    ·
                      refine ⟨800294003236108833144787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4268234683925913776772197 800294003236108833144787)
                      ·
                        rfl

theorem cell23_1558567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_1558567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558567 prefixEnd_1558567 := by exact prefixLift 1558567
  have htrace : WordTrace (prefixWord ++ tailWord_1558567) baseStart_1558567 baseEnd_1558567 := by
    simpa [prefixWord, tailWord_1558567, baseEnd_1558567] using wordTrace_append hprefix tailTrace_1558567
  have hstable : (prefixWord ++ tailWord_1558567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558567).length < 2 ^ (prefixWord ++ tailWord_1558567).sum := by decide
  have hdescent : baseEnd_1558567 < baseStart_1558567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558577 : List Nat := [1, 2, 2, 3, 1, 3, 1, 5, 1, 4]
def baseStart_1558577 : Nat := 118140960795 + 1558577 * 2 ^ 59
def prefixEnd_1558577 : Nat := 4983230072969 + 3 ^ 40 * 1558577 * 2
def baseEnd_1558577 : Nat := 266766379347551264673247

theorem tailTrace_1558577 : CollatzResearch.WordTrace tailWord_1558577 prefixEnd_1558577 266766379347551264673247 := by
  unfold tailWord_1558577
  simp only [CollatzResearch.WordTrace]
  refine ⟨56845973274549187604737985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37897315516366125069825323 56845973274549187604737985)
  ·
    refine ⟨42634479955911890703553489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56845973274549187604737985 42634479955911890703553489)
    ·
      refine ⟨31975859966933918027665117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42634479955911890703553489 31975859966933918027665117)
      ·
        refine ⟨11990947487600219260374419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31975859966933918027665117 11990947487600219260374419)
        ·
          refine ⟨17986421231400328890561629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11990947487600219260374419 17986421231400328890561629)
          ·
            refine ⟨6744907961775123333960611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17986421231400328890561629 6744907961775123333960611)
            ·
              refine ⟨10117361942662685000940917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6744907961775123333960611 10117361942662685000940917)
              ·
                refine ⟨948502682124626718838211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10117361942662685000940917 948502682124626718838211)
                ·
                  refine ⟨1422754023186940078257317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 948502682124626718838211 1422754023186940078257317)
                  ·
                    refine ⟨266766379347551264673247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1422754023186940078257317 266766379347551264673247)
                    ·
                      rfl

theorem cell23_1558577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 1, 4].length) (baseStart_1558577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558577 prefixEnd_1558577 := by exact prefixLift 1558577
  have htrace : WordTrace (prefixWord ++ tailWord_1558577) baseStart_1558577 baseEnd_1558577 := by
    simpa [prefixWord, tailWord_1558577, baseEnd_1558577] using wordTrace_append hprefix tailTrace_1558577
  have hstable : (prefixWord ++ tailWord_1558577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558577).length < 2 ^ (prefixWord ++ tailWord_1558577).sum := by decide
  have hdescent : baseEnd_1558577 < baseStart_1558577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558633 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 3, 6]
def baseStart_1558633 : Nat := 118140960795 + 1558633 * 2 ^ 59
def prefixEnd_1558633 : Nat := 4983230072969 + 3 ^ 40 * 1558633 * 2
def baseEnd_1558633 : Nat := 266775964319768524973161

theorem tailTrace_1558633 : CollatzResearch.WordTrace tailWord_1558633 prefixEnd_1558633 266775964319768524973161 := by
  unfold tailWord_1558633
  simp only [CollatzResearch.WordTrace]
  refine ⟨56848015762346309168776553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37898677174897539445851035 56848015762346309168776553)
  ·
    refine ⟨42636011821759731876582415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56848015762346309168776553 42636011821759731876582415)
    ·
      refine ⟨63954017732639597814873623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42636011821759731876582415 63954017732639597814873623)
      ·
        refine ⟨95931026598959396722310435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63954017732639597814873623 95931026598959396722310435)
        ·
          refine ⟨143896539898439095083465653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95931026598959396722310435 143896539898439095083465653)
          ·
            refine ⟨13490300615478665164074905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 143896539898439095083465653 13490300615478665164074905)
            ·
              refine ⟨10117725461608998873056179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13490300615478665164074905 10117725461608998873056179)
              ·
                refine ⟨15176588192413498309584269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10117725461608998873056179 15176588192413498309584269)
                ·
                  refine ⟨5691220572155061866094101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15176588192413498309584269 5691220572155061866094101)
                  ·
                    refine ⟨266775964319768524973161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5691220572155061866094101 266775964319768524973161)
                    ·
                      rfl

theorem cell23_1558633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 6].length) (baseStart_1558633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558633 prefixEnd_1558633 := by exact prefixLift 1558633
  have htrace : WordTrace (prefixWord ++ tailWord_1558633) baseStart_1558633 baseEnd_1558633 := by
    simpa [prefixWord, tailWord_1558633, baseEnd_1558633] using wordTrace_append hprefix tailTrace_1558633
  have hstable : (prefixWord ++ tailWord_1558633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558633).length < 2 ^ (prefixWord ++ tailWord_1558633).sum := by decide
  have hdescent : baseEnd_1558633 < baseStart_1558633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558660 : List Nat := [2, 3, 2, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_1558660 : Nat := 118140960795 + 1558660 * 2 ^ 59
def prefixEnd_1558660 : Nat := 4983230072969 + 3 ^ 40 * 1558660 * 2
def baseEnd_1558660 : Nat := 800341756936976969281859

theorem tailTrace_1558660 : CollatzResearch.WordTrace tailWord_1558660 prefixEnd_1558660 800341756936976969281859 := by
  unfold tailWord_1558660
  simp only [CollatzResearch.WordTrace]
  refine ⟨28424500266624246390004717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37899333688832328520006289 28424500266624246390004717)
  ·
    refine ⟨10659187599984092396251769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28424500266624246390004717 10659187599984092396251769)
    ·
      refine ⟨7994390699988069297188827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10659187599984092396251769 7994390699988069297188827)
      ·
        refine ⟨11991586049982103945783241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7994390699988069297188827 11991586049982103945783241)
        ·
          refine ⟨8993689537486577959337431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11991586049982103945783241 8993689537486577959337431)
          ·
            refine ⟨13490534306229866939006147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8993689537486577959337431 13490534306229866939006147)
            ·
              refine ⟨20235801459344800408509221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13490534306229866939006147 20235801459344800408509221)
              ·
                refine ⟨3794212773627150076595479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20235801459344800408509221 3794212773627150076595479)
                ·
                  refine ⟨5691319160440725114893219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3794212773627150076595479 5691319160440725114893219)
                  ·
                    refine ⟨8536978740661087672339829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5691319160440725114893219 8536978740661087672339829)
                    ·
                      refine ⟨800341756936976969281859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8536978740661087672339829 800341756936976969281859)
                      ·
                        rfl

theorem cell23_1558660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_1558660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558660 prefixEnd_1558660 := by exact prefixLift 1558660
  have htrace : WordTrace (prefixWord ++ tailWord_1558660) baseStart_1558660 baseEnd_1558660 := by
    simpa [prefixWord, tailWord_1558660, baseEnd_1558660] using wordTrace_append hprefix tailTrace_1558660
  have hstable : (prefixWord ++ tailWord_1558660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558660).length < 2 ^ (prefixWord ++ tailWord_1558660).sum := by decide
  have hdescent : baseEnd_1558660 < baseStart_1558660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558663 : List Nat := [1, 1, 4, 2, 1, 1, 3, 10]
def baseStart_1558663 : Nat := 118140960795 + 1558663 * 2 ^ 59
def prefixEnd_1558663 : Nat := 4983230072969 + 3 ^ 40 * 1558663 * 2
def baseEnd_1558663 : Nat := 29642344347368165094235

theorem tailTrace_1558663 : CollatzResearch.WordTrace tailWord_1558663 prefixEnd_1558663 29642344347368165094235 := by
  unfold tailWord_1558663
  simp only [CollatzResearch.WordTrace]
  refine ⟨56849109952237624292368643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37899406634825082861579095 56849109952237624292368643)
  ·
    refine ⟨85273664928356436438552965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56849109952237624292368643 85273664928356436438552965)
    ·
      refine ⟨15988812174066831832228681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85273664928356436438552965 15988812174066831832228681)
      ·
        refine ⟨11991609130550123874171511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15988812174066831832228681 11991609130550123874171511)
        ·
          refine ⟨17987413695825185811257267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11991609130550123874171511 17987413695825185811257267)
          ·
            refine ⟨26981120543737778716885901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17987413695825185811257267 26981120543737778716885901)
            ·
              refine ⟨10117920203901667018832213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26981120543737778716885901 10117920203901667018832213)
              ·
                refine ⟨29642344347368165094235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10117920203901667018832213 29642344347368165094235)
                ·
                  rfl

theorem cell23_1558663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 10].length) (baseStart_1558663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558663 prefixEnd_1558663 := by exact prefixLift 1558663
  have htrace : WordTrace (prefixWord ++ tailWord_1558663) baseStart_1558663 baseEnd_1558663 := by
    simpa [prefixWord, tailWord_1558663, baseEnd_1558663] using wordTrace_append hprefix tailTrace_1558663
  have hstable : (prefixWord ++ tailWord_1558663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558663).length < 2 ^ (prefixWord ++ tailWord_1558663).sum := by decide
  have hdescent : baseEnd_1558663 < baseStart_1558663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558674 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 5, 2, 2]
def baseStart_1558674 : Nat := 118140960795 + 1558674 * 2 ^ 59
def prefixEnd_1558674 : Nat := 4983230072969 + 3 ^ 40 * 1558674 * 2
def baseEnd_1558674 : Nat := 800348945666139914506795

theorem tailTrace_1558674 : CollatzResearch.WordTrace tailWord_1558674 prefixEnd_1558674 800348945666139914506795 := by
  unfold tailWord_1558674
  simp only [CollatzResearch.WordTrace]
  refine ⟨14212377788799443292754769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37899674103465182114012717 14212377788799443292754769)
  ·
    refine ⟨10659283341599582469566077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14212377788799443292754769 10659283341599582469566077)
    ·
      refine ⟨3997231253099843426087279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10659283341599582469566077 3997231253099843426087279)
      ·
        refine ⟨5995846879649765139130919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3997231253099843426087279 5995846879649765139130919)
        ·
          refine ⟨8993770319474647708696379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5995846879649765139130919 8993770319474647708696379)
          ·
            refine ⟨13490655479211971563044569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8993770319474647708696379 13490655479211971563044569)
            ·
              refine ⟨10117991609408978672283427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13490655479211971563044569 10117991609408978672283427)
              ·
                refine ⟨15176987414113468008425141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10117991609408978672283427 15176987414113468008425141)
                ·
                  refine ⟨1422842570073137625789857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15176987414113468008425141 1422842570073137625789857)
                  ·
                    refine ⟨1067131927554853219342393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1422842570073137625789857 1067131927554853219342393)
                    ·
                      refine ⟨800348945666139914506795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1067131927554853219342393 800348945666139914506795)
                      ·
                        rfl

theorem cell23_1558674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_1558674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558674 prefixEnd_1558674 := by exact prefixLift 1558674
  have htrace : WordTrace (prefixWord ++ tailWord_1558674) baseStart_1558674 baseEnd_1558674 := by
    simpa [prefixWord, tailWord_1558674, baseEnd_1558674] using wordTrace_append hprefix tailTrace_1558674
  have hstable : (prefixWord ++ tailWord_1558674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558674).length < 2 ^ (prefixWord ++ tailWord_1558674).sum := by decide
  have hdescent : baseEnd_1558674 < baseStart_1558674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558687 : List Nat := [1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1558687 : Nat := 118140960795 + 1558687 * 2 ^ 59
def prefixEnd_1558687 : Nat := 4983230072969 + 3 ^ 40 * 1558687 * 2
def baseEnd_1558687 : Nat := 800355620914648363644235

theorem tailTrace_1558687 : CollatzResearch.WordTrace tailWord_1558687 prefixEnd_1558687 800355620914648363644235 := by
  unfold tailWord_1558687
  simp only [CollatzResearch.WordTrace]
  refine ⟨56849985304150676391242315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37899990202767117594161543 56849985304150676391242315)
  ·
    refine ⟨85274977956226014586863473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56849985304150676391242315 85274977956226014586863473)
    ·
      refine ⟨63956233467169510940147605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85274977956226014586863473 63956233467169510940147605)
      ·
        refine ⟨2997948443773570825319419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63956233467169510940147605 2997948443773570825319419)
        ·
          refine ⟨4496922665660356237979129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2997948443773570825319419 4496922665660356237979129)
          ·
            refine ⟨3372691999245267178484347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4496922665660356237979129 3372691999245267178484347)
            ·
              refine ⟨5059037998867900767726521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3372691999245267178484347 5059037998867900767726521)
              ·
                refine ⟨3794278499150925575794891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5059037998867900767726521 3794278499150925575794891)
                ·
                  refine ⟨5691417748726388363692337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3794278499150925575794891 5691417748726388363692337)
                  ·
                    refine ⟨4268563311544791272769253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5691417748726388363692337 4268563311544791272769253)
                    ·
                      refine ⟨800355620914648363644235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4268563311544791272769253 800355620914648363644235)
                      ·
                        rfl

theorem cell23_1558687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1558687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558687 prefixEnd_1558687 := by exact prefixLift 1558687
  have htrace : WordTrace (prefixWord ++ tailWord_1558687) baseStart_1558687 baseEnd_1558687 := by
    simpa [prefixWord, tailWord_1558687, baseEnd_1558687] using wordTrace_append hprefix tailTrace_1558687
  have hstable : (prefixWord ++ tailWord_1558687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558687).length < 2 ^ (prefixWord ++ tailWord_1558687).sum := by decide
  have hdescent : baseEnd_1558687 < baseStart_1558687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558702 : List Nat := [4, 1, 4, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_1558702 : Nat := 118140960795 + 1558702 * 2 ^ 59
def prefixEnd_1558702 : Nat := 4983230072969 + 3 ^ 40 * 1558702 * 2
def baseEnd_1558702 : Nat := 800363323124465804956667

theorem tailTrace_1558702 : CollatzResearch.WordTrace tailWord_1558702 prefixEnd_1558702 800363323124465804956667 := by
  unfold tailWord_1558702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7106316549887041744129795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37900354932730889302025573 7106316549887041744129795)
  ·
    refine ⟨10659474824830562616194693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7106316549887041744129795 10659474824830562616194693)
    ·
      refine ⟨1998651529655730490536505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10659474824830562616194693 1998651529655730490536505)
      ·
        refine ⟨1498988647241797867902379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1998651529655730490536505 1498988647241797867902379)
        ·
          refine ⟨2248482970862696801853569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1498988647241797867902379 2248482970862696801853569)
          ·
            refine ⟨1686362228147022601390177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2248482970862696801853569 1686362228147022601390177)
            ·
              refine ⟨1264771671110266951042633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1686362228147022601390177 1264771671110266951042633)
              ·
                refine ⟨948578753332700213281975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1264771671110266951042633 948578753332700213281975)
                ·
                  refine ⟨1422868129999050319922963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 948578753332700213281975 1422868129999050319922963)
                  ·
                    refine ⟨2134302194998575479884445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1422868129999050319922963 2134302194998575479884445)
                    ·
                      refine ⟨800363323124465804956667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2134302194998575479884445 800363323124465804956667)
                      ·
                        rfl

theorem cell23_1558702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_1558702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558702 prefixEnd_1558702 := by exact prefixLift 1558702
  have htrace : WordTrace (prefixWord ++ tailWord_1558702) baseStart_1558702 baseEnd_1558702 := by
    simpa [prefixWord, tailWord_1558702, baseEnd_1558702] using wordTrace_append hprefix tailTrace_1558702
  have hstable : (prefixWord ++ tailWord_1558702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558702).length < 2 ^ (prefixWord ++ tailWord_1558702).sum := by decide
  have hdescent : baseEnd_1558702 < baseStart_1558702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558724 : List Nat := [2, 3, 3, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_1558724 : Nat := 118140960795 + 1558724 * 2 ^ 59
def prefixEnd_1558724 : Nat := 4983230072969 + 3 ^ 40 * 1558724 * 2
def baseEnd_1558724 : Nat := 800374619698864718881565

theorem tailTrace_1558724 : CollatzResearch.WordTrace tailWord_1558724 prefixEnd_1558724 800374619698864718881565 := by
  unfold tailWord_1558724
  simp only [CollatzResearch.WordTrace]
  refine ⟨28425667402508315855169613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37900889870011087806892817 28425667402508315855169613)
  ·
    refine ⟨10659625275940618445688605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28425667402508315855169613 10659625275940618445688605)
    ·
      refine ⟨3997359478477731917133227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10659625275940618445688605 3997359478477731917133227)
      ·
        refine ⟨5996039217716597875699841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3997359478477731917133227 5996039217716597875699841)
        ·
          refine ⟨4497029413287448406774881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5996039217716597875699841 4497029413287448406774881)
          ·
            refine ⟨3372772059965586305081161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4497029413287448406774881 3372772059965586305081161)
            ·
              refine ⟨2529579044974189728810871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3372772059965586305081161 2529579044974189728810871)
              ·
                refine ⟨3794368567461284593216307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2529579044974189728810871 3794368567461284593216307)
                ·
                  refine ⟨5691552851191926889824461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3794368567461284593216307 5691552851191926889824461)
                  ·
                    refine ⟨2134332319196972583684173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5691552851191926889824461 2134332319196972583684173)
                    ·
                      refine ⟨800374619698864718881565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2134332319196972583684173 800374619698864718881565)
                      ·
                        rfl

theorem cell23_1558724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_1558724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558724 prefixEnd_1558724 := by exact prefixLift 1558724
  have htrace : WordTrace (prefixWord ++ tailWord_1558724) baseStart_1558724 baseEnd_1558724 := by
    simpa [prefixWord, tailWord_1558724, baseEnd_1558724] using wordTrace_append hprefix tailTrace_1558724
  have hstable : (prefixWord ++ tailWord_1558724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558724).length < 2 ^ (prefixWord ++ tailWord_1558724).sum := by decide
  have hdescent : baseEnd_1558724 < baseStart_1558724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558730 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 2, 3, 4]
def baseStart_1558730 : Nat := 118140960795 + 1558730 * 2 ^ 59
def prefixEnd_1558730 : Nat := 4983230072969 + 3 ^ 40 * 1558730 * 2
def baseEnd_1558730 : Nat := 800377700582791695406537

theorem tailTrace_1558730 : CollatzResearch.WordTrace tailWord_1558730 prefixEnd_1558730 800377700582791695406537 := by
  unfold tailWord_1558730
  simp only [CollatzResearch.WordTrace]
  refine ⟨14212888410748723683764411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37901035761996596490038429 14212888410748723683764411)
  ·
    refine ⟨21319332616123085525646617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14212888410748723683764411 21319332616123085525646617)
    ·
      refine ⟨15989499462092314144234963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21319332616123085525646617 15989499462092314144234963)
      ·
        refine ⟨23984249193138471216352445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15989499462092314144234963 23984249193138471216352445)
        ·
          refine ⟨8994093447426926706132167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23984249193138471216352445 8994093447426926706132167)
          ·
            refine ⟨13491140171140390059198251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8994093447426926706132167 13491140171140390059198251)
            ·
              refine ⟨20236710256710585088797377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13491140171140390059198251 20236710256710585088797377)
              ·
                refine ⟨15177532692532938816598033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20236710256710585088797377 15177532692532938816598033)
                ·
                  refine ⟨11383149519399704112448525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15177532692532938816598033 11383149519399704112448525)
                  ·
                    refine ⟨4268681069774889042168197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11383149519399704112448525 4268681069774889042168197)
                    ·
                      refine ⟨800377700582791695406537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4268681069774889042168197 800377700582791695406537)
                      ·
                        rfl

theorem cell23_1558730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_1558730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558730 prefixEnd_1558730 := by exact prefixLift 1558730
  have htrace : WordTrace (prefixWord ++ tailWord_1558730) baseStart_1558730 baseEnd_1558730 := by
    simpa [prefixWord, tailWord_1558730, baseEnd_1558730] using wordTrace_append hprefix tailTrace_1558730
  have hstable : (prefixWord ++ tailWord_1558730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558730).length < 2 ^ (prefixWord ++ tailWord_1558730).sum := by decide
  have hdescent : baseEnd_1558730 < baseStart_1558730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558734 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2]
def baseStart_1558734 : Nat := 118140960795 + 1558734 * 2 ^ 59
def prefixEnd_1558734 : Nat := 4983230072969 + 3 ^ 40 * 1558734 * 2
def baseEnd_1558734 : Nat := 800379754505409679756519

theorem tailTrace_1558734 : CollatzResearch.WordTrace tailWord_1558734 prefixEnd_1558734 800379754505409679756519 := by
  unfold tailWord_1558734
  simp only [CollatzResearch.WordTrace]
  refine ⟨7106462441872550427275407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37901133023320268945468837 7106462441872550427275407)
  ·
    refine ⟨10659693662808825640913111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7106462441872550427275407 10659693662808825640913111)
    ·
      refine ⟨15989540494213238461369667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10659693662808825640913111 15989540494213238461369667)
      ·
        refine ⟨23984310741319857692054501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15989540494213238461369667 23984310741319857692054501)
        ·
          refine ⟨4497058263997473317260219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23984310741319857692054501 4497058263997473317260219)
          ·
            refine ⟨6745587395996209975890329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4497058263997473317260219 6745587395996209975890329)
            ·
              refine ⟨5059190546997157481917747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6745587395996209975890329 5059190546997157481917747)
              ·
                refine ⟨7588785820495736222876621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5059190546997157481917747 7588785820495736222876621)
                ·
                  refine ⟨2845794682685901083578733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7588785820495736222876621 2845794682685901083578733)
                  ·
                    refine ⟨1067173006007212906342025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2845794682685901083578733 1067173006007212906342025)
                    ·
                      refine ⟨800379754505409679756519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1067173006007212906342025 800379754505409679756519)
                      ·
                        rfl

theorem cell23_1558734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2].length) (baseStart_1558734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558734 prefixEnd_1558734 := by exact prefixLift 1558734
  have htrace : WordTrace (prefixWord ++ tailWord_1558734) baseStart_1558734 baseEnd_1558734 := by
    simpa [prefixWord, tailWord_1558734, baseEnd_1558734] using wordTrace_append hprefix tailTrace_1558734
  have hstable : (prefixWord ++ tailWord_1558734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558734).length < 2 ^ (prefixWord ++ tailWord_1558734).sum := by decide
  have hdescent : baseEnd_1558734 < baseStart_1558734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558764 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 4, 2, 2]
def baseStart_1558764 : Nat := 118140960795 + 1558764 * 2 ^ 59
def prefixEnd_1558764 : Nat := 4983230072969 + 3 ^ 40 * 1558764 * 2
def baseEnd_1558764 : Nat := 800395158925044562381381

theorem tailTrace_1558764 : CollatzResearch.WordTrace tailWord_1558764 prefixEnd_1558764 800395158925044562381381 := by
  unfold tailWord_1558764
  simp only [CollatzResearch.WordTrace]
  refine ⟨28426396862435859270897673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37901862483247812361196897 28426396862435859270897673)
  ·
    refine ⟨21319797646826894453173255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28426396862435859270897673 21319797646826894453173255)
    ·
      refine ⟨31979696470240341679759883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21319797646826894453173255 31979696470240341679759883)
      ·
        refine ⟨47969544705360512519639825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31979696470240341679759883 47969544705360512519639825)
        ·
          refine ⟨35977158529020384389729869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47969544705360512519639825 35977158529020384389729869)
          ·
            refine ⟨13491434448382644146148701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35977158529020384389729869 13491434448382644146148701)
            ·
              refine ⟨5059287918143491554805763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13491434448382644146148701 5059287918143491554805763)
              ·
                refine ⟨7588931877215237332208645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5059287918143491554805763 7588931877215237332208645)
                ·
                  refine ⟨1422924726977856999789121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7588931877215237332208645 1422924726977856999789121)
                  ·
                    refine ⟨1067193545233392749841841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1422924726977856999789121 1067193545233392749841841)
                    ·
                      refine ⟨800395158925044562381381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1067193545233392749841841 800395158925044562381381)
                      ·
                        rfl

theorem cell23_1558764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 2, 2].length) (baseStart_1558764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558764 prefixEnd_1558764 := by exact prefixLift 1558764
  have htrace : WordTrace (prefixWord ++ tailWord_1558764) baseStart_1558764 baseEnd_1558764 := by
    simpa [prefixWord, tailWord_1558764, baseEnd_1558764] using wordTrace_append hprefix tailTrace_1558764
  have hstable : (prefixWord ++ tailWord_1558764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558764).length < 2 ^ (prefixWord ++ tailWord_1558764).sum := by decide
  have hdescent : baseEnd_1558764 < baseStart_1558764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558821 : List Nat := [1, 3, 1, 2, 5, 1, 3, 2, 5]
def baseStart_1558821 : Nat := 118140960795 + 1558821 * 2 ^ 59
def prefixEnd_1558821 : Nat := 4983230072969 + 3 ^ 40 * 1558821 * 2
def baseEnd_1558821 : Nat := 88936047480261204374291

theorem tailTrace_1558821 : CollatzResearch.WordTrace tailWord_1558821 prefixEnd_1558821 88936047480261204374291 := by
  unfold tailWord_1558821
  simp only [CollatzResearch.WordTrace]
  refine ⟨56854872685665217276620317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37903248457110144851080211 56854872685665217276620317)
  ·
    refine ⟨21320577257124456478732619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56854872685665217276620317 21320577257124456478732619)
    ·
      refine ⟨31980865885686684718098929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21320577257124456478732619 31980865885686684718098929)
      ·
        refine ⟨23985649414265013538574197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31980865885686684718098929 23985649414265013538574197)
        ·
          refine ⟨2248654632587345019241331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23985649414265013538574197 2248654632587345019241331)
          ·
            refine ⟨3372981948881017528861997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2248654632587345019241331 3372981948881017528861997)
            ·
              refine ⟨1264868230830381573323249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3372981948881017528861997 1264868230830381573323249)
              ·
                refine ⟨948651173122786179992437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1264868230830381573323249 948651173122786179992437)
                ·
                  refine ⟨88936047480261204374291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 948651173122786179992437 88936047480261204374291)
                  ·
                    rfl

theorem cell23_1558821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 5].length) (baseStart_1558821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558821 prefixEnd_1558821 := by exact prefixLift 1558821
  have htrace : WordTrace (prefixWord ++ tailWord_1558821) baseStart_1558821 baseEnd_1558821 := by
    simpa [prefixWord, tailWord_1558821, baseEnd_1558821] using wordTrace_append hprefix tailTrace_1558821
  have hstable : (prefixWord ++ tailWord_1558821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558821).length < 2 ^ (prefixWord ++ tailWord_1558821).sum := by decide
  have hdescent : baseEnd_1558821 < baseStart_1558821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558837 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_1558837 : Nat := 118140960795 + 1558837 * 2 ^ 59
def prefixEnd_1558837 : Nat := 4983230072969 + 3 ^ 40 * 1558837 * 2
def baseEnd_1558837 : Nat := 800432643012822776768545

theorem tailTrace_1558837 : CollatzResearch.WordTrace tailWord_1558837 prefixEnd_1558837 800432643012822776768545 := by
  unfold tailWord_1558837
  simp only [CollatzResearch.WordTrace]
  refine ⟨56855456253607252009202765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37903637502404834672801843 56855456253607252009202765)
  ·
    refine ⟨21320796095102719503451037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56855456253607252009202765 21320796095102719503451037)
    ·
      refine ⟨7995298535663519813794139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21320796095102719503451037 7995298535663519813794139)
      ·
        refine ⟨11992947803495279720691209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7995298535663519813794139 11992947803495279720691209)
        ·
          refine ⟨8994710852621459790518407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11992947803495279720691209 8994710852621459790518407)
          ·
            refine ⟨13492066278932189685777611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8994710852621459790518407 13492066278932189685777611)
            ·
              refine ⟨20238099418398284528666417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13492066278932189685777611 20238099418398284528666417)
              ·
                refine ⟨15178574563798713396499813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20238099418398284528666417 15178574563798713396499813)
                ·
                  refine ⟨2845982730712258761843715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15178574563798713396499813 2845982730712258761843715)
                  ·
                    refine ⟨4268974096068388142765573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2845982730712258761843715 4268974096068388142765573)
                    ·
                      refine ⟨800432643012822776768545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4268974096068388142765573 800432643012822776768545)
                      ·
                        rfl

theorem cell23_1558837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_1558837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558837 prefixEnd_1558837 := by exact prefixLift 1558837
  have htrace : WordTrace (prefixWord ++ tailWord_1558837) baseStart_1558837 baseEnd_1558837 := by
    simpa [prefixWord, tailWord_1558837, baseEnd_1558837] using wordTrace_append hprefix tailTrace_1558837
  have hstable : (prefixWord ++ tailWord_1558837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558837).length < 2 ^ (prefixWord ++ tailWord_1558837).sum := by decide
  have hdescent : baseEnd_1558837 < baseStart_1558837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558847 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 5, 4]
def baseStart_1558847 : Nat := 118140960795 + 1558847 * 2 ^ 59
def prefixEnd_1558847 : Nat := 4983230072969 + 3 ^ 40 * 1558847 * 2
def baseEnd_1558847 : Nat := 266812592606455912547833

theorem tailTrace_1558847 : CollatzResearch.WordTrace tailWord_1558847 prefixEnd_1558847 266812592606455912547833 := by
  unfold tailWord_1558847
  simp only [CollatzResearch.WordTrace]
  refine ⟨56855820983571023717066795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37903880655714015811377863 56855820983571023717066795)
  ·
    refine ⟨85283731475356535575600193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56855820983571023717066795 85283731475356535575600193)
    ·
      refine ⟨63962798606517401681700145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85283731475356535575600193 63962798606517401681700145)
      ·
        refine ⟨47972098954888051261275109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63962798606517401681700145 47972098954888051261275109)
        ·
          refine ⟨8994768554041509611489083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47972098954888051261275109 8994768554041509611489083)
          ·
            refine ⟨13492152831062264417233625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8994768554041509611489083 13492152831062264417233625)
            ·
              refine ⟨10119114623296698312925219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13492152831062264417233625 10119114623296698312925219)
              ·
                refine ⟨15178671934945047469387829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10119114623296698312925219 15178671934945047469387829)
                ·
                  refine ⟨1423000493901098200255109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15178671934945047469387829 1423000493901098200255109)
                  ·
                    refine ⟨266812592606455912547833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1423000493901098200255109 266812592606455912547833)
                    ·
                      rfl

theorem cell23_1558847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 4].length) (baseStart_1558847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558847 prefixEnd_1558847 := by exact prefixLift 1558847
  have htrace : WordTrace (prefixWord ++ tailWord_1558847) baseStart_1558847 baseEnd_1558847 := by
    simpa [prefixWord, tailWord_1558847, baseEnd_1558847] using wordTrace_append hprefix tailTrace_1558847
  have hstable : (prefixWord ++ tailWord_1558847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558847).length < 2 ^ (prefixWord ++ tailWord_1558847).sum := by decide
  have hdescent : baseEnd_1558847 < baseStart_1558847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558907 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 3, 5]
def baseStart_1558907 : Nat := 118140960795 + 1558907 * 2 ^ 59
def prefixEnd_1558907 : Nat := 4983230072969 + 3 ^ 40 * 1558907 * 2
def baseEnd_1558907 : Nat := 266822862219545834297741

theorem tailTrace_1558907 : CollatzResearch.WordTrace tailWord_1558907 prefixEnd_1558907 266822862219545834297741 := by
  unfold tailWord_1558907
  simp only [CollatzResearch.WordTrace]
  refine ⟨56858009363353653964250975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37905339575569102642833983 56858009363353653964250975)
  ·
    refine ⟨85287014045030480946376463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56858009363353653964250975 85287014045030480946376463)
    ·
      refine ⟨127930521067545721419564695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85287014045030480946376463 127930521067545721419564695)
      ·
        refine ⟨191895781601318582129347043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127930521067545721419564695 191895781601318582129347043)
        ·
          refine ⟨287843672401977873194020565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191895781601318582129347043 287843672401977873194020565)
          ·
            refine ⟨6746336071921356402984857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 287843672401977873194020565 6746336071921356402984857)
            ·
              refine ⟨5059752053941017302238643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6746336071921356402984857 5059752053941017302238643)
              ·
                refine ⟨7589628080911525953357965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5059752053941017302238643 7589628080911525953357965)
                ·
                  refine ⟨2846110530341822232509237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7589628080911525953357965 2846110530341822232509237)
                  ·
                    refine ⟨266822862219545834297741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2846110530341822232509237 266822862219545834297741)
                    ·
                      rfl

theorem cell23_1558907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 5].length) (baseStart_1558907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558907 prefixEnd_1558907 := by exact prefixLift 1558907
  have htrace : WordTrace (prefixWord ++ tailWord_1558907) baseStart_1558907 baseEnd_1558907 := by
    simpa [prefixWord, tailWord_1558907, baseEnd_1558907] using wordTrace_append hprefix tailTrace_1558907
  have hstable : (prefixWord ++ tailWord_1558907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558907).length < 2 ^ (prefixWord ++ tailWord_1558907).sum := by decide
  have hdescent : baseEnd_1558907 < baseStart_1558907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558924 : List Nat := [2, 2, 1, 2, 1, 5, 1, 3, 1, 5]
def baseStart_1558924 : Nat := 118140960795 + 1558924 * 2 ^ 59
def prefixEnd_1558924 : Nat := 4983230072969 + 3 ^ 40 * 1558924 * 2
def baseEnd_1558924 : Nat := 266825771943254645460215

theorem tailTrace_1558924 : CollatzResearch.WordTrace tailWord_1558924 prefixEnd_1558924 266825771943254645460215 := by
  unfold tailWord_1558924
  simp only [CollatzResearch.WordTrace]
  refine ⟨28429314702146032933809913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37905752936194710578413217 28429314702146032933809913)
  ·
    refine ⟨21321986026609524700357435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28429314702146032933809913 21321986026609524700357435)
    ·
      refine ⟨31982979039914287050536153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21321986026609524700357435 31982979039914287050536153)
      ·
        refine ⟨23987234279935715287902115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31982979039914287050536153 23987234279935715287902115)
        ·
          refine ⟨35980851419903572931853173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23987234279935715287902115 35980851419903572931853173)
          ·
            refine ⟨3373204820615959962361235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35980851419903572931853173 3373204820615959962361235)
            ·
              refine ⟨5059807230923939943541853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3373204820615959962361235 5059807230923939943541853)
              ·
                refine ⟨1897427711596477478828195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5059807230923939943541853 1897427711596477478828195)
                ·
                  refine ⟨2846141567394716218242293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1897427711596477478828195 2846141567394716218242293)
                  ·
                    refine ⟨266825771943254645460215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2846141567394716218242293 266825771943254645460215)
                    ·
                      rfl

theorem cell23_1558924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 1, 5].length) (baseStart_1558924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558924 prefixEnd_1558924 := by exact prefixLift 1558924
  have htrace : WordTrace (prefixWord ++ tailWord_1558924) baseStart_1558924 baseEnd_1558924 := by
    simpa [prefixWord, tailWord_1558924, baseEnd_1558924] using wordTrace_append hprefix tailTrace_1558924
  have hstable : (prefixWord ++ tailWord_1558924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558924).length < 2 ^ (prefixWord ++ tailWord_1558924).sum := by decide
  have hdescent : baseEnd_1558924 < baseStart_1558924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558938 : List Nat := [3, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3]
def baseStart_1558938 : Nat := 118140960795 + 1558938 * 2 ^ 59
def prefixEnd_1558938 : Nat := 4983230072969 + 3 ^ 40 * 1558938 * 2
def baseEnd_1558938 : Nat := 800484504558926881605581

theorem tailTrace_1558938 : CollatzResearch.WordTrace tailWord_1558938 prefixEnd_1558938 800484504558926881605581 := by
  unfold tailWord_1558938
  simp only [CollatzResearch.WordTrace]
  refine ⟨14214785006560336564657367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37906093350827564172419645 14214785006560336564657367)
  ·
    refine ⟨21322177509840504846986051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14214785006560336564657367 21322177509840504846986051)
    ·
      refine ⟨31983266264760757270479077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21322177509840504846986051 31983266264760757270479077)
      ·
        refine ⟨5996862424642641988214827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31983266264760757270479077 5996862424642641988214827)
        ·
          refine ⟨8995293636963962982322241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5996862424642641988214827 8995293636963962982322241)
          ·
            refine ⟨6746470227722972236741681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8995293636963962982322241 6746470227722972236741681)
            ·
              refine ⟨5059852670792229177556261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6746470227722972236741681 5059852670792229177556261)
              ·
                refine ⟨948722375773542970791799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5059852670792229177556261 948722375773542970791799)
                ·
                  refine ⟨1423083563660314456187699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 948722375773542970791799 1423083563660314456187699)
                  ·
                    refine ⟨2134625345490471684281549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1423083563660314456187699 2134625345490471684281549)
                    ·
                      refine ⟨800484504558926881605581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2134625345490471684281549 800484504558926881605581)
                      ·
                        rfl

theorem cell23_1558938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_1558938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558938 prefixEnd_1558938 := by exact prefixLift 1558938
  have htrace : WordTrace (prefixWord ++ tailWord_1558938) baseStart_1558938 baseEnd_1558938 := by
    simpa [prefixWord, tailWord_1558938, baseEnd_1558938] using wordTrace_append hprefix tailTrace_1558938
  have hstable : (prefixWord ++ tailWord_1558938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558938).length < 2 ^ (prefixWord ++ tailWord_1558938).sum := by decide
  have hdescent : baseEnd_1558938 < baseStart_1558938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558947 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 5]
def baseStart_1558947 : Nat := 118140960795 + 1558947 * 2 ^ 59
def prefixEnd_1558947 : Nat := 4983230072969 + 3 ^ 40 * 1558947 * 2
def baseEnd_1558947 : Nat := 800489125884817346393039

theorem tailTrace_1558947 : CollatzResearch.WordTrace tailWord_1558947 prefixEnd_1558947 800489125884817346393039 := by
  unfold tailWord_1558947
  simp only [CollatzResearch.WordTrace]
  refine ⟨56859468283208740795707095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37906312188805827197138063 56859468283208740795707095)
  ·
    refine ⟨85289202424813111193560643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56859468283208740795707095 85289202424813111193560643)
    ·
      refine ⟨127933803637219666790340965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85289202424813111193560643 127933803637219666790340965)
      ·
        refine ⟨23987588181978687523188931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127933803637219666790340965 23987588181978687523188931)
        ·
          refine ⟨35981382272968031284783397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23987588181978687523188931 35981382272968031284783397)
          ·
            refine ⟨6746509176181505865896887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35981382272968031284783397 6746509176181505865896887)
            ·
              refine ⟨10119763764272258798845331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6746509176181505865896887 10119763764272258798845331)
              ·
                refine ⟨15179645646408388198267997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10119763764272258798845331 15179645646408388198267997)
                ·
                  refine ⟨5692367117403145574350499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15179645646408388198267997 5692367117403145574350499)
                  ·
                    refine ⟨8538550676104718361525749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5692367117403145574350499 8538550676104718361525749)
                    ·
                      refine ⟨800489125884817346393039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8538550676104718361525749 800489125884817346393039)
                      ·
                        rfl

theorem cell23_1558947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_1558947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558947 prefixEnd_1558947 := by exact prefixLift 1558947
  have htrace : WordTrace (prefixWord ++ tailWord_1558947) baseStart_1558947 baseEnd_1558947 := by
    simpa [prefixWord, tailWord_1558947, baseEnd_1558947] using wordTrace_append hprefix tailTrace_1558947
  have hstable : (prefixWord ++ tailWord_1558947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558947).length < 2 ^ (prefixWord ++ tailWord_1558947).sum := by decide
  have hdescent : baseEnd_1558947 < baseStart_1558947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558961 : List Nat := [1, 2, 2, 4, 1, 3, 2, 2, 1, 1, 4]
def baseStart_1558961 : Nat := 118140960795 + 1558961 * 2 ^ 59
def prefixEnd_1558961 : Nat := 4983230072969 + 3 ^ 40 * 1558961 * 2
def baseEnd_1558961 : Nat := 800496314613980291617975

theorem tailTrace_1558961 : CollatzResearch.WordTrace tailWord_1558961 prefixEnd_1558961 800496314613980291617975 := by
  unfold tailWord_1558961
  simp only [CollatzResearch.WordTrace]
  refine ⟨56859978905158021186716737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37906652603438680791144491 56859978905158021186716737)
  ·
    refine ⟨42644984178868515890037553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56859978905158021186716737 42644984178868515890037553)
    ·
      refine ⟨31983738134151386917528165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42644984178868515890037553 31983738134151386917528165)
      ·
        refine ⟨5996950900153385047036531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31983738134151386917528165 5996950900153385047036531)
        ·
          refine ⟨8995426350230077570554797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5996950900153385047036531 8995426350230077570554797)
          ·
            refine ⟨3373284881336279088958049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8995426350230077570554797 3373284881336279088958049)
            ·
              refine ⟨2529963661002209316718537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3373284881336279088958049 2529963661002209316718537)
              ·
                refine ⟨1897472745751656987538903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2529963661002209316718537 1897472745751656987538903)
                ·
                  refine ⟨2846209118627485481308355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1897472745751656987538903 2846209118627485481308355)
                  ·
                    refine ⟨4269313677941228221962533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2846209118627485481308355 4269313677941228221962533)
                    ·
                      refine ⟨800496314613980291617975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4269313677941228221962533 800496314613980291617975)
                      ·
                        rfl

theorem cell23_1558961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_1558961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558961 prefixEnd_1558961 := by exact prefixLift 1558961
  have htrace : WordTrace (prefixWord ++ tailWord_1558961) baseStart_1558961 baseEnd_1558961 := by
    simpa [prefixWord, tailWord_1558961, baseEnd_1558961] using wordTrace_append hprefix tailTrace_1558961
  have hstable : (prefixWord ++ tailWord_1558961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558961).length < 2 ^ (prefixWord ++ tailWord_1558961).sum := by decide
  have hdescent : baseEnd_1558961 < baseStart_1558961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558967 : List Nat := [1, 1, 3, 1, 3, 4, 1, 9]
def baseStart_1558967 : Nat := 118140960795 + 1558967 * 2 ^ 59
def prefixEnd_1558967 : Nat := 4983230072969 + 3 ^ 40 * 1558967 * 2
def baseEnd_1558967 : Nat := 29648125759181750671961

theorem tailTrace_1558967 : CollatzResearch.WordTrace tailWord_1558967 prefixEnd_1558967 29648125759181750671961 := by
  unfold tailWord_1558967
  simp only [CollatzResearch.WordTrace]
  refine ⟨56860197743136284211435155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37906798495424189474290103 56860197743136284211435155)
  ·
    refine ⟨85290296614704426317152733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56860197743136284211435155 85290296614704426317152733)
    ·
      refine ⟨31983861230514159868932275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85290296614704426317152733 31983861230514159868932275)
      ·
        refine ⟨47975791845771239803398413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31983861230514159868932275 47975791845771239803398413)
        ·
          refine ⟨17990921942164214926274405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47975791845771239803398413 17990921942164214926274405)
          ·
            refine ⟨3373297864155790298676451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17990921942164214926274405 3373297864155790298676451)
            ·
              refine ⟨5059946796233685448014677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3373297864155790298676451 5059946796233685448014677)
              ·
                refine ⟨29648125759181750671961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5059946796233685448014677 29648125759181750671961)
                ·
                  rfl

theorem cell23_1558967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 9].length) (baseStart_1558967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558967 prefixEnd_1558967 := by exact prefixLift 1558967
  have htrace : WordTrace (prefixWord ++ tailWord_1558967) baseStart_1558967 baseEnd_1558967 := by
    simpa [prefixWord, tailWord_1558967, baseEnd_1558967] using wordTrace_append hprefix tailTrace_1558967
  have hstable : (prefixWord ++ tailWord_1558967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558967).length < 2 ^ (prefixWord ++ tailWord_1558967).sum := by decide
  have hdescent : baseEnd_1558967 < baseStart_1558967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558974 : List Nat := [4, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_1558974 : Nat := 118140960795 + 1558974 * 2 ^ 59
def prefixEnd_1558974 : Nat := 4983230072969 + 3 ^ 40 * 1558974 * 2
def baseEnd_1558974 : Nat := 800502989862488740755415

theorem tailTrace_1558974 : CollatzResearch.WordTrace tailWord_1558974 prefixEnd_1558974 800502989862488740755415 := by
  unfold tailWord_1558974
  simp only [CollatzResearch.WordTrace]
  refine ⟨7107556631763865550867497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37906968702740616271293317 7107556631763865550867497)
  ·
    refine ⟨5330667473822899163150623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7107556631763865550867497 5330667473822899163150623)
    ·
      refine ⟨7996001210734348744725935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5330667473822899163150623 7996001210734348744725935)
      ·
        refine ⟨11994001816101523117088903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7996001210734348744725935 11994001816101523117088903)
        ·
          refine ⟨17991002724152284675633355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11994001816101523117088903 17991002724152284675633355)
          ·
            refine ⟨26986504086228427013450033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17991002724152284675633355 26986504086228427013450033)
            ·
              refine ⟨20239878064671320260087525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26986504086228427013450033 20239878064671320260087525)
              ·
                refine ⟨3794977137125872548766411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20239878064671320260087525 3794977137125872548766411)
                ·
                  refine ⟨5692465705688808823149617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3794977137125872548766411 5692465705688808823149617)
                  ·
                    refine ⟨4269349279266606617362213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5692465705688808823149617 4269349279266606617362213)
                    ·
                      refine ⟨800502989862488740755415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4269349279266606617362213 800502989862488740755415)
                      ·
                        rfl

theorem cell23_1558974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_1558974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1558974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1558974 prefixEnd_1558974 := by exact prefixLift 1558974
  have htrace : WordTrace (prefixWord ++ tailWord_1558974) baseStart_1558974 baseEnd_1558974 := by
    simpa [prefixWord, tailWord_1558974, baseEnd_1558974] using wordTrace_append hprefix tailTrace_1558974
  have hstable : (prefixWord ++ tailWord_1558974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558974).length < 2 ^ (prefixWord ++ tailWord_1558974).sum := by decide
  have hdescent : baseEnd_1558974 < baseStart_1558974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559017 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 4, 3, 4]
def baseStart_1559017 : Nat := 118140960795 + 1559017 * 2 ^ 59
def prefixEnd_1559017 : Nat := 4983230072969 + 3 ^ 40 * 1559017 * 2
def baseEnd_1559017 : Nat := 800525069530632072517717

theorem tailTrace_1559017 : CollatzResearch.WordTrace tailWord_1559017 prefixEnd_1559017 800525069530632072517717 := by
  unfold tailWord_1559017
  simp only [CollatzResearch.WordTrace]
  refine ⟨56862021392955142750755305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37908014261970095167170203 56862021392955142750755305)
  ·
    refine ⟨42646516044716357063066479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56862021392955142750755305 42646516044716357063066479)
    ·
      refine ⟨63969774067074535594599719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42646516044716357063066479 63969774067074535594599719)
      ·
        refine ⟨95954661100611803391899579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63969774067074535594599719 95954661100611803391899579)
        ·
          refine ⟨143931991650917705087849369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95954661100611803391899579 143931991650917705087849369)
          ·
            refine ⟨107948993738188278815887027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143931991650917705087849369 107948993738188278815887027)
            ·
              refine ⟨161923490607282418223830541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107948993738188278815887027 161923490607282418223830541)
              ·
                refine ⟨60721308977730906833936453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161923490607282418223830541 60721308977730906833936453)
                ·
                  refine ⟨11385245433324545031363085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60721308977730906833936453 11385245433324545031363085)
                  ·
                    refine ⟨4269467037496704386761157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11385245433324545031363085 4269467037496704386761157)
                    ·
                      refine ⟨800525069530632072517717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4269467037496704386761157 800525069530632072517717)
                      ·
                        rfl

theorem cell23_1559017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 3, 4].length) (baseStart_1559017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559017 prefixEnd_1559017 := by exact prefixLift 1559017
  have htrace : WordTrace (prefixWord ++ tailWord_1559017) baseStart_1559017 baseEnd_1559017 := by
    simpa [prefixWord, tailWord_1559017, baseEnd_1559017] using wordTrace_append hprefix tailTrace_1559017
  have hstable : (prefixWord ++ tailWord_1559017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559017).length < 2 ^ (prefixWord ++ tailWord_1559017).sum := by decide
  have hdescent : baseEnd_1559017 < baseStart_1559017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559046 : List Nat := [6, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_1559046 : Nat := 118140960795 + 1559046 * 2 ^ 59
def prefixEnd_1559046 : Nat := 4983230072969 + 3 ^ 40 * 1559046 * 2
def baseEnd_1559046 : Nat := 800539960469612459055085

theorem tailTrace_1559046 : CollatzResearch.WordTrace tailWord_1559046 prefixEnd_1559046 800539960469612459055085 := by
  unfold tailWord_1559046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1776971222182815021986281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37908719406566720469040661 1776971222182815021986281)
  ·
    refine ⟨1332728416637111266489711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1776971222182815021986281 1332728416637111266489711)
    ·
      refine ⟨1999092624955666899734567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1332728416637111266489711 1999092624955666899734567)
      ·
        refine ⟨2998638937433500349601851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1999092624955666899734567 2998638937433500349601851)
        ·
          refine ⟨4497958406150250524402777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2998638937433500349601851 4497958406150250524402777)
          ·
            refine ⟨3373468804612687893302083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4497958406150250524402777 3373468804612687893302083)
            ·
              refine ⟨5060203206919031839953125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3373468804612687893302083 5060203206919031839953125)
              ·
                refine ⟨948788101297318469991211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5060203206919031839953125 948788101297318469991211)
                ·
                  refine ⟨1423182151945977704986817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 948788101297318469991211 1423182151945977704986817)
                  ·
                    refine ⟨1067386613959483278740113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1423182151945977704986817 1067386613959483278740113)
                    ·
                      refine ⟨800539960469612459055085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1067386613959483278740113 800539960469612459055085)
                      ·
                        rfl

theorem cell23_1559046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_1559046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559046 prefixEnd_1559046 := by exact prefixLift 1559046
  have htrace : WordTrace (prefixWord ++ tailWord_1559046) baseStart_1559046 baseEnd_1559046 := by
    simpa [prefixWord, tailWord_1559046, baseEnd_1559046] using wordTrace_append hprefix tailTrace_1559046
  have hstable : (prefixWord ++ tailWord_1559046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559046).length < 2 ^ (prefixWord ++ tailWord_1559046).sum := by decide
  have hdescent : baseEnd_1559046 < baseStart_1559046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559064 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 1, 4, 4]
def baseStart_1559064 : Nat := 118140960795 + 1559064 * 2 ^ 59
def prefixEnd_1559064 : Nat := 4983230072969 + 3 ^ 40 * 1559064 * 2
def baseEnd_1559064 : Nat := 800549203121393388630001

theorem tailTrace_1559064 : CollatzResearch.WordTrace tailWord_1559064 prefixEnd_1559064 800549203121393388630001 := by
  unfold tailWord_1559064
  simp only [CollatzResearch.WordTrace]
  refine ⟨28431867811892434888858123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37909157082523246518477497 28431867811892434888858123)
  ·
    refine ⟨42647801717838652333287185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28431867811892434888858123 42647801717838652333287185)
    ·
      refine ⟨31985851288378989249965389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42647801717838652333287185 31985851288378989249965389)
      ·
        refine ⟨11994694233142120968737021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31985851288378989249965389 11994694233142120968737021)
        ·
          refine ⟨4498010337428295363276383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11994694233142120968737021 4498010337428295363276383)
          ·
            refine ⟨6747015506142443044914575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4498010337428295363276383 6747015506142443044914575)
            ·
              refine ⟨10120523259213664567371863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6747015506142443044914575 10120523259213664567371863)
              ·
                refine ⟨15180784888820496851057795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10120523259213664567371863 15180784888820496851057795)
                ·
                  refine ⟨22771177333230745276586693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15180784888820496851057795 22771177333230745276586693)
                  ·
                    refine ⟨4269595749980764739360005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22771177333230745276586693 4269595749980764739360005)
                    ·
                      refine ⟨800549203121393388630001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4269595749980764739360005 800549203121393388630001)
                      ·
                        rfl

theorem cell23_1559064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_1559064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559064 prefixEnd_1559064 := by exact prefixLift 1559064
  have htrace : WordTrace (prefixWord ++ tailWord_1559064) baseStart_1559064 baseEnd_1559064 := by
    simpa [prefixWord, tailWord_1559064, baseEnd_1559064] using wordTrace_append hprefix tailTrace_1559064
  have hstable : (prefixWord ++ tailWord_1559064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559064).length < 2 ^ (prefixWord ++ tailWord_1559064).sum := by decide
  have hdescent : baseEnd_1559064 < baseStart_1559064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559068 : List Nat := [2, 2, 3, 1, 2, 3, 2, 1, 1, 4, 2]
def baseStart_1559068 : Nat := 118140960795 + 1559068 * 2 ^ 59
def prefixEnd_1559068 : Nat := 4983230072969 + 3 ^ 40 * 1559068 * 2
def baseEnd_1559068 : Nat := 800551257044011372979983

theorem tailTrace_1559068 : CollatzResearch.WordTrace tailWord_1559068 prefixEnd_1559068 800551257044011372979983 := by
  unfold tailWord_1559068
  simp only [CollatzResearch.WordTrace]
  refine ⟨28431940757885189230430929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37909254343846918973907905 28431940757885189230430929)
  ·
    refine ⟨21323955568413891922823197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28431940757885189230430929 21323955568413891922823197)
    ·
      refine ⟨7996483338155209471058699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21323955568413891922823197 7996483338155209471058699)
      ·
        refine ⟨11994725007232814206588049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7996483338155209471058699 11994725007232814206588049)
        ·
          refine ⟨8996043755424610654941037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11994725007232814206588049 8996043755424610654941037)
          ·
            refine ⟨3373516408284228995602889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8996043755424610654941037 3373516408284228995602889)
            ·
              refine ⟨2530137306213171746702167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3373516408284228995602889 2530137306213171746702167)
              ·
                refine ⟨3795205959319757620053251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2530137306213171746702167 3795205959319757620053251)
                ·
                  refine ⟨5692808938979636430079877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3795205959319757620053251 5692808938979636430079877)
                  ·
                    refine ⟨1067401676058681830639977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5692808938979636430079877 1067401676058681830639977)
                    ·
                      refine ⟨800551257044011372979983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1067401676058681830639977 800551257044011372979983)
                      ·
                        rfl

theorem cell23_1559068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_1559068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559068 prefixEnd_1559068 := by exact prefixLift 1559068
  have htrace : WordTrace (prefixWord ++ tailWord_1559068) baseStart_1559068 baseEnd_1559068 := by
    simpa [prefixWord, tailWord_1559068, baseEnd_1559068] using wordTrace_append hprefix tailTrace_1559068
  have hstable : (prefixWord ++ tailWord_1559068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559068).length < 2 ^ (prefixWord ++ tailWord_1559068).sum := by decide
  have hdescent : baseEnd_1559068 < baseStart_1559068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559091 : List Nat := [1, 1, 1, 2, 4, 2, 4, 3, 5]
def baseStart_1559091 : Nat := 118140960795 + 1559091 * 2 ^ 59
def prefixEnd_1559091 : Nat := 4983230072969 + 3 ^ 40 * 1559091 * 2
def baseEnd_1559091 : Nat := 88951451899896086999153

theorem tailTrace_1559091 : CollatzResearch.WordTrace tailWord_1559091 prefixEnd_1559091 88951451899896086999153 := by
  unfold tailWord_1559091
  simp only [CollatzResearch.WordTrace]
  refine ⟨56864720394687053388949127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37909813596458035592632751 56864720394687053388949127)
  ·
    refine ⟨85297080592030580083423691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56864720394687053388949127 85297080592030580083423691)
    ·
      refine ⟨127945620888045870125135537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85297080592030580083423691 127945620888045870125135537)
      ·
        refine ⟨95959215666034402593851653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127945620888045870125135537 95959215666034402593851653)
        ·
          refine ⟨17992352937381450486347185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95959215666034402593851653 17992352937381450486347185)
          ·
            refine ⟨13494264703036087864760389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17992352937381450486347185 13494264703036087864760389)
            ·
              refine ⟨2530174631819266474642573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13494264703036087864760389 2530174631819266474642573)
              ·
                refine ⟨948815486932224927990965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2530174631819266474642573 948815486932224927990965)
                ·
                  refine ⟨88951451899896086999153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 948815486932224927990965 88951451899896086999153)
                  ·
                    rfl

theorem cell23_1559091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 5].length) (baseStart_1559091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559091 prefixEnd_1559091 := by exact prefixLift 1559091
  have htrace : WordTrace (prefixWord ++ tailWord_1559091) baseStart_1559091 baseEnd_1559091 := by
    simpa [prefixWord, tailWord_1559091, baseEnd_1559091] using wordTrace_append hprefix tailTrace_1559091
  have hstable : (prefixWord ++ tailWord_1559091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559091).length < 2 ^ (prefixWord ++ tailWord_1559091).sum := by decide
  have hdescent : baseEnd_1559091 < baseStart_1559091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559101 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 2, 3, 3]
def baseStart_1559101 : Nat := 118140960795 + 1559101 * 2 ^ 59
def prefixEnd_1559101 : Nat := 4983230072969 + 3 ^ 40 * 1559101 * 2
def baseEnd_1559101 : Nat := 800568201905609743867331

theorem tailTrace_1559101 : CollatzResearch.WordTrace tailWord_1559101 prefixEnd_1559101 800568201905609743867331 := by
  unfold tailWord_1559101
  simp only [CollatzResearch.WordTrace]
  refine ⟨56865085124650825096813157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37910056749767216731208771 56865085124650825096813157)
  ·
    refine ⟨10662203460872029705652467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56865085124650825096813157 10662203460872029705652467)
    ·
      refine ⟨15993305191308044558478701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10662203460872029705652467 15993305191308044558478701)
      ·
        refine ⟨5997489446740516709429513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15993305191308044558478701 5997489446740516709429513)
        ·
          refine ⟨4498117085055387532072135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5997489446740516709429513 4498117085055387532072135)
          ·
            refine ⟨6747175627583081298108203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4498117085055387532072135 6747175627583081298108203)
            ·
              refine ⟨10120763441374621947162305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6747175627583081298108203 10120763441374621947162305)
              ·
                refine ⟨7590572581030966460371729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10120763441374621947162305 7590572581030966460371729)
                ·
                  refine ⟨5692929435773224845278797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7590572581030966460371729 5692929435773224845278797)
                  ·
                    refine ⟨2134848538414959316979549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5692929435773224845278797 2134848538414959316979549)
                    ·
                      refine ⟨800568201905609743867331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2134848538414959316979549 800568201905609743867331)
                      ·
                        rfl

theorem cell23_1559101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_1559101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559101 prefixEnd_1559101 := by exact prefixLift 1559101
  have htrace : WordTrace (prefixWord ++ tailWord_1559101) baseStart_1559101 baseEnd_1559101 := by
    simpa [prefixWord, tailWord_1559101, baseEnd_1559101] using wordTrace_append hprefix tailTrace_1559101
  have hstable : (prefixWord ++ tailWord_1559101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559101).length < 2 ^ (prefixWord ++ tailWord_1559101).sum := by decide
  have hdescent : baseEnd_1559101 < baseStart_1559101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559102 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 4, 2, 2]
def baseStart_1559102 : Nat := 118140960795 + 1559102 * 2 ^ 59
def prefixEnd_1559102 : Nat := 4983230072969 + 3 ^ 40 * 1559102 * 2
def baseEnd_1559102 : Nat := 800568715386264239954827

theorem tailTrace_1559102 : CollatzResearch.WordTrace tailWord_1559102 prefixEnd_1559102 800568715386264239954827 := by
  unfold tailWord_1559102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7108140199705900283449945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37910081065098134845066373 7108140199705900283449945)
  ·
    refine ⟨5331105149779425212587459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7108140199705900283449945 5331105149779425212587459)
    ·
      refine ⟨7996657724669137818881189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5331105149779425212587459 7996657724669137818881189)
      ·
        refine ⟨1499373323375463341040223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7996657724669137818881189 1499373323375463341040223)
        ·
          refine ⟨2249059985063195011560335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1499373323375463341040223 2249059985063195011560335)
          ·
            refine ⟨3373589977594792517340503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2249059985063195011560335 3373589977594792517340503)
            ·
              refine ⟨5060384966392188776010755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3373589977594792517340503 5060384966392188776010755)
              ·
                refine ⟨7590577449588283164016133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5060384966392188776010755 7590577449588283164016133)
                ·
                  refine ⟨1423233271797803093253025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7590577449588283164016133 1423233271797803093253025)
                  ·
                    refine ⟨1067424953848352319939769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1423233271797803093253025 1067424953848352319939769)
                    ·
                      refine ⟨800568715386264239954827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1067424953848352319939769 800568715386264239954827)
                      ·
                        rfl

theorem cell23_1559102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_1559102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559102 prefixEnd_1559102 := by exact prefixLift 1559102
  have htrace : WordTrace (prefixWord ++ tailWord_1559102) baseStart_1559102 baseEnd_1559102 := by
    simpa [prefixWord, tailWord_1559102, baseEnd_1559102] using wordTrace_append hprefix tailTrace_1559102
  have hstable : (prefixWord ++ tailWord_1559102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559102).length < 2 ^ (prefixWord ++ tailWord_1559102).sum := by decide
  have hdescent : baseEnd_1559102 < baseStart_1559102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559104 : List Nat := [2, 1, 1, 2, 2, 2, 2, 4, 2, 5]
def baseStart_1559104 : Nat := 118140960795 + 1559104 * 2 ^ 59
def prefixEnd_1559104 : Nat := 4983230072969 + 3 ^ 40 * 1559104 * 2
def baseEnd_1559104 : Nat := 266856580782524410709939

theorem tailTrace_1559104 : CollatzResearch.WordTrace tailWord_1559104 prefixEnd_1559104 266856580782524410709939 := by
  unfold tailWord_1559104
  simp only [CollatzResearch.WordTrace]
  refine ⟨28432597271819978304586183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37910129695759971072781577 28432597271819978304586183)
  ·
    refine ⟨42648895907729967456879275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28432597271819978304586183 42648895907729967456879275)
    ·
      refine ⟨63973343861594951185318913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42648895907729967456879275 63973343861594951185318913)
      ·
        refine ⟨47980007896196213388989185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63973343861594951185318913 47980007896196213388989185)
        ·
          refine ⟨35985005922147160041741889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47980007896196213388989185 35985005922147160041741889)
          ·
            refine ⟨26988754441610370031306417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35985005922147160041741889 26988754441610370031306417)
            ·
              refine ⟨20241565831207777523479813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26988754441610370031306417 20241565831207777523479813)
              ·
                refine ⟨3795293593351458285652465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20241565831207777523479813 3795293593351458285652465)
                ·
                  refine ⟨2846470195013593714239349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3795293593351458285652465 2846470195013593714239349)
                  ·
                    refine ⟨266856580782524410709939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2846470195013593714239349 266856580782524410709939)
                    ·
                      rfl

theorem cell23_1559104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 2, 5].length) (baseStart_1559104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559104 prefixEnd_1559104 := by exact prefixLift 1559104
  have htrace : WordTrace (prefixWord ++ tailWord_1559104) baseStart_1559104 baseEnd_1559104 := by
    simpa [prefixWord, tailWord_1559104, baseEnd_1559104] using wordTrace_append hprefix tailTrace_1559104
  have hstable : (prefixWord ++ tailWord_1559104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559104).length < 2 ^ (prefixWord ++ tailWord_1559104).sum := by decide
  have hdescent : baseEnd_1559104 < baseStart_1559104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559161 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 4, 2, 3]
def baseStart_1559161 : Nat := 118140960795 + 1559161 * 2 ^ 59
def prefixEnd_1559161 : Nat := 4983230072969 + 3 ^ 40 * 1559161 * 2
def baseEnd_1559161 : Nat := 800599010744879509117055

theorem tailTrace_1559161 : CollatzResearch.WordTrace tailWord_1559161 prefixEnd_1559161 800599010744879509117055 := by
  unfold tailWord_1559161
  simp only [CollatzResearch.WordTrace]
  refine ⟨56867273504433455343997337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37911515669622303562664891 56867273504433455343997337)
  ·
    refine ⟨42650455128325091507998003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56867273504433455343997337 42650455128325091507998003)
    ·
      refine ⟨63975682692487637261997005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42650455128325091507998003 63975682692487637261997005)
      ·
        refine ⟨23990881009682863973248877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63975682692487637261997005 23990881009682863973248877)
        ·
          refine ⟨8996580378631073989968329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23990881009682863973248877 8996580378631073989968329)
          ·
            refine ⟨6747435283973305492476247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8996580378631073989968329 6747435283973305492476247)
            ·
              refine ⟨10121152925959958238714371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6747435283973305492476247 10121152925959958238714371)
              ·
                refine ⟨15181729388939937358071557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10121152925959958238714371 15181729388939937358071557)
                ·
                  refine ⟨2846574260426238254638417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15181729388939937358071557 2846574260426238254638417)
                  ·
                    refine ⟨2134930695319678690978813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2846574260426238254638417 2134930695319678690978813)
                    ·
                      refine ⟨800599010744879509117055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2134930695319678690978813 800599010744879509117055)
                      ·
                        rfl

theorem cell23_1559161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_1559161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559161 prefixEnd_1559161 := by exact prefixLift 1559161
  have htrace : WordTrace (prefixWord ++ tailWord_1559161) baseStart_1559161 baseEnd_1559161 := by
    simpa [prefixWord, tailWord_1559161, baseEnd_1559161] using wordTrace_append hprefix tailTrace_1559161
  have hstable : (prefixWord ++ tailWord_1559161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559161).length < 2 ^ (prefixWord ++ tailWord_1559161).sum := by decide
  have hdescent : baseEnd_1559161 < baseStart_1559161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559164 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 8]
def baseStart_1559164 : Nat := 118140960795 + 1559164 * 2 ^ 59
def prefixEnd_1559164 : Nat := 4983230072969 + 3 ^ 40 * 1559164 * 2
def baseEnd_1559164 : Nat := 88955616798538110819949

theorem tailTrace_1559164 : CollatzResearch.WordTrace tailWord_1559164 prefixEnd_1559164 88955616798538110819949 := by
  unfold tailWord_1559164
  simp only [CollatzResearch.WordTrace]
  refine ⟨28433691461711293428178273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37911588615615057904237697 28433691461711293428178273)
  ·
    refine ⟨21325268596283470071133705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28433691461711293428178273 21325268596283470071133705)
    ·
      refine ⟨15993951447212602553350279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21325268596283470071133705 15993951447212602553350279)
      ·
        refine ⟨23990927170818903830025419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15993951447212602553350279 23990927170818903830025419)
        ·
          refine ⟨35986390756228355745038129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23990927170818903830025419 35986390756228355745038129)
          ·
            refine ⟨26989793067171266808778597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35986390756228355745038129 26989793067171266808778597)
            ·
              refine ⟨5060586200094612526645987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26989793067171266808778597 5060586200094612526645987)
              ·
                refine ⟨7590879300141918789968981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5060586200094612526645987 7590879300141918789968981)
                ·
                  refine ⟨88955616798538110819949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7590879300141918789968981 88955616798538110819949)
                  ·
                    rfl

theorem cell23_1559164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 8].length) (baseStart_1559164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559164 prefixEnd_1559164 := by exact prefixLift 1559164
  have htrace : WordTrace (prefixWord ++ tailWord_1559164) baseStart_1559164 baseEnd_1559164 := by
    simpa [prefixWord, tailWord_1559164, baseEnd_1559164] using wordTrace_append hprefix tailTrace_1559164
  have hstable : (prefixWord ++ tailWord_1559164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559164).length < 2 ^ (prefixWord ++ tailWord_1559164).sum := by decide
  have hdescent : baseEnd_1559164 < baseStart_1559164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559168 : List Nat := [2, 1, 1, 2, 1, 7, 1, 1, 3, 4]
def baseStart_1559168 : Nat := 118140960795 + 1559168 * 2 ^ 59
def prefixEnd_1559168 : Nat := 4983230072969 + 3 ^ 40 * 1559168 * 2
def baseEnd_1559168 : Nat := 266867535036486993909841

theorem tailTrace_1559168 : CollatzResearch.WordTrace tailWord_1559168 prefixEnd_1559168 266867535036486993909841 := by
  unfold tailWord_1559168
  simp only [CollatzResearch.WordTrace]
  refine ⟨28433764407704047769751079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37911685876938730359668105 28433764407704047769751079)
  ·
    refine ⟨42650646611556071654626619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28433764407704047769751079 42650646611556071654626619)
    ·
      refine ⟨63975969917334107481939929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42650646611556071654626619 63975969917334107481939929)
      ·
        refine ⟨47981977438000580611454947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63975969917334107481939929 47981977438000580611454947)
        ·
          refine ⟨71972966157000870917182421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47981977438000580611454947 71972966157000870917182421)
          ·
            refine ⟨1686866394304707912121463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 71972966157000870917182421 1686866394304707912121463)
            ·
              refine ⟨2530299591457061868182195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1686866394304707912121463 2530299591457061868182195)
              ·
                refine ⟨3795449387185592802273293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2530299591457061868182195 3795449387185592802273293)
                ·
                  refine ⟨1423293520194597300852485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3795449387185592802273293 1423293520194597300852485)
                  ·
                    refine ⟨266867535036486993909841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1423293520194597300852485 266867535036486993909841)
                    ·
                      rfl

theorem cell23_1559168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 3, 4].length) (baseStart_1559168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559168 prefixEnd_1559168 := by exact prefixLift 1559168
  have htrace : WordTrace (prefixWord ++ tailWord_1559168) baseStart_1559168 baseEnd_1559168 := by
    simpa [prefixWord, tailWord_1559168, baseEnd_1559168] using wordTrace_append hprefix tailTrace_1559168
  have hstable : (prefixWord ++ tailWord_1559168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559168).length < 2 ^ (prefixWord ++ tailWord_1559168).sum := by decide
  have hdescent : baseEnd_1559168 < baseStart_1559168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559170 : List Nat := [3, 4, 3, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_1559170 : Nat := 118140960795 + 1559170 * 2 ^ 59
def prefixEnd_1559170 : Nat := 4983230072969 + 3 ^ 40 * 1559170 * 2
def baseEnd_1559170 : Nat := 800603632070769973904515

theorem tailTrace_1559170 : CollatzResearch.WordTrace tailWord_1559170 prefixEnd_1559170 800603632070769973904515 := by
  unfold tailWord_1559170
  simp only [CollatzResearch.WordTrace]
  refine ⟨14216900440350212470268741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37911734507600566587383309 14216900440350212470268741)
  ·
    refine ⟨2665668832565664838175389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14216900440350212470268741 2665668832565664838175389)
    ·
      refine ⟨999625812212124314315771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2665668832565664838175389 999625812212124314315771)
      ·
        refine ⟨1499438718318186471473657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 999625812212124314315771 1499438718318186471473657)
        ·
          refine ⟨1124579038738639853605243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1499438718318186471473657 1124579038738639853605243)
          ·
            refine ⟨1686868558107959780407865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1124579038738639853605243 1686868558107959780407865)
            ·
              refine ⟨1265151418580969835305899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1686868558107959780407865 1265151418580969835305899)
              ·
                refine ⟨1897727127871454752958849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1265151418580969835305899 1897727127871454752958849)
                ·
                  refine ⟨1423295345903591064719137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1897727127871454752958849 1423295345903591064719137)
                  ·
                    refine ⟨1067471509427693298539353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1423295345903591064719137 1067471509427693298539353)
                    ·
                      refine ⟨800603632070769973904515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1067471509427693298539353 800603632070769973904515)
                      ·
                        rfl

theorem cell23_1559170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_1559170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559170 prefixEnd_1559170 := by exact prefixLift 1559170
  have htrace : WordTrace (prefixWord ++ tailWord_1559170) baseStart_1559170 baseEnd_1559170 := by
    simpa [prefixWord, tailWord_1559170, baseEnd_1559170] using wordTrace_append hprefix tailTrace_1559170
  have hstable : (prefixWord ++ tailWord_1559170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559170).length < 2 ^ (prefixWord ++ tailWord_1559170).sum := by decide
  have hdescent : baseEnd_1559170 < baseStart_1559170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559231 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 4]
def baseStart_1559231 : Nat := 118140960795 + 1559231 * 2 ^ 59
def prefixEnd_1559231 : Nat := 4983230072969 + 3 ^ 40 * 1559231 * 2
def baseEnd_1559231 : Nat := 800634954390694235241733

theorem tailTrace_1559231 : CollatzResearch.WordTrace tailWord_1559231 prefixEnd_1559231 800634954390694235241733 := by
  unfold tailWord_1559231
  simp only [CollatzResearch.WordTrace]
  refine ⟨56869826614179857299045547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37913217742786571532697031 56869826614179857299045547)
  ·
    refine ⟨85304739921269785948568321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56869826614179857299045547 85304739921269785948568321)
    ·
      refine ⟨63978554940952339461426241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85304739921269785948568321 63978554940952339461426241)
      ·
        refine ⟨47983916205714254596069681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63978554940952339461426241 47983916205714254596069681)
        ·
          refine ⟨35987937154285690947052261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47983916205714254596069681 35987937154285690947052261)
          ·
            refine ⟨6747738216428567052572299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35987937154285690947052261 6747738216428567052572299)
            ·
              refine ⟨10121607324642850578858449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6747738216428567052572299 10121607324642850578858449)
              ·
                refine ⟨7591205493482137934143837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10121607324642850578858449 7591205493482137934143837)
                ·
                  refine ⟨2846702060055801725303939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7591205493482137934143837 2846702060055801725303939)
                  ·
                    refine ⟨4270053090083702587955909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2846702060055801725303939 4270053090083702587955909)
                    ·
                      refine ⟨800634954390694235241733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4270053090083702587955909 800634954390694235241733)
                      ·
                        rfl

theorem cell23_1559231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_1559231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559231 prefixEnd_1559231 := by exact prefixLift 1559231
  have htrace : WordTrace (prefixWord ++ tailWord_1559231) baseStart_1559231 baseEnd_1559231 := by
    simpa [prefixWord, tailWord_1559231, baseEnd_1559231] using wordTrace_append hprefix tailTrace_1559231
  have hstable : (prefixWord ++ tailWord_1559231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559231).length < 2 ^ (prefixWord ++ tailWord_1559231).sum := by decide
  have hdescent : baseEnd_1559231 < baseStart_1559231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559265 : List Nat := [1, 2, 3, 1, 4, 1, 4, 1, 1, 1, 4]
def baseStart_1559265 : Nat := 118140960795 + 1559265 * 2 ^ 59
def prefixEnd_1559265 : Nat := 4983230072969 + 3 ^ 40 * 1559265 * 2
def baseEnd_1559265 : Nat := 800652412732947102216577

theorem tailTrace_1559265 : CollatzResearch.WordTrace tailWord_1559265 prefixEnd_1559265 800652412732947102216577 := by
  unfold tailWord_1559265
  simp only [CollatzResearch.WordTrace]
  refine ⟨56871066696056681105783249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37914044464037787403855499 56871066696056681105783249)
  ·
    refine ⟨42653300022042510829337437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56871066696056681105783249 42653300022042510829337437)
    ·
      refine ⟨15994987508265941561001539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42653300022042510829337437 15994987508265941561001539)
      ·
        refine ⟨23992481262398912341502309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15994987508265941561001539 23992481262398912341502309)
        ·
          refine ⟨4498590236699796064031683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23992481262398912341502309 4498590236699796064031683)
          ·
            refine ⟨6747885355049694096047525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4498590236699796064031683 6747885355049694096047525)
            ·
              refine ⟨1265228504071817643008911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6747885355049694096047525 1265228504071817643008911)
              ·
                refine ⟨1897842756107726464513367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1265228504071817643008911 1897842756107726464513367)
                ·
                  refine ⟨2846764134161589696770051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1897842756107726464513367 2846764134161589696770051)
                  ·
                    refine ⟨4270146201242384545155077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2846764134161589696770051 4270146201242384545155077)
                    ·
                      refine ⟨800652412732947102216577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4270146201242384545155077 800652412732947102216577)
                      ·
                        rfl

theorem cell23_1559265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 1, 1, 4].length) (baseStart_1559265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559265 prefixEnd_1559265 := by exact prefixLift 1559265
  have htrace : WordTrace (prefixWord ++ tailWord_1559265) baseStart_1559265 baseEnd_1559265 := by
    simpa [prefixWord, tailWord_1559265, baseEnd_1559265] using wordTrace_append hprefix tailTrace_1559265
  have hstable : (prefixWord ++ tailWord_1559265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559265).length < 2 ^ (prefixWord ++ tailWord_1559265).sum := by decide
  have hdescent : baseEnd_1559265 < baseStart_1559265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559282 : List Nat := [3, 2, 1, 3, 1, 3, 2, 1, 3, 2, 2]
def baseStart_1559282 : Nat := 118140960795 + 1559282 * 2 ^ 59
def prefixEnd_1559282 : Nat := 4983230072969 + 3 ^ 40 * 1559282 * 2
def baseEnd_1559282 : Nat := 800661141904073535703999

theorem tailTrace_1559282 : CollatzResearch.WordTrace tailWord_1559282 prefixEnd_1559282 800661141904073535703999 := by
  unfold tailWord_1559282
  simp only [CollatzResearch.WordTrace]
  refine ⟨14217921684248773252288025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37914457824663395339434733 14217921684248773252288025)
  ·
    refine ⟨10663441263186579939216019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14217921684248773252288025 10663441263186579939216019)
    ·
      refine ⟨15995161894779869908824029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10663441263186579939216019 15995161894779869908824029)
      ·
        refine ⟨5998185710542451215809011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15995161894779869908824029 5998185710542451215809011)
        ·
          refine ⟨8997278565813676823713517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5998185710542451215809011 8997278565813676823713517)
          ·
            refine ⟨3373979462180128808892569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8997278565813676823713517 3373979462180128808892569)
            ·
              refine ⟨2530484596635096606669427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3373979462180128808892569 2530484596635096606669427)
              ·
                refine ⟨3795726894952644910004141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2530484596635096606669427 3795726894952644910004141)
                ·
                  refine ⟨1423397585607241841251553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3795726894952644910004141 1423397585607241841251553)
                  ·
                    refine ⟨1067548189205431380938665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1423397585607241841251553 1067548189205431380938665)
                    ·
                      refine ⟨800661141904073535703999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1067548189205431380938665 800661141904073535703999)
                      ·
                        rfl

theorem cell23_1559282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_1559282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559282 prefixEnd_1559282 := by exact prefixLift 1559282
  have htrace : WordTrace (prefixWord ++ tailWord_1559282) baseStart_1559282 baseEnd_1559282 := by
    simpa [prefixWord, tailWord_1559282, baseEnd_1559282] using wordTrace_append hprefix tailTrace_1559282
  have hstable : (prefixWord ++ tailWord_1559282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559282).length < 2 ^ (prefixWord ++ tailWord_1559282).sum := by decide
  have hdescent : baseEnd_1559282 < baseStart_1559282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559349 : List Nat := [1, 3, 3, 1, 3, 3, 2, 1, 2, 1, 3]
def baseStart_1559349 : Nat := 118140960795 + 1559349 * 2 ^ 59
def prefixEnd_1559349 : Nat := 4983230072969 + 3 ^ 40 * 1559349 * 2
def baseEnd_1559349 : Nat := 800695545107924773566191

theorem tailTrace_1559349 : CollatzResearch.WordTrace tailWord_1559349 prefixEnd_1559349 800695545107924773566191 := by
  unfold tailWord_1559349
  simp only [CollatzResearch.WordTrace]
  refine ⟨56874130427752363451841101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37916086951834908967894067 56874130427752363451841101)
  ·
    refine ⟨21327798910407136294440413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56874130427752363451841101 21327798910407136294440413)
    ·
      refine ⟨7997924591402676110415155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21327798910407136294440413 7997924591402676110415155)
      ·
        refine ⟨11996886887104014165622733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7997924591402676110415155 11996886887104014165622733)
        ·
          refine ⟨4498832582664005312108525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11996886887104014165622733 4498832582664005312108525)
          ·
            refine ⟨1687062218499001992040697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4498832582664005312108525 1687062218499001992040697)
            ·
              refine ⟨1265296663874251494030523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1687062218499001992040697 1265296663874251494030523)
              ·
                refine ⟨1897944995811377241045785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1265296663874251494030523 1897944995811377241045785)
                ·
                  refine ⟨1423458746858532930784339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1897944995811377241045785 1423458746858532930784339)
                  ·
                    refine ⟨2135188120287799396176509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1423458746858532930784339 2135188120287799396176509)
                    ·
                      refine ⟨800695545107924773566191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2135188120287799396176509 800695545107924773566191)
                      ·
                        rfl

theorem cell23_1559349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_1559349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559349 prefixEnd_1559349 := by exact prefixLift 1559349
  have htrace : WordTrace (prefixWord ++ tailWord_1559349) baseStart_1559349 baseEnd_1559349 := by
    simpa [prefixWord, tailWord_1559349, baseEnd_1559349] using wordTrace_append hprefix tailTrace_1559349
  have hstable : (prefixWord ++ tailWord_1559349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559349).length < 2 ^ (prefixWord ++ tailWord_1559349).sum := by decide
  have hdescent : baseEnd_1559349 < baseStart_1559349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559351 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 4]
def baseStart_1559351 : Nat := 118140960795 + 1559351 * 2 ^ 59
def prefixEnd_1559351 : Nat := 4983230072969 + 3 ^ 40 * 1559351 * 2
def baseEnd_1559351 : Nat := 800696572069233765741181

theorem tailTrace_1559351 : CollatzResearch.WordTrace tailWord_1559351 prefixEnd_1559351 800696572069233765741181 := by
  unfold tailWord_1559351
  simp only [CollatzResearch.WordTrace]
  refine ⟨56874203373745117793413907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37916135582496745195609271 56874203373745117793413907)
  ·
    refine ⟨85311305060617676690120861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56874203373745117793413907 85311305060617676690120861)
    ·
      refine ⟨31991739397731628758795323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85311305060617676690120861 31991739397731628758795323)
      ·
        refine ⟨47987609096597443138192985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31991739397731628758795323 47987609096597443138192985)
        ·
          refine ⟨35990706822448082353644739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47987609096597443138192985 35990706822448082353644739)
          ·
            refine ⟨53986060233672123530467109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35990706822448082353644739 53986060233672123530467109)
            ·
              refine ⟨10122386293813523161962583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53986060233672123530467109 10122386293813523161962583)
              ·
                refine ⟨15183579440720284742943875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10122386293813523161962583 15183579440720284742943875)
                ·
                  refine ⟨22775369161080427114415813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15183579440720284742943875 22775369161080427114415813)
                  ·
                    refine ⟨4270381717702580083952965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22775369161080427114415813 4270381717702580083952965)
                    ·
                      refine ⟨800696572069233765741181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4270381717702580083952965 800696572069233765741181)
                      ·
                        rfl

theorem cell23_1559351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_1559351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559351 prefixEnd_1559351 := by exact prefixLift 1559351
  have htrace : WordTrace (prefixWord ++ tailWord_1559351) baseStart_1559351 baseEnd_1559351 := by
    simpa [prefixWord, tailWord_1559351, baseEnd_1559351] using wordTrace_append hprefix tailTrace_1559351
  have hstable : (prefixWord ++ tailWord_1559351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559351).length < 2 ^ (prefixWord ++ tailWord_1559351).sum := by decide
  have hdescent : baseEnd_1559351 < baseStart_1559351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559395 : List Nat := [1, 1, 1, 5, 3, 2, 1, 4, 5]
def baseStart_1559395 : Nat := 118140960795 + 1559395 * 2 ^ 59
def prefixEnd_1559395 : Nat := 4983230072969 + 3 ^ 40 * 1559395 * 2
def baseEnd_1559395 : Nat := 88968796135336843732331

theorem tailTrace_1559395 : CollatzResearch.WordTrace tailWord_1559395 prefixEnd_1559395 88968796135336843732331 := by
  unfold tailWord_1559395
  simp only [CollatzResearch.WordTrace]
  refine ⟨56875808185585713308015639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37917205457057142205343759 56875808185585713308015639)
  ·
    refine ⟨85313712278378569962023459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56875808185585713308015639 85313712278378569962023459)
    ·
      refine ⟨127970568417567854943035189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85313712278378569962023459 127970568417567854943035189)
      ·
        refine ⟨11997240789146986400909549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127970568417567854943035189 11997240789146986400909549)
        ·
          refine ⟨4498965295930119900341081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11997240789146986400909549 4498965295930119900341081)
          ·
            refine ⟨3374223971947589925255811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4498965295930119900341081 3374223971947589925255811)
            ·
              refine ⟨5061335957921384887883717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3374223971947589925255811 5061335957921384887883717)
              ·
                refine ⟨949000492110259666478197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5061335957921384887883717 949000492110259666478197)
                ·
                  refine ⟨88968796135336843732331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 949000492110259666478197 88968796135336843732331)
                  ·
                    rfl

theorem cell23_1559395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 5].length) (baseStart_1559395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559395 prefixEnd_1559395 := by exact prefixLift 1559395
  have htrace : WordTrace (prefixWord ++ tailWord_1559395) baseStart_1559395 baseEnd_1559395 := by
    simpa [prefixWord, tailWord_1559395, baseEnd_1559395] using wordTrace_append hprefix tailTrace_1559395
  have hstable : (prefixWord ++ tailWord_1559395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559395).length < 2 ^ (prefixWord ++ tailWord_1559395).sum := by decide
  have hdescent : baseEnd_1559395 < baseStart_1559395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559445 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 2, 4, 2]
def baseStart_1559445 : Nat := 118140960795 + 1559445 * 2 ^ 59
def prefixEnd_1559445 : Nat := 4983230072969 + 3 ^ 40 * 1559445 * 2
def baseEnd_1559445 : Nat := 800744839250756397965749

theorem tailTrace_1559445 : CollatzResearch.WordTrace tailWord_1559445 prefixEnd_1559445 800744839250756397965749 := by
  unfold tailWord_1559445
  simp only [CollatzResearch.WordTrace]
  refine ⟨56877631835404571847335789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37918421223603047898223859 56877631835404571847335789)
  ·
    refine ⟨21329111938276714442750921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56877631835404571847335789 21329111938276714442750921)
    ·
      refine ⟨15996833953707535832063191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21329111938276714442750921 15996833953707535832063191)
      ·
        refine ⟨23995250930561303748094787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15996833953707535832063191 23995250930561303748094787)
        ·
          refine ⟨35992876395841955622142181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23995250930561303748094787 35992876395841955622142181)
          ·
            refine ⟨6748664324220366679151659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35992876395841955622142181 6748664324220366679151659)
            ·
              refine ⟨10122996486330550018727489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6748664324220366679151659 10122996486330550018727489)
              ·
                refine ⟨7592247364747912514045617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10122996486330550018727489 7592247364747912514045617)
                ·
                  refine ⟨5694185523560934385534213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7592247364747912514045617 5694185523560934385534213)
                  ·
                    refine ⟨1067659785667675197287665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5694185523560934385534213 1067659785667675197287665)
                    ·
                      refine ⟨800744839250756397965749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1067659785667675197287665 800744839250756397965749)
                      ·
                        rfl

theorem cell23_1559445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 4, 2].length) (baseStart_1559445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559445 prefixEnd_1559445 := by exact prefixLift 1559445
  have htrace : WordTrace (prefixWord ++ tailWord_1559445) baseStart_1559445 baseEnd_1559445 := by
    simpa [prefixWord, tailWord_1559445, baseEnd_1559445] using wordTrace_append hprefix tailTrace_1559445
  have hstable : (prefixWord ++ tailWord_1559445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559445).length < 2 ^ (prefixWord ++ tailWord_1559445).sum := by decide
  have hdescent : baseEnd_1559445 < baseStart_1559445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559455 : List Nat := [1, 1, 2, 5, 2, 1, 1, 3, 3, 4]
def baseStart_1559455 : Nat := 118140960795 + 1559455 * 2 ^ 59
def prefixEnd_1559455 : Nat := 4983230072969 + 3 ^ 40 * 1559455 * 2
def baseEnd_1559455 : Nat := 266916658019100452946901

theorem tailTrace_1559455 : CollatzResearch.WordTrace tailWord_1559455 prefixEnd_1559455 266916658019100452946901 := by
  unfold tailWord_1559455
  simp only [CollatzResearch.WordTrace]
  refine ⟨56877996565368343555199819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37918664376912229036799879 56877996565368343555199819)
  ·
    refine ⟨85316994848052515332799729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56877996565368343555199819 85316994848052515332799729)
    ·
      refine ⟨63987746136039386499599797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85316994848052515332799729 63987746136039386499599797)
      ·
        refine ⟨5998851200253692484337481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63987746136039386499599797 5998851200253692484337481)
        ·
          refine ⟨4499138400190269363253111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5998851200253692484337481 4499138400190269363253111)
          ·
            refine ⟨6748707600285404044879667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4499138400190269363253111 6748707600285404044879667)
            ·
              refine ⟨10123061400428106067319501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6748707600285404044879667 10123061400428106067319501)
              ·
                refine ⟨3796148025160539775244813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10123061400428106067319501 3796148025160539775244813)
                ·
                  refine ⟨1423555509435202415716805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3796148025160539775244813 1423555509435202415716805)
                  ·
                    refine ⟨266916658019100452946901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1423555509435202415716805 266916658019100452946901)
                    ·
                      rfl

theorem cell23_1559455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 4].length) (baseStart_1559455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559455 prefixEnd_1559455 := by exact prefixLift 1559455
  have htrace : WordTrace (prefixWord ++ tailWord_1559455) baseStart_1559455 baseEnd_1559455 := by
    simpa [prefixWord, tailWord_1559455, baseEnd_1559455] using wordTrace_append hprefix tailTrace_1559455
  have hstable : (prefixWord ++ tailWord_1559455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559455).length < 2 ^ (prefixWord ++ tailWord_1559455).sum := by decide
  have hdescent : baseEnd_1559455 < baseStart_1559455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559495 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 5, 1, 3]
def baseStart_1559495 : Nat := 118140960795 + 1559495 * 2 ^ 59
def prefixEnd_1559495 : Nat := 4983230072969 + 3 ^ 40 * 1559495 * 2
def baseEnd_1559495 : Nat := 800770513283481202340519

theorem tailTrace_1559495 : CollatzResearch.WordTrace tailWord_1559495 prefixEnd_1559495 800770513283481202340519 := by
  unfold tailWord_1559495
  simp only [CollatzResearch.WordTrace]
  refine ⟨56879455485223430386655939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37919636990148953591103959 56879455485223430386655939)
  ·
    refine ⟨85319183227835145579983909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56879455485223430386655939 85319183227835145579983909)
    ·
      refine ⟨15997346855219089796246983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85319183227835145579983909 15997346855219089796246983)
      ·
        refine ⟨23996020282828634694370475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15997346855219089796246983 23996020282828634694370475)
        ·
          refine ⟨35994030424242952041555713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23996020282828634694370475 35994030424242952041555713)
          ·
            refine ⟨26995522818182214031166785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35994030424242952041555713 26995522818182214031166785)
            ·
              refine ⟨20246642113636660523375089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26995522818182214031166785 20246642113636660523375089)
              ·
                refine ⟨15184981585227495392531317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20246642113636660523375089 15184981585227495392531317)
                ·
                  refine ⟨1423592023615077693049811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15184981585227495392531317 1423592023615077693049811)
                  ·
                    refine ⟨2135388035422616539574717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1423592023615077693049811 2135388035422616539574717)
                    ·
                      refine ⟨800770513283481202340519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2135388035422616539574717 800770513283481202340519)
                      ·
                        rfl

theorem cell23_1559495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_1559495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559495 prefixEnd_1559495 := by exact prefixLift 1559495
  have htrace : WordTrace (prefixWord ++ tailWord_1559495) baseStart_1559495 baseEnd_1559495 := by
    simpa [prefixWord, tailWord_1559495, baseEnd_1559495] using wordTrace_append hprefix tailTrace_1559495
  have hstable : (prefixWord ++ tailWord_1559495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559495).length < 2 ^ (prefixWord ++ tailWord_1559495).sum := by decide
  have hdescent : baseEnd_1559495 < baseStart_1559495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559498 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 5, 5]
def baseStart_1559498 : Nat := 118140960795 + 1559498 * 2 ^ 59
def prefixEnd_1559498 : Nat := 4983230072969 + 3 ^ 40 * 1559498 * 2
def baseEnd_1559498 : Nat := 266924017908481563534335

theorem tailTrace_1559498 : CollatzResearch.WordTrace tailWord_1559498 prefixEnd_1559498 266924017908481563534335 := by
  unfold tailWord_1559498
  simp only [CollatzResearch.WordTrace]
  refine ⟨14219891226053140474753787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37919709936141707932676765 14219891226053140474753787)
  ·
    refine ⟨21329836839079710712130681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14219891226053140474753787 21329836839079710712130681)
    ·
      refine ⟨15997377629309783034098011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21329836839079710712130681 15997377629309783034098011)
      ·
        refine ⟨23996066443964674551147017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15997377629309783034098011 23996066443964674551147017)
        ·
          refine ⟨17997049832973505913360263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23996066443964674551147017 17997049832973505913360263)
          ·
            refine ⟨26995574749460258870040395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17997049832973505913360263 26995574749460258870040395)
            ·
              refine ⟨40493362124190388305060593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26995574749460258870040395 40493362124190388305060593)
              ·
                refine ⟨30370021593142791228795445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40493362124190388305060593 30370021593142791228795445)
                ·
                  refine ⟨2847189524357136677699573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30370021593142791228795445 2847189524357136677699573)
                  ·
                    refine ⟨266924017908481563534335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2847189524357136677699573 266924017908481563534335)
                    ·
                      rfl

theorem cell23_1559498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_1559498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559498 prefixEnd_1559498 := by exact prefixLift 1559498
  have htrace : WordTrace (prefixWord ++ tailWord_1559498) baseStart_1559498 baseEnd_1559498 := by
    simpa [prefixWord, tailWord_1559498, baseEnd_1559498] using wordTrace_append hprefix tailTrace_1559498
  have hstable : (prefixWord ++ tailWord_1559498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559498).length < 2 ^ (prefixWord ++ tailWord_1559498).sum := by decide
  have hdescent : baseEnd_1559498 < baseStart_1559498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559506 : List Nat := [3, 2, 2, 3, 1, 2, 3, 2, 1, 4]
def baseStart_1559506 : Nat := 118140960795 + 1559506 * 2 ^ 59
def prefixEnd_1559506 : Nat := 4983230072969 + 3 ^ 40 * 1559506 * 2
def baseEnd_1559506 : Nat := 266925387190226886434323

theorem tailTrace_1559506 : CollatzResearch.WordTrace tailWord_1559506 prefixEnd_1559506 266925387190226886434323 := by
  unfold tailWord_1559506
  simp only [CollatzResearch.WordTrace]
  refine ⟨14219964172045894816326593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37919904458789052843537581 14219964172045894816326593)
  ·
    refine ⟨10664973129034421112244945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14219964172045894816326593 10664973129034421112244945)
    ·
      refine ⟨7998729846775815834183709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10664973129034421112244945 7998729846775815834183709)
      ·
        refine ⟨2999523692540930937818891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7998729846775815834183709 2999523692540930937818891)
        ·
          refine ⟨4499285538811396406728337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2999523692540930937818891 4499285538811396406728337)
          ·
            refine ⟨3374464154108547305046253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4499285538811396406728337 3374464154108547305046253)
            ·
              refine ⟨1265424057790705239392345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3374464154108547305046253 1265424057790705239392345)
              ·
                refine ⟨949068043343028929544259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1265424057790705239392345 949068043343028929544259)
                ·
                  refine ⟨1423602065014543394316389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 949068043343028929544259 1423602065014543394316389)
                  ·
                    refine ⟨266925387190226886434323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1423602065014543394316389 266925387190226886434323)
                    ·
                      rfl

theorem cell23_1559506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_1559506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559506 prefixEnd_1559506 := by exact prefixLift 1559506
  have htrace : WordTrace (prefixWord ++ tailWord_1559506) baseStart_1559506 baseEnd_1559506 := by
    simpa [prefixWord, tailWord_1559506, baseEnd_1559506] using wordTrace_append hprefix tailTrace_1559506
  have hstable : (prefixWord ++ tailWord_1559506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559506).length < 2 ^ (prefixWord ++ tailWord_1559506).sum := by decide
  have hdescent : baseEnd_1559506 < baseStart_1559506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559512 : List Nat := [2, 1, 2, 2, 2, 3, 3, 1, 3, 1, 3]
def baseStart_1559512 : Nat := 118140960795 + 1559512 * 2 ^ 59
def prefixEnd_1559512 : Nat := 4983230072969 + 3 ^ 40 * 1559512 * 2
def baseEnd_1559512 : Nat := 800779242454607635827941

theorem tailTrace_1559512 : CollatzResearch.WordTrace tailWord_1559512 prefixEnd_1559512 800779242454607635827941 := by
  unfold tailWord_1559512
  simp only [CollatzResearch.WordTrace]
  refine ⟨28440037763080921145012395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37920050350774561526683193 28440037763080921145012395)
  ·
    refine ⟨42660056644621381717518593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28440037763080921145012395 42660056644621381717518593)
    ·
      refine ⟨31995042483466036288138945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42660056644621381717518593 31995042483466036288138945)
      ·
        refine ⟨23996281862599527216104209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31995042483466036288138945 23996281862599527216104209)
        ·
          refine ⟨17997211396949645412078157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23996281862599527216104209 17997211396949645412078157)
          ·
            refine ⟨6748954273856117029529309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17997211396949645412078157 6748954273856117029529309)
            ·
              refine ⟨2530857852696043886073491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6748954273856117029529309 2530857852696043886073491)
              ·
                refine ⟨3796286779044065829110237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2530857852696043886073491 3796286779044065829110237)
                ·
                  refine ⟨1423607542141524685916339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3796286779044065829110237 1423607542141524685916339)
                  ·
                    refine ⟨2135411313212287028874509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1423607542141524685916339 2135411313212287028874509)
                    ·
                      refine ⟨800779242454607635827941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2135411313212287028874509 800779242454607635827941)
                      ·
                        rfl

theorem cell23_1559512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_1559512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559512 prefixEnd_1559512 := by exact prefixLift 1559512
  have htrace : WordTrace (prefixWord ++ tailWord_1559512) baseStart_1559512 baseEnd_1559512 := by
    simpa [prefixWord, tailWord_1559512, baseEnd_1559512] using wordTrace_append hprefix tailTrace_1559512
  have hstable : (prefixWord ++ tailWord_1559512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559512).length < 2 ^ (prefixWord ++ tailWord_1559512).sum := by decide
  have hdescent : baseEnd_1559512 < baseStart_1559512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559519 : List Nat := [1, 1, 2, 3, 6, 1, 2, 1, 6]
def baseStart_1559519 : Nat := 118140960795 + 1559519 * 2 ^ 59
def prefixEnd_1559519 : Nat := 4983230072969 + 3 ^ 40 * 1559519 * 2
def baseEnd_1559519 : Nat := 88975870757687678715601

theorem tailTrace_1559519 : CollatzResearch.WordTrace tailWord_1559519 prefixEnd_1559519 88975870757687678715601 := by
  unfold tailWord_1559519
  simp only [CollatzResearch.WordTrace]
  refine ⟨56880330837136482485529611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37920220558090988323686407 56880330837136482485529611)
  ·
    refine ⟨85320496255704723728294417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56880330837136482485529611 85320496255704723728294417)
    ·
      refine ⟨63990372191778542796220813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85320496255704723728294417 63990372191778542796220813)
      ·
        refine ⟨23996389571916953548582805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63990372191778542796220813 23996389571916953548582805)
        ·
          refine ⟨1124830761183607197589819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23996389571916953548582805 1124830761183607197589819)
          ·
            refine ⟨1687246141775410796384729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1124830761183607197589819 1687246141775410796384729)
            ·
              refine ⟨1265434606331558097288547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1687246141775410796384729 1265434606331558097288547)
              ·
                refine ⟨1898151909497337145932821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1265434606331558097288547 1898151909497337145932821)
                ·
                  refine ⟨88975870757687678715601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1898151909497337145932821 88975870757687678715601)
                  ·
                    rfl

theorem cell23_1559519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 6].length) (baseStart_1559519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559519 prefixEnd_1559519 := by exact prefixLift 1559519
  have htrace : WordTrace (prefixWord ++ tailWord_1559519) baseStart_1559519 baseEnd_1559519 := by
    simpa [prefixWord, tailWord_1559519, baseEnd_1559519] using wordTrace_append hprefix tailTrace_1559519
  have hstable : (prefixWord ++ tailWord_1559519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559519).length < 2 ^ (prefixWord ++ tailWord_1559519).sum := by decide
  have hdescent : baseEnd_1559519 < baseStart_1559519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559535 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 4]
def baseStart_1559535 : Nat := 118140960795 + 1559535 * 2 ^ 59
def prefixEnd_1559535 : Nat := 4983230072969 + 3 ^ 40 * 1559535 * 2
def baseEnd_1559535 : Nat := 800791052509661045840335

theorem tailTrace_1559535 : CollatzResearch.WordTrace tailWord_1559535 prefixEnd_1559535 800791052509661045840335 := by
  unfold tailWord_1559535
  simp only [CollatzResearch.WordTrace]
  refine ⟨56880914405078517218112059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37920609603385678145408039 56880914405078517218112059)
  ·
    refine ⟨85321371607617775827168089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56880914405078517218112059 85321371607617775827168089)
    ·
      refine ⟨63991028705713331870376067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85321371607617775827168089 63991028705713331870376067)
      ·
        refine ⟨95986543058569997805564101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63991028705713331870376067 95986543058569997805564101)
        ·
          refine ⟨17997476823481874588543269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95986543058569997805564101 17997476823481874588543269)
          ·
            refine ⟨3374526904402851485351863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17997476823481874588543269 3374526904402851485351863)
            ·
              refine ⟨5061790356604277228027795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3374526904402851485351863 5061790356604277228027795)
              ·
                refine ⟨7592685534906415842041693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5061790356604277228027795 7592685534906415842041693)
                ·
                  refine ⟨2847257075589905940765635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7592685534906415842041693 2847257075589905940765635)
                  ·
                    refine ⟨4270885613384858911148453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2847257075589905940765635 4270885613384858911148453)
                    ·
                      refine ⟨800791052509661045840335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4270885613384858911148453 800791052509661045840335)
                      ·
                        rfl

theorem cell23_1559535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 4].length) (baseStart_1559535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559535 prefixEnd_1559535 := by exact prefixLift 1559535
  have htrace : WordTrace (prefixWord ++ tailWord_1559535) baseStart_1559535 baseEnd_1559535 := by
    simpa [prefixWord, tailWord_1559535, baseEnd_1559535] using wordTrace_append hprefix tailTrace_1559535
  have hstable : (prefixWord ++ tailWord_1559535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559535).length < 2 ^ (prefixWord ++ tailWord_1559535).sum := by decide
  have hdescent : baseEnd_1559535 < baseStart_1559535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559562 : List Nat := [3, 1, 2, 2, 3, 1, 1, 4, 2, 4]
def baseStart_1559562 : Nat := 118140960795 + 1559562 * 2 ^ 59
def prefixEnd_1559562 : Nat := 4983230072969 + 3 ^ 40 * 1559562 * 2
def baseEnd_1559562 : Nat := 266934972162444146734237

theorem tailTrace_1559562 : CollatzResearch.WordTrace tailWord_1559562 prefixEnd_1559562 266934972162444146734237 := by
  unfold tailWord_1559562
  simp only [CollatzResearch.WordTrace]
  refine ⟨14220474793995175207336235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37921266117320467219563293 14220474793995175207336235)
  ·
    refine ⟨21330712190992762811004353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14220474793995175207336235 21330712190992762811004353)
    ·
      refine ⟨15998034143244572108253265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21330712190992762811004353 15998034143244572108253265)
      ·
        refine ⟨11998525607433429081189949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15998034143244572108253265 11998525607433429081189949)
        ·
          refine ⟨4499447102787535905446231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11998525607433429081189949 4499447102787535905446231)
          ·
            refine ⟨6749170654181303858169347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4499447102787535905446231 6749170654181303858169347)
            ·
              refine ⟨10123755981271955787254021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6749170654181303858169347 10123755981271955787254021)
              ·
                refine ⟨1898204246488491710110129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10123755981271955787254021 1898204246488491710110129)
                ·
                  refine ⟨1423653184866368782582597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1898204246488491710110129 1423653184866368782582597)
                  ·
                    refine ⟨266934972162444146734237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1423653184866368782582597 266934972162444146734237)
                    ·
                      rfl

theorem cell23_1559562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_1559562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559562 prefixEnd_1559562 := by exact prefixLift 1559562
  have htrace : WordTrace (prefixWord ++ tailWord_1559562) baseStart_1559562 baseEnd_1559562 := by
    simpa [prefixWord, tailWord_1559562, baseEnd_1559562] using wordTrace_append hprefix tailTrace_1559562
  have hstable : (prefixWord ++ tailWord_1559562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559562).length < 2 ^ (prefixWord ++ tailWord_1559562).sum := by decide
  have hdescent : baseEnd_1559562 < baseStart_1559562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559575 : List Nat := [1, 1, 3, 5, 1, 1, 3, 8]
def baseStart_1559575 : Nat := 118140960795 + 1559575 * 2 ^ 59
def prefixEnd_1559575 : Nat := 4983230072969 + 3 ^ 40 * 1559575 * 2
def baseEnd_1559575 : Nat := 29659688582808921827413

theorem tailTrace_1559575 : CollatzResearch.WordTrace tailWord_1559575 prefixEnd_1559575 29659688582808921827413 := by
  unfold tailWord_1559575
  simp only [CollatzResearch.WordTrace]
  refine ⟨56882373324933604049568179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37921582216622402699712119 56882373324933604049568179)
  ·
    refine ⟨85323559987400406074352269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56882373324933604049568179 85323559987400406074352269)
    ·
      refine ⟨31996334995275152277882101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85323559987400406074352269 31996334995275152277882101)
      ·
        refine ⟨2999656405807045526051447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31996334995275152277882101 2999656405807045526051447)
        ·
          refine ⟨4499484608710568289077171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2999656405807045526051447 4499484608710568289077171)
          ·
            refine ⟨6749226913065852433615757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4499484608710568289077171 6749226913065852433615757)
            ·
              refine ⟨2530960092399694662605909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6749226913065852433615757 2530960092399694662605909)
              ·
                refine ⟨29659688582808921827413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2530960092399694662605909 29659688582808921827413)
                ·
                  rfl

theorem cell23_1559575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 8].length) (baseStart_1559575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559575 prefixEnd_1559575 := by exact prefixLift 1559575
  have htrace : WordTrace (prefixWord ++ tailWord_1559575) baseStart_1559575 baseEnd_1559575 := by
    simpa [prefixWord, tailWord_1559575, baseEnd_1559575] using wordTrace_append hprefix tailTrace_1559575
  have hstable : (prefixWord ++ tailWord_1559575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559575).length < 2 ^ (prefixWord ++ tailWord_1559575).sum := by decide
  have hdescent : baseEnd_1559575 < baseStart_1559575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559602 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3]
def baseStart_1559602 : Nat := 118140960795 + 1559602 * 2 ^ 59
def prefixEnd_1559602 : Nat := 4983230072969 + 3 ^ 40 * 1559602 * 2
def baseEnd_1559602 : Nat := 800825455713512283702527

theorem tailTrace_1559602 : CollatzResearch.WordTrace tailWord_1559602 prefixEnd_1559602 800825455713512283702527 := by
  unfold tailWord_1559602
  simp only [CollatzResearch.WordTrace]
  refine ⟨14220839523958946915200265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37922238730557191773867373 14220839523958946915200265)
  ·
    refine ⟨10665629642969210186400199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14220839523958946915200265 10665629642969210186400199)
    ·
      refine ⟨15998444464453815279600299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10665629642969210186400199 15998444464453815279600299)
      ·
        refine ⟨23997666696680722919400449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15998444464453815279600299 23997666696680722919400449)
        ·
          refine ⟨17998250022510542189550337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23997666696680722919400449 17998250022510542189550337)
          ·
            refine ⟨13498687516882906642162753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17998250022510542189550337 13498687516882906642162753)
            ·
              refine ⟨10124015637662179981622065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13498687516882906642162753 10124015637662179981622065)
              ·
                refine ⟨7593011728246634986216549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10124015637662179981622065 7593011728246634986216549)
                ·
                  refine ⟨1423689699046244059915603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7593011728246634986216549 1423689699046244059915603)
                  ·
                    refine ⟨2135534548569366089873405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1423689699046244059915603 2135534548569366089873405)
                    ·
                      refine ⟨800825455713512283702527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2135534548569366089873405 800825455713512283702527)
                      ·
                        rfl

theorem cell23_1559602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_1559602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559602 prefixEnd_1559602 := by exact prefixLift 1559602
  have htrace : WordTrace (prefixWord ++ tailWord_1559602) baseStart_1559602 baseEnd_1559602 := by
    simpa [prefixWord, tailWord_1559602, baseEnd_1559602] using wordTrace_append hprefix tailTrace_1559602
  have hstable : (prefixWord ++ tailWord_1559602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559602).length < 2 ^ (prefixWord ++ tailWord_1559602).sum := by decide
  have hdescent : baseEnd_1559602 < baseStart_1559602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559606 : List Nat := [5, 1, 2, 1, 1, 2, 4, 1, 1, 2, 3]
def baseStart_1559606 : Nat := 118140960795 + 1559606 * 2 ^ 59
def prefixEnd_1559606 : Nat := 4983230072969 + 3 ^ 40 * 1559606 * 2
def baseEnd_1559606 : Nat := 800827509636130268052509

theorem tailTrace_1559606 : CollatzResearch.WordTrace tailWord_1559606 prefixEnd_1559606 800827509636130268052509 := by
  unfold tailWord_1559606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3555218999238831021496667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37922335991880864229297781 3555218999238831021496667)
  ·
    refine ⟨5332828498858246532245001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3555218999238831021496667 5332828498858246532245001)
    ·
      refine ⟨3999621374143684899183751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5332828498858246532245001 3999621374143684899183751)
      ·
        refine ⟨5999432061215527348775627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3999621374143684899183751 5999432061215527348775627)
        ·
          refine ⟨8999148091823291023163441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5999432061215527348775627 8999148091823291023163441)
          ·
            refine ⟨6749361068867468267372581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8999148091823291023163441 6749361068867468267372581)
            ·
              refine ⟨1265505200412650300132359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6749361068867468267372581 1265505200412650300132359)
              ·
                refine ⟨1898257800618975450198539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1265505200412650300132359 1898257800618975450198539)
                ·
                  refine ⟨2847386700928463175297809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1898257800618975450198539 2847386700928463175297809)
                  ·
                    refine ⟨2135540025696347381473357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2847386700928463175297809 2135540025696347381473357)
                    ·
                      refine ⟨800827509636130268052509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2135540025696347381473357 800827509636130268052509)
                      ·
                        rfl

theorem cell23_1559606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_1559606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559606 prefixEnd_1559606 := by exact prefixLift 1559606
  have htrace : WordTrace (prefixWord ++ tailWord_1559606) baseStart_1559606 baseEnd_1559606 := by
    simpa [prefixWord, tailWord_1559606, baseEnd_1559606] using wordTrace_append hprefix tailTrace_1559606
  have hstable : (prefixWord ++ tailWord_1559606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559606).length < 2 ^ (prefixWord ++ tailWord_1559606).sum := by decide
  have hdescent : baseEnd_1559606 < baseStart_1559606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559642 : List Nat := [3, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2]
def baseStart_1559642 : Nat := 118140960795 + 1559642 * 2 ^ 59
def prefixEnd_1559642 : Nat := 4983230072969 + 3 ^ 40 * 1559642 * 2
def baseEnd_1559642 : Nat := 800845994939692127202343

theorem tailTrace_1559642 : CollatzResearch.WordTrace tailWord_1559642 prefixEnd_1559642 800845994939692127202343 := by
  unfold tailWord_1559642
  simp only [CollatzResearch.WordTrace]
  refine ⟨14221204253922718623064295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37923211343793916328171453 14221204253922718623064295)
  ·
    refine ⟨21331806380884077934596443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14221204253922718623064295 21331806380884077934596443)
    ·
      refine ⟨31997709571326116901894665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21331806380884077934596443 31997709571326116901894665)
      ·
        refine ⟨23998282178494587676420999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31997709571326116901894665 23998282178494587676420999)
        ·
          refine ⟨35997423267741881514631499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23998282178494587676420999 35997423267741881514631499)
          ·
            refine ⟨53996134901612822271947249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35997423267741881514631499 53996134901612822271947249)
            ·
              refine ⟨40497101176209616703960437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53996134901612822271947249 40497101176209616703960437)
              ·
                refine ⟨3796603235269651565996291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40497101176209616703960437 3796603235269651565996291)
                ·
                  refine ⟨5694904852904477348994437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3796603235269651565996291 5694904852904477348994437)
                  ·
                    refine ⟨1067794659919589502936457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5694904852904477348994437 1067794659919589502936457)
                    ·
                      refine ⟨800845994939692127202343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1067794659919589502936457 800845994939692127202343)
                      ·
                        rfl

theorem cell23_1559642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2].length) (baseStart_1559642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559642 prefixEnd_1559642 := by exact prefixLift 1559642
  have htrace : WordTrace (prefixWord ++ tailWord_1559642) baseStart_1559642 baseEnd_1559642 := by
    simpa [prefixWord, tailWord_1559642, baseEnd_1559642] using wordTrace_append hprefix tailTrace_1559642
  have hstable : (prefixWord ++ tailWord_1559642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559642).length < 2 ^ (prefixWord ++ tailWord_1559642).sum := by decide
  have hdescent : baseEnd_1559642 < baseStart_1559642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559662 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_1559662 : Nat := 118140960795 + 1559662 * 2 ^ 59
def prefixEnd_1559662 : Nat := 4983230072969 + 3 ^ 40 * 1559662 * 2
def baseEnd_1559662 : Nat := 800856264552782048952251

theorem tailTrace_1559662 : CollatzResearch.WordTrace tailWord_1559662 prefixEnd_1559662 800856264552782048952251 := by
  unfold tailWord_1559662
  simp only [CollatzResearch.WordTrace]
  refine ⟨7110693309452302238498155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37923697650412278605323493 7110693309452302238498155)
  ·
    refine ⟨10666039964178453357747233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7110693309452302238498155 10666039964178453357747233)
    ·
      refine ⟨7999529973133840018310425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10666039964178453357747233 7999529973133840018310425)
      ·
        refine ⟨5999647479850380013732819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7999529973133840018310425 5999647479850380013732819)
        ·
          refine ⟨8999471219775570020599229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5999647479850380013732819 8999471219775570020599229)
          ·
            refine ⟨3374801707415838757724711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8999471219775570020599229 3374801707415838757724711)
            ·
              refine ⟨5062202561123758136587067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3374801707415838757724711 5062202561123758136587067)
              ·
                refine ⟨7593303841685637204880601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5062202561123758136587067 7593303841685637204880601)
                ·
                  refine ⟨5694977881264227903660451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7593303841685637204880601 5694977881264227903660451)
                  ·
                    refine ⟨8542466821896341855490677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5694977881264227903660451 8542466821896341855490677)
                    ·
                      refine ⟨800856264552782048952251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8542466821896341855490677 800856264552782048952251)
                      ·
                        rfl

theorem cell23_1559662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_1559662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559662 prefixEnd_1559662 := by exact prefixLift 1559662
  have htrace : WordTrace (prefixWord ++ tailWord_1559662) baseStart_1559662 baseEnd_1559662 := by
    simpa [prefixWord, tailWord_1559662, baseEnd_1559662] using wordTrace_append hprefix tailTrace_1559662
  have hstable : (prefixWord ++ tailWord_1559662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559662).length < 2 ^ (prefixWord ++ tailWord_1559662).sum := by decide
  have hdescent : baseEnd_1559662 < baseStart_1559662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559675 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 3]
def baseStart_1559675 : Nat := 118140960795 + 1559675 * 2 ^ 59
def prefixEnd_1559675 : Nat := 4983230072969 + 3 ^ 40 * 1559675 * 2
def baseEnd_1559675 : Nat := 800862939801290498089691

theorem tailTrace_1559675 : CollatzResearch.WordTrace tailWord_1559675 prefixEnd_1559675 800862939801290498089691 := by
  unfold tailWord_1559675
  simp only [CollatzResearch.WordTrace]
  refine ⟨56886020624571321128208479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37924013749714214085472319 56886020624571321128208479)
  ·
    refine ⟨85329030936856981692312719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56886020624571321128208479 85329030936856981692312719)
    ·
      refine ⟨127993546405285472538469079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85329030936856981692312719 127993546405285472538469079)
      ·
        refine ⟨191990319607928208807703619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127993546405285472538469079 191990319607928208807703619)
        ·
          refine ⟨287985479411892313211555429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191990319607928208807703619 287985479411892313211555429)
          ·
            refine ⟨53997277389729808727166643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 287985479411892313211555429 53997277389729808727166643)
            ·
              refine ⟨80995916084594713090749965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53997277389729808727166643 80995916084594713090749965)
              ·
                refine ⟨30373468531723017409031237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80995916084594713090749965 30373468531723017409031237)
                ·
                  refine ⟨5695025349698065764193357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30373468531723017409031237 5695025349698065764193357)
                  ·
                    refine ⟨2135634506136774661572509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5695025349698065764193357 2135634506136774661572509)
                    ·
                      refine ⟨800862939801290498089691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2135634506136774661572509 800862939801290498089691)
                      ·
                        rfl

theorem cell23_1559675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 3].length) (baseStart_1559675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559675 prefixEnd_1559675 := by exact prefixLift 1559675
  have htrace : WordTrace (prefixWord ++ tailWord_1559675) baseStart_1559675 baseEnd_1559675 := by
    simpa [prefixWord, tailWord_1559675, baseEnd_1559675] using wordTrace_append hprefix tailTrace_1559675
  have hstable : (prefixWord ++ tailWord_1559675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559675).length < 2 ^ (prefixWord ++ tailWord_1559675).sum := by decide
  have hdescent : baseEnd_1559675 < baseStart_1559675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559712 : List Nat := [2, 1, 1, 4, 2, 1, 4, 1, 2, 5]
def baseStart_1559712 : Nat := 118140960795 + 1559712 * 2 ^ 59
def prefixEnd_1559712 : Nat := 4983230072969 + 3 ^ 40 * 1559712 * 2
def baseEnd_1559712 : Nat := 266960646195168951109007

theorem tailTrace_1559712 : CollatzResearch.WordTrace tailWord_1559712 prefixEnd_1559712 266960646195168951109007 := by
  unfold tailWord_1559712
  simp only [CollatzResearch.WordTrace]
  refine ⟨28443685062718638223652695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37924913416958184298203593 28443685062718638223652695)
  ·
    refine ⟨42665527594077957335479043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28443685062718638223652695 42665527594077957335479043)
    ·
      refine ⟨63998291391116936003218565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42665527594077957335479043 63998291391116936003218565)
      ·
        refine ⟨11999679635834425500603481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63998291391116936003218565 11999679635834425500603481)
        ·
          refine ⟨8999759726875819125452611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11999679635834425500603481 8999759726875819125452611)
          ·
            refine ⟨13499639590313728688178917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8999759726875819125452611 13499639590313728688178917)
            ·
              refine ⟨2531182423183824129033547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13499639590313728688178917 2531182423183824129033547)
              ·
                refine ⟨3796773634775736193550321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2531182423183824129033547 3796773634775736193550321)
                ·
                  refine ⟨2847580226081802145162741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3796773634775736193550321 2847580226081802145162741)
                  ·
                    refine ⟨266960646195168951109007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2847580226081802145162741 266960646195168951109007)
                    ·
                      rfl

theorem cell23_1559712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 2, 5].length) (baseStart_1559712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559712 prefixEnd_1559712 := by exact prefixLift 1559712
  have htrace : WordTrace (prefixWord ++ tailWord_1559712) baseStart_1559712 baseEnd_1559712 := by
    simpa [prefixWord, tailWord_1559712, baseEnd_1559712] using wordTrace_append hprefix tailTrace_1559712
  have hstable : (prefixWord ++ tailWord_1559712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559712).length < 2 ^ (prefixWord ++ tailWord_1559712).sum := by decide
  have hdescent : baseEnd_1559712 < baseStart_1559712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559715 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 4]
def baseStart_1559715 : Nat := 118140960795 + 1559715 * 2 ^ 59
def prefixEnd_1559715 : Nat := 4983230072969 + 3 ^ 40 * 1559715 * 2
def baseEnd_1559715 : Nat := 800883479027470341589507

theorem tailTrace_1559715 : CollatzResearch.WordTrace tailWord_1559715 prefixEnd_1559715 800883479027470341589507 := by
  unfold tailWord_1559715
  simp only [CollatzResearch.WordTrace]
  refine ⟨56887479544426407959664599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37924986362950938639776399 56887479544426407959664599)
  ·
    refine ⟨85331219316639611939496899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56887479544426407959664599 85331219316639611939496899)
    ·
      refine ⟨127996828974959417909245349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85331219316639611939496899 127996828974959417909245349)
      ·
        refine ⟨23999405432804890857983503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127996828974959417909245349 23999405432804890857983503)
        ·
          refine ⟨35999108149207336286975255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23999405432804890857983503 35999108149207336286975255)
          ·
            refine ⟨53998662223811004430462883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35999108149207336286975255 53998662223811004430462883)
            ·
              refine ⟨80997993335716506645694325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53998662223811004430462883 80997993335716506645694325)
              ·
                refine ⟨7593561875223422498033843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80997993335716506645694325 7593561875223422498033843)
                ·
                  refine ⟨11390342812835133747050765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7593561875223422498033843 11390342812835133747050765)
                  ·
                    refine ⟨4271378554813175155144037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11390342812835133747050765 4271378554813175155144037)
                    ·
                      refine ⟨800883479027470341589507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4271378554813175155144037 800883479027470341589507)
                      ·
                        rfl

theorem cell23_1559715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_1559715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559715 prefixEnd_1559715 := by exact prefixLift 1559715
  have htrace : WordTrace (prefixWord ++ tailWord_1559715) baseStart_1559715 baseEnd_1559715 := by
    simpa [prefixWord, tailWord_1559715, baseEnd_1559715] using wordTrace_append hprefix tailTrace_1559715
  have hstable : (prefixWord ++ tailWord_1559715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559715).length < 2 ^ (prefixWord ++ tailWord_1559715).sum := by decide
  have hdescent : baseEnd_1559715 < baseStart_1559715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559735 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 5]
def baseStart_1559735 : Nat := 118140960795 + 1559735 * 2 ^ 59
def prefixEnd_1559735 : Nat := 4983230072969 + 3 ^ 40 * 1559735 * 2
def baseEnd_1559735 : Nat := 800893748640560263339415

theorem tailTrace_1559735 : CollatzResearch.WordTrace tailWord_1559735 prefixEnd_1559735 800893748640560263339415 := by
  unfold tailWord_1559735
  simp only [CollatzResearch.WordTrace]
  refine ⟨56888209004353951375392659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37925472669569300916928439 56888209004353951375392659)
  ·
    refine ⟨85332313506530927063088989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56888209004353951375392659 85332313506530927063088989)
    ·
      refine ⟨31999617564949097648658371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85332313506530927063088989 31999617564949097648658371)
      ·
        refine ⟨47999426347423646472987557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31999617564949097648658371 47999426347423646472987557)
        ·
          refine ⟨8999892440141933713685167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47999426347423646472987557 8999892440141933713685167)
          ·
            refine ⟨13499838660212900570527751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8999892440141933713685167 13499838660212900570527751)
            ·
              refine ⟨20249757990319350855791627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13499838660212900570527751 20249757990319350855791627)
              ·
                refine ⟨30374636985479026283687441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20249757990319350855791627 30374636985479026283687441)
                ·
                  refine ⟨22780977739109269712765581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30374636985479026283687441 22780977739109269712765581)
                  ·
                    refine ⟨8542866652165976142287093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22780977739109269712765581 8542866652165976142287093)
                    ·
                      refine ⟨800893748640560263339415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8542866652165976142287093 800893748640560263339415)
                      ·
                        rfl

theorem cell23_1559735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_1559735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559735 prefixEnd_1559735 := by exact prefixLift 1559735
  have htrace : WordTrace (prefixWord ++ tailWord_1559735) baseStart_1559735 baseEnd_1559735 := by
    simpa [prefixWord, tailWord_1559735, baseEnd_1559735] using wordTrace_append hprefix tailTrace_1559735
  have hstable : (prefixWord ++ tailWord_1559735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559735).length < 2 ^ (prefixWord ++ tailWord_1559735).sum := by decide
  have hdescent : baseEnd_1559735 < baseStart_1559735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559752 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 4, 2, 3]
def baseStart_1559752 : Nat := 118140960795 + 1559752 * 2 ^ 59
def prefixEnd_1559752 : Nat := 4983230072969 + 3 ^ 40 * 1559752 * 2
def baseEnd_1559752 : Nat := 800902477811686696826837

theorem tailTrace_1559752 : CollatzResearch.WordTrace tailWord_1559752 prefixEnd_1559752 800902477811686696826837 := by
  unfold tailWord_1559752
  simp only [CollatzResearch.WordTrace]
  refine ⟨28444414522646181639380755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37925886030194908852507673 28444414522646181639380755)
  ·
    refine ⟨42666621783969272459071133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28444414522646181639380755 42666621783969272459071133)
    ·
      refine ⟨15999983168988477172151675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42666621783969272459071133 15999983168988477172151675)
      ·
        refine ⟨23999974753482715758227513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15999983168988477172151675 23999974753482715758227513)
        ·
          refine ⟨17999981065112036818670635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23999974753482715758227513 17999981065112036818670635)
          ·
            refine ⟨26999971597668055228005953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17999981065112036818670635 26999971597668055228005953)
            ·
              refine ⟨20249978698251041421004465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26999971597668055228005953 20249978698251041421004465)
              ·
                refine ⟨15187484023688281065753349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20249978698251041421004465 15187484023688281065753349)
                ·
                  refine ⟨2847653254441552699828753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15187484023688281065753349 2847653254441552699828753)
                  ·
                    refine ⟨2135739940831164524871565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2847653254441552699828753 2135739940831164524871565)
                    ·
                      refine ⟨800902477811686696826837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2135739940831164524871565 800902477811686696826837)
                      ·
                        rfl

theorem cell23_1559752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_1559752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559752 prefixEnd_1559752 := by exact prefixLift 1559752
  have htrace : WordTrace (prefixWord ++ tailWord_1559752) baseStart_1559752 baseEnd_1559752 := by
    simpa [prefixWord, tailWord_1559752, baseEnd_1559752] using wordTrace_append hprefix tailTrace_1559752
  have hstable : (prefixWord ++ tailWord_1559752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559752).length < 2 ^ (prefixWord ++ tailWord_1559752).sum := by decide
  have hdescent : baseEnd_1559752 < baseStart_1559752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559766 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_1559766 : Nat := 118140960795 + 1559766 * 2 ^ 59
def prefixEnd_1559766 : Nat := 4983230072969 + 3 ^ 40 * 1559766 * 2
def baseEnd_1559766 : Nat := 800909666540849642051773

theorem tailTrace_1559766 : CollatzResearch.WordTrace tailWord_1559766 prefixEnd_1559766 800909666540849642051773 := by
  unfold tailWord_1559766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3555583729202602729360697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37926226444827762446514101 3555583729202602729360697)
  ·
    refine ⟨2666687796901952047020523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3555583729202602729360697 2666687796901952047020523)
    ·
      refine ⟨4000031695352928070530785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2666687796901952047020523 4000031695352928070530785)
      ·
        refine ⟨3000023771514696052898089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4000031695352928070530785 3000023771514696052898089)
        ·
          refine ⟨2250017828636022039673567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3000023771514696052898089 2250017828636022039673567)
          ·
            refine ⟨3375026742954033059510351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2250017828636022039673567 3375026742954033059510351)
            ·
              refine ⟨5062540114431049589265527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3375026742954033059510351 5062540114431049589265527)
              ·
                refine ⟨7593810171646574383898291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5062540114431049589265527 7593810171646574383898291)
                ·
                  refine ⟨11390715257469861575847437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7593810171646574383898291 11390715257469861575847437)
                  ·
                    refine ⟨4271518221551198090942789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11390715257469861575847437 4271518221551198090942789)
                    ·
                      refine ⟨800909666540849642051773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4271518221551198090942789 800909666540849642051773)
                      ·
                        rfl

theorem cell23_1559766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_1559766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559766 prefixEnd_1559766 := by exact prefixLift 1559766
  have htrace : WordTrace (prefixWord ++ tailWord_1559766) baseStart_1559766 baseEnd_1559766 := by
    simpa [prefixWord, tailWord_1559766, baseEnd_1559766] using wordTrace_append hprefix tailTrace_1559766
  have hstable : (prefixWord ++ tailWord_1559766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559766).length < 2 ^ (prefixWord ++ tailWord_1559766).sum := by decide
  have hdescent : baseEnd_1559766 < baseStart_1559766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559776 : List Nat := [2, 1, 1, 3, 1, 5, 2, 3, 1, 4]
def baseStart_1559776 : Nat := 118140960795 + 1559776 * 2 ^ 59
def prefixEnd_1559776 : Nat := 4983230072969 + 3 ^ 40 * 1559776 * 2
def baseEnd_1559776 : Nat := 266971600449131534308909

theorem tailTrace_1559776 : CollatzResearch.WordTrace tailWord_1559776 prefixEnd_1559776 266971600449131534308909 := by
  unfold tailWord_1559776
  simp only [CollatzResearch.WordTrace]
  refine ⟨28444852198602707688817591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37926469598136943585090121 28444852198602707688817591)
  ·
    refine ⟨42667278297904061533226387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28444852198602707688817591 42667278297904061533226387)
    ·
      refine ⟨64000917446856092299839581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42667278297904061533226387 64000917446856092299839581)
      ·
        refine ⟨24000344042571034612439843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64000917446856092299839581 24000344042571034612439843)
        ·
          refine ⟨36000516063856551918659765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24000344042571034612439843 36000516063856551918659765)
          ·
            refine ⟨3375048380986551742374353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36000516063856551918659765 3375048380986551742374353)
            ·
              refine ⟨2531286285739913806780765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3375048380986551742374353 2531286285739913806780765)
              ·
                refine ⟨949232357152467677542787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2531286285739913806780765 949232357152467677542787)
                ·
                  refine ⟨1423848535728701516314181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 949232357152467677542787 1423848535728701516314181)
                  ·
                    refine ⟨266971600449131534308909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1423848535728701516314181 266971600449131534308909)
                    ·
                      rfl

theorem cell23_1559776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 1, 4].length) (baseStart_1559776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559776 prefixEnd_1559776 := by exact prefixLift 1559776
  have htrace : WordTrace (prefixWord ++ tailWord_1559776) baseStart_1559776 baseEnd_1559776 := by
    simpa [prefixWord, tailWord_1559776, baseEnd_1559776] using wordTrace_append hprefix tailTrace_1559776
  have hstable : (prefixWord ++ tailWord_1559776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559776).length < 2 ^ (prefixWord ++ tailWord_1559776).sum := by decide
  have hdescent : baseEnd_1559776 < baseStart_1559776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559789 : List Nat := [1, 5, 1, 2, 2, 1, 3, 2, 6]
def baseStart_1559789 : Nat := 118140960795 + 1559789 * 2 ^ 59
def prefixEnd_1559789 : Nat := 4983230072969 + 3 ^ 40 * 1559789 * 2
def baseEnd_1559789 : Nat := 88991275177322561340463

theorem tailTrace_1559789 : CollatzResearch.WordTrace tailWord_1559789 prefixEnd_1559789 88991275177322561340463 := by
  unfold tailWord_1559789
  simp only [CollatzResearch.WordTrace]
  refine ⟨56890178546158318597858421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37926785697438879065238947 56890178546158318597858421)
  ·
    refine ⟨5333454238702342368549227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56890178546158318597858421 5333454238702342368549227)
    ·
      refine ⟨8000181358053513552823841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5333454238702342368549227 8000181358053513552823841)
      ·
        refine ⟨6000136018540135164617881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8000181358053513552823841 6000136018540135164617881)
        ·
          refine ⟨4500102013905101373463411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6000136018540135164617881 4500102013905101373463411)
          ·
            refine ⟨6750153020857652060195117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4500102013905101373463411 6750153020857652060195117)
            ·
              refine ⟨2531307382821619522573169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6750153020857652060195117 2531307382821619522573169)
              ·
                refine ⟨1898480537116214641929877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2531307382821619522573169 1898480537116214641929877)
                ·
                  refine ⟨88991275177322561340463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1898480537116214641929877 88991275177322561340463)
                  ·
                    rfl

theorem cell23_1559789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_1559789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559789 prefixEnd_1559789 := by exact prefixLift 1559789
  have htrace : WordTrace (prefixWord ++ tailWord_1559789) baseStart_1559789 baseEnd_1559789 := by
    simpa [prefixWord, tailWord_1559789, baseEnd_1559789] using wordTrace_append hprefix tailTrace_1559789
  have hstable : (prefixWord ++ tailWord_1559789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559789).length < 2 ^ (prefixWord ++ tailWord_1559789).sum := by decide
  have hdescent : baseEnd_1559789 < baseStart_1559789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559806 : List Nat := [4, 2, 2, 1, 1, 3, 3, 1, 6]
def baseStart_1559806 : Nat := 118140960795 + 1559806 * 2 ^ 59
def prefixEnd_1559806 : Nat := 4983230072969 + 3 ^ 40 * 1559806 * 2
def baseEnd_1559806 : Nat := 88992245085225498394621

theorem tailTrace_1559806 : CollatzResearch.WordTrace tailWord_1559806 prefixEnd_1559806 88992245085225498394621 := by
  unfold tailWord_1559806
  simp only [CollatzResearch.WordTrace]
  refine ⟨7111349823387091312653409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37927199058064487000818181 7111349823387091312653409)
  ·
    refine ⟨5333512367540318484490057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7111349823387091312653409 5333512367540318484490057)
    ·
      refine ⟨4000134275655238863367543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5333512367540318484490057 4000134275655238863367543)
      ·
        refine ⟨6000201413482858295051315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4000134275655238863367543 6000201413482858295051315)
        ·
          refine ⟨9000302120224287442576973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6000201413482858295051315 9000302120224287442576973)
          ·
            refine ⟨3375113295084107790966365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9000302120224287442576973 3375113295084107790966365)
            ·
              refine ⟨1265667485656540421612387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3375113295084107790966365 1265667485656540421612387)
              ·
                refine ⟨1898501228484810632418581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1265667485656540421612387 1898501228484810632418581)
                ·
                  refine ⟨88992245085225498394621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1898501228484810632418581 88992245085225498394621)
                  ·
                    rfl

theorem cell23_1559806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_1559806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559806 prefixEnd_1559806 := by exact prefixLift 1559806
  have htrace : WordTrace (prefixWord ++ tailWord_1559806) baseStart_1559806 baseEnd_1559806 := by
    simpa [prefixWord, tailWord_1559806, baseEnd_1559806] using wordTrace_append hprefix tailTrace_1559806
  have hstable : (prefixWord ++ tailWord_1559806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559806).length < 2 ^ (prefixWord ++ tailWord_1559806).sum := by decide
  have hdescent : baseEnd_1559806 < baseStart_1559806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559809 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 1, 5, 2]
def baseStart_1559809 : Nat := 118140960795 + 1559809 * 2 ^ 59
def prefixEnd_1559809 : Nat := 4983230072969 + 3 ^ 40 * 1559809 * 2
def baseEnd_1559809 : Nat := 800931746208992973814075

theorem tailTrace_1559809 : CollatzResearch.WordTrace tailWord_1559809 prefixEnd_1559809 800931746208992973814075 := by
  unfold tailWord_1559809
  simp only [CollatzResearch.WordTrace]
  refine ⟨56890908006085862013586481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37927272004057241342390987 56890908006085862013586481)
  ·
    refine ⟨42668181004564396510189861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56890908006085862013586481 42668181004564396510189861)
    ·
      refine ⟨8000283938355824345660599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42668181004564396510189861 8000283938355824345660599)
      ·
        refine ⟨12000425907533736518490899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8000283938355824345660599 12000425907533736518490899)
        ·
          refine ⟨18000638861300604777736349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12000425907533736518490899 18000638861300604777736349)
          ·
            refine ⟨6750239572987726791651131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18000638861300604777736349 6750239572987726791651131)
            ·
              refine ⟨10125359359481590187476697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6750239572987726791651131 10125359359481590187476697)
              ·
                refine ⟨7594019519611192640607523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10125359359481590187476697 7594019519611192640607523)
                ·
                  refine ⟨11391029279416788960911285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7594019519611192640607523 11391029279416788960911285)
                  ·
                    refine ⟨1067908994945323965085433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11391029279416788960911285 1067908994945323965085433)
                    ·
                      refine ⟨800931746208992973814075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1067908994945323965085433 800931746208992973814075)
                      ·
                        rfl

theorem cell23_1559809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_1559809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559809 prefixEnd_1559809 := by exact prefixLift 1559809
  have htrace : WordTrace (prefixWord ++ tailWord_1559809) baseStart_1559809 baseEnd_1559809 := by
    simpa [prefixWord, tailWord_1559809, baseEnd_1559809] using wordTrace_append hprefix tailTrace_1559809
  have hstable : (prefixWord ++ tailWord_1559809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559809).length < 2 ^ (prefixWord ++ tailWord_1559809).sum := by decide
  have hdescent : baseEnd_1559809 < baseStart_1559809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559819 : List Nat := [1, 1, 1, 1, 5, 4, 2, 2, 1, 5]
def baseStart_1559819 : Nat := 118140960795 + 1559819 * 2 ^ 59
def prefixEnd_1559819 : Nat := 4983230072969 + 3 ^ 40 * 1559819 * 2
def baseEnd_1559819 : Nat := 266978960338512644896343

theorem tailTrace_1559819 : CollatzResearch.WordTrace tailWord_1559819 prefixEnd_1559819 266978960338512644896343 := by
  unfold tailWord_1559819
  simp only [CollatzResearch.WordTrace]
  refine ⟨56891272736049633721450511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37927515157366422480967007 56891272736049633721450511)
  ·
    refine ⟨85336909104074450582175767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56891272736049633721450511 85336909104074450582175767)
    ·
      refine ⟨128005363656111675873263651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85336909104074450582175767 128005363656111675873263651)
      ·
        refine ⟨192008045484167513809895477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128005363656111675873263651 192008045484167513809895477)
        ·
          refine ⟨18000754264140704419677701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 192008045484167513809895477 18000754264140704419677701)
          ·
            refine ⟨3375141424526382078689569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18000754264140704419677701 3375141424526382078689569)
            ·
              refine ⟨2531356068394786559017177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3375141424526382078689569 2531356068394786559017177)
              ·
                refine ⟨1898517051296089919262883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2531356068394786559017177 1898517051296089919262883)
                ·
                  refine ⟨2847775576944134878894325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1898517051296089919262883 2847775576944134878894325)
                  ·
                    refine ⟨266978960338512644896343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2847775576944134878894325 266978960338512644896343)
                    ·
                      rfl

theorem cell23_1559819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 5].length) (baseStart_1559819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559819 prefixEnd_1559819 := by exact prefixLift 1559819
  have htrace : WordTrace (prefixWord ++ tailWord_1559819) baseStart_1559819 baseEnd_1559819 := by
    simpa [prefixWord, tailWord_1559819, baseEnd_1559819] using wordTrace_append hprefix tailTrace_1559819
  have hstable : (prefixWord ++ tailWord_1559819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559819).length < 2 ^ (prefixWord ++ tailWord_1559819).sum := by decide
  have hdescent : baseEnd_1559819 < baseStart_1559819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559873 : List Nat := [1, 2, 5, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_1559873 : Nat := 118140960795 + 1559873 * 2 ^ 59
def prefixEnd_1559873 : Nat := 4983230072969 + 3 ^ 40 * 1559873 * 2
def baseEnd_1559873 : Nat := 800964608970880723413781

theorem tailTrace_1559873 : CollatzResearch.WordTrace tailWord_1559873 prefixEnd_1559873 800964608970880723413781 := by
  unfold tailWord_1559873
  simp only [CollatzResearch.WordTrace]
  refine ⟨56893242277854000943916273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37928828185236000629277515 56893242277854000943916273)
  ·
    refine ⟨42669931708390500707937205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56893242277854000943916273 42669931708390500707937205)
    ·
      refine ⟨4000306097661609441369113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42669931708390500707937205 4000306097661609441369113)
      ·
        refine ⟨3000229573246207081026835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4000306097661609441369113 3000229573246207081026835)
        ·
          refine ⟨4500344359869310621540253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3000229573246207081026835 4500344359869310621540253)
          ·
            refine ⟨1687629134950991483077595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4500344359869310621540253 1687629134950991483077595)
            ·
              refine ⟨2531443702426487224616393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1687629134950991483077595 2531443702426487224616393)
              ·
                refine ⟨1898582776819865418462295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2531443702426487224616393 1898582776819865418462295)
                ·
                  refine ⟨2847874165229798127693443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1898582776819865418462295 2847874165229798127693443)
                  ·
                    refine ⟨4271811247844697191540165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2847874165229798127693443 4271811247844697191540165)
                    ·
                      refine ⟨800964608970880723413781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4271811247844697191540165 800964608970880723413781)
                      ·
                        rfl

theorem cell23_1559873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_1559873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559873 prefixEnd_1559873 := by exact prefixLift 1559873
  have htrace : WordTrace (prefixWord ++ tailWord_1559873) baseStart_1559873 baseEnd_1559873 := by
    simpa [prefixWord, tailWord_1559873, baseEnd_1559873] using wordTrace_append hprefix tailTrace_1559873
  have hstable : (prefixWord ++ tailWord_1559873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559873).length < 2 ^ (prefixWord ++ tailWord_1559873).sum := by decide
  have hdescent : baseEnd_1559873 < baseStart_1559873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559889 : List Nat := [1, 2, 2, 1, 4, 1, 3, 2, 1, 3, 3]
def baseStart_1559889 : Nat := 118140960795 + 1559889 * 2 ^ 59
def prefixEnd_1559889 : Nat := 4983230072969 + 3 ^ 40 * 1559889 * 2
def baseEnd_1559889 : Nat := 800972824661352660813707

theorem tailTrace_1559889 : CollatzResearch.WordTrace tailWord_1559889 prefixEnd_1559889 800972824661352660813707 := by
  unfold tailWord_1559889
  simp only [CollatzResearch.WordTrace]
  refine ⟨56893825845796035676498721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37929217230530690450999147 56893825845796035676498721)
  ·
    refine ⟨42670369384347026757374041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56893825845796035676498721 42670369384347026757374041)
    ·
      refine ⟨32002777038260270068030531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42670369384347026757374041 32002777038260270068030531)
      ·
        refine ⟨48004165557390405102045797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32002777038260270068030531 48004165557390405102045797)
        ·
          refine ⟨9000781042010700956633587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48004165557390405102045797 9000781042010700956633587)
          ·
            refine ⟨13501171563016051434950381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9000781042010700956633587 13501171563016051434950381)
            ·
              refine ⟨5062939336131019288106393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13501171563016051434950381 5062939336131019288106393)
              ·
                refine ⟨3797204502098264466079795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5062939336131019288106393 3797204502098264466079795)
                ·
                  refine ⟨5695806753147396699119693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3797204502098264466079795 5695806753147396699119693)
                  ·
                    refine ⟨2135927532430273762169885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5695806753147396699119693 2135927532430273762169885)
                    ·
                      refine ⟨800972824661352660813707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2135927532430273762169885 800972824661352660813707)
                      ·
                        rfl

theorem cell23_1559889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 3, 3].length) (baseStart_1559889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559889 prefixEnd_1559889 := by exact prefixLift 1559889
  have htrace : WordTrace (prefixWord ++ tailWord_1559889) baseStart_1559889 baseEnd_1559889 := by
    simpa [prefixWord, tailWord_1559889, baseEnd_1559889] using wordTrace_append hprefix tailTrace_1559889
  have hstable : (prefixWord ++ tailWord_1559889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559889).length < 2 ^ (prefixWord ++ tailWord_1559889).sum := by decide
  have hdescent : baseEnd_1559889 < baseStart_1559889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559893 : List Nat := [1, 3, 2, 2, 3, 2, 3, 1, 1, 2, 3]
def baseStart_1559893 : Nat := 118140960795 + 1559893 * 2 ^ 59
def prefixEnd_1559893 : Nat := 4983230072969 + 3 ^ 40 * 1559893 * 2
def baseEnd_1559893 : Nat := 800974878583970645163689

theorem tailTrace_1559893 : CollatzResearch.WordTrace tailWord_1559893 prefixEnd_1559893 800974878583970645163689 := by
  unfold tailWord_1559893
  simp only [CollatzResearch.WordTrace]
  refine ⟨56893971737781544359644333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37929314491854362906429555 56893971737781544359644333)
  ·
    refine ⟨21335239401668079134866625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56893971737781544359644333 21335239401668079134866625)
    ·
      refine ⟨16001429551251059351149969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21335239401668079134866625 16001429551251059351149969)
      ·
        refine ⟨12001072163438294513362477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16001429551251059351149969 12001072163438294513362477)
        ·
          refine ⟨4500402061289360442510929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12001072163438294513362477 4500402061289360442510929)
          ·
            refine ⟨3375301545967020331883197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4500402061289360442510929 3375301545967020331883197)
            ·
              refine ⟨1265738079737632624456199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3375301545967020331883197 1265738079737632624456199)
              ·
                refine ⟨1898607119606448936684299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1265738079737632624456199 1898607119606448936684299)
                ·
                  refine ⟨2847910679409673405026449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1898607119606448936684299 2847910679409673405026449)
                  ·
                    refine ⟨2135933009557255053769837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2847910679409673405026449 2135933009557255053769837)
                    ·
                      refine ⟨800974878583970645163689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2135933009557255053769837 800974878583970645163689)
                      ·
                        rfl

theorem cell23_1559893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_1559893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559893 prefixEnd_1559893 := by exact prefixLift 1559893
  have htrace : WordTrace (prefixWord ++ tailWord_1559893) baseStart_1559893 baseEnd_1559893 := by
    simpa [prefixWord, tailWord_1559893, baseEnd_1559893] using wordTrace_append hprefix tailTrace_1559893
  have hstable : (prefixWord ++ tailWord_1559893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559893).length < 2 ^ (prefixWord ++ tailWord_1559893).sum := by decide
  have hdescent : baseEnd_1559893 < baseStart_1559893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559901 : List Nat := [1, 4, 5, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_1559901 : Nat := 118140960795 + 1559901 * 2 ^ 59
def prefixEnd_1559901 : Nat := 4983230072969 + 3 ^ 40 * 1559901 * 2
def baseEnd_1559901 : Nat := 800978986429206613863653

theorem tailTrace_1559901 : CollatzResearch.WordTrace tailWord_1559901 prefixEnd_1559901 800978986429206613863653 := by
  unfold tailWord_1559901
  simp only [CollatzResearch.WordTrace]
  refine ⟨56894263521752561725935557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37929509014501707817290371 56894263521752561725935557)
  ·
    refine ⟨10667674410328605323612917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56894263521752561725935557 10667674410328605323612917)
    ·
      refine ⟨1000094475968306749088711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10667674410328605323612917 1000094475968306749088711)
      ·
        refine ⟨1500141713952460123633067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1000094475968306749088711 1500141713952460123633067)
        ·
          refine ⟨2250212570928690185449601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1500141713952460123633067 2250212570928690185449601)
          ·
            refine ⟨1687659428196517639087201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2250212570928690185449601 1687659428196517639087201)
            ·
              refine ⟨1265744571147388229315401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1687659428196517639087201 1265744571147388229315401)
              ·
                refine ⟨949308428360541171986551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1265744571147388229315401 949308428360541171986551)
                ·
                  refine ⟨1423962642540811757979827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 949308428360541171986551 1423962642540811757979827)
                  ·
                    refine ⟨2135943963811217636969741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1423962642540811757979827 2135943963811217636969741)
                    ·
                      refine ⟨800978986429206613863653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2135943963811217636969741 800978986429206613863653)
                      ·
                        rfl

theorem cell23_1559901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_1559901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559901 prefixEnd_1559901 := by exact prefixLift 1559901
  have htrace : WordTrace (prefixWord ++ tailWord_1559901) baseStart_1559901 baseEnd_1559901 := by
    simpa [prefixWord, tailWord_1559901, baseEnd_1559901] using wordTrace_append hprefix tailTrace_1559901
  have hstable : (prefixWord ++ tailWord_1559901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559901).length < 2 ^ (prefixWord ++ tailWord_1559901).sum := by decide
  have hdescent : baseEnd_1559901 < baseStart_1559901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559907 : List Nat := [1, 1, 1, 5, 2, 4, 2, 2, 1, 2, 2]
def baseStart_1559907 : Nat := 118140960795 + 1559907 * 2 ^ 59
def prefixEnd_1559907 : Nat := 4983230072969 + 3 ^ 40 * 1559907 * 2
def baseEnd_1559907 : Nat := 800982067313133590388625

theorem tailTrace_1559907 : CollatzResearch.WordTrace tailWord_1559907 prefixEnd_1559907 800982067313133590388625 := by
  unfold tailWord_1559907
  simp only [CollatzResearch.WordTrace]
  refine ⟨56894482359730824750653975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37929654906487216500435983 56894482359730824750653975)
  ·
    refine ⟨85341723539596237125980963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56894482359730824750653975 85341723539596237125980963)
    ·
      refine ⟨128012585309394355688971445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85341723539596237125980963 128012585309394355688971445)
      ·
        refine ⟨12001179872755720845841073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128012585309394355688971445 12001179872755720845841073)
        ·
          refine ⟨9000884904566790634380805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12001179872755720845841073 9000884904566790634380805)
          ·
            refine ⟨1687665919606273243946401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9000884904566790634380805 1687665919606273243946401)
            ·
              refine ⟨1265749439704704932959801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1687665919606273243946401 1265749439704704932959801)
              ·
                refine ⟨949312079778528699719851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1265749439704704932959801 949312079778528699719851)
                ·
                  refine ⟨1423968119667793049579777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 949312079778528699719851 1423968119667793049579777)
                  ·
                    refine ⟨1067976089750844787184833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1423968119667793049579777 1067976089750844787184833)
                    ·
                      refine ⟨800982067313133590388625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1067976089750844787184833 800982067313133590388625)
                      ·
                        rfl

theorem cell23_1559907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_1559907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559907 prefixEnd_1559907 := by exact prefixLift 1559907
  have htrace : WordTrace (prefixWord ++ tailWord_1559907) baseStart_1559907 baseEnd_1559907 := by
    simpa [prefixWord, tailWord_1559907, baseEnd_1559907] using wordTrace_append hprefix tailTrace_1559907
  have hstable : (prefixWord ++ tailWord_1559907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559907).length < 2 ^ (prefixWord ++ tailWord_1559907).sum := by decide
  have hdescent : baseEnd_1559907 < baseStart_1559907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559916 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 3, 3, 2]
def baseStart_1559916 : Nat := 118140960795 + 1559916 * 2 ^ 59
def prefixEnd_1559916 : Nat := 4983230072969 + 3 ^ 40 * 1559916 * 2
def baseEnd_1559916 : Nat := 800986688639024055176083

theorem tailTrace_1559916 : CollatzResearch.WordTrace tailWord_1559916 prefixEnd_1559916 800986688639024055176083 := by
  unfold tailWord_1559916
  simp only [CollatzResearch.WordTrace]
  refine ⟨28447405308349109643865801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37929873744465479525154401 28447405308349109643865801)
  ·
    refine ⟨21335553981261832232899351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28447405308349109643865801 21335553981261832232899351)
    ·
      refine ⟨32003330971892748349349027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21335553981261832232899351 32003330971892748349349027)
      ·
        refine ⟨48004996457839122524023541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32003330971892748349349027 48004996457839122524023541)
        ·
          refine ⟨4500468417922417736627207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48004996457839122524023541 4500468417922417736627207)
          ·
            refine ⟨6750702626883626604940811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4500468417922417736627207 6750702626883626604940811)
            ·
              refine ⟨10126053940325439907411217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6750702626883626604940811 10126053940325439907411217)
              ·
                refine ⟨7594540455244079930558413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10126053940325439907411217 7594540455244079930558413)
                ·
                  refine ⟨2847952670716529973959405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7594540455244079930558413 2847952670716529973959405)
                  ·
                    refine ⟨1067982251518698740234777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2847952670716529973959405 1067982251518698740234777)
                    ·
                      refine ⟨800986688639024055176083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1067982251518698740234777 800986688639024055176083)
                      ·
                        rfl

theorem cell23_1559916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 3, 2].length) (baseStart_1559916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559916 prefixEnd_1559916 := by exact prefixLift 1559916
  have htrace : WordTrace (prefixWord ++ tailWord_1559916) baseStart_1559916 baseEnd_1559916 := by
    simpa [prefixWord, tailWord_1559916, baseEnd_1559916] using wordTrace_append hprefix tailTrace_1559916
  have hstable : (prefixWord ++ tailWord_1559916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559916).length < 2 ^ (prefixWord ++ tailWord_1559916).sum := by decide
  have hdescent : baseEnd_1559916 < baseStart_1559916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559950 : List Nat := [4, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2]
def baseStart_1559950 : Nat := 118140960795 + 1559950 * 2 ^ 59
def prefixEnd_1559950 : Nat := 4983230072969 + 3 ^ 40 * 1559950 * 2
def baseEnd_1559950 : Nat := 801004146981276922150927

theorem tailTrace_1559950 : CollatzResearch.WordTrace tailWord_1559950 prefixEnd_1559950 801004146981276922150927 := by
  unfold tailWord_1559950
  simp only [CollatzResearch.WordTrace]
  refine ⟨7112006337321880386808663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37930700465716695396312869 7112006337321880386808663)
  ·
    refine ⟨10668009505982820580212995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7112006337321880386808663 10668009505982820580212995)
    ·
      refine ⟨16002014258974230870319493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10668009505982820580212995 16002014258974230870319493)
      ·
        refine ⟨3000377673557668288184905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16002014258974230870319493 3000377673557668288184905)
        ·
          refine ⟨2250283255168251216138679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3000377673557668288184905 2250283255168251216138679)
          ·
            refine ⟨3375424882752376824208019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2250283255168251216138679 3375424882752376824208019)
            ·
              refine ⟨5063137324128565236312029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3375424882752376824208019 5063137324128565236312029)
              ·
                refine ⟨1898676496548211963617011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5063137324128565236312029 1898676496548211963617011)
                ·
                  refine ⟨2848014744822317945425517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1898676496548211963617011 2848014744822317945425517)
                  ·
                    refine ⟨1068005529308369229534569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2848014744822317945425517 1068005529308369229534569)
                    ·
                      refine ⟨801004146981276922150927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1068005529308369229534569 801004146981276922150927)
                      ·
                        rfl

theorem cell23_1559950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_1559950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1559950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1559950 prefixEnd_1559950 := by exact prefixLift 1559950
  have htrace : WordTrace (prefixWord ++ tailWord_1559950) baseStart_1559950 baseEnd_1559950 := by
    simpa [prefixWord, tailWord_1559950, baseEnd_1559950] using wordTrace_append hprefix tailTrace_1559950
  have hstable : (prefixWord ++ tailWord_1559950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559950).length < 2 ^ (prefixWord ++ tailWord_1559950).sum := by decide
  have hdescent : baseEnd_1559950 < baseStart_1559950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560020 : List Nat := [2, 4, 1, 2, 3, 1, 3, 2, 5]
def baseStart_1560020 : Nat := 118140960795 + 1560020 * 2 ^ 59
def prefixEnd_1560020 : Nat := 4983230072969 + 3 ^ 40 * 1560020 * 2
def baseEnd_1560020 : Nat := 89004454514121294252845

theorem tailTrace_1560020 : CollatzResearch.WordTrace tailWord_1560020 prefixEnd_1560020 89004454514121294252845 := by
  unfold tailWord_1560020
  simp only [CollatzResearch.WordTrace]
  refine ⟨28449301904160722524758757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37932402538880963366345009 28449301904160722524758757)
  ·
    refine ⟨5334244107030135473392267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28449301904160722524758757 5334244107030135473392267)
    ·
      refine ⟨8001366160545203210088401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5334244107030135473392267 8001366160545203210088401)
      ·
        refine ⟨6001024620408902407566301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8001366160545203210088401 6001024620408902407566301)
        ·
          refine ⟨2250384232653338402837363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6001024620408902407566301 2250384232653338402837363)
          ·
            refine ⟨3375576348980007604256045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2250384232653338402837363 3375576348980007604256045)
            ·
              refine ⟨1265841130867502851596017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3375576348980007604256045 1265841130867502851596017)
              ·
                refine ⟨949380848150627138697013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1265841130867502851596017 949380848150627138697013)
                ·
                  refine ⟨89004454514121294252845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 949380848150627138697013 89004454514121294252845)
                  ·
                    rfl

theorem cell23_1560020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_1560020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560020 prefixEnd_1560020 := by exact prefixLift 1560020
  have htrace : WordTrace (prefixWord ++ tailWord_1560020) baseStart_1560020 baseEnd_1560020 := by
    simpa [prefixWord, tailWord_1560020, baseEnd_1560020] using wordTrace_append hprefix tailTrace_1560020
  have hstable : (prefixWord ++ tailWord_1560020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560020).length < 2 ^ (prefixWord ++ tailWord_1560020).sum := by decide
  have hdescent : baseEnd_1560020 < baseStart_1560020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560036 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 2, 4, 2]
def baseStart_1560036 : Nat := 118140960795 + 1560036 * 2 ^ 59
def prefixEnd_1560036 : Nat := 4983230072969 + 3 ^ 40 * 1560036 * 2
def baseEnd_1560036 : Nat := 801048306317563585675531

theorem tailTrace_1560036 : CollatzResearch.WordTrace tailWord_1560036 prefixEnd_1560036 801048306317563585675531 := by
  unfold tailWord_1560036
  simp only [CollatzResearch.WordTrace]
  refine ⟨28449593688131739891049981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37932791584175653188066641 28449593688131739891049981)
  ·
    refine ⟨10668597633049402459143743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28449593688131739891049981 10668597633049402459143743)
    ·
      refine ⟨16002896449574103688715615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10668597633049402459143743 16002896449574103688715615)
      ·
        refine ⟨24004344674361155533073423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16002896449574103688715615 24004344674361155533073423)
        ·
          refine ⟨36006517011541733299610135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24004344674361155533073423 36006517011541733299610135)
          ·
            refine ⟨54009775517312599949415203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36006517011541733299610135 54009775517312599949415203)
            ·
              refine ⟨81014663275968899924122805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54009775517312599949415203 81014663275968899924122805)
              ·
                refine ⟨7595124682122084367886513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81014663275968899924122805 7595124682122084367886513)
                ·
                  refine ⟨5696343511591563275914885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7595124682122084367886513 5696343511591563275914885)
                  ·
                    refine ⟨1068064408423418114234041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5696343511591563275914885 1068064408423418114234041)
                    ·
                      refine ⟨801048306317563585675531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1068064408423418114234041 801048306317563585675531)
                      ·
                        rfl

theorem cell23_1560036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 2, 4, 2].length) (baseStart_1560036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560036 prefixEnd_1560036 := by exact prefixLift 1560036
  have htrace : WordTrace (prefixWord ++ tailWord_1560036) baseStart_1560036 baseEnd_1560036 := by
    simpa [prefixWord, tailWord_1560036, baseEnd_1560036] using wordTrace_append hprefix tailTrace_1560036
  have hstable : (prefixWord ++ tailWord_1560036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560036).length < 2 ^ (prefixWord ++ tailWord_1560036).sum := by decide
  have hdescent : baseEnd_1560036 < baseStart_1560036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560046 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 5, 4]
def baseStart_1560046 : Nat := 118140960795 + 1560046 * 2 ^ 59
def prefixEnd_1560046 : Nat := 4983230072969 + 3 ^ 40 * 1560046 * 2
def baseEnd_1560046 : Nat := 267017813708036182183495

theorem tailTrace_1560046 : CollatzResearch.WordTrace tailWord_1560046 prefixEnd_1560046 267017813708036182183495 := by
  unfold tailWord_1560046
  simp only [CollatzResearch.WordTrace]
  refine ⟨7112444013278406436245499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37933034737484834326642661 7112444013278406436245499)
  ·
    refine ⟨10668666019917609654368249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7112444013278406436245499 10668666019917609654368249)
    ·
      refine ⟨8001499514938207240776187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10668666019917609654368249 8001499514938207240776187)
      ·
        refine ⟨12002249272407310861164281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8001499514938207240776187 12002249272407310861164281)
        ·
          refine ⟨9001686954305483145873211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12002249272407310861164281 9001686954305483145873211)
          ·
            refine ⟨13502530431458224718809817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9001686954305483145873211 13502530431458224718809817)
            ·
              refine ⟨10126897823593668539107363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13502530431458224718809817 10126897823593668539107363)
              ·
                refine ⟨15190346735390502808661045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10126897823593668539107363 15190346735390502808661045)
                ·
                  refine ⟨1424095006442859638311973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15190346735390502808661045 1424095006442859638311973)
                  ·
                    refine ⟨267017813708036182183495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1424095006442859638311973 267017813708036182183495)
                    ·
                      rfl

theorem cell23_1560046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_1560046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560046 prefixEnd_1560046 := by exact prefixLift 1560046
  have htrace : WordTrace (prefixWord ++ tailWord_1560046) baseStart_1560046 baseEnd_1560046 := by
    simpa [prefixWord, tailWord_1560046, baseEnd_1560046] using wordTrace_append hprefix tailTrace_1560046
  have hstable : (prefixWord ++ tailWord_1560046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560046).length < 2 ^ (prefixWord ++ tailWord_1560046).sum := by decide
  have hdescent : baseEnd_1560046 < baseStart_1560046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560053 : List Nat := [1, 3, 5, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1560053 : Nat := 118140960795 + 1560053 * 2 ^ 59
def prefixEnd_1560053 : Nat := 4983230072969 + 3 ^ 40 * 1560053 * 2
def baseEnd_1560053 : Nat := 801057035488690019162953

theorem tailTrace_1560053 : CollatzResearch.WordTrace tailWord_1560053 prefixEnd_1560053 801057035488690019162953 := by
  unfold tailWord_1560053
  simp only [CollatzResearch.WordTrace]
  refine ⟨56899807417201891685468813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37933204944801261123645875 56899807417201891685468813)
  ·
    refine ⟨21337427781450709382050805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56899807417201891685468813 21337427781450709382050805)
    ·
      refine ⟨2000383854511004004567263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21337427781450709382050805 2000383854511004004567263)
      ·
        refine ⟨3000575781766506006850895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2000383854511004004567263 3000575781766506006850895)
        ·
          refine ⟨4500863672649759010276343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3000575781766506006850895 4500863672649759010276343)
          ·
            refine ⟨6751295508974638515414515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4500863672649759010276343 6751295508974638515414515)
            ·
              refine ⟨10126943263461957773121773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6751295508974638515414515 10126943263461957773121773)
              ·
                refine ⟨3797603723798234164920665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10126943263461957773121773 3797603723798234164920665)
                ·
                  refine ⟨2848202792848675623690499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3797603723798234164920665 2848202792848675623690499)
                  ·
                    refine ⟨4272304189273013435535749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2848202792848675623690499 4272304189273013435535749)
                    ·
                      refine ⟨801057035488690019162953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4272304189273013435535749 801057035488690019162953)
                      ·
                        rfl

theorem cell23_1560053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1560053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560053 prefixEnd_1560053 := by exact prefixLift 1560053
  have htrace : WordTrace (prefixWord ++ tailWord_1560053) baseStart_1560053 baseEnd_1560053 := by
    simpa [prefixWord, tailWord_1560053, baseEnd_1560053] using wordTrace_append hprefix tailTrace_1560053
  have hstable : (prefixWord ++ tailWord_1560053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560053).length < 2 ^ (prefixWord ++ tailWord_1560053).sum := by decide
  have hdescent : baseEnd_1560053 < baseStart_1560053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560056 : List Nat := [2, 1, 2, 1, 1, 5, 1, 3, 2, 2, 3]
def baseStart_1560056 : Nat := 118140960795 + 1560056 * 2 ^ 59
def prefixEnd_1560056 : Nat := 4983230072969 + 3 ^ 40 * 1560056 * 2
def baseEnd_1560056 : Nat := 801058575930653507425439

theorem tailTrace_1560056 : CollatzResearch.WordTrace tailWord_1560056 prefixEnd_1560056 801058575930653507425439 := by
  unfold tailWord_1560056
  simp only [CollatzResearch.WordTrace]
  refine ⟨28449958418095511598914011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37933277890794015465218681 28449958418095511598914011)
  ·
    refine ⟨42674937627143267398371017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28449958418095511598914011 42674937627143267398371017)
    ·
      refine ⟨32006203220357450548778263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42674937627143267398371017 32006203220357450548778263)
      ·
        refine ⟨48009304830536175823167395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32006203220357450548778263 48009304830536175823167395)
        ·
          refine ⟨72013957245804263734751093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48009304830536175823167395 72013957245804263734751093)
          ·
            refine ⟨6751308491794149725132915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72013957245804263734751093 6751308491794149725132915)
            ·
              refine ⟨10126962737691224587699373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6751308491794149725132915 10126962737691224587699373)
              ·
                refine ⟨3797611026634209220387265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10126962737691224587699373 3797611026634209220387265)
                ·
                  refine ⟨2848208269975656915290449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3797611026634209220387265 2848208269975656915290449)
                  ·
                    refine ⟨2136156202481742686467837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2848208269975656915290449 2136156202481742686467837)
                    ·
                      refine ⟨801058575930653507425439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2136156202481742686467837 801058575930653507425439)
                      ·
                        rfl

theorem cell23_1560056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 2, 2, 3].length) (baseStart_1560056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560056 prefixEnd_1560056 := by exact prefixLift 1560056
  have htrace : WordTrace (prefixWord ++ tailWord_1560056) baseStart_1560056 baseEnd_1560056 := by
    simpa [prefixWord, tailWord_1560056, baseEnd_1560056] using wordTrace_append hprefix tailTrace_1560056
  have hstable : (prefixWord ++ tailWord_1560056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560056).length < 2 ^ (prefixWord ++ tailWord_1560056).sum := by decide
  have hdescent : baseEnd_1560056 < baseStart_1560056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560106 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 3, 5]
def baseStart_1560106 : Nat := 118140960795 + 1560106 * 2 ^ 59
def prefixEnd_1560106 : Nat := 4983230072969 + 3 ^ 40 * 1560106 * 2
def baseEnd_1560106 : Nat := 267028083321126103933403

theorem tailTrace_1560106 : CollatzResearch.WordTrace tailWord_1560106 prefixEnd_1560106 267028083321126103933403 := by
  unfold tailWord_1560106
  simp only [CollatzResearch.WordTrace]
  refine ⟨14225435121502470434287043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37934493657339921158098781 14225435121502470434287043)
  ·
    refine ⟨21338152682253705651430565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14225435121502470434287043 21338152682253705651430565)
    ·
      refine ⟨4000903627922569809643231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21338152682253705651430565 4000903627922569809643231)
      ·
        refine ⟨6001355441883854714464847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4000903627922569809643231 6001355441883854714464847)
        ·
          refine ⟨9002033162825782071697271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6001355441883854714464847 9002033162825782071697271)
          ·
            refine ⟨13503049744238673107545907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9002033162825782071697271 13503049744238673107545907)
            ·
              refine ⟨20254574616358009661318861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13503049744238673107545907 20254574616358009661318861)
              ·
                refine ⟨7595465481134253622994573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20254574616358009661318861 7595465481134253622994573)
                ·
                  refine ⟨2848299555425345108622965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7595465481134253622994573 2848299555425345108622965)
                  ·
                    refine ⟨267028083321126103933403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2848299555425345108622965 267028083321126103933403)
                    ·
                      rfl

theorem cell23_1560106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_1560106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560106 prefixEnd_1560106 := by exact prefixLift 1560106
  have htrace : WordTrace (prefixWord ++ tailWord_1560106) baseStart_1560106 baseEnd_1560106 := by
    simpa [prefixWord, tailWord_1560106, baseEnd_1560106] using wordTrace_append hprefix tailTrace_1560106
  have hstable : (prefixWord ++ tailWord_1560106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560106).length < 2 ^ (prefixWord ++ tailWord_1560106).sum := by decide
  have hdescent : baseEnd_1560106 < baseStart_1560106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560120 : List Nat := [2, 1, 2, 1, 4, 2, 1, 5, 1, 1, 3]
def baseStart_1560120 : Nat := 118140960795 + 1560120 * 2 ^ 59
def prefixEnd_1560120 : Nat := 4983230072969 + 3 ^ 40 * 1560120 * 2
def baseEnd_1560120 : Nat := 801091438692541257025145

theorem tailTrace_1560120 : CollatzResearch.WordTrace tailWord_1560120 prefixEnd_1560120 801091438692541257025145 := by
  unfold tailWord_1560120
  simp only [CollatzResearch.WordTrace]
  refine ⟨28451125553979581064078907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37934834071972774752105209 28451125553979581064078907)
  ·
    refine ⟨42676688330969371596118361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28451125553979581064078907 42676688330969371596118361)
    ·
      refine ⟨32007516248227028697088771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42676688330969371596118361 32007516248227028697088771)
      ·
        refine ⟨48011274372340543045633157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32007516248227028697088771 48011274372340543045633157)
        ·
          refine ⟨9002113944813851821056217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48011274372340543045633157 9002113944813851821056217)
          ·
            refine ⟨6751585458610388865792163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9002113944813851821056217 6751585458610388865792163)
            ·
              refine ⟨10127378187915583298688245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6751585458610388865792163 10127378187915583298688245)
              ·
                refine ⟨949441705117085934252023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10127378187915583298688245 949441705117085934252023)
                ·
                  refine ⟨1424162557675628901378035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 949441705117085934252023 1424162557675628901378035)
                  ·
                    refine ⟨2136243836513443352067053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1424162557675628901378035 2136243836513443352067053)
                    ·
                      refine ⟨801091438692541257025145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2136243836513443352067053 801091438692541257025145)
                      ·
                        rfl

theorem cell23_1560120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 1, 1, 3].length) (baseStart_1560120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560120 prefixEnd_1560120 := by exact prefixLift 1560120
  have htrace : WordTrace (prefixWord ++ tailWord_1560120) baseStart_1560120 baseEnd_1560120 := by
    simpa [prefixWord, tailWord_1560120, baseEnd_1560120] using wordTrace_append hprefix tailTrace_1560120
  have hstable : (prefixWord ++ tailWord_1560120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560120).length < 2 ^ (prefixWord ++ tailWord_1560120).sum := by decide
  have hdescent : baseEnd_1560120 < baseStart_1560120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560139 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 6]
def baseStart_1560139 : Nat := 118140960795 + 1560139 * 2 ^ 59
def prefixEnd_1560139 : Nat := 4983230072969 + 3 ^ 40 * 1560139 * 2
def baseEnd_1560139 : Nat := 801101194824976682687557

theorem tailTrace_1560139 : CollatzResearch.WordTrace tailWord_1560139 prefixEnd_1560139 801101194824976682687557 := by
  unfold tailWord_1560139
  simp only [CollatzResearch.WordTrace]
  refine ⟨56902944094890328373099471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37935296063260218915399647 56902944094890328373099471)
  ·
    refine ⟨85354416142335492559649207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56902944094890328373099471 85354416142335492559649207)
    ·
      refine ⟨128031624213503238839473811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85354416142335492559649207 128031624213503238839473811)
      ·
        refine ⟨192047436320254858259210717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128031624213503238839473811 192047436320254858259210717)
        ·
          refine ⟨72017788620095571847204019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192047436320254858259210717 72017788620095571847204019)
          ·
            refine ⟨108026682930143357770806029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72017788620095571847204019 108026682930143357770806029)
            ·
              refine ⟨40510006098803759164052261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108026682930143357770806029 40510006098803759164052261)
              ·
                refine ⟨7595626143525704843259799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40510006098803759164052261 7595626143525704843259799)
                ·
                  refine ⟨11393439215288557264889699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7595626143525704843259799 11393439215288557264889699)
                  ·
                    refine ⟨17090158822932835897334549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11393439215288557264889699 17090158822932835897334549)
                    ·
                      refine ⟨801101194824976682687557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17090158822932835897334549 801101194824976682687557)
                      ·
                        rfl

theorem cell23_1560139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 6].length) (baseStart_1560139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560139 prefixEnd_1560139 := by exact prefixLift 1560139
  have htrace : WordTrace (prefixWord ++ tailWord_1560139) baseStart_1560139 baseEnd_1560139 := by
    simpa [prefixWord, tailWord_1560139, baseEnd_1560139] using wordTrace_append hprefix tailTrace_1560139
  have hstable : (prefixWord ++ tailWord_1560139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560139).length < 2 ^ (prefixWord ++ tailWord_1560139).sum := by decide
  have hdescent : baseEnd_1560139 < baseStart_1560139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560146 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_1560146 : Nat := 118140960795 + 1560146 * 2 ^ 59
def prefixEnd_1560146 : Nat := 4983230072969 + 3 ^ 40 * 1560146 * 2
def baseEnd_1560146 : Nat := 801104789189558155300025

theorem tailTrace_1560146 : CollatzResearch.WordTrace tailWord_1560146 prefixEnd_1560146 801104789189558155300025 := by
  unfold tailWord_1560146
  simp only [CollatzResearch.WordTrace]
  refine ⟨14225799851466242142151073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37935466270576645712402861 14225799851466242142151073)
  ·
    refine ⟨10669349888599681606613305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14225799851466242142151073 10669349888599681606613305)
    ·
      refine ⟨8002012416449761204959979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10669349888599681606613305 8002012416449761204959979)
      ·
        refine ⟨12003018624674641807439969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8002012416449761204959979 12003018624674641807439969)
        ·
          refine ⟨9002263968505981355579977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12003018624674641807439969 9002263968505981355579977)
          ·
            refine ⟨6751697976379486016684983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9002263968505981355579977 6751697976379486016684983)
            ·
              refine ⟨10127546964569229025027475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6751697976379486016684983 10127546964569229025027475)
              ·
                refine ⟨15191320446853843537541213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10127546964569229025027475 15191320446853843537541213)
                ·
                  refine ⟨5696745167570191326577955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15191320446853843537541213 5696745167570191326577955)
                  ·
                    refine ⟨8545117751355286989866933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5696745167570191326577955 8545117751355286989866933)
                    ·
                      refine ⟨801104789189558155300025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8545117751355286989866933 801104789189558155300025)
                      ·
                        rfl

theorem cell23_1560146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_1560146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560146 prefixEnd_1560146 := by exact prefixLift 1560146
  have htrace : WordTrace (prefixWord ++ tailWord_1560146) baseStart_1560146 baseEnd_1560146 := by
    simpa [prefixWord, tailWord_1560146, baseEnd_1560146] using wordTrace_append hprefix tailTrace_1560146
  have hstable : (prefixWord ++ tailWord_1560146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560146).length < 2 ^ (prefixWord ++ tailWord_1560146).sum := by decide
  have hdescent : baseEnd_1560146 < baseStart_1560146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560149 : List Nat := [1, 3, 2, 2, 1, 1, 1, 12]
def baseStart_1560149 : Nat := 118140960795 + 1560149 * 2 ^ 59
def prefixEnd_1560149 : Nat := 4983230072969 + 3 ^ 40 * 1560149 * 2
def baseEnd_1560149 : Nat := 29670604801167468280093

theorem tailTrace_1560149 : CollatzResearch.WordTrace tailWord_1560149 prefixEnd_1560149 29670604801167468280093 := by
  unfold tailWord_1560149
  simp only [CollatzResearch.WordTrace]
  refine ⟨56903308824854100080963501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37935539216569400053975667 56903308824854100080963501)
  ·
    refine ⟨21338740809320287530361313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56903308824854100080963501 21338740809320287530361313)
    ·
      refine ⟨16004055606990215647770985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21338740809320287530361313 16004055606990215647770985)
      ·
        refine ⟨12003041705242661735828239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16004055606990215647770985 12003041705242661735828239)
        ·
          refine ⟨18004562557863992603742359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12003041705242661735828239 18004562557863992603742359)
          ·
            refine ⟨27006843836795988905613539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18004562557863992603742359 27006843836795988905613539)
            ·
              refine ⟨40510265755193983358420309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27006843836795988905613539 40510265755193983358420309)
              ·
                refine ⟨29670604801167468280093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 40510265755193983358420309 29670604801167468280093)
                ·
                  rfl

theorem cell23_1560149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 12].length) (baseStart_1560149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560149 prefixEnd_1560149 := by exact prefixLift 1560149
  have htrace : WordTrace (prefixWord ++ tailWord_1560149) baseStart_1560149 baseEnd_1560149 := by
    simpa [prefixWord, tailWord_1560149, baseEnd_1560149] using wordTrace_append hprefix tailTrace_1560149
  have hstable : (prefixWord ++ tailWord_1560149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560149).length < 2 ^ (prefixWord ++ tailWord_1560149).sum := by decide
  have hdescent : baseEnd_1560149 < baseStart_1560149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560157 : List Nat := [1, 4, 4, 2, 1, 1, 2, 2, 1, 5]
def baseStart_1560157 : Nat := 118140960795 + 1560157 * 2 ^ 59
def prefixEnd_1560157 : Nat := 4983230072969 + 3 ^ 40 * 1560157 * 2
def baseEnd_1560157 : Nat := 267036812492252537420825

theorem tailTrace_1560157 : CollatzResearch.WordTrace tailWord_1560157 prefixEnd_1560157 267036812492252537420825 := by
  unfold tailWord_1560157
  simp only [CollatzResearch.WordTrace]
  refine ⟨56903600608825117447254725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37935733739216744964836483 56903600608825117447254725)
  ·
    refine ⟨10669425114154709521360261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56903600608825117447254725 10669425114154709521360261)
    ·
      refine ⟨2000517208904008035255049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10669425114154709521360261 2000517208904008035255049)
      ·
        refine ⟨1500387906678006026441287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2000517208904008035255049 1500387906678006026441287)
        ·
          refine ⟨2250581860017009039661931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1500387906678006026441287 2250581860017009039661931)
          ·
            refine ⟨3375872790025513559492897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2250581860017009039661931 3375872790025513559492897)
            ·
              refine ⟨2531904592519135169619673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3375872790025513559492897 2531904592519135169619673)
              ·
                refine ⟨1898928444389351377214755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2531904592519135169619673 1898928444389351377214755)
                ·
                  refine ⟨2848392666584027065822133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1898928444389351377214755 2848392666584027065822133)
                  ·
                    refine ⟨267036812492252537420825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2848392666584027065822133 267036812492252537420825)
                    ·
                      rfl

theorem cell23_1560157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_1560157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560157 prefixEnd_1560157 := by exact prefixLift 1560157
  have htrace : WordTrace (prefixWord ++ tailWord_1560157) baseStart_1560157 baseEnd_1560157 := by
    simpa [prefixWord, tailWord_1560157, baseEnd_1560157] using wordTrace_append hprefix tailTrace_1560157
  have hstable : (prefixWord ++ tailWord_1560157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560157).length < 2 ^ (prefixWord ++ tailWord_1560157).sum := by decide
  have hdescent : baseEnd_1560157 < baseStart_1560157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560163 : List Nat := [1, 1, 1, 5, 1, 3, 1, 4, 1, 2, 3]
def baseStart_1560163 : Nat := 118140960795 + 1560163 * 2 ^ 59
def prefixEnd_1560163 : Nat := 4983230072969 + 3 ^ 40 * 1560163 * 2
def baseEnd_1560163 : Nat := 801113518360684588787447

theorem tailTrace_1560163 : CollatzResearch.WordTrace tailWord_1560163 prefixEnd_1560163 801113518360684588787447 := by
  unfold tailWord_1560163
  simp only [CollatzResearch.WordTrace]
  refine ⟨56903819446803380471973143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37935879631202253647982095 56903819446803380471973143)
  ·
    refine ⟨85355729170205070707959715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56903819446803380471973143 85355729170205070707959715)
    ·
      refine ⟨128033593755307606061939573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85355729170205070707959715 128033593755307606061939573)
      ·
        refine ⟨12003149414560088068306835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128033593755307606061939573 12003149414560088068306835)
        ·
          refine ⟨18004724121840132102460253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12003149414560088068306835 18004724121840132102460253)
          ·
            refine ⟨6751771545690049538422595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18004724121840132102460253 6751771545690049538422595)
            ·
              refine ⟨10127657318535074307633893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6751771545690049538422595 10127657318535074307633893)
              ·
                refine ⟨1898935747225326432681355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10127657318535074307633893 1898935747225326432681355)
                ·
                  refine ⟨2848403620837989649022033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1898935747225326432681355 2848403620837989649022033)
                  ·
                    refine ⟨2136302715628492236766525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2848403620837989649022033 2136302715628492236766525)
                    ·
                      refine ⟨801113518360684588787447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2136302715628492236766525 801113518360684588787447)
                      ·
                        rfl

theorem cell23_1560163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_1560163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560163 prefixEnd_1560163 := by exact prefixLift 1560163
  have htrace : WordTrace (prefixWord ++ tailWord_1560163) baseStart_1560163 baseEnd_1560163 := by
    simpa [prefixWord, tailWord_1560163, baseEnd_1560163] using wordTrace_append hprefix tailTrace_1560163
  have hstable : (prefixWord ++ tailWord_1560163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560163).length < 2 ^ (prefixWord ++ tailWord_1560163).sum := by decide
  have hdescent : baseEnd_1560163 < baseStart_1560163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560203 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 3, 3, 2]
def baseStart_1560203 : Nat := 118140960795 + 1560203 * 2 ^ 59
def prefixEnd_1560203 : Nat := 4983230072969 + 3 ^ 40 * 1560203 * 2
def baseEnd_1560203 : Nat := 801134057586864432287263

theorem tailTrace_1560203 : CollatzResearch.WordTrace tailWord_1560203 prefixEnd_1560203 801134057586864432287263 := by
  unfold tailWord_1560203
  simp only [CollatzResearch.WordTrace]
  refine ⟨56905278366658467303429263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37936852244438978202286175 56905278366658467303429263)
  ·
    refine ⟨85357917549987700955143895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56905278366658467303429263 85357917549987700955143895)
    ·
      refine ⟨128036876324981551432715843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85357917549987700955143895 128036876324981551432715843)
      ·
        refine ⟨192055314487472327149073765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128036876324981551432715843 192055314487472327149073765)
        ·
          refine ⟨36010371466401061340451331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192055314487472327149073765 36010371466401061340451331)
          ·
            refine ⟨54015557199601592010676997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36010371466401061340451331 54015557199601592010676997)
            ·
              refine ⟨10127916974925298502001937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54015557199601592010676997 10127916974925298502001937)
              ·
                refine ⟨7595937731193973876501453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10127916974925298502001937 7595937731193973876501453)
                ·
                  refine ⟨2848476649197740203688045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7595937731193973876501453 2848476649197740203688045)
                  ·
                    refine ⟨1068178743449152576383017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2848476649197740203688045 1068178743449152576383017)
                    ·
                      refine ⟨801134057586864432287263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1068178743449152576383017 801134057586864432287263)
                      ·
                        rfl

theorem cell23_1560203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 3, 2].length) (baseStart_1560203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560203 prefixEnd_1560203 := by exact prefixLift 1560203
  have htrace : WordTrace (prefixWord ++ tailWord_1560203) baseStart_1560203 baseEnd_1560203 := by
    simpa [prefixWord, tailWord_1560203, baseEnd_1560203] using wordTrace_append hprefix tailTrace_1560203
  have hstable : (prefixWord ++ tailWord_1560203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560203).length < 2 ^ (prefixWord ++ tailWord_1560203).sum := by decide
  have hdescent : baseEnd_1560203 < baseStart_1560203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560236 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 3]
def baseStart_1560236 : Nat := 118140960795 + 1560236 * 2 ^ 59
def prefixEnd_1560236 : Nat := 4983230072969 + 3 ^ 40 * 1560236 * 2
def baseEnd_1560236 : Nat := 801151002448462803174611

theorem tailTrace_1560236 : CollatzResearch.WordTrace tailWord_1560236 prefixEnd_1560236 801151002448462803174611 := by
  unfold tailWord_1560236
  simp only [CollatzResearch.WordTrace]
  refine ⟨28453240987769456969690281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37937654650359275959587041 28453240987769456969690281)
  ·
    refine ⟨21339930740827092727267711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28453240987769456969690281 21339930740827092727267711)
    ·
      refine ⟨32009896111240639090901567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21339930740827092727267711 32009896111240639090901567)
      ·
        refine ⟨48014844166860958636352351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32009896111240639090901567 48014844166860958636352351)
        ·
          refine ⟨72022266250291437954528527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48014844166860958636352351 72022266250291437954528527)
          ·
            refine ⟨108033399375437156931792791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72022266250291437954528527 108033399375437156931792791)
            ·
              refine ⟨162050099063155735397689187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108033399375437156931792791 162050099063155735397689187)
              ·
                refine ⟨243075148594733603096533781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162050099063155735397689187 243075148594733603096533781)
                ·
                  refine ⟨11394147590378137645150021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 243075148594733603096533781 11394147590378137645150021)
                  ·
                    refine ⟨2136402673195900808465629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11394147590378137645150021 2136402673195900808465629)
                    ·
                      refine ⟨801151002448462803174611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2136402673195900808465629 801151002448462803174611)
                      ·
                        rfl

theorem cell23_1560236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 3].length) (baseStart_1560236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560236 prefixEnd_1560236 := by exact prefixLift 1560236
  have htrace : WordTrace (prefixWord ++ tailWord_1560236) baseStart_1560236 baseEnd_1560236 := by
    simpa [prefixWord, tailWord_1560236, baseEnd_1560236] using wordTrace_append hprefix tailTrace_1560236
  have hstable : (prefixWord ++ tailWord_1560236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560236).length < 2 ^ (prefixWord ++ tailWord_1560236).sum := by decide
  have hdescent : baseEnd_1560236 < baseStart_1560236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560256 : List Nat := [2, 1, 1, 2, 4, 1, 2, 3, 7]
def baseStart_1560256 : Nat := 118140960795 + 1560256 * 2 ^ 59
def prefixEnd_1560256 : Nat := 4983230072969 + 3 ^ 40 * 1560256 * 2
def baseEnd_1560256 : Nat := 89017919117950302769391

theorem tailTrace_1560256 : CollatzResearch.WordTrace tailWord_1560256 prefixEnd_1560256 89017919117950302769391 := by
  unfold tailWord_1560256
  simp only [CollatzResearch.WordTrace]
  refine ⟨28453605717733228677554311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37938140956977638236739081 28453605717733228677554311)
  ·
    refine ⟨42680408576599843016331467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28453605717733228677554311 42680408576599843016331467)
    ·
      refine ⟨64020612864899764524497201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42680408576599843016331467 64020612864899764524497201)
      ·
        refine ⟨48015459648674823393372901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64020612864899764524497201 48015459648674823393372901)
        ·
          refine ⟨9002898684126529386257419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48015459648674823393372901 9002898684126529386257419)
          ·
            refine ⟨13504348026189794079386129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9002898684126529386257419 13504348026189794079386129)
            ·
              refine ⟨10128261019642345559539597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13504348026189794079386129 10128261019642345559539597)
              ·
                refine ⟨3798097882365879584827349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10128261019642345559539597 3798097882365879584827349)
                ·
                  refine ⟨89017919117950302769391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3798097882365879584827349 89017919117950302769391)
                  ·
                    rfl

theorem cell23_1560256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 7].length) (baseStart_1560256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560256 prefixEnd_1560256 := by exact prefixLift 1560256
  have htrace : WordTrace (prefixWord ++ tailWord_1560256) baseStart_1560256 baseEnd_1560256 := by
    simpa [prefixWord, tailWord_1560256, baseEnd_1560256] using wordTrace_append hprefix tailTrace_1560256
  have hstable : (prefixWord ++ tailWord_1560256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560256).length < 2 ^ (prefixWord ++ tailWord_1560256).sum := by decide
  have hdescent : baseEnd_1560256 < baseStart_1560256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560360 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_1560360 : Nat := 118140960795 + 1560360 * 2 ^ 59
def prefixEnd_1560360 : Nat := 4983230072969 + 3 ^ 40 * 1560360 * 2
def baseEnd_1560360 : Nat := 801214674049620318024041

theorem tailTrace_1560360 : CollatzResearch.WordTrace tailWord_1560360 prefixEnd_1560360 801214674049620318024041 := by
  unfold tailWord_1560360
  simp only [CollatzResearch.WordTrace]
  refine ⟨28455502313544841558447267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37940669751393122077929689 28455502313544841558447267)
  ·
    refine ⟨42683253470317262337670901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28455502313544841558447267 42683253470317262337670901)
    ·
      refine ⟨4001555012842243344156647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42683253470317262337670901 4001555012842243344156647)
      ·
        refine ⟨6002332519263365016234971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4001555012842243344156647 6002332519263365016234971)
        ·
          refine ⟨9003498778895047524352457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6002332519263365016234971 9003498778895047524352457)
          ·
            refine ⟨6752624084171285643264343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9003498778895047524352457 6752624084171285643264343)
            ·
              refine ⟨10128936126256928464896515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6752624084171285643264343 10128936126256928464896515)
              ·
                refine ⟨15193404189385392697344773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10128936126256928464896515 15193404189385392697344773)
                ·
                  refine ⟨2848763285509761130752145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15193404189385392697344773 2848763285509761130752145)
                  ·
                    refine ⟨2136572464132320848064109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2848763285509761130752145 2136572464132320848064109)
                    ·
                      refine ⟨801214674049620318024041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2136572464132320848064109 801214674049620318024041)
                      ·
                        rfl

theorem cell23_1560360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_1560360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560360 prefixEnd_1560360 := by exact prefixLift 1560360
  have htrace : WordTrace (prefixWord ++ tailWord_1560360) baseStart_1560360 baseEnd_1560360 := by
    simpa [prefixWord, tailWord_1560360, baseEnd_1560360] using wordTrace_append hprefix tailTrace_1560360
  have hstable : (prefixWord ++ tailWord_1560360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560360).length < 2 ^ (prefixWord ++ tailWord_1560360).sum := by decide
  have hdescent : baseEnd_1560360 < baseStart_1560360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560380 : List Nat := [2, 2, 2, 2, 1, 1, 6, 1, 6]
def baseStart_1560380 : Nat := 118140960795 + 1560380 * 2 ^ 59
def prefixEnd_1560380 : Nat := 4983230072969 + 3 ^ 40 * 1560380 * 2
def baseEnd_1560380 : Nat := 89024993740301137752661

theorem tailTrace_1560380 : CollatzResearch.WordTrace tailWord_1560380 prefixEnd_1560380 89024993740301137752661 := by
  unfold tailWord_1560380
  simp only [CollatzResearch.WordTrace]
  refine ⟨28455867043508613266311297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37941156058011484355081729 28455867043508613266311297)
  ·
    refine ⟨21341900282631459949733473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28455867043508613266311297 21341900282631459949733473)
    ·
      refine ⟨16006425211973594962300105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21341900282631459949733473 16006425211973594962300105)
      ·
        refine ⟨12004818908980196221725079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16006425211973594962300105 12004818908980196221725079)
        ·
          refine ⟨18007228363470294332587619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12004818908980196221725079 18007228363470294332587619)
          ·
            refine ⟨27010842545205441498881429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18007228363470294332587619 27010842545205441498881429)
            ·
              refine ⟨1266133244306505070260067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27010842545205441498881429 1266133244306505070260067)
              ·
                refine ⟨1899199866459757605390101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1266133244306505070260067 1899199866459757605390101)
                ·
                  refine ⟨89024993740301137752661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1899199866459757605390101 89024993740301137752661)
                  ·
                    rfl

theorem cell23_1560380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 6].length) (baseStart_1560380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560380 prefixEnd_1560380 := by exact prefixLift 1560380
  have htrace : WordTrace (prefixWord ++ tailWord_1560380) baseStart_1560380 baseEnd_1560380 := by
    simpa [prefixWord, tailWord_1560380, baseEnd_1560380] using wordTrace_append hprefix tailTrace_1560380
  have hstable : (prefixWord ++ tailWord_1560380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560380).length < 2 ^ (prefixWord ++ tailWord_1560380).sum := by decide
  have hdescent : baseEnd_1560380 < baseStart_1560380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560393 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 3, 5]
def baseStart_1560393 : Nat := 118140960795 + 1560393 * 2 ^ 59
def prefixEnd_1560393 : Nat := 4983230072969 + 3 ^ 40 * 1560393 * 2
def baseEnd_1560393 : Nat := 267077206303739562970463

theorem tailTrace_1560393 : CollatzResearch.WordTrace tailWord_1560393 prefixEnd_1560393 267077206303739562970463 := by
  unfold tailWord_1560393
  simp only [CollatzResearch.WordTrace]
  refine ⟨56912208235970129752845833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37941472157313419835230555 56912208235970129752845833)
  ·
    refine ⟨42684156176977597314634375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56912208235970129752845833 42684156176977597314634375)
    ·
      refine ⟨64026234265466395971951563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42684156176977597314634375 64026234265466395971951563)
      ·
        refine ⟨96039351398199593957927345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64026234265466395971951563 96039351398199593957927345)
        ·
          refine ⟨72029513548649695468445509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96039351398199593957927345 72029513548649695468445509)
          ·
            refine ⟨13505533790371817900333533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72029513548649695468445509 13505533790371817900333533)
            ·
              refine ⟨5064575171389431712625075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13505533790371817900333533 5064575171389431712625075)
              ·
                refine ⟨7596862757084147568937613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5064575171389431712625075 7596862757084147568937613)
                ·
                  refine ⟨2848823533906555338351605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7596862757084147568937613 2848823533906555338351605)
                  ·
                    refine ⟨267077206303739562970463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2848823533906555338351605 267077206303739562970463)
                    ·
                      rfl

theorem cell23_1560393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 5].length) (baseStart_1560393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560393 prefixEnd_1560393 := by exact prefixLift 1560393
  have htrace : WordTrace (prefixWord ++ tailWord_1560393) baseStart_1560393 baseEnd_1560393 := by
    simpa [prefixWord, tailWord_1560393, baseEnd_1560393] using wordTrace_append hprefix tailTrace_1560393
  have hstable : (prefixWord ++ tailWord_1560393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560393).length < 2 ^ (prefixWord ++ tailWord_1560393).sum := by decide
  have hdescent : baseEnd_1560393 < baseStart_1560393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560423 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 3, 6]
def baseStart_1560423 : Nat := 118140960795 + 1560423 * 2 ^ 59
def prefixEnd_1560423 : Nat := 4983230072969 + 3 ^ 40 * 1560423 * 2
def baseEnd_1560423 : Nat := 267082341110284523845417

theorem tailTrace_1560423 : CollatzResearch.WordTrace tailWord_1560423 prefixEnd_1560423 267082341110284523845417 := by
  unfold tailWord_1560423
  simp only [CollatzResearch.WordTrace]
  refine ⟨56913302425861444876437923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37942201617240963250958615 56913302425861444876437923)
  ·
    refine ⟨85369953638792167314656885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56913302425861444876437923 85369953638792167314656885)
    ·
      refine ⟨8003433153636765685749083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85369953638792167314656885 8003433153636765685749083)
      ·
        refine ⟨12005149730455148528623625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8003433153636765685749083 12005149730455148528623625)
        ·
          refine ⟨9003862297841361396467719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12005149730455148528623625 9003862297841361396467719)
          ·
            refine ⟨13505793446762042094701579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9003862297841361396467719 13505793446762042094701579)
            ·
              refine ⟨20258690170143063142052369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13505793446762042094701579 20258690170143063142052369)
              ·
                refine ⟨15194017627607297356539277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20258690170143063142052369 15194017627607297356539277)
                ·
                  refine ⟨5697756610352736508702229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15194017627607297356539277 5697756610352736508702229)
                  ·
                    refine ⟨267082341110284523845417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5697756610352736508702229 267082341110284523845417)
                    ·
                      rfl

theorem cell23_1560423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_1560423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560423 prefixEnd_1560423 := by exact prefixLift 1560423
  have htrace : WordTrace (prefixWord ++ tailWord_1560423) baseStart_1560423 baseEnd_1560423 := by
    simpa [prefixWord, tailWord_1560423, baseEnd_1560423] using wordTrace_append hprefix tailTrace_1560423
  have hstable : (prefixWord ++ tailWord_1560423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560423).length < 2 ^ (prefixWord ++ tailWord_1560423).sum := by decide
  have hdescent : baseEnd_1560423 < baseStart_1560423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560424 : List Nat := [2, 1, 4, 2, 1, 1, 3, 4, 1, 1, 3]
def baseStart_1560424 : Nat := 118140960795 + 1560424 * 2 ^ 59
def prefixEnd_1560424 : Nat := 4983230072969 + 3 ^ 40 * 1560424 * 2
def baseEnd_1560424 : Nat := 801247536811508067623747

theorem tailTrace_1560424 : CollatzResearch.WordTrace tailWord_1560424 prefixEnd_1560424 801247536811508067623747 := by
  unfold tailWord_1560424
  simp only [CollatzResearch.WordTrace]
  refine ⟨28456669449428911023612163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37942225932571881364816217 28456669449428911023612163)
  ·
    refine ⟨42685004174143366535418245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28456669449428911023612163 42685004174143366535418245)
    ·
      refine ⟨8003438282651881225390921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42685004174143366535418245 8003438282651881225390921)
      ·
        refine ⟨6002578711988910919043191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8003438282651881225390921 6002578711988910919043191)
        ·
          refine ⟨9003868067983366378564787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6002578711988910919043191 9003868067983366378564787)
          ·
            refine ⟨13505802101975049567847181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9003868067983366378564787 13505802101975049567847181)
            ·
              refine ⟨5064675788240643587942693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13505802101975049567847181 5064675788240643587942693)
              ·
                refine ⟨949626710295120672739255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5064675788240643587942693 949626710295120672739255)
                ·
                  refine ⟨1424440065442681009108883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 949626710295120672739255 1424440065442681009108883)
                  ·
                    refine ⟨2136660098164021513663325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1424440065442681009108883 2136660098164021513663325)
                    ·
                      refine ⟨801247536811508067623747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2136660098164021513663325 801247536811508067623747)
                      ·
                        rfl

theorem cell23_1560424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_1560424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560424 prefixEnd_1560424 := by exact prefixLift 1560424
  have htrace : WordTrace (prefixWord ++ tailWord_1560424) baseStart_1560424 baseEnd_1560424 := by
    simpa [prefixWord, tailWord_1560424, baseEnd_1560424] using wordTrace_append hprefix tailTrace_1560424
  have hstable : (prefixWord ++ tailWord_1560424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560424).length < 2 ^ (prefixWord ++ tailWord_1560424).sum := by decide
  have hdescent : baseEnd_1560424 < baseStart_1560424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560433 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 3, 1, 5]
def baseStart_1560433 : Nat := 118140960795 + 1560433 * 2 ^ 59
def prefixEnd_1560433 : Nat := 4983230072969 + 3 ^ 40 * 1560433 * 2
def baseEnd_1560433 : Nat := 801252158137398532411205

theorem tailTrace_1560433 : CollatzResearch.WordTrace tailWord_1560433 prefixEnd_1560433 801252158137398532411205 := by
  unfold tailWord_1560433
  simp only [CollatzResearch.WordTrace]
  refine ⟨56913667155825216584301953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37942444770550144389534635 56913667155825216584301953)
  ·
    refine ⟨42685250366868912438226465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56913667155825216584301953 42685250366868912438226465)
    ·
      refine ⟨32013937775151684328669849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42685250366868912438226465 32013937775151684328669849)
      ·
        refine ⟨24010453331363763246502387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32013937775151684328669849 24010453331363763246502387)
        ·
          refine ⟨36015679997045644869753581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24010453331363763246502387 36015679997045644869753581)
          ·
            refine ⟨13505879998892116826157593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36015679997045644869753581 13505879998892116826157593)
            ·
              refine ⟨10129409999169087619618195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13505879998892116826157593 10129409999169087619618195)
              ·
                refine ⟨15194114998753631429427293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10129409999169087619618195 15194114998753631429427293)
                ·
                  refine ⟨5697793124532611786035235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15194114998753631429427293 5697793124532611786035235)
                  ·
                    refine ⟨8546689686798917679052853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5697793124532611786035235 8546689686798917679052853)
                    ·
                      refine ⟨801252158137398532411205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8546689686798917679052853 801252158137398532411205)
                      ·
                        rfl

theorem cell23_1560433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_1560433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560433 prefixEnd_1560433 := by exact prefixLift 1560433
  have htrace : WordTrace (prefixWord ++ tailWord_1560433) baseStart_1560433 baseEnd_1560433 := by
    simpa [prefixWord, tailWord_1560433, baseEnd_1560433] using wordTrace_append hprefix tailTrace_1560433
  have hstable : (prefixWord ++ tailWord_1560433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560433).length < 2 ^ (prefixWord ++ tailWord_1560433).sum := by decide
  have hdescent : baseEnd_1560433 < baseStart_1560433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560463 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 3]
def baseStart_1560463 : Nat := 118140960795 + 1560463 * 2 ^ 59
def prefixEnd_1560463 : Nat := 4983230072969 + 3 ^ 40 * 1560463 * 2
def baseEnd_1560463 : Nat := 801267562557033415036067

theorem tailTrace_1560463 : CollatzResearch.WordTrace tailWord_1560463 prefixEnd_1560463 801267562557033415036067 := by
  unfold tailWord_1560463
  simp only [CollatzResearch.WordTrace]
  refine ⟨56914761345716531707894043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37943174230477687805262695 56914761345716531707894043)
  ·
    refine ⟨85372142018574797561841065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56914761345716531707894043 85372142018574797561841065)
    ·
      refine ⟨64029106513931098171380799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85372142018574797561841065 64029106513931098171380799)
      ·
        refine ⟨96043659770896647257071199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64029106513931098171380799 96043659770896647257071199)
        ·
          refine ⟨144065489656344970885606799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96043659770896647257071199 144065489656344970885606799)
          ·
            refine ⟨216098234484517456328410199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144065489656344970885606799 216098234484517456328410199)
            ·
              refine ⟨324147351726776184492615299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216098234484517456328410199 324147351726776184492615299)
              ·
                refine ⟨486221027590164276738922949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324147351726776184492615299 486221027590164276738922949)
                ·
                  refine ⟨91166442673155801888548053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 486221027590164276738922949 91166442673155801888548053)
                  ·
                    refine ⟨2136713500152089106762845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 91166442673155801888548053 2136713500152089106762845)
                    ·
                      refine ⟨801267562557033415036067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2136713500152089106762845 801267562557033415036067)
                      ·
                        rfl

theorem cell23_1560463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 3].length) (baseStart_1560463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560463 prefixEnd_1560463 := by exact prefixLift 1560463
  have htrace : WordTrace (prefixWord ++ tailWord_1560463) baseStart_1560463 baseEnd_1560463 := by
    simpa [prefixWord, tailWord_1560463, baseEnd_1560463] using wordTrace_append hprefix tailTrace_1560463
  have hstable : (prefixWord ++ tailWord_1560463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560463).length < 2 ^ (prefixWord ++ tailWord_1560463).sum := by decide
  have hdescent : baseEnd_1560463 < baseStart_1560463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560464 : List Nat := [2, 1, 1, 1, 1, 1, 2, 9, 1, 2, 2]
def baseStart_1560464 : Nat := 118140960795 + 1560464 * 2 ^ 59
def prefixEnd_1560464 : Nat := 4983230072969 + 3 ^ 40 * 1560464 * 2
def baseEnd_1560464 : Nat := 801268076037687911123563

theorem tailTrace_1560464 : CollatzResearch.WordTrace tailWord_1560464 prefixEnd_1560464 801268076037687911123563 := by
  unfold tailWord_1560464
  simp only [CollatzResearch.WordTrace]
  refine ⟨28457398909356454439340223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37943198545808605919120297 28457398909356454439340223)
  ·
    refine ⟨42686098364034681659010335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28457398909356454439340223 42686098364034681659010335)
    ·
      refine ⟨64029147546052022488515503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42686098364034681659010335 64029147546052022488515503)
      ·
        refine ⟨96043721319078033732773255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64029147546052022488515503 96043721319078033732773255)
        ·
          refine ⟨144065581978617050599159883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96043721319078033732773255 144065581978617050599159883)
          ·
            refine ⟨216098372967925575898739825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144065581978617050599159883 216098372967925575898739825)
            ·
              refine ⟨162073779725944181924054869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216098372967925575898739825 162073779725944181924054869)
              ·
                refine ⟨949651053081704190961259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 162073779725944181924054869 949651053081704190961259)
                ·
                  refine ⟨1424476579622556286441889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 949651053081704190961259 1424476579622556286441889)
                  ·
                    refine ⟨1068357434716917214831417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1424476579622556286441889 1068357434716917214831417)
                    ·
                      refine ⟨801268076037687911123563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1068357434716917214831417 801268076037687911123563)
                      ·
                        rfl

theorem cell23_1560464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 1, 2, 2].length) (baseStart_1560464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560464 prefixEnd_1560464 := by exact prefixLift 1560464
  have htrace : WordTrace (prefixWord ++ tailWord_1560464) baseStart_1560464 baseEnd_1560464 := by
    simpa [prefixWord, tailWord_1560464, baseEnd_1560464] using wordTrace_append hprefix tailTrace_1560464
  have hstable : (prefixWord ++ tailWord_1560464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560464).length < 2 ^ (prefixWord ++ tailWord_1560464).sum := by decide
  have hdescent : baseEnd_1560464 < baseStart_1560464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560474 : List Nat := [3, 1, 1, 4, 2, 3, 1, 2, 2, 4]
def baseStart_1560474 : Nat := 118140960795 + 1560474 * 2 ^ 59
def prefixEnd_1560474 : Nat := 4983230072969 + 3 ^ 40 * 1560474 * 2
def baseEnd_1560474 : Nat := 267091070281410957332839

theorem tailTrace_1560474 : CollatzResearch.WordTrace tailWord_1560474 prefixEnd_1560474 267091070281410957332839 := by
  unfold tailWord_1560474
  simp only [CollatzResearch.WordTrace]
  refine ⟨14228790637169170146636119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37943441699117787057696317 14228790637169170146636119)
  ·
    refine ⟨21343185955753755219954179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14228790637169170146636119 21343185955753755219954179)
    ·
      refine ⟨32014778933630632829931269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21343185955753755219954179 32014778933630632829931269)
      ·
        refine ⟨6002771050055743655612113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32014778933630632829931269 6002771050055743655612113)
        ·
          refine ⟨4502078287541807741709085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6002771050055743655612113 4502078287541807741709085)
          ·
            refine ⟨1688279357828177903140907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4502078287541807741709085 1688279357828177903140907)
            ·
              refine ⟨2532419036742266854711361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1688279357828177903140907 2532419036742266854711361)
              ·
                refine ⟨1899314277556700141033521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2532419036742266854711361 1899314277556700141033521)
                ·
                  refine ⟨1424485708167525105775141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1899314277556700141033521 1424485708167525105775141)
                  ·
                    refine ⟨267091070281410957332839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1424485708167525105775141 267091070281410957332839)
                    ·
                      rfl

theorem cell23_1560474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 2, 4].length) (baseStart_1560474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560474 prefixEnd_1560474 := by exact prefixLift 1560474
  have htrace : WordTrace (prefixWord ++ tailWord_1560474) baseStart_1560474 baseEnd_1560474 := by
    simpa [prefixWord, tailWord_1560474, baseEnd_1560474] using wordTrace_append hprefix tailTrace_1560474
  have hstable : (prefixWord ++ tailWord_1560474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560474).length < 2 ^ (prefixWord ++ tailWord_1560474).sum := by decide
  have hdescent : baseEnd_1560474 < baseStart_1560474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560481 : List Nat := [1, 2, 3, 4, 2, 1, 2, 1, 3, 2, 2]
def baseStart_1560481 : Nat := 118140960795 + 1560481 * 2 ^ 59
def prefixEnd_1560481 : Nat := 4983230072969 + 3 ^ 40 * 1560481 * 2
def baseEnd_1560481 : Nat := 801276805208814344610985

theorem tailTrace_1560481 : CollatzResearch.WordTrace tailWord_1560481 prefixEnd_1560481 801276805208814344610985 := by
  unfold tailWord_1560481
  simp only [CollatzResearch.WordTrace]
  refine ⟨56915417859651320782049297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37943611906434213854699531 56915417859651320782049297)
  ·
    refine ⟨42686563394738490586536973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56915417859651320782049297 42686563394738490586536973)
    ·
      refine ⟨16007461273026933969951365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42686563394738490586536973 16007461273026933969951365)
      ·
        refine ⟨3001398988692550119365881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16007461273026933969951365 3001398988692550119365881)
        ·
          refine ⟨2251049241519412589524411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3001398988692550119365881 2251049241519412589524411)
          ·
            refine ⟨3376573862279118884286617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2251049241519412589524411 3376573862279118884286617)
            ·
              refine ⟨2532430396709339163214963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3376573862279118884286617 2532430396709339163214963)
              ·
                refine ⟨3798645595064008744822445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2532430396709339163214963 3798645595064008744822445)
                ·
                  refine ⟨1424492098149003279308417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3798645595064008744822445 1424492098149003279308417)
                  ·
                    refine ⟨1068369073611752459481313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1424492098149003279308417 1068369073611752459481313)
                    ·
                      refine ⟨801276805208814344610985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1068369073611752459481313 801276805208814344610985)
                      ·
                        rfl

theorem cell23_1560481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_1560481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560481 prefixEnd_1560481 := by exact prefixLift 1560481
  have htrace : WordTrace (prefixWord ++ tailWord_1560481) baseStart_1560481 baseEnd_1560481 := by
    simpa [prefixWord, tailWord_1560481, baseEnd_1560481] using wordTrace_append hprefix tailTrace_1560481
  have hstable : (prefixWord ++ tailWord_1560481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560481).length < 2 ^ (prefixWord ++ tailWord_1560481).sum := by decide
  have hdescent : baseEnd_1560481 < baseStart_1560481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560497 : List Nat := [1, 2, 2, 4, 2, 1, 3, 1, 1, 3, 3]
def baseStart_1560497 : Nat := 118140960795 + 1560497 * 2 ^ 59
def prefixEnd_1560497 : Nat := 4983230072969 + 3 ^ 40 * 1560497 * 2
def baseEnd_1560497 : Nat := 801285020899286282010911

theorem tailTrace_1560497 : CollatzResearch.WordTrace tailWord_1560497 prefixEnd_1560497 801285020899286282010911 := by
  unfold tailWord_1560497
  simp only [CollatzResearch.WordTrace]
  refine ⟨56916001427593355514631745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37944000951728903676421163 56916001427593355514631745)
  ·
    refine ⟨42687001070695016635973809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56916001427593355514631745 42687001070695016635973809)
    ·
      refine ⟨32015250803021262476980357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42687001070695016635973809 32015250803021262476980357)
      ·
        refine ⟨6002859525566486714433817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32015250803021262476980357 6002859525566486714433817)
        ·
          refine ⟨4502144644174865035825363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6002859525566486714433817 4502144644174865035825363)
          ·
            refine ⟨6753216966262297553738045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4502144644174865035825363 6753216966262297553738045)
            ·
              refine ⟨2532456362348361582651767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6753216966262297553738045 2532456362348361582651767)
              ·
                refine ⟨3798684543522542373977651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2532456362348361582651767 3798684543522542373977651)
                ·
                  refine ⟨5698026815283813560966477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3798684543522542373977651 5698026815283813560966477)
                  ·
                    refine ⟨2136760055731430085362429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5698026815283813560966477 2136760055731430085362429)
                    ·
                      refine ⟨801285020899286282010911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2136760055731430085362429 801285020899286282010911)
                      ·
                        rfl

theorem cell23_1560497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_1560497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560497 prefixEnd_1560497 := by exact prefixLift 1560497
  have htrace : WordTrace (prefixWord ++ tailWord_1560497) baseStart_1560497 baseEnd_1560497 := by
    simpa [prefixWord, tailWord_1560497, baseEnd_1560497] using wordTrace_append hprefix tailTrace_1560497
  have hstable : (prefixWord ++ tailWord_1560497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560497).length < 2 ^ (prefixWord ++ tailWord_1560497).sum := by decide
  have hdescent : baseEnd_1560497 < baseStart_1560497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560507 : List Nat := [1, 1, 1, 1, 1, 2, 2, 8, 1, 3, 2]
def baseStart_1560507 : Nat := 118140960795 + 1560507 * 2 ^ 59
def prefixEnd_1560507 : Nat := 4983230072969 + 3 ^ 40 * 1560507 * 2
def baseEnd_1560507 : Nat := 801290155705831242885865

theorem tailTrace_1560507 : CollatzResearch.WordTrace tailWord_1560507 prefixEnd_1560507 801290155705831242885865 := by
  unfold tailWord_1560507
  simp only [CollatzResearch.WordTrace]
  refine ⟨56916366157557127222495775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37944244105038084814997183 56916366157557127222495775)
  ·
    refine ⟨85374549236335690833743663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56916366157557127222495775 85374549236335690833743663)
    ·
      refine ⟨128061823854503536250615495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85374549236335690833743663 128061823854503536250615495)
      ·
        refine ⟨192092735781755304375923243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128061823854503536250615495 192092735781755304375923243)
        ·
          refine ⟨288139103672632956563884865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192092735781755304375923243 288139103672632956563884865)
          ·
            refine ⟨216104327754474717422913649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288139103672632956563884865 216104327754474717422913649)
            ·
              refine ⟨162078245815856038067185237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216104327754474717422913649 162078245815856038067185237)
              ·
                refine ⟨1899354443154562946099827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 162078245815856038067185237 1899354443154562946099827)
                ·
                  refine ⟨2849031664731844419149741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1899354443154562946099827 2849031664731844419149741)
                  ·
                    refine ⟨1068386874274441657181153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2849031664731844419149741 1068386874274441657181153)
                    ·
                      refine ⟨801290155705831242885865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1068386874274441657181153 801290155705831242885865)
                      ·
                        rfl

theorem cell23_1560507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 3, 2].length) (baseStart_1560507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560507 prefixEnd_1560507 := by exact prefixLift 1560507
  have htrace : WordTrace (prefixWord ++ tailWord_1560507) baseStart_1560507 baseEnd_1560507 := by
    simpa [prefixWord, tailWord_1560507, baseEnd_1560507] using wordTrace_append hprefix tailTrace_1560507
  have hstable : (prefixWord ++ tailWord_1560507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560507).length < 2 ^ (prefixWord ++ tailWord_1560507).sum := by decide
  have hdescent : baseEnd_1560507 < baseStart_1560507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560510 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_1560510 : Nat := 118140960795 + 1560510 * 2 ^ 59
def prefixEnd_1560510 : Nat := 4983230072969 + 3 ^ 40 * 1560510 * 2
def baseEnd_1560510 : Nat := 801291696147794731148351

theorem tailTrace_1560510 : CollatzResearch.WordTrace tailWord_1560510 prefixEnd_1560510 801291696147794731148351 := by
  unfold tailWord_1560510
  simp only [CollatzResearch.WordTrace]
  refine ⟨7114559447068282341856873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37944317051030839156569989 7114559447068282341856873)
  ·
    refine ⟨5335919585301211756392655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7114559447068282341856873 5335919585301211756392655)
    ·
      refine ⟨8003879377951817634588983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5335919585301211756392655 8003879377951817634588983)
      ·
        refine ⟨12005819066927726451883475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8003879377951817634588983 12005819066927726451883475)
        ·
          refine ⟨18008728600391589677825213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12005819066927726451883475 18008728600391589677825213)
          ·
            refine ⟨6753273225146846129184455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18008728600391589677825213 6753273225146846129184455)
            ·
              refine ⟨10129909837720269193776683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6753273225146846129184455 10129909837720269193776683)
              ·
                refine ⟨15194864756580403790665025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10129909837720269193776683 15194864756580403790665025)
                ·
                  refine ⟨11396148567435302842998769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15194864756580403790665025 11396148567435302842998769)
                  ·
                    refine ⟨8547111425576477132249077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11396148567435302842998769 8547111425576477132249077)
                    ·
                      refine ⟨801291696147794731148351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8547111425576477132249077 801291696147794731148351)
                      ·
                        rfl

theorem cell23_1560510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_1560510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560510 prefixEnd_1560510 := by exact prefixLift 1560510
  have htrace : WordTrace (prefixWord ++ tailWord_1560510) baseStart_1560510 baseEnd_1560510 := by
    simpa [prefixWord, tailWord_1560510, baseEnd_1560510] using wordTrace_append hprefix tailTrace_1560510
  have hstable : (prefixWord ++ tailWord_1560510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560510).length < 2 ^ (prefixWord ++ tailWord_1560510).sum := by decide
  have hdescent : baseEnd_1560510 < baseStart_1560510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560524 : List Nat := [2, 2, 1, 4, 1, 2, 2, 3, 1, 3, 2]
def baseStart_1560524 : Nat := 118140960795 + 1560524 * 2 ^ 59
def prefixEnd_1560524 : Nat := 4983230072969 + 3 ^ 40 * 1560524 * 2
def baseEnd_1560524 : Nat := 801298884876957676373287

theorem tailTrace_1560524 : CollatzResearch.WordTrace tailWord_1560524 prefixEnd_1560524 801298884876957676373287 := by
  unfold tailWord_1560524
  simp only [CollatzResearch.WordTrace]
  refine ⟨28458493099247769562932313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37944657465663692750576417 28458493099247769562932313)
  ·
    refine ⟨21343869824435827172199235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28458493099247769562932313 21343869824435827172199235)
    ·
      refine ⟨32015804736653740758298853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21343869824435827172199235 32015804736653740758298853)
      ·
        refine ⟨6002963388122576392181035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32015804736653740758298853 6002963388122576392181035)
        ·
          refine ⟨9004445082183864588271553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6002963388122576392181035 9004445082183864588271553)
          ·
            refine ⟨6753333811637898441203665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9004445082183864588271553 6753333811637898441203665)
            ·
              refine ⟨5065000358728423830902749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6753333811637898441203665 5065000358728423830902749)
              ·
                refine ⟨1899375134523158936588531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5065000358728423830902749 1899375134523158936588531)
                ·
                  refine ⟨2849062701784738404882797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1899375134523158936588531 2849062701784738404882797)
                  ·
                    refine ⟨1068398513169276901831049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2849062701784738404882797 1068398513169276901831049)
                    ·
                      refine ⟨801298884876957676373287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1068398513169276901831049 801298884876957676373287)
                      ·
                        rfl

theorem cell23_1560524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_1560524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560524 prefixEnd_1560524 := by exact prefixLift 1560524
  have htrace : WordTrace (prefixWord ++ tailWord_1560524) baseStart_1560524 baseEnd_1560524 := by
    simpa [prefixWord, tailWord_1560524, baseEnd_1560524] using wordTrace_append hprefix tailTrace_1560524
  have hstable : (prefixWord ++ tailWord_1560524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560524).length < 2 ^ (prefixWord ++ tailWord_1560524).sum := by decide
  have hdescent : baseEnd_1560524 < baseStart_1560524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560563 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 8]
def baseStart_1560563 : Nat := 118140960795 + 1560563 * 2 ^ 59
def prefixEnd_1560563 : Nat := 4983230072969 + 3 ^ 40 * 1560563 * 2
def baseEnd_1560563 : Nat := 801318910622483023785607

theorem tailTrace_1560563 : CollatzResearch.WordTrace tailWord_1560563 prefixEnd_1560563 801318910622483023785607 := by
  unfold tailWord_1560563
  simp only [CollatzResearch.WordTrace]
  refine ⟨56918408645354248786534343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37945605763569499191022895 56918408645354248786534343)
  ·
    refine ⟨85377612968031373179801515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56918408645354248786534343 85377612968031373179801515)
    ·
      refine ⟨128066419452047059769702273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85377612968031373179801515 128066419452047059769702273)
      ·
        refine ⟨96049814589035294827276705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128066419452047059769702273 96049814589035294827276705)
        ·
          refine ⟨72037360941776471120457529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96049814589035294827276705 72037360941776471120457529)
          ·
            refine ⟨54028020706332353340343147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72037360941776471120457529 54028020706332353340343147)
            ·
              refine ⟨81042031059498530010514721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54028020706332353340343147 81042031059498530010514721)
              ·
                refine ⟨60781523294623897507886041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81042031059498530010514721 60781523294623897507886041)
                ·
                  refine ⟨45586142470967923130914531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60781523294623897507886041 45586142470967923130914531)
                  ·
                    refine ⟨68379213706451884696371797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45586142470967923130914531 68379213706451884696371797)
                    ·
                      refine ⟨801318910622483023785607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 68379213706451884696371797 801318910622483023785607)
                      ·
                        rfl

theorem cell23_1560563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_1560563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560563 prefixEnd_1560563 := by exact prefixLift 1560563
  have htrace : WordTrace (prefixWord ++ tailWord_1560563) baseStart_1560563 baseEnd_1560563 := by
    simpa [prefixWord, tailWord_1560563, baseEnd_1560563] using wordTrace_append hprefix tailTrace_1560563
  have hstable : (prefixWord ++ tailWord_1560563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560563).length < 2 ^ (prefixWord ++ tailWord_1560563).sum := by decide
  have hdescent : baseEnd_1560563 < baseStart_1560563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560570 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3]
def baseStart_1560570 : Nat := 118140960795 + 1560570 * 2 ^ 59
def prefixEnd_1560570 : Nat := 4983230072969 + 3 ^ 40 * 1560570 * 2
def baseEnd_1560570 : Nat := 801322504987064496398075

theorem tailTrace_1560570 : CollatzResearch.WordTrace tailWord_1560570 prefixEnd_1560570 801322504987064496398075 := by
  unfold tailWord_1560570
  simp only [CollatzResearch.WordTrace]
  refine ⟨14229665989082222245509791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37945775970885925988026109 14229665989082222245509791)
  ·
    refine ⟨21344498983623333368264687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14229665989082222245509791 21344498983623333368264687)
    ·
      refine ⟨32016748475435000052397031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21344498983623333368264687 32016748475435000052397031)
      ·
        refine ⟨48025122713152500078595547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32016748475435000052397031 48025122713152500078595547)
        ·
          refine ⟨72037684069728750117893321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48025122713152500078595547 72037684069728750117893321)
          ·
            refine ⟨54028263052296562588419991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72037684069728750117893321 54028263052296562588419991)
            ·
              refine ⟨81042394578444843882629987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54028263052296562588419991 81042394578444843882629987)
              ·
                refine ⟨121563591867667265823944981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81042394578444843882629987 121563591867667265823944981)
                ·
                  refine ⟨5698293368796903085497421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121563591867667265823944981 5698293368796903085497421)
                  ·
                    refine ⟨2136860013298838657061533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5698293368796903085497421 2136860013298838657061533)
                    ·
                      refine ⟨801322504987064496398075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2136860013298838657061533 801322504987064496398075)
                      ·
                        rfl

theorem cell23_1560570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3].length) (baseStart_1560570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560570 prefixEnd_1560570 := by exact prefixLift 1560570
  have htrace : WordTrace (prefixWord ++ tailWord_1560570) baseStart_1560570 baseEnd_1560570 := by
    simpa [prefixWord, tailWord_1560570, baseEnd_1560570] using wordTrace_append hprefix tailTrace_1560570
  have hstable : (prefixWord ++ tailWord_1560570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560570).length < 2 ^ (prefixWord ++ tailWord_1560570).sum := by decide
  have hdescent : baseEnd_1560570 < baseStart_1560570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560577 : List Nat := [1, 2, 4, 1, 2, 1, 2, 5, 5]
def baseStart_1560577 : Nat := 118140960795 + 1560577 * 2 ^ 59
def prefixEnd_1560577 : Nat := 4983230072969 + 3 ^ 40 * 1560577 * 2
def baseEnd_1560577 : Nat := 89036233261293996556727

theorem tailTrace_1560577 : CollatzResearch.WordTrace tailWord_1560577 prefixEnd_1560577 89036233261293996556727 := by
  unfold tailWord_1560577
  simp only [CollatzResearch.WordTrace]
  refine ⟨56918919267303529177543985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37945946178202352785029323 56918919267303529177543985)
  ·
    refine ⟨42689189450477646883157989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56918919267303529177543985 42689189450477646883157989)
    ·
      refine ⟨8004223021964558790592123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42689189450477646883157989 8004223021964558790592123)
      ·
        refine ⟨12006334532946838185888185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8004223021964558790592123 12006334532946838185888185)
        ·
          refine ⟨9004750899710128639416139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12006334532946838185888185 9004750899710128639416139)
          ·
            refine ⟨13507126349565192959124209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9004750899710128639416139 13507126349565192959124209)
            ·
              refine ⟨10130344762173894719343157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13507126349565192959124209 10130344762173894719343157)
              ·
                refine ⟨949719821453802629938421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10130344762173894719343157 949719821453802629938421)
                ·
                  refine ⟨89036233261293996556727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 949719821453802629938421 89036233261293996556727)
                  ·
                    rfl

theorem cell23_1560577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 5].length) (baseStart_1560577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560577 prefixEnd_1560577 := by exact prefixLift 1560577
  have htrace : WordTrace (prefixWord ++ tailWord_1560577) baseStart_1560577 baseEnd_1560577 := by
    simpa [prefixWord, tailWord_1560577, baseEnd_1560577] using wordTrace_append hprefix tailTrace_1560577
  have hstable : (prefixWord ++ tailWord_1560577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560577).length < 2 ^ (prefixWord ++ tailWord_1560577).sum := by decide
  have hdescent : baseEnd_1560577 < baseStart_1560577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560582 : List Nat := [6, 2, 1, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_1560582 : Nat := 118140960795 + 1560582 * 2 ^ 59
def prefixEnd_1560582 : Nat := 4983230072969 + 3 ^ 40 * 1560582 * 2
def baseEnd_1560582 : Nat := 801328666754918449448021

theorem tailTrace_1560582 : CollatzResearch.WordTrace tailWord_1560582 prefixEnd_1560582 801328666754918449448021 := by
  unfold tailWord_1560582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1778721926008919219733625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37946067754856943354317333 1778721926008919219733625)
  ·
    refine ⟨1334041444506689414800219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1778721926008919219733625 1334041444506689414800219)
    ·
      refine ⟨2001062166760034122200329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1334041444506689414800219 2001062166760034122200329)
      ·
        refine ⟨1500796625070025591650247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2001062166760034122200329 1500796625070025591650247)
        ·
          refine ⟨2251194937605038387475371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1500796625070025591650247 2251194937605038387475371)
          ·
            refine ⟨3376792406407557581213057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2251194937605038387475371 3376792406407557581213057)
            ·
              refine ⟨2532594304805668185909793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3376792406407557581213057 2532594304805668185909793)
              ·
                refine ⟨1899445728604251139432345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2532594304805668185909793 1899445728604251139432345)
                ·
                  refine ⟨1424584296453188354574259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1899445728604251139432345 1424584296453188354574259)
                  ·
                    refine ⟨2136876444679782531861389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1424584296453188354574259 2136876444679782531861389)
                    ·
                      refine ⟨801328666754918449448021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2136876444679782531861389 801328666754918449448021)
                      ·
                        rfl

theorem cell23_1560582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_1560582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560582 prefixEnd_1560582 := by exact prefixLift 1560582
  have htrace : WordTrace (prefixWord ++ tailWord_1560582) baseStart_1560582 baseEnd_1560582 := by
    simpa [prefixWord, tailWord_1560582, baseEnd_1560582] using wordTrace_append hprefix tailTrace_1560582
  have hstable : (prefixWord ++ tailWord_1560582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560582).length < 2 ^ (prefixWord ++ tailWord_1560582).sum := by decide
  have hdescent : baseEnd_1560582 < baseStart_1560582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560600 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 1, 2, 5]
def baseStart_1560600 : Nat := 118140960795 + 1560600 * 2 ^ 59
def prefixEnd_1560600 : Nat := 4983230072969 + 3 ^ 40 * 1560600 * 2
def baseEnd_1560600 : Nat := 801337909406699379022937

theorem tailTrace_1560600 : CollatzResearch.WordTrace tailWord_1560600 prefixEnd_1560600 801337909406699379022937 := by
  unfold tailWord_1560600
  simp only [CollatzResearch.WordTrace]
  refine ⟨28459879073110102052815627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37946505430813469403754169 28459879073110102052815627)
  ·
    refine ⟨42689818609665153079223441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28459879073110102052815627 42689818609665153079223441)
    ·
      refine ⟨32017363957248864809417581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42689818609665153079223441 32017363957248864809417581)
      ·
        refine ⟨12006511483968324303531593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32017363957248864809417581 12006511483968324303531593)
        ·
          refine ⟨9004883612976243227648695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12006511483968324303531593 9004883612976243227648695)
          ·
            refine ⟨13507325419464364841473043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9004883612976243227648695 13507325419464364841473043)
            ·
              refine ⟨20260988129196547262209565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13507325419464364841473043 20260988129196547262209565)
              ·
                refine ⟨7597870548448705223328587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20260988129196547262209565 7597870548448705223328587)
                ·
                  refine ⟨11396805822673057834992881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7597870548448705223328587 11396805822673057834992881)
                  ·
                    refine ⟨8547604367004793376244661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11396805822673057834992881 8547604367004793376244661)
                    ·
                      refine ⟨801337909406699379022937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8547604367004793376244661 801337909406699379022937)
                      ·
                        rfl

theorem cell23_1560600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_1560600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560600 prefixEnd_1560600 := by exact prefixLift 1560600
  have htrace : WordTrace (prefixWord ++ tailWord_1560600) baseStart_1560600 baseEnd_1560600 := by
    simpa [prefixWord, tailWord_1560600, baseEnd_1560600] using wordTrace_append hprefix tailTrace_1560600
  have hstable : (prefixWord ++ tailWord_1560600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560600).length < 2 ^ (prefixWord ++ tailWord_1560600).sum := by decide
  have hdescent : baseEnd_1560600 < baseStart_1560600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560627 : List Nat := [1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 4]
def baseStart_1560627 : Nat := 118140960795 + 1560627 * 2 ^ 59
def prefixEnd_1560627 : Nat := 4983230072969 + 3 ^ 40 * 1560627 * 2
def baseEnd_1560627 : Nat := 801351773384370773385313

theorem tailTrace_1560627 : CollatzResearch.WordTrace tailWord_1560627 prefixEnd_1560627 801351773384370773385313 := by
  unfold tailWord_1560627
  simp only [CollatzResearch.WordTrace]
  refine ⟨56920742917122387716864135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37947161944748258477909423 56920742917122387716864135)
  ·
    refine ⟨85381114375683581575296203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56920742917122387716864135 85381114375683581575296203)
    ·
      refine ⟨128071671563525372362944305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85381114375683581575296203 128071671563525372362944305)
      ·
        refine ⟨96053753672644029272208229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128071671563525372362944305 96053753672644029272208229)
        ·
          refine ⟨18010078813620755488539043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96053753672644029272208229 18010078813620755488539043)
          ·
            refine ⟨27015118220431133232808565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18010078813620755488539043 27015118220431133232808565)
            ·
              refine ⟨2532667333165418740575803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27015118220431133232808565 2532667333165418740575803)
              ·
                refine ⟨3799000999748128110863705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2532667333165418740575803 3799000999748128110863705)
                ·
                  refine ⟨2849250749811096083147779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3799000999748128110863705 2849250749811096083147779)
                  ·
                    refine ⟨4273876124716644124721669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2849250749811096083147779 4273876124716644124721669)
                    ·
                      refine ⟨801351773384370773385313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4273876124716644124721669 801351773384370773385313)
                      ·
                        rfl

theorem cell23_1560627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 4].length) (baseStart_1560627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560627 prefixEnd_1560627 := by exact prefixLift 1560627
  have htrace : WordTrace (prefixWord ++ tailWord_1560627) baseStart_1560627 baseEnd_1560627 := by
    simpa [prefixWord, tailWord_1560627, baseEnd_1560627] using wordTrace_append hprefix tailTrace_1560627
  have hstable : (prefixWord ++ tailWord_1560627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560627).length < 2 ^ (prefixWord ++ tailWord_1560627).sum := by decide
  have hdescent : baseEnd_1560627 < baseStart_1560627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560637 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 5, 4]
def baseStart_1560637 : Nat := 118140960795 + 1560637 * 2 ^ 59
def prefixEnd_1560637 : Nat := 4983230072969 + 3 ^ 40 * 1560637 * 2
def baseEnd_1560637 : Nat := 267118969396971911420089

theorem tailTrace_1560637 : CollatzResearch.WordTrace tailWord_1560637 prefixEnd_1560637 267118969396971911420089 := by
  unfold tailWord_1560637
  simp only [CollatzResearch.WordTrace]
  refine ⟨56921107647086159424728165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37947405098057439616485443 56921107647086159424728165)
  ·
    refine ⟨10672707683828654892136531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56921107647086159424728165 10672707683828654892136531)
    ·
      refine ⟨16009061525742982338204797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10672707683828654892136531 16009061525742982338204797)
      ·
        refine ⟨6003398072153618376826799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16009061525742982338204797 6003398072153618376826799)
        ·
          refine ⟨9005097108230427565240199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6003398072153618376826799 9005097108230427565240199)
          ·
            refine ⟨13507645662345641347860299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9005097108230427565240199 13507645662345641347860299)
            ·
              refine ⟨20261468493518462021790449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13507645662345641347860299 20261468493518462021790449)
              ·
                refine ⟨15196101370138846516342837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20261468493518462021790449 15196101370138846516342837)
                ·
                  refine ⟨1424634503450516860907141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15196101370138846516342837 1424634503450516860907141)
                  ·
                    refine ⟨267118969396971911420089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1424634503450516860907141 267118969396971911420089)
                    ·
                      rfl

theorem cell23_1560637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_1560637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560637 prefixEnd_1560637 := by exact prefixLift 1560637
  have htrace : WordTrace (prefixWord ++ tailWord_1560637) baseStart_1560637 baseEnd_1560637 := by
    simpa [prefixWord, tailWord_1560637, baseEnd_1560637] using wordTrace_append hprefix tailTrace_1560637
  have hstable : (prefixWord ++ tailWord_1560637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560637).length < 2 ^ (prefixWord ++ tailWord_1560637).sum := by decide
  have hdescent : baseEnd_1560637 < baseStart_1560637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560640 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 6]
def baseStart_1560640 : Nat := 118140960795 + 1560640 * 2 ^ 59
def prefixEnd_1560640 : Nat := 4983230072969 + 3 ^ 40 * 1560640 * 2
def baseEnd_1560640 : Nat := 801358448632879222522753

theorem tailTrace_1560640 : CollatzResearch.WordTrace tailWord_1560640 prefixEnd_1560640 801358448632879222522753 := by
  unfold tailWord_1560640
  simp only [CollatzResearch.WordTrace]
  refine ⟨28460608533037645468543687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37947478044050193958058249 28460608533037645468543687)
  ·
    refine ⟨42690912799556468202815531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28460608533037645468543687 42690912799556468202815531)
    ·
      refine ⟨64036369199334702304223297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42690912799556468202815531 64036369199334702304223297)
      ·
        refine ⟨48027276899501026728167473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64036369199334702304223297 48027276899501026728167473)
        ·
          refine ⟨36020457674625770046125605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48027276899501026728167473 36020457674625770046125605)
          ·
            refine ⟨6753835813992331883648551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36020457674625770046125605 6753835813992331883648551)
            ·
              refine ⟨10130753720988497825472827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6753835813992331883648551 10130753720988497825472827)
              ·
                refine ⟨15196130581482746738209241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10130753720988497825472827 15196130581482746738209241)
                ·
                  refine ⟨11397097936112060053656931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15196130581482746738209241 11397097936112060053656931)
                  ·
                    refine ⟨17095646904168090080485397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11397097936112060053656931 17095646904168090080485397)
                    ·
                      refine ⟨801358448632879222522753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17095646904168090080485397 801358448632879222522753)
                      ·
                        rfl

theorem cell23_1560640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_1560640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560640 prefixEnd_1560640 := by exact prefixLift 1560640
  have htrace : WordTrace (prefixWord ++ tailWord_1560640) baseStart_1560640 baseEnd_1560640 := by
    simpa [prefixWord, tailWord_1560640, baseEnd_1560640] using wordTrace_append hprefix tailTrace_1560640
  have hstable : (prefixWord ++ tailWord_1560640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560640).length < 2 ^ (prefixWord ++ tailWord_1560640).sum := by decide
  have hdescent : baseEnd_1560640 < baseStart_1560640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560647 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 3]
def baseStart_1560647 : Nat := 118140960795 + 1560647 * 2 ^ 59
def prefixEnd_1560647 : Nat := 4983230072969 + 3 ^ 40 * 1560647 * 2
def baseEnd_1560647 : Nat := 801362042997460695135221

theorem tailTrace_1560647 : CollatzResearch.WordTrace tailWord_1560647 prefixEnd_1560647 801362042997460695135221 := by
  unfold tailWord_1560647
  simp only [CollatzResearch.WordTrace]
  refine ⟨56921472377049931132592195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37947648251366620755061463 56921472377049931132592195)
  ·
    refine ⟨85382208565574896698888293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56921472377049931132592195 85382208565574896698888293)
    ·
      refine ⟨16009164106045293131041555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85382208565574896698888293 16009164106045293131041555)
      ·
        refine ⟨24013746159067939696562333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16009164106045293131041555 24013746159067939696562333)
        ·
          refine ⟨9005154809650477386210875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24013746159067939696562333 9005154809650477386210875)
          ·
            refine ⟨13507732214475716079316313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9005154809650477386210875 13507732214475716079316313)
            ·
              refine ⟨10130799160856787059487235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13507732214475716079316313 10130799160856787059487235)
              ·
                refine ⟨15196198741285180589230853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10130799160856787059487235 15196198741285180589230853)
                ·
                  refine ⟨2849287263990971360480785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15196198741285180589230853 2849287263990971360480785)
                  ·
                    refine ⟨2136965447993228520360589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2849287263990971360480785 2136965447993228520360589)
                    ·
                      refine ⟨801362042997460695135221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2136965447993228520360589 801362042997460695135221)
                      ·
                        rfl

theorem cell23_1560647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_1560647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560647 prefixEnd_1560647 := by exact prefixLift 1560647
  have htrace : WordTrace (prefixWord ++ tailWord_1560647) baseStart_1560647 baseEnd_1560647 := by
    simpa [prefixWord, tailWord_1560647, baseEnd_1560647] using wordTrace_append hprefix tailTrace_1560647
  have hstable : (prefixWord ++ tailWord_1560647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560647).length < 2 ^ (prefixWord ++ tailWord_1560647).sum := by decide
  have hdescent : baseEnd_1560647 < baseStart_1560647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560654 : List Nat := [4, 1, 1, 1, 1, 5, 2, 1, 3, 4]
def baseStart_1560654 : Nat := 118140960795 + 1560654 * 2 ^ 59
def prefixEnd_1560654 : Nat := 4983230072969 + 3 ^ 40 * 1560654 * 2
def baseEnd_1560654 : Nat := 267121879120680722582563

theorem tailTrace_1560654 : CollatzResearch.WordTrace tailWord_1560654 prefixEnd_1560654 267121879120680722582563 := by
  unfold tailWord_1560654
  simp only [CollatzResearch.WordTrace]
  refine ⟨7115215961003071416012127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37947818458683047552064677 7115215961003071416012127)
  ·
    refine ⟨10672823941504607124018191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7115215961003071416012127 10672823941504607124018191)
    ·
      refine ⟨16009235912256910686027287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10672823941504607124018191 16009235912256910686027287)
      ·
        refine ⟨24013853868385366029040931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16009235912256910686027287 24013853868385366029040931)
        ·
          refine ⟨36020780802578049043561397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24013853868385366029040931 36020780802578049043561397)
          ·
            refine ⟨3376948200241692097833881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36020780802578049043561397 3376948200241692097833881)
            ·
              refine ⟨2532711150181269073375411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3376948200241692097833881 2532711150181269073375411)
              ·
                refine ⟨3799066725271903610063117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2532711150181269073375411 3799066725271903610063117)
                ·
                  refine ⟨1424650021976963853773669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3799066725271903610063117 1424650021976963853773669)
                  ·
                    refine ⟨267121879120680722582563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1424650021976963853773669 267121879120680722582563)
                    ·
                      rfl

theorem cell23_1560654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_1560654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560654 prefixEnd_1560654 := by exact prefixLift 1560654
  have htrace : WordTrace (prefixWord ++ tailWord_1560654) baseStart_1560654 baseEnd_1560654 := by
    simpa [prefixWord, tailWord_1560654, baseEnd_1560654] using wordTrace_append hprefix tailTrace_1560654
  have hstable : (prefixWord ++ tailWord_1560654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560654).length < 2 ^ (prefixWord ++ tailWord_1560654).sum := by decide
  have hdescent : baseEnd_1560654 < baseStart_1560654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560711 : List Nat := [1, 1, 4, 2, 1, 1, 2, 6, 1, 1, 3]
def baseStart_1560711 : Nat := 118140960795 + 1560711 * 2 ^ 59
def prefixEnd_1560711 : Nat := 4983230072969 + 3 ^ 40 * 1560711 * 2
def baseEnd_1560711 : Nat := 801394905759348444734927

theorem tailTrace_1560711 : CollatzResearch.WordTrace tailWord_1560711 prefixEnd_1560711 801394905759348444734927 := by
  unfold tailWord_1560711
  simp only [CollatzResearch.WordTrace]
  refine ⟨56923806648818070062921987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37949204432545380041947991 56923806648818070062921987)
  ·
    refine ⟨85385709973227105094382981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56923806648818070062921987 85385709973227105094382981)
    ·
      refine ⟨16009820619980082205196809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85385709973227105094382981 16009820619980082205196809)
      ·
        refine ⟨12007365464985061653897607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16009820619980082205196809 12007365464985061653897607)
        ·
          refine ⟨18011048197477592480846411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12007365464985061653897607 18011048197477592480846411)
          ·
            refine ⟨27016572296216388721269617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18011048197477592480846411 27016572296216388721269617)
            ·
              refine ⟨20262429222162291540952213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27016572296216388721269617 20262429222162291540952213)
              ·
                refine ⟨949801369788857415982135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20262429222162291540952213 949801369788857415982135)
                ·
                  refine ⟨1424702054683286123973203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 949801369788857415982135 1424702054683286123973203)
                  ·
                    refine ⟨2137053082024929185959805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1424702054683286123973203 2137053082024929185959805)
                    ·
                      refine ⟨801394905759348444734927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2137053082024929185959805 801394905759348444734927)
                      ·
                        rfl

theorem cell23_1560711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_1560711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560711 prefixEnd_1560711 := by exact prefixLift 1560711
  have htrace : WordTrace (prefixWord ++ tailWord_1560711) baseStart_1560711 baseEnd_1560711 := by
    simpa [prefixWord, tailWord_1560711, baseEnd_1560711] using wordTrace_append hprefix tailTrace_1560711
  have hstable : (prefixWord ++ tailWord_1560711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560711).length < 2 ^ (prefixWord ++ tailWord_1560711).sum := by decide
  have hdescent : baseEnd_1560711 < baseStart_1560711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560718 : List Nat := [4, 1, 1, 3, 4, 1, 2, 1, 6]
def baseStart_1560718 : Nat := 118140960795 + 1560718 * 2 ^ 59
def prefixEnd_1560718 : Nat := 4983230072969 + 3 ^ 40 * 1560718 * 2
def baseEnd_1560718 : Nat := 89044277791547768594155

theorem tailTrace_1560718 : CollatzResearch.WordTrace tailWord_1560718 prefixEnd_1560718 89044277791547768594155 := by
  unfold tailWord_1560718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7115507744974088782303351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37949374639861806838951205 7115507744974088782303351)
  ·
    refine ⟨10673261617461133173455027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7115507744974088782303351 10673261617461133173455027)
    ·
      refine ⟨16009892426191699760182541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10673261617461133173455027 16009892426191699760182541)
      ·
        refine ⟨6003709659821887410068453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16009892426191699760182541 6003709659821887410068453)
        ·
          refine ⟨1125695561216603889387835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6003709659821887410068453 1125695561216603889387835)
          ·
            refine ⟨1688543341824905834081753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125695561216603889387835 1688543341824905834081753)
            ·
              refine ⟨1266407506368679375561315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1688543341824905834081753 1266407506368679375561315)
              ·
                refine ⟨1899611259553019063341973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1266407506368679375561315 1899611259553019063341973)
                ·
                  refine ⟨89044277791547768594155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1899611259553019063341973 89044277791547768594155)
                  ·
                    rfl

theorem cell23_1560718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_1560718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560718 prefixEnd_1560718 := by exact prefixLift 1560718
  have htrace : WordTrace (prefixWord ++ tailWord_1560718) baseStart_1560718 baseEnd_1560718 := by
    simpa [prefixWord, tailWord_1560718, baseEnd_1560718] using wordTrace_append hprefix tailTrace_1560718
  have hstable : (prefixWord ++ tailWord_1560718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560718).length < 2 ^ (prefixWord ++ tailWord_1560718).sum := by decide
  have hdescent : baseEnd_1560718 < baseStart_1560718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560738 : List Nat := [3, 3, 1, 3, 1, 2, 2, 1, 2, 3, 2]
def baseStart_1560738 : Nat := 118140960795 + 1560738 * 2 ^ 59
def prefixEnd_1560738 : Nat := 4983230072969 + 3 ^ 40 * 1560738 * 2
def baseEnd_1560738 : Nat := 801408769737019839097303

theorem tailTrace_1560738 : CollatzResearch.WordTrace tailWord_1560738 prefixEnd_1560738 801408769737019839097303 := by
  unfold tailWord_1560738
  simp only [CollatzResearch.WordTrace]
  refine ⟨14231197854930063418538717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37949860946480169116103245 14231197854930063418538717)
  ·
    refine ⟨5336699195598773781952019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14231197854930063418538717 5336699195598773781952019)
    ·
      refine ⟨8005048793398160672928029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5336699195598773781952019 8005048793398160672928029)
      ·
        refine ⟨3001893297524310252348011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8005048793398160672928029 3001893297524310252348011)
        ·
          refine ⟨4502839946286465378522017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3001893297524310252348011 4502839946286465378522017)
          ·
            refine ⟨3377129959714849033891513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4502839946286465378522017 3377129959714849033891513)
            ·
              refine ⟨2532847469786136775418635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3377129959714849033891513 2532847469786136775418635)
              ·
                refine ⟨3799271204679205163127953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2532847469786136775418635 3799271204679205163127953)
                ·
                  refine ⟨2849453403509403872345965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3799271204679205163127953 2849453403509403872345965)
                  ·
                    refine ⟨1068545026316026452129737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2849453403509403872345965 1068545026316026452129737)
                    ·
                      refine ⟨801408769737019839097303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1068545026316026452129737 801408769737019839097303)
                      ·
                        rfl

theorem cell23_1560738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_1560738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560738 prefixEnd_1560738 := by exact prefixLift 1560738
  have htrace : WordTrace (prefixWord ++ tailWord_1560738) baseStart_1560738 baseEnd_1560738 := by
    simpa [prefixWord, tailWord_1560738, baseEnd_1560738] using wordTrace_append hprefix tailTrace_1560738
  have hstable : (prefixWord ++ tailWord_1560738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560738).length < 2 ^ (prefixWord ++ tailWord_1560738).sum := by decide
  have hdescent : baseEnd_1560738 < baseStart_1560738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560756 : List Nat := [2, 5, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_1560756 : Nat := 118140960795 + 1560756 * 2 ^ 59
def prefixEnd_1560756 : Nat := 4983230072969 + 3 ^ 40 * 1560756 * 2
def baseEnd_1560756 : Nat := 267139337462933589557407

theorem tailTrace_1560756 : CollatzResearch.WordTrace tailWord_1560756 prefixEnd_1560756 267139337462933589557407 := by
  unfold tailWord_1560756
  simp only [CollatzResearch.WordTrace]
  refine ⟨28462723966827521374155061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37950298622436695165540081 28462723966827521374155061)
  ·
    refine ⟨2668380371890080128827037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28462723966827521374155061 2668380371890080128827037)
    ·
      refine ⟨1000642639458780048310139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2668380371890080128827037 1000642639458780048310139)
      ·
        refine ⟨1500963959188170072465209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1000642639458780048310139 1500963959188170072465209)
        ·
          refine ⟨1125722969391127554348907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1500963959188170072465209 1125722969391127554348907)
          ·
            refine ⟨1688584454086691331523361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125722969391127554348907 1688584454086691331523361)
            ·
              refine ⟨1266438340565018498642521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1688584454086691331523361 1266438340565018498642521)
              ·
                refine ⟨949828755423763873981891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1266438340565018498642521 949828755423763873981891)
                ·
                  refine ⟨1424743133135645810972837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 949828755423763873981891 1424743133135645810972837)
                  ·
                    refine ⟨267139337462933589557407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1424743133135645810972837 267139337462933589557407)
                    ·
                      rfl

theorem cell23_1560756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_1560756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560756 prefixEnd_1560756 := by exact prefixLift 1560756
  have htrace : WordTrace (prefixWord ++ tailWord_1560756) baseStart_1560756 baseEnd_1560756 := by
    simpa [prefixWord, tailWord_1560756, baseEnd_1560756] using wordTrace_append hprefix tailTrace_1560756
  have hstable : (prefixWord ++ tailWord_1560756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560756).length < 2 ^ (prefixWord ++ tailWord_1560756).sum := by decide
  have hdescent : baseEnd_1560756 < baseStart_1560756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560757 : List Nat := [1, 3, 3, 4, 12]
def baseStart_1560757 : Nat := 118140960795 + 1560757 * 2 ^ 59
def prefixEnd_1560757 : Nat := 4983230072969 + 3 ^ 40 * 1560757 * 2
def baseEnd_1560757 : Nat := 1099339541659060719835

theorem tailTrace_1560757 : CollatzResearch.WordTrace tailWord_1560757 prefixEnd_1560757 1099339541659060719835 := by
  unfold tailWord_1560757
  simp only [CollatzResearch.WordTrace]
  refine ⟨56925484406651419919096525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37950322937767613279397683 56925484406651419919096525)
  ·
    refine ⟨21347056652494282469661197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56925484406651419919096525 21347056652494282469661197)
    ·
      refine ⟨8005146244685355926122949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21347056652494282469661197 8005146244685355926122949)
      ·
        refine ⟨1500964920878504236148053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8005146244685355926122949 1500964920878504236148053)
        ·
          refine ⟨1099339541659060719835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1500964920878504236148053 1099339541659060719835)
          ·
            rfl

theorem cell23_1560757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 12].length) (baseStart_1560757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560757 prefixEnd_1560757 := by exact prefixLift 1560757
  have htrace : WordTrace (prefixWord ++ tailWord_1560757) baseStart_1560757 baseEnd_1560757 := by
    simpa [prefixWord, tailWord_1560757, baseEnd_1560757] using wordTrace_append hprefix tailTrace_1560757
  have hstable : (prefixWord ++ tailWord_1560757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560757).length < 2 ^ (prefixWord ++ tailWord_1560757).sum := by decide
  have hdescent : baseEnd_1560757 < baseStart_1560757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560767 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 3]
def baseStart_1560767 : Nat := 118140960795 + 1560767 * 2 ^ 59
def prefixEnd_1560767 : Nat := 4983230072969 + 3 ^ 40 * 1560767 * 2
def baseEnd_1560767 : Nat := 801423660676000225634669

theorem tailTrace_1560767 : CollatzResearch.WordTrace tailWord_1560767 prefixEnd_1560767 801423660676000225634669 := by
  unfold tailWord_1560767
  simp only [CollatzResearch.WordTrace]
  refine ⟨56925849136615191626960555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37950566091076794417973703 56925849136615191626960555)
  ·
    refine ⟨85388773704922787440440833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56925849136615191626960555 85388773704922787440440833)
    ·
      refine ⟨64041580278692090580330625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85388773704922787440440833 64041580278692090580330625)
      ·
        refine ⟨48031185209019067935247969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64041580278692090580330625 48031185209019067935247969)
        ·
          refine ⟨36023388906764300951435977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48031185209019067935247969 36023388906764300951435977)
          ·
            refine ⟨27017541680073225713576983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36023388906764300951435977 27017541680073225713576983)
            ·
              refine ⟨40526312520109838570365475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27017541680073225713576983 40526312520109838570365475)
              ·
                refine ⟨60789468780164757855548213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40526312520109838570365475 60789468780164757855548213)
                ·
                  refine ⟨5699012698140446048957645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60789468780164757855548213 5699012698140446048957645)
                  ·
                    refine ⟨2137129761802667268359117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5699012698140446048957645 2137129761802667268359117)
                    ·
                      refine ⟨801423660676000225634669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2137129761802667268359117 801423660676000225634669)
                      ·
                        rfl

theorem cell23_1560767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 3].length) (baseStart_1560767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560767 prefixEnd_1560767 := by exact prefixLift 1560767
  have htrace : WordTrace (prefixWord ++ tailWord_1560767) baseStart_1560767 baseEnd_1560767 := by
    simpa [prefixWord, tailWord_1560767, baseEnd_1560767] using wordTrace_append hprefix tailTrace_1560767
  have hstable : (prefixWord ++ tailWord_1560767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560767).length < 2 ^ (prefixWord ++ tailWord_1560767).sum := by decide
  have hdescent : baseEnd_1560767 < baseStart_1560767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560811 : List Nat := [1, 1, 1, 1, 2, 5, 3, 3, 1, 3, 2]
def baseStart_1560811 : Nat := 118140960795 + 1560811 * 2 ^ 59
def prefixEnd_1560811 : Nat := 4983230072969 + 3 ^ 40 * 1560811 * 2
def baseEnd_1560811 : Nat := 801446253824798053484467

theorem tailTrace_1560811 : CollatzResearch.WordTrace tailWord_1560811 prefixEnd_1560811 801446253824798053484467 := by
  unfold tailWord_1560811
  simp only [CollatzResearch.WordTrace]
  refine ⟨56927453948455787141562287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37951635965637191427708191 56927453948455787141562287)
  ·
    refine ⟨85391180922683680712343431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56927453948455787141562287 85391180922683680712343431)
    ·
      refine ⟨128086771384025521068515147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85391180922683680712343431 128086771384025521068515147)
      ·
        refine ⟨192130157076038281602772721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128086771384025521068515147 192130157076038281602772721)
        ·
          refine ⟨144097617807028711202079541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192130157076038281602772721 144097617807028711202079541)
          ·
            refine ⟨13509151669408941675194957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 144097617807028711202079541 13509151669408941675194957)
            ·
              refine ⟨5065931876028353128198109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13509151669408941675194957 5065931876028353128198109)
              ·
                refine ⟨1899724453510632423074291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5065931876028353128198109 1899724453510632423074291)
                ·
                  refine ⟨2849586680265948634611437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1899724453510632423074291 2849586680265948634611437)
                  ·
                    refine ⟨1068595005099730737979289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2849586680265948634611437 1068595005099730737979289)
                    ·
                      refine ⟨801446253824798053484467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1068595005099730737979289 801446253824798053484467)
                      ·
                        rfl

theorem cell23_1560811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 3, 2].length) (baseStart_1560811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560811 prefixEnd_1560811 := by exact prefixLift 1560811
  have htrace : WordTrace (prefixWord ++ tailWord_1560811) baseStart_1560811 baseEnd_1560811 := by
    simpa [prefixWord, tailWord_1560811, baseEnd_1560811] using wordTrace_append hprefix tailTrace_1560811
  have hstable : (prefixWord ++ tailWord_1560811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560811).length < 2 ^ (prefixWord ++ tailWord_1560811).sum := by decide
  have hdescent : baseEnd_1560811 < baseStart_1560811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560817 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 2, 6]
def baseStart_1560817 : Nat := 118140960795 + 1560817 * 2 ^ 59
def prefixEnd_1560817 : Nat := 4983230072969 + 3 ^ 40 * 1560817 * 2
def baseEnd_1560817 : Nat := 267149778236241676669813

theorem tailTrace_1560817 : CollatzResearch.WordTrace tailWord_1560817 prefixEnd_1560817 267149778236241676669813 := by
  unfold tailWord_1560817
  simp only [CollatzResearch.WordTrace]
  refine ⟨56927672786434050166280705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37951781857622700110853803 56927672786434050166280705)
  ·
    refine ⟨42695754589825537624710529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56927672786434050166280705 42695754589825537624710529)
    ·
      refine ⟨32021815942369153218532897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42695754589825537624710529 32021815942369153218532897)
      ·
        refine ⟨24016361956776864913899673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32021815942369153218532897 24016361956776864913899673)
        ·
          refine ⟨18012271467582648685424755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24016361956776864913899673 18012271467582648685424755)
          ·
            refine ⟨27018407201373973028137133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18012271467582648685424755 27018407201373973028137133)
            ·
              refine ⟨10131902700515239885551425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27018407201373973028137133 10131902700515239885551425)
              ·
                refine ⟨7598927025386429914163569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10131902700515239885551425 7598927025386429914163569)
                ·
                  refine ⟨5699195269039822435622677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7598927025386429914163569 5699195269039822435622677)
                  ·
                    refine ⟨267149778236241676669813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5699195269039822435622677 267149778236241676669813)
                    ·
                      rfl

theorem cell23_1560817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_1560817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560817 prefixEnd_1560817 := by exact prefixLift 1560817
  have htrace : WordTrace (prefixWord ++ tailWord_1560817) baseStart_1560817 baseEnd_1560817 := by
    simpa [prefixWord, tailWord_1560817, baseEnd_1560817] using wordTrace_append hprefix tailTrace_1560817
  have hstable : (prefixWord ++ tailWord_1560817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560817).length < 2 ^ (prefixWord ++ tailWord_1560817).sum := by decide
  have hdescent : baseEnd_1560817 < baseStart_1560817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560818 : List Nat := [3, 2, 1, 3, 2, 1, 3, 2, 2, 1, 3]
def baseStart_1560818 : Nat := 118140960795 + 1560818 * 2 ^ 59
def prefixEnd_1560818 : Nat := 4983230072969 + 3 ^ 40 * 1560818 * 2
def baseEnd_1560818 : Nat := 801449848189379526096935

theorem tailTrace_1560818 : CollatzResearch.WordTrace tailWord_1560818 prefixEnd_1560818 801449848189379526096935 := by
  unfold tailWord_1560818
  simp only [CollatzResearch.WordTrace]
  refine ⟨14231927314857606834266777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37951806172953618224711405 14231927314857606834266777)
  ·
    refine ⟨10673945486143205125700083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14231927314857606834266777 10673945486143205125700083)
    ·
      refine ⟨16010918229214807688550125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10673945486143205125700083 16010918229214807688550125)
      ·
        refine ⟨6004094335955552883206297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16010918229214807688550125 6004094335955552883206297)
        ·
          refine ⟨4503070751966664662404723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6004094335955552883206297 4503070751966664662404723)
          ·
            refine ⟨6754606127949996993607085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4503070751966664662404723 6754606127949996993607085)
            ·
              refine ⟨2532977297981248872602657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6754606127949996993607085 2532977297981248872602657)
              ·
                refine ⟨1899732973485936654451993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2532977297981248872602657 1899732973485936654451993)
                ·
                  refine ⟨1424799730114452490838995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1899732973485936654451993 1424799730114452490838995)
                  ·
                    refine ⟨2137199595171678736258493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1424799730114452490838995 2137199595171678736258493)
                    ·
                      refine ⟨801449848189379526096935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2137199595171678736258493 801449848189379526096935)
                      ·
                        rfl

theorem cell23_1560818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_1560818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560818 prefixEnd_1560818 := by exact prefixLift 1560818
  have htrace : WordTrace (prefixWord ++ tailWord_1560818) baseStart_1560818 baseEnd_1560818 := by
    simpa [prefixWord, tailWord_1560818, baseEnd_1560818] using wordTrace_append hprefix tailTrace_1560818
  have hstable : (prefixWord ++ tailWord_1560818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560818).length < 2 ^ (prefixWord ++ tailWord_1560818).sum := by decide
  have hdescent : baseEnd_1560818 < baseStart_1560818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560824 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 3, 4, 2]
def baseStart_1560824 : Nat := 118140960795 + 1560824 * 2 ^ 59
def prefixEnd_1560824 : Nat := 4983230072969 + 3 ^ 40 * 1560824 * 2
def baseEnd_1560824 : Nat := 801452929073306502621907

theorem tailTrace_1560824 : CollatzResearch.WordTrace tailWord_1560824 prefixEnd_1560824 801452929073306502621907 := by
  unfold tailWord_1560824
  simp only [CollatzResearch.WordTrace]
  refine ⟨28463964048704345180892763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37951952064939126907857017 28463964048704345180892763)
  ·
    refine ⟨42695946073056517771339145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28463964048704345180892763 42695946073056517771339145)
    ·
      refine ⟨32021959554792388328504359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42695946073056517771339145 32021959554792388328504359)
      ·
        refine ⟨48032939332188582492756539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32021959554792388328504359 48032939332188582492756539)
        ·
          refine ⟨72049408998282873739134809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48032939332188582492756539 72049408998282873739134809)
          ·
            refine ⟨54037056748712155304351107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72049408998282873739134809 54037056748712155304351107)
            ·
              refine ⟨81055585123068232956526661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54037056748712155304351107 81055585123068232956526661)
              ·
                refine ⟨15197922210575293679348749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81055585123068232956526661 15197922210575293679348749)
                ·
                  refine ⟨5699220828965735129755781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15197922210575293679348749 5699220828965735129755781)
                  ·
                    refine ⟨1068603905431075336829209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5699220828965735129755781 1068603905431075336829209)
                    ·
                      refine ⟨801452929073306502621907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1068603905431075336829209 801452929073306502621907)
                      ·
                        rfl

theorem cell23_1560824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 3, 4, 2].length) (baseStart_1560824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560824 prefixEnd_1560824 := by exact prefixLift 1560824
  have htrace : WordTrace (prefixWord ++ tailWord_1560824) baseStart_1560824 baseEnd_1560824 := by
    simpa [prefixWord, tailWord_1560824, baseEnd_1560824] using wordTrace_append hprefix tailTrace_1560824
  have hstable : (prefixWord ++ tailWord_1560824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560824).length < 2 ^ (prefixWord ++ tailWord_1560824).sum := by decide
  have hdescent : baseEnd_1560824 < baseStart_1560824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560837 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 1, 4, 4]
def baseStart_1560837 : Nat := 118140960795 + 1560837 * 2 ^ 59
def prefixEnd_1560837 : Nat := 4983230072969 + 3 ^ 40 * 1560837 * 2
def baseEnd_1560837 : Nat := 801459604321814951759347

theorem tailTrace_1560837 : CollatzResearch.WordTrace tailWord_1560837 prefixEnd_1560837 801459604321814951759347 := by
  unfold tailWord_1560837
  simp only [CollatzResearch.WordTrace]
  refine ⟨56928402246361593582008765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37952268164241062388005843 56928402246361593582008765)
  ·
    refine ⟨21348150842385597593253287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56928402246361593582008765 21348150842385597593253287)
    ·
      refine ⟨32022226263578396389879931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21348150842385597593253287 32022226263578396389879931)
      ·
        refine ⟨48033339395367594584819897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32022226263578396389879931 48033339395367594584819897)
        ·
          refine ⟨36025004546525695938614923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48033339395367594584819897 36025004546525695938614923)
          ·
            refine ⟨54037506819788543907922385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36025004546525695938614923 54037506819788543907922385)
            ·
              refine ⟨40528130114841407930941789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54037506819788543907922385 40528130114841407930941789)
              ·
                refine ⟨15198048793065527974103171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40528130114841407930941789 15198048793065527974103171)
                ·
                  refine ⟨22797073189598291961154757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15198048793065527974103171 22797073189598291961154757)
                  ·
                    refine ⟨4274451223049679742716517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22797073189598291961154757 4274451223049679742716517)
                    ·
                      refine ⟨801459604321814951759347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4274451223049679742716517 801459604321814951759347)
                      ·
                        rfl

theorem cell23_1560837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_1560837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560837 prefixEnd_1560837 := by exact prefixLift 1560837
  have htrace : WordTrace (prefixWord ++ tailWord_1560837) baseStart_1560837 baseEnd_1560837 := by
    simpa [prefixWord, tailWord_1560837, baseEnd_1560837] using wordTrace_append hprefix tailTrace_1560837
  have hstable : (prefixWord ++ tailWord_1560837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560837).length < 2 ^ (prefixWord ++ tailWord_1560837).sum := by decide
  have hdescent : baseEnd_1560837 < baseStart_1560837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560841 : List Nat := [1, 2, 1, 1, 3, 4, 3, 1, 1, 4, 2]
def baseStart_1560841 : Nat := 118140960795 + 1560841 * 2 ^ 59
def prefixEnd_1560841 : Nat := 4983230072969 + 3 ^ 40 * 1560841 * 2
def baseEnd_1560841 : Nat := 801461658244432936109329

theorem tailTrace_1560841 : CollatzResearch.WordTrace tailWord_1560841 prefixEnd_1560841 801461658244432936109329 := by
  unfold tailWord_1560841
  simp only [CollatzResearch.WordTrace]
  refine ⟨56928548138347102265154377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37952365425564734843436251 56928548138347102265154377)
  ·
    refine ⟨42696411103760326698865783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56928548138347102265154377 42696411103760326698865783)
    ·
      refine ⟨64044616655640490048298675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42696411103760326698865783 64044616655640490048298675)
      ·
        refine ⟨96066924983460735072448013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64044616655640490048298675 96066924983460735072448013)
        ·
          refine ⟨36025096868797775652168005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96066924983460735072448013 36025096868797775652168005)
          ·
            refine ⟨6754705662899582934781501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36025096868797775652168005 6754705662899582934781501)
            ·
              refine ⟨2533014623587343600543063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6754705662899582934781501 2533014623587343600543063)
              ·
                refine ⟨3799521935381015400814595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2533014623587343600543063 3799521935381015400814595)
                ·
                  refine ⟨5699282903071523101221893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3799521935381015400814595 5699282903071523101221893)
                  ·
                    refine ⟨1068615544325910581479105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5699282903071523101221893 1068615544325910581479105)
                    ·
                      refine ⟨801461658244432936109329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1068615544325910581479105 801461658244432936109329)
                      ·
                        rfl

theorem cell23_1560841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 4, 2].length) (baseStart_1560841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560841 prefixEnd_1560841 := by exact prefixLift 1560841
  have htrace : WordTrace (prefixWord ++ tailWord_1560841) baseStart_1560841 baseEnd_1560841 := by
    simpa [prefixWord, tailWord_1560841, baseEnd_1560841] using wordTrace_append hprefix tailTrace_1560841
  have hstable : (prefixWord ++ tailWord_1560841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560841).length < 2 ^ (prefixWord ++ tailWord_1560841).sum := by decide
  have hdescent : baseEnd_1560841 < baseStart_1560841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560861 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 2, 1, 5]
def baseStart_1560861 : Nat := 118140960795 + 1560861 * 2 ^ 59
def prefixEnd_1560861 : Nat := 4983230072969 + 3 ^ 40 * 1560861 * 2
def baseEnd_1560861 : Nat := 801471927857522857859237

theorem tailTrace_1560861 : CollatzResearch.WordTrace tailWord_1560861 prefixEnd_1560861 801471927857522857859237 := by
  unfold tailWord_1560861
  simp only [CollatzResearch.WordTrace]
  refine ⟨56929277598274645680882437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37952851732183097120588291 56929277598274645680882437)
  ·
    refine ⟨10674239549676496065165457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56929277598274645680882437 10674239549676496065165457)
    ·
      refine ⟨8005679662257372048874093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10674239549676496065165457 8005679662257372048874093)
      ·
        refine ⟨3002129873346514518327785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8005679662257372048874093 3002129873346514518327785)
        ·
          refine ⟨2251597405009885888745839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3002129873346514518327785 2251597405009885888745839)
          ·
            refine ⟨3377396107514828833118759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2251597405009885888745839 3377396107514828833118759)
            ·
              refine ⟨5066094161272243249678139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3377396107514828833118759 5066094161272243249678139)
              ·
                refine ⟨7599141241908364874517209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5066094161272243249678139 7599141241908364874517209)
                ·
                  refine ⟨5699355931431273655887907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7599141241908364874517209 5699355931431273655887907)
                  ·
                    refine ⟨8549033897146910483831861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5699355931431273655887907 8549033897146910483831861)
                    ·
                      refine ⟨801471927857522857859237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8549033897146910483831861 801471927857522857859237)
                      ·
                        rfl

theorem cell23_1560861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_1560861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560861 prefixEnd_1560861 := by exact prefixLift 1560861
  have htrace : WordTrace (prefixWord ++ tailWord_1560861) baseStart_1560861 baseEnd_1560861 := by
    simpa [prefixWord, tailWord_1560861, baseEnd_1560861] using wordTrace_append hprefix tailTrace_1560861
  have hstable : (prefixWord ++ tailWord_1560861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560861).length < 2 ^ (prefixWord ++ tailWord_1560861).sum := by decide
  have hdescent : baseEnd_1560861 < baseStart_1560861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560881 : List Nat := [1, 2, 2, 3, 4, 2, 1, 1, 7]
def baseStart_1560881 : Nat := 118140960795 + 1560881 * 2 ^ 59
def prefixEnd_1560881 : Nat := 4983230072969 + 3 ^ 40 * 1560881 * 2
def baseEnd_1560881 : Nat := 89053577496734753289905

theorem tailTrace_1560881 : CollatzResearch.WordTrace tailWord_1560881 prefixEnd_1560881 89053577496734753289905 := by
  unfold tailWord_1560881
  simp only [CollatzResearch.WordTrace]
  refine ⟨56930007058202189096610497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37953338038801459397740331 56930007058202189096610497)
  ·
    refine ⟨42697505293651641822457873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56930007058202189096610497 42697505293651641822457873)
    ·
      refine ⟨32023128970238731366843405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42697505293651641822457873 32023128970238731366843405)
      ·
        refine ⟨12008673363839524262566277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32023128970238731366843405 12008673363839524262566277)
        ·
          refine ⟨2251626255719910799231177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12008673363839524262566277 2251626255719910799231177)
          ·
            refine ⟨1688719691789933099423383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2251626255719910799231177 1688719691789933099423383)
            ·
              refine ⟨2533079537684899649135075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1688719691789933099423383 2533079537684899649135075)
              ·
                refine ⟨3799619306527349473702613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2533079537684899649135075 3799619306527349473702613)
                ·
                  refine ⟨89053577496734753289905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3799619306527349473702613 89053577496734753289905)
                  ·
                    rfl

theorem cell23_1560881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 7].length) (baseStart_1560881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560881 prefixEnd_1560881 := by exact prefixLift 1560881
  have htrace : WordTrace (prefixWord ++ tailWord_1560881) baseStart_1560881 baseEnd_1560881 := by
    simpa [prefixWord, tailWord_1560881, baseEnd_1560881] using wordTrace_append hprefix tailTrace_1560881
  have hstable : (prefixWord ++ tailWord_1560881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560881).length < 2 ^ (prefixWord ++ tailWord_1560881).sum := by decide
  have hdescent : baseEnd_1560881 < baseStart_1560881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560914 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_1560914 : Nat := 118140960795 + 1560914 * 2 ^ 59
def prefixEnd_1560914 : Nat := 4983230072969 + 3 ^ 40 * 1560914 * 2
def baseEnd_1560914 : Nat := 801499142332211150496493

theorem tailTrace_1560914 : CollatzResearch.WordTrace tailWord_1560914 prefixEnd_1560914 801499142332211150496493 := by
  unfold tailWord_1560914
  simp only [CollatzResearch.WordTrace]
  refine ⟨14232802666770658933140449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37954140444721757155041197 14232802666770658933140449)
  ·
    refine ⟨10674602000077994199855337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14232802666770658933140449 10674602000077994199855337)
    ·
      refine ⟨8005951500058495649891503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10674602000077994199855337 8005951500058495649891503)
      ·
        refine ⟨12008927250087743474837255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8005951500058495649891503 12008927250087743474837255)
        ·
          refine ⟨18013390875131615212255883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12008927250087743474837255 18013390875131615212255883)
          ·
            refine ⟨27020086312697422818383825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18013390875131615212255883 27020086312697422818383825)
            ·
              refine ⟨20265064734523067113787869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27020086312697422818383825 20265064734523067113787869)
              ·
                refine ⟨7599399275446150167670451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20265064734523067113787869 7599399275446150167670451)
                ·
                  refine ⟨11399098913169225251505677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7599399275446150167670451 11399098913169225251505677)
                  ·
                    refine ⟨4274662092438459469314629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11399098913169225251505677 4274662092438459469314629)
                    ·
                      refine ⟨801499142332211150496493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4274662092438459469314629 801499142332211150496493)
                      ·
                        rfl

theorem cell23_1560914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_1560914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560914 prefixEnd_1560914 := by exact prefixLift 1560914
  have htrace : WordTrace (prefixWord ++ tailWord_1560914) baseStart_1560914 baseEnd_1560914 := by
    simpa [prefixWord, tailWord_1560914, baseEnd_1560914] using wordTrace_append hprefix tailTrace_1560914
  have hstable : (prefixWord ++ tailWord_1560914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560914).length < 2 ^ (prefixWord ++ tailWord_1560914).sum := by decide
  have hdescent : baseEnd_1560914 < baseStart_1560914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560931 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 2, 4, 2]
def baseStart_1560931 : Nat := 118140960795 + 1560931 * 2 ^ 59
def prefixEnd_1560931 : Nat := 4983230072969 + 3 ^ 40 * 1560931 * 2
def baseEnd_1560931 : Nat := 801507871503337583983915

theorem tailTrace_1560931 : CollatzResearch.WordTrace tailWord_1560931 prefixEnd_1560931 801507871503337583983915 := by
  unfold tailWord_1560931
  simp only [CollatzResearch.WordTrace]
  refine ⟨56931830708021047635930647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37954553805347365090620431 56931830708021047635930647)
  ·
    refine ⟨85397746062031571453895971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56931830708021047635930647 85397746062031571453895971)
    ·
      refine ⟨128096619093047357180843957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85397746062031571453895971 128096619093047357180843957)
      ·
        refine ⟨12009058039973189735704121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128096619093047357180843957 12009058039973189735704121)
        ·
          refine ⟨9006793529979892301778091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12009058039973189735704121 9006793529979892301778091)
          ·
            refine ⟨13510190294969838452667137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9006793529979892301778091 13510190294969838452667137)
            ·
              refine ⟨10132642721227378839500353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13510190294969838452667137 10132642721227378839500353)
              ·
                refine ⟨7599482040920534129625265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10132642721227378839500353 7599482040920534129625265)
                ·
                  refine ⟨5699611530690400597218949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7599482040920534129625265 5699611530690400597218949)
                  ·
                    refine ⟨1068677162004450111978553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5699611530690400597218949 1068677162004450111978553)
                    ·
                      refine ⟨801507871503337583983915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1068677162004450111978553 801507871503337583983915)
                      ·
                        rfl

theorem cell23_1560931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_1560931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560931 prefixEnd_1560931 := by exact prefixLift 1560931
  have htrace : WordTrace (prefixWord ++ tailWord_1560931) baseStart_1560931 baseEnd_1560931 := by
    simpa [prefixWord, tailWord_1560931, baseEnd_1560931] using wordTrace_append hprefix tailTrace_1560931
  have hstable : (prefixWord ++ tailWord_1560931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560931).length < 2 ^ (prefixWord ++ tailWord_1560931).sum := by decide
  have hdescent : baseEnd_1560931 < baseStart_1560931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560941 : List Nat := [1, 5, 1, 1, 1, 2, 2, 3, 3, 4]
def baseStart_1560941 : Nat := 118140960795 + 1560941 * 2 ^ 59
def prefixEnd_1560941 : Nat := 4983230072969 + 3 ^ 40 * 1560941 * 2
def baseEnd_1560941 : Nat := 267171002103294181619623

theorem tailTrace_1560941 : CollatzResearch.WordTrace tailWord_1560941 prefixEnd_1560941 267171002103294181619623 := by
  unfold tailWord_1560941
  simp only [CollatzResearch.WordTrace]
  refine ⟨56932195437984819343794677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37954796958656546229196451 56932195437984819343794677)
  ·
    refine ⟨5337393322311076813480751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56932195437984819343794677 5337393322311076813480751)
    ·
      refine ⟨8006089983466615220221127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5337393322311076813480751 8006089983466615220221127)
      ·
        refine ⟨12009134975199922830331691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8006089983466615220221127 12009134975199922830331691)
        ·
          refine ⟨18013702462799884245497537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12009134975199922830331691 18013702462799884245497537)
          ·
            refine ⟨13510276847099913184123153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18013702462799884245497537 13510276847099913184123153)
            ·
              refine ⟨10132707635324934888092365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13510276847099913184123153 10132707635324934888092365)
              ·
                refine ⟨3799765363246850583034637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10132707635324934888092365 3799765363246850583034637)
                ·
                  refine ⟨1424912011217568968637989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3799765363246850583034637 1424912011217568968637989)
                  ·
                    refine ⟨267171002103294181619623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1424912011217568968637989 267171002103294181619623)
                    ·
                      rfl

theorem cell23_1560941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_1560941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560941 prefixEnd_1560941 := by exact prefixLift 1560941
  have htrace : WordTrace (prefixWord ++ tailWord_1560941) baseStart_1560941 baseEnd_1560941 := by
    simpa [prefixWord, tailWord_1560941, baseEnd_1560941] using wordTrace_append hprefix tailTrace_1560941
  have hstable : (prefixWord ++ tailWord_1560941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560941).length < 2 ^ (prefixWord ++ tailWord_1560941).sum := by decide
  have hdescent : baseEnd_1560941 < baseStart_1560941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560962 : List Nat := [3, 4, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_1560962 : Nat := 118140960795 + 1560962 * 2 ^ 59
def prefixEnd_1560962 : Nat := 4983230072969 + 3 ^ 40 * 1560962 * 2
def baseEnd_1560962 : Nat := 267174596467875654232091

theorem tailTrace_1560962 : CollatzResearch.WordTrace tailWord_1560962 prefixEnd_1560962 267174596467875654232091 := by
  unfold tailWord_1560962
  simp only [CollatzResearch.WordTrace]
  refine ⟨14233240342727184982577285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37955307580605826620206093 14233240342727184982577285)
  ·
    refine ⟨2668732564261347184233241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14233240342727184982577285 2668732564261347184233241)
    ·
      refine ⟨2001549423196010388174931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2668732564261347184233241 2001549423196010388174931)
      ·
        refine ⟨3002324134794015582262397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2001549423196010388174931 3002324134794015582262397)
        ·
          refine ⟨1125871550547755843348399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3002324134794015582262397 1125871550547755843348399)
          ·
            refine ⟨1688807325821633765022599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125871550547755843348399 1688807325821633765022599)
            ·
              refine ⟨2533210988732450647533899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1688807325821633765022599 2533210988732450647533899)
              ·
                refine ⟨3799816483098675971300849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2533210988732450647533899 3799816483098675971300849)
                ·
                  refine ⟨2849862362324006978475637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3799816483098675971300849 2849862362324006978475637)
                  ·
                    refine ⟨267174596467875654232091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2849862362324006978475637 267174596467875654232091)
                    ·
                      rfl

theorem cell23_1560962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_1560962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560962 prefixEnd_1560962 := by exact prefixLift 1560962
  have htrace : WordTrace (prefixWord ++ tailWord_1560962) baseStart_1560962 baseEnd_1560962 := by
    simpa [prefixWord, tailWord_1560962, baseEnd_1560962] using wordTrace_append hprefix tailTrace_1560962
  have hstable : (prefixWord ++ tailWord_1560962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560962).length < 2 ^ (prefixWord ++ tailWord_1560962).sum := by decide
  have hdescent : baseEnd_1560962 < baseStart_1560962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560981 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 7, 1, 3]
def baseStart_1560981 : Nat := 118140960795 + 1560981 * 2 ^ 59
def prefixEnd_1560981 : Nat := 4983230072969 + 3 ^ 40 * 1560981 * 2
def baseEnd_1560981 : Nat := 801533545536062388358685

theorem tailTrace_1560981 : CollatzResearch.WordTrace tailWord_1560981 prefixEnd_1560981 801533545536062388358685 := by
  unfold tailWord_1560981
  simp only [CollatzResearch.WordTrace]
  refine ⟨56933654357839906175250797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37955769571893270783500531 56933654357839906175250797)
  ·
    refine ⟨21350120384189964815719049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56933654357839906175250797 21350120384189964815719049)
    ·
      refine ⟨16012590288142473611789287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21350120384189964815719049 16012590288142473611789287)
      ·
        refine ⟨24018885432213710417683931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16012590288142473611789287 24018885432213710417683931)
        ·
          refine ⟨36028328148320565626525897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24018885432213710417683931 36028328148320565626525897)
          ·
            refine ⟨27021246111240424219894423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36028328148320565626525897 27021246111240424219894423)
            ·
              refine ⟨40531869166860636329841635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27021246111240424219894423 40531869166860636329841635)
              ·
                refine ⟨60797803750290954494762453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40531869166860636329841635 60797803750290954494762453)
                ·
                  refine ⟨1424948525397444245970995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 60797803750290954494762453 1424948525397444245970995)
                  ·
                    refine ⟨2137422788096166368956493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1424948525397444245970995 2137422788096166368956493)
                    ·
                      refine ⟨801533545536062388358685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2137422788096166368956493 801533545536062388358685)
                      ·
                        rfl

theorem cell23_1560981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_1560981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1560981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1560981 prefixEnd_1560981 := by exact prefixLift 1560981
  have htrace : WordTrace (prefixWord ++ tailWord_1560981) baseStart_1560981 baseEnd_1560981 := by
    simpa [prefixWord, tailWord_1560981, baseEnd_1560981] using wordTrace_append hprefix tailTrace_1560981
  have hstable : (prefixWord ++ tailWord_1560981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560981).length < 2 ^ (prefixWord ++ tailWord_1560981).sum := by decide
  have hdescent : baseEnd_1560981 < baseStart_1560981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561005 : List Nat := [1, 5, 2, 2, 2, 1, 3, 1, 6]
def baseStart_1561005 : Nat := 118140960795 + 1561005 * 2 ^ 59
def prefixEnd_1561005 : Nat := 4983230072969 + 3 ^ 40 * 1561005 * 2
def baseEnd_1561005 : Nat := 89060652119085588273175

theorem tailTrace_1561005 : CollatzResearch.WordTrace tailWord_1561005 prefixEnd_1561005 89060652119085588273175 := by
  unfold tailWord_1561005
  simp only [CollatzResearch.WordTrace]
  refine ⟨56934529709752958274124469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37956353139835305516082979 56934529709752958274124469)
  ·
    refine ⟨5337612160289339838199169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56934529709752958274124469 5337612160289339838199169)
    ·
      refine ⟨4003209120217004878649377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5337612160289339838199169 4003209120217004878649377)
      ·
        refine ⟨3002406840162753658987033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4003209120217004878649377 3002406840162753658987033)
        ·
          refine ⟨2251805130122065244240275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3002406840162753658987033 2251805130122065244240275)
          ·
            refine ⟨3377707695183097866360413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2251805130122065244240275 3377707695183097866360413)
            ·
              refine ⟨1266640385693661699885155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3377707695183097866360413 1266640385693661699885155)
              ·
                refine ⟨1899960578540492549827733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1266640385693661699885155 1899960578540492549827733)
                ·
                  refine ⟨89060652119085588273175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1899960578540492549827733 89060652119085588273175)
                  ·
                    rfl

theorem cell23_1561005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_1561005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561005 prefixEnd_1561005 := by exact prefixLift 1561005
  have htrace : WordTrace (prefixWord ++ tailWord_1561005) baseStart_1561005 baseEnd_1561005 := by
    simpa [prefixWord, tailWord_1561005, baseEnd_1561005] using wordTrace_append hprefix tailTrace_1561005
  have hstable : (prefixWord ++ tailWord_1561005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561005).length < 2 ^ (prefixWord ++ tailWord_1561005).sum := by decide
  have hdescent : baseEnd_1561005 < baseStart_1561005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561024 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 5]
def baseStart_1561024 : Nat := 118140960795 + 1561024 * 2 ^ 59
def prefixEnd_1561024 : Nat := 4983230072969 + 3 ^ 40 * 1561024 * 2
def baseEnd_1561024 : Nat := 801555625204205720120987

theorem tailTrace_1561024 : CollatzResearch.WordTrace tailWord_1561024 prefixEnd_1561024 801555625204205720120987 := by
  unfold tailWord_1561024
  simp only [CollatzResearch.WordTrace]
  refine ⟨28467611348342062259533063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37956815131122749679377417 28467611348342062259533063)
  ·
    refine ⟨42701417022513093389299595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28467611348342062259533063 42701417022513093389299595)
    ·
      refine ⟨64052125533769640083949393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42701417022513093389299595 64052125533769640083949393)
      ·
        refine ⟨48039094150327230062962045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64052125533769640083949393 48039094150327230062962045)
        ·
          refine ⟨18014660306372711273610767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48039094150327230062962045 18014660306372711273610767)
          ·
            refine ⟨27021990459559066910416151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18014660306372711273610767 27021990459559066910416151)
            ·
              refine ⟨40532985689338600365624227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27021990459559066910416151 40532985689338600365624227)
              ·
                refine ⟨60799478534007900548436341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40532985689338600365624227 60799478534007900548436341)
                ·
                  refine ⟨5699951112563240676415907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60799478534007900548436341 5699951112563240676415907)
                  ·
                    refine ⟨8549926668844861014623861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5699951112563240676415907 8549926668844861014623861)
                    ·
                      refine ⟨801555625204205720120987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8549926668844861014623861 801555625204205720120987)
                      ·
                        rfl

theorem cell23_1561024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_1561024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561024 prefixEnd_1561024 := by exact prefixLift 1561024
  have htrace : WordTrace (prefixWord ++ tailWord_1561024) baseStart_1561024 baseEnd_1561024 := by
    simpa [prefixWord, tailWord_1561024, baseEnd_1561024] using wordTrace_append hprefix tailTrace_1561024
  have hstable : (prefixWord ++ tailWord_1561024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561024).length < 2 ^ (prefixWord ++ tailWord_1561024).sum := by decide
  have hdescent : baseEnd_1561024 < baseStart_1561024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561031 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 4, 4]
def baseStart_1561031 : Nat := 118140960795 + 1561031 * 2 ^ 59
def prefixEnd_1561031 : Nat := 4983230072969 + 3 ^ 40 * 1561031 * 2
def baseEnd_1561031 : Nat := 267186406522929064244485

theorem tailTrace_1561031 : CollatzResearch.WordTrace tailWord_1561031 prefixEnd_1561031 267186406522929064244485 := by
  unfold tailWord_1561031
  simp only [CollatzResearch.WordTrace]
  refine ⟨56935478007658764714570947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37956985338439176476380631 56935478007658764714570947)
  ·
    refine ⟨85403217011488147071856421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56935478007658764714570947 85403217011488147071856421)
    ·
      refine ⟨16013103189654027575973079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85403217011488147071856421 16013103189654027575973079)
      ·
        refine ⟨24019654784481041363959619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16013103189654027575973079 24019654784481041363959619)
        ·
          refine ⟨36029482176721562045939429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24019654784481041363959619 36029482176721562045939429)
          ·
            refine ⟨6755527908135292883613643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36029482176721562045939429 6755527908135292883613643)
            ·
              refine ⟨10133291862202939325420465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6755527908135292883613643 10133291862202939325420465)
              ·
                refine ⟨7599968896652204494065349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10133291862202939325420465 7599968896652204494065349)
                ·
                  refine ⟨1424994168122288342637253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7599968896652204494065349 1424994168122288342637253)
                  ·
                    refine ⟨267186406522929064244485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1424994168122288342637253 267186406522929064244485)
                    ·
                      rfl

theorem cell23_1561031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_1561031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561031 prefixEnd_1561031 := by exact prefixLift 1561031
  have htrace : WordTrace (prefixWord ++ tailWord_1561031) baseStart_1561031 baseEnd_1561031 := by
    simpa [prefixWord, tailWord_1561031, baseEnd_1561031] using wordTrace_append hprefix tailTrace_1561031
  have hstable : (prefixWord ++ tailWord_1561031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561031).length < 2 ^ (prefixWord ++ tailWord_1561031).sum := by decide
  have hdescent : baseEnd_1561031 < baseStart_1561031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561032 : List Nat := [2, 1, 3, 1, 3, 4, 1, 3, 1, 1, 3]
def baseStart_1561032 : Nat := 118140960795 + 1561032 * 2 ^ 59
def prefixEnd_1561032 : Nat := 4983230072969 + 3 ^ 40 * 1561032 * 2
def baseEnd_1561032 : Nat := 801559733049441688820951

theorem tailTrace_1561032 : CollatzResearch.WordTrace tailWord_1561032 prefixEnd_1561032 801559733049441688820951 := by
  unfold tailWord_1561032
  simp only [CollatzResearch.WordTrace]
  refine ⟨28467757240327570942678675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37957009653770094590238233 28467757240327570942678675)
  ·
    refine ⟨42701635860491356414018013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28467757240327570942678675 42701635860491356414018013)
    ·
      refine ⟨16013113447684258655256755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42701635860491356414018013 16013113447684258655256755)
      ·
        refine ⟨24019670171526387982885133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16013113447684258655256755 24019670171526387982885133)
        ·
          refine ⟨9007376314322395493581925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24019670171526387982885133 9007376314322395493581925)
          ·
            refine ⟨1688883058935449155046611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9007376314322395493581925 1688883058935449155046611)
            ·
              refine ⟨2533324588403173732569917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1688883058935449155046611 2533324588403173732569917)
              ·
                refine ⟨949996720651190149713719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2533324588403173732569917 949996720651190149713719)
                ·
                  refine ⟨1424995080976785224570579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 949996720651190149713719 1424995080976785224570579)
                  ·
                    refine ⟨2137492621465177836855869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1424995080976785224570579 2137492621465177836855869)
                    ·
                      refine ⟨801559733049441688820951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2137492621465177836855869 801559733049441688820951)
                      ·
                        rfl

theorem cell23_1561032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 1, 1, 3].length) (baseStart_1561032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561032 prefixEnd_1561032 := by exact prefixLift 1561032
  have htrace : WordTrace (prefixWord ++ tailWord_1561032) baseStart_1561032 baseEnd_1561032 := by
    simpa [prefixWord, tailWord_1561032, baseEnd_1561032] using wordTrace_append hprefix tailTrace_1561032
  have hstable : (prefixWord ++ tailWord_1561032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561032).length < 2 ^ (prefixWord ++ tailWord_1561032).sum := by decide
  have hdescent : baseEnd_1561032 < baseStart_1561032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561042 : List Nat := [3, 2, 2, 4, 1, 1, 1, 2, 2, 3, 2]
def baseStart_1561042 : Nat := 118140960795 + 1561042 * 2 ^ 59
def prefixEnd_1561042 : Nat := 4983230072969 + 3 ^ 40 * 1561042 * 2
def baseEnd_1561042 : Nat := 801564867855986649695905

theorem tailTrace_1561042 : CollatzResearch.WordTrace tailWord_1561042 prefixEnd_1561042 801564867855986649695905 := by
  unfold tailWord_1561042
  simp only [CollatzResearch.WordTrace]
  refine ⟨14233969802654728398305345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37957252807079275728814253 14233969802654728398305345)
  ·
    refine ⟨10675477351991046298729009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14233969802654728398305345 10675477351991046298729009)
    ·
      refine ⟨8006608013993284724046757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10675477351991046298729009 8006608013993284724046757)
      ·
        refine ⟨1501239002623740885758767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8006608013993284724046757 1501239002623740885758767)
        ·
          refine ⟨2251858503935611328638151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1501239002623740885758767 2251858503935611328638151)
          ·
            refine ⟨3377787755903416992957227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2251858503935611328638151 3377787755903416992957227)
            ·
              refine ⟨5066681633855125489435841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3377787755903416992957227 5066681633855125489435841)
              ·
                refine ⟨3800011225391344117076881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5066681633855125489435841 3800011225391344117076881)
                ·
                  refine ⟨2850008419043508087807661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3800011225391344117076881 2850008419043508087807661)
                  ·
                    refine ⟨1068753157141315532927873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2850008419043508087807661 1068753157141315532927873)
                    ·
                      refine ⟨801564867855986649695905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1068753157141315532927873 801564867855986649695905)
                      ·
                        rfl

theorem cell23_1561042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_1561042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561042 prefixEnd_1561042 := by exact prefixLift 1561042
  have htrace : WordTrace (prefixWord ++ tailWord_1561042) baseStart_1561042 baseEnd_1561042 := by
    simpa [prefixWord, tailWord_1561042, baseEnd_1561042] using wordTrace_append hprefix tailTrace_1561042
  have hstable : (prefixWord ++ tailWord_1561042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561042).length < 2 ^ (prefixWord ++ tailWord_1561042).sum := by decide
  have hdescent : baseEnd_1561042 < baseStart_1561042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561055 : List Nat := [1, 1, 2, 3, 3, 2, 3, 1, 3, 2, 2]
def baseStart_1561055 : Nat := 118140960795 + 1561055 * 2 ^ 59
def prefixEnd_1561055 : Nat := 4983230072969 + 3 ^ 40 * 1561055 * 2
def baseEnd_1561055 : Nat := 801571543104495098833345

theorem tailTrace_1561055 : CollatzResearch.WordTrace tailWord_1561055 prefixEnd_1561055 801571543104495098833345 := by
  unfold tailWord_1561055
  simp only [CollatzResearch.WordTrace]
  refine ⟨56936353359571816813444619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37957568906381211208963079 56936353359571816813444619)
  ·
    refine ⟨85404530039357725220166929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56936353359571816813444619 85404530039357725220166929)
    ·
      refine ⟨64053397529518293915125197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85404530039357725220166929 64053397529518293915125197)
      ·
        refine ⟨24020024073569360218171949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64053397529518293915125197 24020024073569360218171949)
        ·
          refine ⟨9007509027588510081814481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24020024073569360218171949 9007509027588510081814481)
          ·
            refine ⟨6755631770691382561360861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9007509027588510081814481 6755631770691382561360861)
            ·
              refine ⟨2533361914009268460510323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6755631770691382561360861 2533361914009268460510323)
              ·
                refine ⟨3800042871013902690765485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2533361914009268460510323 3800042871013902690765485)
                ·
                  refine ⟨1425016076630213509037057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3800042871013902690765485 1425016076630213509037057)
                  ·
                    refine ⟨1068762057472660131777793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1425016076630213509037057 1068762057472660131777793)
                    ·
                      refine ⟨801571543104495098833345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1068762057472660131777793 801571543104495098833345)
                      ·
                        rfl

theorem cell23_1561055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 2, 2].length) (baseStart_1561055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561055 prefixEnd_1561055 := by exact prefixLift 1561055
  have htrace : WordTrace (prefixWord ++ tailWord_1561055) baseStart_1561055 baseEnd_1561055 := by
    simpa [prefixWord, tailWord_1561055, baseEnd_1561055] using wordTrace_append hprefix tailTrace_1561055
  have hstable : (prefixWord ++ tailWord_1561055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561055).length < 2 ^ (prefixWord ++ tailWord_1561055).sum := by decide
  have hdescent : baseEnd_1561055 < baseStart_1561055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561071 : List Nat := [1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 3]
def baseStart_1561071 : Nat := 118140960795 + 1561071 * 2 ^ 59
def prefixEnd_1561071 : Nat := 4983230072969 + 3 ^ 40 * 1561071 * 2
def baseEnd_1561071 : Nat := 801579758794967036233271

theorem tailTrace_1561071 : CollatzResearch.WordTrace tailWord_1561071 prefixEnd_1561071 801579758794967036233271 := by
  unfold tailWord_1561071
  simp only [CollatzResearch.WordTrace]
  refine ⟨56936936927513851546027067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37957957951675901030684711 56936936927513851546027067)
  ·
    refine ⟨85405405391270777319040601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56936936927513851546027067 85405405391270777319040601)
    ·
      refine ⟨64054054043453082989280451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85405405391270777319040601 64054054043453082989280451)
      ·
        refine ⟨96081081065179624483920677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64054054043453082989280451 96081081065179624483920677)
        ·
          refine ⟨18015202699721179590735127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96081081065179624483920677 18015202699721179590735127)
          ·
            refine ⟨27022804049581769386102691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18015202699721179590735127 27022804049581769386102691)
            ·
              refine ⟨40534206074372654079154037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27022804049581769386102691 40534206074372654079154037)
              ·
                refine ⟨3800081819472436319920691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40534206074372654079154037 3800081819472436319920691)
                ·
                  refine ⟨5700122729208654479881037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3800081819472436319920691 5700122729208654479881037)
                  ·
                    refine ⟨2137546023453245429955389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5700122729208654479881037 2137546023453245429955389)
                    ·
                      refine ⟨801579758794967036233271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2137546023453245429955389 801579758794967036233271)
                      ·
                        rfl

theorem cell23_1561071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 3].length) (baseStart_1561071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561071 prefixEnd_1561071 := by exact prefixLift 1561071
  have htrace : WordTrace (prefixWord ++ tailWord_1561071) baseStart_1561071 baseEnd_1561071 := by
    simpa [prefixWord, tailWord_1561071, baseEnd_1561071] using wordTrace_append hprefix tailTrace_1561071
  have hstable : (prefixWord ++ tailWord_1561071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561071).length < 2 ^ (prefixWord ++ tailWord_1561071).sum := by decide
  have hdescent : baseEnd_1561071 < baseStart_1561071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561092 : List Nat := [2, 3, 2, 3, 1, 2, 3, 1, 1, 2, 3]
def baseStart_1561092 : Nat := 118140960795 + 1561092 * 2 ^ 59
def prefixEnd_1561092 : Nat := 4983230072969 + 3 ^ 40 * 1561092 * 2
def baseEnd_1561092 : Nat := 801590541888711454070675

theorem tailTrace_1561092 : CollatzResearch.WordTrace tailWord_1561092 prefixEnd_1561092 801590541888711454070675 := by
  unfold tailWord_1561092
  simp only [CollatzResearch.WordTrace]
  refine ⟨28468851430218886066270765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37958468573625181421694353 28468851430218886066270765)
  ·
    refine ⟨10675819286332082274851537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28468851430218886066270765 10675819286332082274851537)
    ·
      refine ⟨8006864464749061706138653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10675819286332082274851537 8006864464749061706138653)
      ·
        refine ⟨3002574174280898139801995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8006864464749061706138653 3002574174280898139801995)
        ·
          refine ⟨4503861261421347209702993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3002574174280898139801995 4503861261421347209702993)
          ·
            refine ⟨3377895946066010407277245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4503861261421347209702993 3377895946066010407277245)
            ·
              refine ⟨1266710979774753902728967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3377895946066010407277245 1266710979774753902728967)
              ·
                refine ⟨1900066469662130854093451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1266710979774753902728967 1900066469662130854093451)
                ·
                  refine ⟨2850099704493196281140177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1900066469662130854093451 2850099704493196281140177)
                  ·
                    refine ⟨2137574778369897210855133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2850099704493196281140177 2137574778369897210855133)
                    ·
                      refine ⟨801590541888711454070675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2137574778369897210855133 801590541888711454070675)
                      ·
                        rfl

theorem cell23_1561092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_1561092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561092 prefixEnd_1561092 := by exact prefixLift 1561092
  have htrace : WordTrace (prefixWord ++ tailWord_1561092) baseStart_1561092 baseEnd_1561092 := by
    simpa [prefixWord, tailWord_1561092, baseEnd_1561092] using wordTrace_append hprefix tailTrace_1561092
  have hstable : (prefixWord ++ tailWord_1561092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561092).length < 2 ^ (prefixWord ++ tailWord_1561092).sum := by decide
  have hdescent : baseEnd_1561092 < baseStart_1561092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561108 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 2, 7]
def baseStart_1561108 : Nat := 118140960795 + 1561108 * 2 ^ 59
def prefixEnd_1561108 : Nat := 4983230072969 + 3 ^ 40 * 1561108 * 2
def baseEnd_1561108 : Nat := 267199585859727797156867

theorem tailTrace_1561108 : CollatzResearch.WordTrace tailWord_1561108 prefixEnd_1561108 267199585859727797156867 := by
  unfold tailWord_1561108
  simp only [CollatzResearch.WordTrace]
  refine ⟨28469143214189903432561989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37958857618919871243415985 28469143214189903432561989)
  ·
    refine ⟨5337964352660606893605373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28469143214189903432561989 5337964352660606893605373)
    ·
      refine ⟨2001736632247727585102015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5337964352660606893605373 2001736632247727585102015)
      ·
        refine ⟨3002604948371591377653023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2001736632247727585102015 3002604948371591377653023)
        ·
          refine ⟨4503907422557387066479535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3002604948371591377653023 4503907422557387066479535)
          ·
            refine ⟨6755861133836080599719303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4503907422557387066479535 6755861133836080599719303)
            ·
              refine ⟨10133791700754120899578955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6755861133836080599719303 10133791700754120899578955)
              ·
                refine ⟨15200687551131181349368433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10133791700754120899578955 15200687551131181349368433)
                ·
                  refine ⟨11400515663348386012026325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15200687551131181349368433 11400515663348386012026325)
                  ·
                    refine ⟨267199585859727797156867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11400515663348386012026325 267199585859727797156867)
                    ·
                      rfl

theorem cell23_1561108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_1561108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561108 prefixEnd_1561108 := by exact prefixLift 1561108
  have htrace : WordTrace (prefixWord ++ tailWord_1561108) baseStart_1561108 baseEnd_1561108 := by
    simpa [prefixWord, tailWord_1561108, baseEnd_1561108] using wordTrace_append hprefix tailTrace_1561108
  have hstable : (prefixWord ++ tailWord_1561108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561108).length < 2 ^ (prefixWord ++ tailWord_1561108).sum := by decide
  have hdescent : baseEnd_1561108 < baseStart_1561108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561121 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 2, 6]
def baseStart_1561121 : Nat := 118140960795 + 1561121 * 2 ^ 59
def prefixEnd_1561121 : Nat := 4983230072969 + 3 ^ 40 * 1561121 * 2
def baseEnd_1561121 : Nat := 267201810942563946869347

theorem tailTrace_1561121 : CollatzResearch.WordTrace tailWord_1561121 prefixEnd_1561121 267201810942563946869347 := by
  unfold tailWord_1561121
  simp only [CollatzResearch.WordTrace]
  refine ⟨56938760577332710085347217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37959173718221806723564811 56938760577332710085347217)
  ·
    refine ⟨42704070432999532564010413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56938760577332710085347217 42704070432999532564010413)
    ·
      refine ⟨16014026412374824711503905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42704070432999532564010413 16014026412374824711503905)
      ·
        refine ⟨12010519809281118533627929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16014026412374824711503905 12010519809281118533627929)
        ·
          refine ⟨9007889856960838900220947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12010519809281118533627929 9007889856960838900220947)
          ·
            refine ⟨13511834785441258350331421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9007889856960838900220947 13511834785441258350331421)
            ·
              refine ⟨5066938044540471881374283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13511834785441258350331421 5066938044540471881374283)
              ·
                refine ⟨7600407066810707822061425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5066938044540471881374283 7600407066810707822061425)
                ·
                  refine ⟨5700305300108030866546069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7600407066810707822061425 5700305300108030866546069)
                  ·
                    refine ⟨267201810942563946869347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5700305300108030866546069 267201810942563946869347)
                    ·
                      rfl

theorem cell23_1561121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_1561121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561121 prefixEnd_1561121 := by exact prefixLift 1561121
  have htrace : WordTrace (prefixWord ++ tailWord_1561121) baseStart_1561121 baseEnd_1561121 := by
    simpa [prefixWord, tailWord_1561121, baseEnd_1561121] using wordTrace_append hprefix tailTrace_1561121
  have hstable : (prefixWord ++ tailWord_1561121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561121).length < 2 ^ (prefixWord ++ tailWord_1561121).sum := by decide
  have hdescent : baseEnd_1561121 < baseStart_1561121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561141 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_1561141 : Nat := 118140960795 + 1561141 * 2 ^ 59
def prefixEnd_1561141 : Nat := 4983230072969 + 3 ^ 40 * 1561141 * 2
def baseEnd_1561141 : Nat := 801615702440781762357949

theorem tailTrace_1561141 : CollatzResearch.WordTrace tailWord_1561141 prefixEnd_1561141 801615702440781762357949 := by
  unfold tailWord_1561141
  simp only [CollatzResearch.WordTrace]
  refine ⟨56939490037260253501075277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37959660024840169000716851 56939490037260253501075277)
  ·
    refine ⟨21352308763972595062903229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56939490037260253501075277 21352308763972595062903229)
    ·
      refine ⟨8007115786489723148588711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21352308763972595062903229 8007115786489723148588711)
      ·
        refine ⟨12010673679734584722883067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8007115786489723148588711 12010673679734584722883067)
        ·
          refine ⟨18016010519601877084324601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12010673679734584722883067 18016010519601877084324601)
          ·
            refine ⟨13512007889701407813243451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18016010519601877084324601 13512007889701407813243451)
            ·
              refine ⟨20268011834552111719865177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13512007889701407813243451 20268011834552111719865177)
              ·
                refine ⟨15201008875914083789898883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20268011834552111719865177 15201008875914083789898883)
                ·
                  refine ⟨22801513313871125684848325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15201008875914083789898883 22801513313871125684848325)
                  ·
                    refine ⟨4275283746350836065909061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22801513313871125684848325 4275283746350836065909061)
                    ·
                      refine ⟨801615702440781762357949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4275283746350836065909061 801615702440781762357949)
                      ·
                        rfl

theorem cell23_1561141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_1561141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561141 prefixEnd_1561141 := by exact prefixLift 1561141
  have htrace : WordTrace (prefixWord ++ tailWord_1561141) baseStart_1561141 baseEnd_1561141 := by
    simpa [prefixWord, tailWord_1561141, baseEnd_1561141] using wordTrace_append hprefix tailTrace_1561141
  have hstable : (prefixWord ++ tailWord_1561141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561141).length < 2 ^ (prefixWord ++ tailWord_1561141).sum := by decide
  have hdescent : baseEnd_1561141 < baseStart_1561141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561145 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 4, 2, 2]
def baseStart_1561145 : Nat := 118140960795 + 1561145 * 2 ^ 59
def prefixEnd_1561145 : Nat := 4983230072969 + 3 ^ 40 * 1561145 * 2
def baseEnd_1561145 : Nat := 801617756363399746707931

theorem tailTrace_1561145 : CollatzResearch.WordTrace tailWord_1561145 prefixEnd_1561145 801617756363399746707931 := by
  unfold tailWord_1561145
  simp only [CollatzResearch.WordTrace]
  refine ⟨56939635929245762184220889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37959757286163841456147259 56939635929245762184220889)
  ·
    refine ⟨42704726946934321638165667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56939635929245762184220889 42704726946934321638165667)
    ·
      refine ⟨64057090420401482457248501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42704726946934321638165667 64057090420401482457248501)
      ·
        refine ⟨6005352226912638980367047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64057090420401482457248501 6005352226912638980367047)
        ·
          refine ⟨9008028340368958470550571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6005352226912638980367047 9008028340368958470550571)
          ·
            refine ⟨13512042510553437705825857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9008028340368958470550571 13512042510553437705825857)
            ·
              refine ⟨10134031882915078279369393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13512042510553437705825857 10134031882915078279369393)
              ·
                refine ⟨7600523912186308709527045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10134031882915078279369393 7600523912186308709527045)
                ·
                  refine ⟨1425098233534932883036321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7600523912186308709527045 1425098233534932883036321)
                  ·
                    refine ⟨1068823675151199662277241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1425098233534932883036321 1068823675151199662277241)
                    ·
                      refine ⟨801617756363399746707931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1068823675151199662277241 801617756363399746707931)
                      ·
                        rfl

theorem cell23_1561145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_1561145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561145 prefixEnd_1561145 := by exact prefixLift 1561145
  have htrace : WordTrace (prefixWord ++ tailWord_1561145) baseStart_1561145 baseEnd_1561145 := by
    simpa [prefixWord, tailWord_1561145, baseEnd_1561145] using wordTrace_append hprefix tailTrace_1561145
  have hstable : (prefixWord ++ tailWord_1561145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561145).length < 2 ^ (prefixWord ++ tailWord_1561145).sum := by decide
  have hdescent : baseEnd_1561145 < baseStart_1561145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561149 : List Nat := [1, 4, 1, 3, 2, 3, 2, 1, 1, 3, 2]
def baseStart_1561149 : Nat := 118140960795 + 1561149 * 2 ^ 59
def prefixEnd_1561149 : Nat := 4983230072969 + 3 ^ 40 * 1561149 * 2
def baseEnd_1561149 : Nat := 801619810286017731057913

theorem tailTrace_1561149 : CollatzResearch.WordTrace tailWord_1561149 prefixEnd_1561149 801619810286017731057913 := by
  unfold tailWord_1561149
  simp only [CollatzResearch.WordTrace]
  refine ⟨56939781821231270867366501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37959854547487513911577667 56939781821231270867366501)
  ·
    refine ⟨10676209091480863287631219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56939781821231270867366501 10676209091480863287631219)
    ·
      refine ⟨16014313637221294931446829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10676209091480863287631219 16014313637221294931446829)
      ·
        refine ⟨6005367613957985599292561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16014313637221294931446829 6005367613957985599292561)
        ·
          refine ⟨4504025710468489199469421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6005367613957985599292561 4504025710468489199469421)
          ·
            refine ⟨1689009641425683449801033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4504025710468489199469421 1689009641425683449801033)
            ·
              refine ⟨1266757231069262587350775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1689009641425683449801033 1266757231069262587350775)
              ·
                refine ⟨1900135846603893881026163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1266757231069262587350775 1900135846603893881026163)
                ·
                  refine ⟨2850203769905840821539245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1900135846603893881026163 2850203769905840821539245)
                  ·
                    refine ⟨1068826413714690308077217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2850203769905840821539245 1068826413714690308077217)
                    ·
                      refine ⟨801619810286017731057913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1068826413714690308077217 801619810286017731057913)
                      ·
                        rfl

theorem cell23_1561149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_1561149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561149 prefixEnd_1561149 := by exact prefixLift 1561149
  have htrace : WordTrace (prefixWord ++ tailWord_1561149) baseStart_1561149 baseEnd_1561149 := by
    simpa [prefixWord, tailWord_1561149, baseEnd_1561149] using wordTrace_append hprefix tailTrace_1561149
  have hstable : (prefixWord ++ tailWord_1561149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561149).length < 2 ^ (prefixWord ++ tailWord_1561149).sum := by decide
  have hdescent : baseEnd_1561149 < baseStart_1561149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561162 : List Nat := [3, 1, 2, 1, 1, 4, 3, 2, 2, 2, 2]
def baseStart_1561162 : Nat := 118140960795 + 1561162 * 2 ^ 59
def prefixEnd_1561162 : Nat := 4983230072969 + 3 ^ 40 * 1561162 * 2
def baseEnd_1561162 : Nat := 801626485534526180195353

theorem tailTrace_1561162 : CollatzResearch.WordTrace tailWord_1561162 prefixEnd_1561162 801626485534526180195353 := by
  unfold tailWord_1561162
  simp only [CollatzResearch.WordTrace]
  refine ⟨14235063992546043521897435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37960170646789449391726493 14235063992546043521897435)
  ·
    refine ⟨21352595988819065282846153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14235063992546043521897435 21352595988819065282846153)
    ·
      refine ⟨16014446991614298962134615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21352595988819065282846153 16014446991614298962134615)
      ·
        refine ⟨24021670487421448443201923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16014446991614298962134615 24021670487421448443201923)
        ·
          refine ⟨36032505731132172664802885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24021670487421448443201923 36032505731132172664802885)
          ·
            refine ⟨6756094824587282374650541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36032505731132172664802885 6756094824587282374650541)
            ·
              refine ⟨2533535559220230890493953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6756094824587282374650541 2533535559220230890493953)
              ·
                refine ⟨1900151669415173167870465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2533535559220230890493953 1900151669415173167870465)
                ·
                  refine ⟨1425113752061379875902849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1900151669415173167870465 1425113752061379875902849)
                  ·
                    refine ⟨1068835314046034906927137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1425113752061379875902849 1068835314046034906927137)
                    ·
                      refine ⟨801626485534526180195353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1068835314046034906927137 801626485534526180195353)
                      ·
                        rfl

theorem cell23_1561162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 2, 2, 2].length) (baseStart_1561162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561162 prefixEnd_1561162 := by exact prefixLift 1561162
  have htrace : WordTrace (prefixWord ++ tailWord_1561162) baseStart_1561162 baseEnd_1561162 := by
    simpa [prefixWord, tailWord_1561162, baseEnd_1561162] using wordTrace_append hprefix tailTrace_1561162
  have hstable : (prefixWord ++ tailWord_1561162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561162).length < 2 ^ (prefixWord ++ tailWord_1561162).sum := by decide
  have hdescent : baseEnd_1561162 < baseStart_1561162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561191 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_1561191 : Nat := 118140960795 + 1561191 * 2 ^ 59
def prefixEnd_1561191 : Nat := 4983230072969 + 3 ^ 40 * 1561191 * 2
def baseEnd_1561191 : Nat := 801641376473506566732719

theorem tailTrace_1561191 : CollatzResearch.WordTrace tailWord_1561191 prefixEnd_1561191 801641376473506566732719 := by
  unfold tailWord_1561191
  simp only [CollatzResearch.WordTrace]
  refine ⟨56941313687079112040395427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37960875791386074693596951 56941313687079112040395427)
  ·
    refine ⟨85411970530618668060593141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56941313687079112040395427 85411970530618668060593141)
    ·
      refine ⟨8007372237245500130680607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85411970530618668060593141 8007372237245500130680607)
      ·
        refine ⟨12011058355868250196020911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8007372237245500130680607 12011058355868250196020911)
        ·
          refine ⟨18016587533802375294031367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12011058355868250196020911 18016587533802375294031367)
          ·
            refine ⟨27024881300703562941047051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18016587533802375294031367 27024881300703562941047051)
            ·
              refine ⟨40537321951055344411570577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27024881300703562941047051 40537321951055344411570577)
              ·
                refine ⟨30402991463291508308677933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40537321951055344411570577 30402991463291508308677933)
                ·
                  refine ⟨11401121798734315615754225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30402991463291508308677933 11401121798734315615754225)
                  ·
                    refine ⟨8550841349050736711815669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11401121798734315615754225 8550841349050736711815669)
                    ·
                      refine ⟨801641376473506566732719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8550841349050736711815669 801641376473506566732719)
                      ·
                        rfl

theorem cell23_1561191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_1561191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561191 prefixEnd_1561191 := by exact prefixLift 1561191
  have htrace : WordTrace (prefixWord ++ tailWord_1561191) baseStart_1561191 baseEnd_1561191 := by
    simpa [prefixWord, tailWord_1561191, baseEnd_1561191] using wordTrace_append hprefix tailTrace_1561191
  have hstable : (prefixWord ++ tailWord_1561191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561191).length < 2 ^ (prefixWord ++ tailWord_1561191).sum := by decide
  have hdescent : baseEnd_1561191 < baseStart_1561191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561198 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 1, 7]
def baseStart_1561198 : Nat := 118140960795 + 1561198 * 2 ^ 59
def prefixEnd_1561198 : Nat := 4983230072969 + 3 ^ 40 * 1561198 * 2
def baseEnd_1561198 : Nat := 267214990279362679781729

theorem tailTrace_1561198 : CollatzResearch.WordTrace tailWord_1561198 prefixEnd_1561198 267214990279362679781729 := by
  unfold tailWord_1561198
  simp only [CollatzResearch.WordTrace]
  refine ⟨7117696124756719029487531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37961045998702501490600165 7117696124756719029487531)
  ·
    refine ⟨10676544187135078544231297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7117696124756719029487531 10676544187135078544231297)
    ·
      refine ⟨8007408140351308908173473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10676544187135078544231297 8007408140351308908173473)
      ·
        refine ⟨6005556105263481681130105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8007408140351308908173473 6005556105263481681130105)
        ·
          refine ⟨4504167078947611260847579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6005556105263481681130105 4504167078947611260847579)
          ·
            refine ⟨6756250618421416891271369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4504167078947611260847579 6756250618421416891271369)
            ·
              refine ⟨5067187963816062668453527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6756250618421416891271369 5067187963816062668453527)
              ·
                refine ⟨7600781945724094002680291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5067187963816062668453527 7600781945724094002680291)
                ·
                  refine ⟨11401172918586141004020437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7600781945724094002680291 11401172918586141004020437)
                  ·
                    refine ⟨267214990279362679781729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11401172918586141004020437 267214990279362679781729)
                    ·
                      rfl

theorem cell23_1561198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_1561198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561198 prefixEnd_1561198 := by exact prefixLift 1561198
  have htrace : WordTrace (prefixWord ++ tailWord_1561198) baseStart_1561198 baseEnd_1561198 := by
    simpa [prefixWord, tailWord_1561198, baseEnd_1561198] using wordTrace_append hprefix tailTrace_1561198
  have hstable : (prefixWord ++ tailWord_1561198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561198).length < 2 ^ (prefixWord ++ tailWord_1561198).sum := by decide
  have hdescent : baseEnd_1561198 < baseStart_1561198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561202 : List Nat := [3, 2, 1, 2, 4, 2, 1, 3, 5]
def baseStart_1561202 : Nat := 118140960795 + 1561202 * 2 ^ 59
def prefixEnd_1561202 : Nat := 4983230072969 + 3 ^ 40 * 1561202 * 2
def baseEnd_1561202 : Nat := 89071891640078447077241

theorem tailTrace_1561202 : CollatzResearch.WordTrace tailWord_1561202 prefixEnd_1561202 89071891640078447077241 := by
  unfold tailWord_1561202
  simp only [CollatzResearch.WordTrace]
  refine ⟨14235428722509815229761465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37961143260026173946030573 14235428722509815229761465)
  ·
    refine ⟨10676571541882361422321099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14235428722509815229761465 10676571541882361422321099)
    ·
      refine ⟨16014857312823542133481649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10676571541882361422321099 16014857312823542133481649)
      ·
        refine ⟨12011142984617656600111237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16014857312823542133481649 12011142984617656600111237)
        ·
          refine ⟨2252089309615810612520857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12011142984617656600111237 2252089309615810612520857)
          ·
            refine ⟨1689066982211857959390643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2252089309615810612520857 1689066982211857959390643)
            ·
              refine ⟨2533600473317786939085965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1689066982211857959390643 2533600473317786939085965)
              ·
                refine ⟨950100177494170102157237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2533600473317786939085965 950100177494170102157237)
                ·
                  refine ⟨89071891640078447077241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 950100177494170102157237 89071891640078447077241)
                  ·
                    rfl

theorem cell23_1561202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_1561202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561202 prefixEnd_1561202 := by exact prefixLift 1561202
  have htrace : WordTrace (prefixWord ++ tailWord_1561202) baseStart_1561202 baseEnd_1561202 := by
    simpa [prefixWord, tailWord_1561202, baseEnd_1561202] using wordTrace_append hprefix tailTrace_1561202
  have hstable : (prefixWord ++ tailWord_1561202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561202).length < 2 ^ (prefixWord ++ tailWord_1561202).sum := by decide
  have hdescent : baseEnd_1561202 < baseStart_1561202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561228 : List Nat := [2, 2, 1, 2, 1, 1, 2, 5, 3, 4]
def baseStart_1561228 : Nat := 118140960795 + 1561228 * 2 ^ 59
def prefixEnd_1561228 : Nat := 4983230072969 + 3 ^ 40 * 1561228 * 2
def baseEnd_1561228 : Nat := 267220125085907640656683

theorem tailTrace_1561228 : CollatzResearch.WordTrace tailWord_1561228 prefixEnd_1561228 267220125085907640656683 := by
  unfold tailWord_1561228
  simp only [CollatzResearch.WordTrace]
  refine ⟨28471331593972533679746169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37961775458630044906328225 28471331593972533679746169)
  ·
    refine ⟨21353498695479400259809627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28471331593972533679746169 21353498695479400259809627)
    ·
      refine ⟨32030248043219100389714441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21353498695479400259809627 32030248043219100389714441)
      ·
        refine ⟨24022686032414325292285831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32030248043219100389714441 24022686032414325292285831)
        ·
          refine ⟨36034029048621487938428747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24022686032414325292285831 36034029048621487938428747)
          ·
            refine ⟨54051043572932231907643121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36034029048621487938428747 54051043572932231907643121)
            ·
              refine ⟨40538282679699173930732341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54051043572932231907643121 40538282679699173930732341)
              ·
                refine ⟨3800464001221797556006157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40538282679699173930732341 3800464001221797556006157)
                ·
                  refine ⟨1425174000458174083502309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3800464001221797556006157 1425174000458174083502309)
                  ·
                    refine ⟨267220125085907640656683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1425174000458174083502309 267220125085907640656683)
                    ·
                      rfl

theorem cell23_1561228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 3, 4].length) (baseStart_1561228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561228 prefixEnd_1561228 := by exact prefixLift 1561228
  have htrace : WordTrace (prefixWord ++ tailWord_1561228) baseStart_1561228 baseEnd_1561228 := by
    simpa [prefixWord, tailWord_1561228, baseEnd_1561228] using wordTrace_append hprefix tailTrace_1561228
  have hstable : (prefixWord ++ tailWord_1561228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561228).length < 2 ^ (prefixWord ++ tailWord_1561228).sum := by decide
  have hdescent : baseEnd_1561228 < baseStart_1561228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561278 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_1561278 : Nat := 118140960795 + 1561278 * 2 ^ 59
def prefixEnd_1561278 : Nat := 4983230072969 + 3 ^ 40 * 1561278 * 2
def baseEnd_1561278 : Nat := 801686049290447726344819

theorem tailTrace_1561278 : CollatzResearch.WordTrace tailWord_1561278 prefixEnd_1561278 801686049290447726344819 := by
  unfold tailWord_1561278
  simp only [CollatzResearch.WordTrace]
  refine ⟨7118060854720490737351561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37962991225175950599208325 7118060854720490737351561)
  ·
    refine ⟨5338545641040368053013671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7118060854720490737351561 5338545641040368053013671)
    ·
      refine ⟨8007818461560552079520507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5338545641040368053013671 8007818461560552079520507)
      ·
        refine ⟨12011727692340828119280761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8007818461560552079520507 12011727692340828119280761)
        ·
          refine ⟨9008795769255621089460571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12011727692340828119280761 9008795769255621089460571)
          ·
            refine ⟨13513193653883431634190857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9008795769255621089460571 13513193653883431634190857)
            ·
              refine ⟨10134895240412573725643143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13513193653883431634190857 10134895240412573725643143)
              ·
                refine ⟨15202342860618860588464715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10134895240412573725643143 15202342860618860588464715)
                ·
                  refine ⟨22803514290928290882697073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15202342860618860588464715 22803514290928290882697073)
                  ·
                    refine ⟨17102635718196218162022805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22803514290928290882697073 17102635718196218162022805)
                    ·
                      refine ⟨801686049290447726344819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17102635718196218162022805 801686049290447726344819)
                      ·
                        rfl

theorem cell23_1561278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_1561278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561278 prefixEnd_1561278 := by exact prefixLift 1561278
  have htrace : WordTrace (prefixWord ++ tailWord_1561278) baseStart_1561278 baseEnd_1561278 := by
    simpa [prefixWord, tailWord_1561278, baseEnd_1561278] using wordTrace_append hprefix tailTrace_1561278
  have hstable : (prefixWord ++ tailWord_1561278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561278).length < 2 ^ (prefixWord ++ tailWord_1561278).sum := by decide
  have hdescent : baseEnd_1561278 < baseStart_1561278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561279 : List Nat := [1, 1, 2, 2, 2, 6, 2, 2, 1, 4]
def baseStart_1561279 : Nat := 118140960795 + 1561279 * 2 ^ 59
def prefixEnd_1561279 : Nat := 4983230072969 + 3 ^ 40 * 1561279 * 2
def baseEnd_1561279 : Nat := 267228854257034074144105

theorem tailTrace_1561279 : CollatzResearch.WordTrace tailWord_1561279 prefixEnd_1561279 267228854257034074144105 := by
  unfold tailWord_1561279
  simp only [CollatzResearch.WordTrace]
  refine ⟨56944523310760303069598891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37963015540506868713065927 56944523310760303069598891)
  ·
    refine ⟨85416784966140454604398337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56944523310760303069598891 85416784966140454604398337)
    ·
      refine ⟨64062588724605340953298753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85416784966140454604398337 64062588724605340953298753)
      ·
        refine ⟨48046941543454005714974065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64062588724605340953298753 48046941543454005714974065)
        ·
          refine ⟨36035206157590504286230549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48046941543454005714974065 36035206157590504286230549)
          ·
            refine ⟨1689150288637054888417057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36035206157590504286230549 1689150288637054888417057)
            ·
              refine ⟨1266862716477791166312793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1689150288637054888417057 1266862716477791166312793)
              ·
                refine ⟨950147037358343374734595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1266862716477791166312793 950147037358343374734595)
                ·
                  refine ⟨1425220556037515062101893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 950147037358343374734595 1425220556037515062101893)
                  ·
                    refine ⟨267228854257034074144105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1425220556037515062101893 267228854257034074144105)
                    ·
                      rfl

theorem cell23_1561279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 1, 4].length) (baseStart_1561279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561279 prefixEnd_1561279 := by exact prefixLift 1561279
  have htrace : WordTrace (prefixWord ++ tailWord_1561279) baseStart_1561279 baseEnd_1561279 := by
    simpa [prefixWord, tailWord_1561279, baseEnd_1561279] using wordTrace_append hprefix tailTrace_1561279
  have hstable : (prefixWord ++ tailWord_1561279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561279).length < 2 ^ (prefixWord ++ tailWord_1561279).sum := by decide
  have hdescent : baseEnd_1561279 < baseStart_1561279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561286 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_1561286 : Nat := 118140960795 + 1561286 * 2 ^ 59
def prefixEnd_1561286 : Nat := 4983230072969 + 3 ^ 40 * 1561286 * 2
def baseEnd_1561286 : Nat := 801690157135683695044783

theorem tailTrace_1561286 : CollatzResearch.WordTrace tailWord_1561286 prefixEnd_1561286 801690157135683695044783 := by
  unfold tailWord_1561286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1779524331929216977034491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37963185747823295510069141 1779524331929216977034491)
  ·
    refine ⟨2669286497893825465551737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1779524331929216977034491 2669286497893825465551737)
    ·
      refine ⟨2001964873420369099163803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2669286497893825465551737 2001964873420369099163803)
      ·
        refine ⟨3002947310130553648745705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2001964873420369099163803 3002947310130553648745705)
        ·
          refine ⟨2252210482597915236559279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3002947310130553648745705 2252210482597915236559279)
          ·
            refine ⟨3378315723896872854838919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2252210482597915236559279 3378315723896872854838919)
            ·
              refine ⟨5067473585845309282258379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3378315723896872854838919 5067473585845309282258379)
              ·
                refine ⟨7601210378767963923387569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5067473585845309282258379 7601210378767963923387569)
                ·
                  refine ⟨5700907784075972942540677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7601210378767963923387569 5700907784075972942540677)
                  ·
                    refine ⟨1068920209514244926726377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5700907784075972942540677 1068920209514244926726377)
                    ·
                      refine ⟨801690157135683695044783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1068920209514244926726377 801690157135683695044783)
                      ·
                        rfl

theorem cell23_1561286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_1561286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561286 prefixEnd_1561286 := by exact prefixLift 1561286
  have htrace : WordTrace (prefixWord ++ tailWord_1561286) baseStart_1561286 baseEnd_1561286 := by
    simpa [prefixWord, tailWord_1561286, baseEnd_1561286] using wordTrace_append hprefix tailTrace_1561286
  have hstable : (prefixWord ++ tailWord_1561286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561286).length < 2 ^ (prefixWord ++ tailWord_1561286).sum := by decide
  have hdescent : baseEnd_1561286 < baseStart_1561286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561288 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 3, 5]
def baseStart_1561288 : Nat := 118140960795 + 1561288 * 2 ^ 59
def prefixEnd_1561288 : Nat := 4983230072969 + 3 ^ 40 * 1561288 * 2
def baseEnd_1561288 : Nat := 267230394698997562406591

theorem tailTrace_1561288 : CollatzResearch.WordTrace tailWord_1561288 prefixEnd_1561288 267230394698997562406591 := by
  unfold tailWord_1561288
  simp only [CollatzResearch.WordTrace]
  refine ⟨28472425783863848803338259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37963234378485131737784345 28472425783863848803338259)
  ·
    refine ⟨42708638675795773205007389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28472425783863848803338259 42708638675795773205007389)
    ·
      refine ⟨16015739503423414951877771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42708638675795773205007389 16015739503423414951877771)
      ·
        refine ⟨24023609255135122427816657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16015739503423414951877771 24023609255135122427816657)
        ·
          refine ⟨18017706941351341820862493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24023609255135122427816657 18017706941351341820862493)
          ·
            refine ⟨6756640103006753182823435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18017706941351341820862493 6756640103006753182823435)
            ·
              refine ⟨10134960154510129774235153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6756640103006753182823435 10134960154510129774235153)
              ·
                refine ⟨7601220115882597330676365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10134960154510129774235153 7601220115882597330676365)
                ·
                  refine ⟨2850457543455973999003637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7601220115882597330676365 2850457543455973999003637)
                  ·
                    refine ⟨267230394698997562406591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2850457543455973999003637 267230394698997562406591)
                    ·
                      rfl

theorem cell23_1561288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_1561288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561288 prefixEnd_1561288 := by exact prefixLift 1561288
  have htrace : WordTrace (prefixWord ++ tailWord_1561288) baseStart_1561288 baseEnd_1561288 := by
    simpa [prefixWord, tailWord_1561288, baseEnd_1561288] using wordTrace_append hprefix tailTrace_1561288
  have hstable : (prefixWord ++ tailWord_1561288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561288).length < 2 ^ (prefixWord ++ tailWord_1561288).sum := by decide
  have hdescent : baseEnd_1561288 < baseStart_1561288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561328 : List Nat := [2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 5]
def baseStart_1561328 : Nat := 118140960795 + 1561328 * 2 ^ 59
def prefixEnd_1561328 : Nat := 4983230072969 + 3 ^ 40 * 1561328 * 2
def baseEnd_1561328 : Nat := 801711723323172530719589

theorem tailTrace_1561328 : CollatzResearch.WordTrace tailWord_1561328 prefixEnd_1561328 801711723323172530719589 := by
  unfold tailWord_1561328
  simp only [CollatzResearch.WordTrace]
  refine ⟨28473155243791392219066319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37964206991721856292088425 28473155243791392219066319)
  ·
    refine ⟨42709732865687088328599479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28473155243791392219066319 42709732865687088328599479)
    ·
      refine ⟨64064599298530632492899219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42709732865687088328599479 64064599298530632492899219)
      ·
        refine ⟨96096898947795948739348829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64064599298530632492899219 96096898947795948739348829)
        ·
          refine ⟨36036337105423480777255811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96096898947795948739348829 36036337105423480777255811)
          ·
            refine ⟨54054505658135221165883717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36036337105423480777255811 54054505658135221165883717)
            ·
              refine ⟨10135219810900353968603197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54054505658135221165883717 10135219810900353968603197)
              ·
                refine ⟨3800707429087632738226199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10135219810900353968603197 3800707429087632738226199)
                ·
                  refine ⟨5701061143631449107339299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3800707429087632738226199 5701061143631449107339299)
                  ·
                    refine ⟨8551591715447173661008949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5701061143631449107339299 8551591715447173661008949)
                    ·
                      refine ⟨801711723323172530719589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8551591715447173661008949 801711723323172530719589)
                      ·
                        rfl

theorem cell23_1561328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 5].length) (baseStart_1561328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561328 prefixEnd_1561328 := by exact prefixLift 1561328
  have htrace : WordTrace (prefixWord ++ tailWord_1561328) baseStart_1561328 baseEnd_1561328 := by
    simpa [prefixWord, tailWord_1561328, baseEnd_1561328] using wordTrace_append hprefix tailTrace_1561328
  have hstable : (prefixWord ++ tailWord_1561328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561328).length < 2 ^ (prefixWord ++ tailWord_1561328).sum := by decide
  have hdescent : baseEnd_1561328 < baseStart_1561328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561338 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4]
def baseStart_1561338 : Nat := 118140960795 + 1561338 * 2 ^ 59
def prefixEnd_1561338 : Nat := 4983230072969 + 3 ^ 40 * 1561338 * 2
def baseEnd_1561338 : Nat := 801716858129717491594543

theorem tailTrace_1561338 : CollatzResearch.WordTrace tailWord_1561338 prefixEnd_1561338 801716858129717491594543 := by
  unfold tailWord_1561338
  simp only [CollatzResearch.WordTrace]
  refine ⟨14236668804386639036499167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37964450145031037430664445 14236668804386639036499167)
  ·
    refine ⟨21355003206579958554748751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14236668804386639036499167 21355003206579958554748751)
    ·
      refine ⟨32032504809869937832123127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21355003206579958554748751 32032504809869937832123127)
      ·
        refine ⟨48048757214804906748184691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32032504809869937832123127 48048757214804906748184691)
        ·
          refine ⟨72073135822207360122277037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48048757214804906748184691 72073135822207360122277037)
          ·
            refine ⟨27027425933327760045853889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72073135822207360122277037 27027425933327760045853889)
            ·
              refine ⟨20270569449995820034390417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27027425933327760045853889 20270569449995820034390417)
              ·
                refine ⟨15202927087496865025792813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20270569449995820034390417 15202927087496865025792813)
                ·
                  refine ⟨5701097657811324384672305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15202927087496865025792813 5701097657811324384672305)
                  ·
                    refine ⟨4275823243358493288504229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5701097657811324384672305 4275823243358493288504229)
                    ·
                      refine ⟨801716858129717491594543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4275823243358493288504229 801716858129717491594543)
                      ·
                        rfl

theorem cell23_1561338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_1561338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561338 prefixEnd_1561338 := by exact prefixLift 1561338
  have htrace : WordTrace (prefixWord ++ tailWord_1561338) baseStart_1561338 baseEnd_1561338 := by
    simpa [prefixWord, tailWord_1561338, baseEnd_1561338] using wordTrace_append hprefix tailTrace_1561338
  have hstable : (prefixWord ++ tailWord_1561338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561338).length < 2 ^ (prefixWord ++ tailWord_1561338).sum := by decide
  have hdescent : baseEnd_1561338 < baseStart_1561338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561348 : List Nat := [2, 3, 2, 2, 1, 1, 2, 10]
def baseStart_1561348 : Nat := 118140960795 + 1561348 * 2 ^ 59
def prefixEnd_1561348 : Nat := 4983230072969 + 3 ^ 40 * 1561348 * 2
def baseEnd_1561348 : Nat := 29693407145787498239611

theorem tailTrace_1561348 : CollatzResearch.WordTrace tailWord_1561348 prefixEnd_1561348 29693407145787498239611 := by
  unfold tailWord_1561348
  simp only [CollatzResearch.WordTrace]
  refine ⟨28473519973755163926930349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37964693298340218569240465 28473519973755163926930349)
  ·
    refine ⟨10677569990158186472598881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28473519973755163926930349 10677569990158186472598881)
    ·
      refine ⟨8008177492618639854449161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10677569990158186472598881 8008177492618639854449161)
      ·
        refine ⟨6006133119463979890836871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8008177492618639854449161 6006133119463979890836871)
        ·
          refine ⟨9009199679195969836255307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6006133119463979890836871 9009199679195969836255307)
          ·
            refine ⟨13513799518793954754382961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9009199679195969836255307 13513799518793954754382961)
            ·
              refine ⟨10135349639095466065787221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13513799518793954754382961 10135349639095466065787221)
              ·
                refine ⟨29693407145787498239611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10135349639095466065787221 29693407145787498239611)
                ·
                  rfl

theorem cell23_1561348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 10].length) (baseStart_1561348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561348 prefixEnd_1561348 := by exact prefixLift 1561348
  have htrace : WordTrace (prefixWord ++ tailWord_1561348) baseStart_1561348 baseEnd_1561348 := by
    simpa [prefixWord, tailWord_1561348, baseEnd_1561348] using wordTrace_append hprefix tailTrace_1561348
  have hstable : (prefixWord ++ tailWord_1561348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561348).length < 2 ^ (prefixWord ++ tailWord_1561348).sum := by decide
  have hdescent : baseEnd_1561348 < baseStart_1561348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561376 : List Nat := [2, 1, 1, 5, 1, 2, 3, 3, 1, 2, 2]
def baseStart_1561376 : Nat := 118140960795 + 1561376 * 2 ^ 59
def prefixEnd_1561376 : Nat := 4983230072969 + 3 ^ 40 * 1561376 * 2
def baseEnd_1561376 : Nat := 801736370394588342919369

theorem tailTrace_1561376 : CollatzResearch.WordTrace tailWord_1561376 prefixEnd_1561376 801736370394588342919369 := by
  unfold tailWord_1561376
  simp only [CollatzResearch.WordTrace]
  refine ⟨28474030595704444317939991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37965374127605925757253321 28474030595704444317939991)
  ·
    refine ⟨42711045893556666476909987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28474030595704444317939991 42711045893556666476909987)
    ·
      refine ⟨64066568840334999715364981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42711045893556666476909987 64066568840334999715364981)
      ·
        refine ⟨6006240828781406223315467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64066568840334999715364981 6006240828781406223315467)
        ·
          refine ⟨9009361243172109334973201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6006240828781406223315467 9009361243172109334973201)
          ·
            refine ⟨6757020932379082001229901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9009361243172109334973201 6757020932379082001229901)
            ·
              refine ⟨2533882849642155750461213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6757020932379082001229901 2533882849642155750461213)
              ·
                refine ⟨950206068615808406422955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2533882849642155750461213 950206068615808406422955)
                ·
                  refine ⟨1425309102923712609634433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 950206068615808406422955 1425309102923712609634433)
                  ·
                    refine ⟨1068981827192784457225825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1425309102923712609634433 1068981827192784457225825)
                    ·
                      refine ⟨801736370394588342919369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1068981827192784457225825 801736370394588342919369)
                      ·
                        rfl

theorem cell23_1561376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_1561376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561376 prefixEnd_1561376 := by exact prefixLift 1561376
  have htrace : WordTrace (prefixWord ++ tailWord_1561376) baseStart_1561376 baseEnd_1561376 := by
    simpa [prefixWord, tailWord_1561376, baseEnd_1561376] using wordTrace_append hprefix tailTrace_1561376
  have hstable : (prefixWord ++ tailWord_1561376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561376).length < 2 ^ (prefixWord ++ tailWord_1561376).sum := by decide
  have hdescent : baseEnd_1561376 < baseStart_1561376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561388 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 5]
def baseStart_1561388 : Nat := 118140960795 + 1561388 * 2 ^ 59
def prefixEnd_1561388 : Nat := 4983230072969 + 3 ^ 40 * 1561388 * 2
def baseEnd_1561388 : Nat := 801742532162442295969313

theorem tailTrace_1561388 : CollatzResearch.WordTrace tailWord_1561388 prefixEnd_1561388 801742532162442295969313 := by
  unfold tailWord_1561388
  simp only [CollatzResearch.WordTrace]
  refine ⟨28474249433682707342658409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37965665911576943123544545 28474249433682707342658409)
  ·
    refine ⟨21355687075262030506993807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28474249433682707342658409 21355687075262030506993807)
    ·
      refine ⟨32033530612893045760490711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21355687075262030506993807 32033530612893045760490711)
      ·
        refine ⟨48050295919339568640736067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32033530612893045760490711 48050295919339568640736067)
        ·
          refine ⟨72075443879009352961104101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48050295919339568640736067 72075443879009352961104101)
          ·
            refine ⟨13514145727314253680207019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72075443879009352961104101 13514145727314253680207019)
            ·
              refine ⟨20271218590971380520310529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13514145727314253680207019 20271218590971380520310529)
              ·
                refine ⟨15203413943228535390232897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20271218590971380520310529 15203413943228535390232897)
                ·
                  refine ⟨11402560457421401542674673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15203413943228535390232897 11402560457421401542674673)
                  ·
                    refine ⟨8551920343066051157006005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11402560457421401542674673 8551920343066051157006005)
                    ·
                      refine ⟨801742532162442295969313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8551920343066051157006005 801742532162442295969313)
                      ·
                        rfl

theorem cell23_1561388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_1561388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561388 prefixEnd_1561388 := by exact prefixLift 1561388
  have htrace : WordTrace (prefixWord ++ tailWord_1561388) baseStart_1561388 baseEnd_1561388 := by
    simpa [prefixWord, tailWord_1561388, baseEnd_1561388] using wordTrace_append hprefix tailTrace_1561388
  have hstable : (prefixWord ++ tailWord_1561388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561388).length < 2 ^ (prefixWord ++ tailWord_1561388).sum := by decide
  have hdescent : baseEnd_1561388 < baseStart_1561388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561408 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 2, 6]
def baseStart_1561408 : Nat := 118140960795 + 1561408 * 2 ^ 59
def prefixEnd_1561408 : Nat := 4983230072969 + 3 ^ 40 * 1561408 * 2
def baseEnd_1561408 : Nat := 267250933925177405906407

theorem tailTrace_1561408 : CollatzResearch.WordTrace tailWord_1561408 prefixEnd_1561408 267250933925177405906407 := by
  unfold tailWord_1561408
  simp only [CollatzResearch.WordTrace]
  refine ⟨28474614163646479050522439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37966152218195305400696585 28474614163646479050522439)
  ·
    refine ⟨42711921245469718575783659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28474614163646479050522439 42711921245469718575783659)
    ·
      refine ⟨64067881868204577863675489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42711921245469718575783659 64067881868204577863675489)
      ·
        refine ⟨48050911401153433397756617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64067881868204577863675489 48050911401153433397756617)
        ·
          refine ⟨36038183550865075048317463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48050911401153433397756617 36038183550865075048317463)
          ·
            refine ⟨54057275326297612572476195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36038183550865075048317463 54057275326297612572476195)
            ·
              refine ⟨81085912989446418858714293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54057275326297612572476195 81085912989446418858714293)
              ·
                refine ⟨7601804342760601768004465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81085912989446418858714293 7601804342760601768004465)
                ·
                  refine ⟨5701353257070451326003349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7601804342760601768004465 5701353257070451326003349)
                  ·
                    refine ⟨267250933925177405906407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5701353257070451326003349 267250933925177405906407)
                    ·
                      rfl

theorem cell23_1561408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 2, 6].length) (baseStart_1561408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561408 prefixEnd_1561408 := by exact prefixLift 1561408
  have htrace : WordTrace (prefixWord ++ tailWord_1561408) baseStart_1561408 baseEnd_1561408 := by
    simpa [prefixWord, tailWord_1561408, baseEnd_1561408] using wordTrace_append hprefix tailTrace_1561408
  have hstable : (prefixWord ++ tailWord_1561408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561408).length < 2 ^ (prefixWord ++ tailWord_1561408).sum := by decide
  have hdescent : baseEnd_1561408 < baseStart_1561408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561432 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 6, 2, 2]
def baseStart_1561432 : Nat := 118140960795 + 1561432 * 2 ^ 59
def prefixEnd_1561432 : Nat := 4983230072969 + 3 ^ 40 * 1561432 * 2
def baseEnd_1561432 : Nat := 801765125311240123819111

theorem tailTrace_1561432 : CollatzResearch.WordTrace tailWord_1561432 prefixEnd_1561432 801765125311240123819111 := by
  unfold tailWord_1561432
  simp only [CollatzResearch.WordTrace]
  refine ⟨28475051839603005099959275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37966735786137340133279033 28475051839603005099959275)
  ·
    refine ⟨42712577759404507649938913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28475051839603005099959275 42712577759404507649938913)
    ·
      refine ⟨32034433319553380737454185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42712577759404507649938913 32034433319553380737454185)
      ·
        refine ⟨24025824989665035553090639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32034433319553380737454185 24025824989665035553090639)
        ·
          refine ⟨36038737484497553329635959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24025824989665035553090639 36038737484497553329635959)
          ·
            refine ⟨54058106226746329994453939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36038737484497553329635959 54058106226746329994453939)
            ·
              refine ⟨81087159340119494991680909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54058106226746329994453939 81087159340119494991680909)
              ·
                refine ⟨30407684752544810621880341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81087159340119494991680909 30407684752544810621880341)
                ·
                  refine ⟨1425360222775537997900641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30407684752544810621880341 1425360222775537997900641)
                  ·
                    refine ⟨1069020167081653498425481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1425360222775537997900641 1069020167081653498425481)
                    ·
                      refine ⟨801765125311240123819111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1069020167081653498425481 801765125311240123819111)
                      ·
                        rfl

theorem cell23_1561432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 6, 2, 2].length) (baseStart_1561432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561432 prefixEnd_1561432 := by exact prefixLift 1561432
  have htrace : WordTrace (prefixWord ++ tailWord_1561432) baseStart_1561432 baseEnd_1561432 := by
    simpa [prefixWord, tailWord_1561432, baseEnd_1561432] using wordTrace_append hprefix tailTrace_1561432
  have hstable : (prefixWord ++ tailWord_1561432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561432).length < 2 ^ (prefixWord ++ tailWord_1561432).sum := by decide
  have hdescent : baseEnd_1561432 < baseStart_1561432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561462 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1561462 : Nat := 118140960795 + 1561462 * 2 ^ 59
def prefixEnd_1561462 : Nat := 4983230072969 + 3 ^ 40 * 1561462 * 2
def baseEnd_1561462 : Nat := 801780529730875006443973

theorem tailTrace_1561462 : CollatzResearch.WordTrace tailWord_1561462 prefixEnd_1561462 801780529730875006443973 := by
  unfold tailWord_1561462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3559449866818582832719415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37967465246064883549007093 3559449866818582832719415)
  ·
    refine ⟨5339174800227874249079123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3559449866818582832719415 5339174800227874249079123)
    ·
      refine ⟨8008762200341811373618685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5339174800227874249079123 8008762200341811373618685)
      ·
        refine ⟨3003285825128179265107007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8008762200341811373618685 3003285825128179265107007)
        ·
          refine ⟨4504928737692268897660511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3003285825128179265107007 4504928737692268897660511)
          ·
            refine ⟨6757393106538403346490767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4504928737692268897660511 6757393106538403346490767)
            ·
              refine ⟨10136089659807605019736151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6757393106538403346490767 10136089659807605019736151)
              ·
                refine ⟨15204134489711407529604227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10136089659807605019736151 15204134489711407529604227)
                ·
                  refine ⟨22806201734567111294406341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15204134489711407529604227 22806201734567111294406341)
                  ·
                    refine ⟨4276162825231333367701189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22806201734567111294406341 4276162825231333367701189)
                    ·
                      refine ⟨801780529730875006443973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4276162825231333367701189 801780529730875006443973)
                      ·
                        rfl

theorem cell23_1561462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1561462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561462 prefixEnd_1561462 := by exact prefixLift 1561462
  have htrace : WordTrace (prefixWord ++ tailWord_1561462) baseStart_1561462 baseEnd_1561462 := by
    simpa [prefixWord, tailWord_1561462, baseEnd_1561462] using wordTrace_append hprefix tailTrace_1561462
  have hstable : (prefixWord ++ tailWord_1561462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561462).length < 2 ^ (prefixWord ++ tailWord_1561462).sum := by decide
  have hdescent : baseEnd_1561462 < baseStart_1561462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561465 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 1, 5, 3]
def baseStart_1561465 : Nat := 118140960795 + 1561465 * 2 ^ 59
def prefixEnd_1561465 : Nat := 4983230072969 + 3 ^ 40 * 1561465 * 2
def baseEnd_1561465 : Nat := 801782070172838494706459

theorem tailTrace_1561465 : CollatzResearch.WordTrace tailWord_1561465 prefixEnd_1561465 801782070172838494706459 := by
  unfold tailWord_1561465
  simp only [CollatzResearch.WordTrace]
  refine ⟨56951307288086456835869849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37967538192057637890579899 56951307288086456835869849)
  ·
    refine ⟨42713480466064842626902387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56951307288086456835869849 42713480466064842626902387)
    ·
      refine ⟨64070220699097263940353581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42713480466064842626902387 64070220699097263940353581)
      ·
        refine ⟨24026332762161473977632593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64070220699097263940353581 24026332762161473977632593)
        ·
          refine ⟨18019749571621105483224445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24026332762161473977632593 18019749571621105483224445)
          ·
            refine ⟨6757406089357914556209167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18019749571621105483224445 6757406089357914556209167)
            ·
              refine ⟨10136109134036871834313751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6757406089357914556209167 10136109134036871834313751)
              ·
                refine ⟨15204163701055307751470627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10136109134036871834313751 15204163701055307751470627)
                ·
                  refine ⟨22806245551582961627205941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15204163701055307751470627 22806245551582961627205941)
                  ·
                    refine ⟨2138085520460902652550557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22806245551582961627205941 2138085520460902652550557)
                    ·
                      refine ⟨801782070172838494706459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2138085520460902652550557 801782070172838494706459)
                      ·
                        rfl

theorem cell23_1561465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_1561465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561465 prefixEnd_1561465 := by exact prefixLift 1561465
  have htrace : WordTrace (prefixWord ++ tailWord_1561465) baseStart_1561465 baseEnd_1561465 := by
    simpa [prefixWord, tailWord_1561465, baseEnd_1561465] using wordTrace_append hprefix tailTrace_1561465
  have hstable : (prefixWord ++ tailWord_1561465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561465).length < 2 ^ (prefixWord ++ tailWord_1561465).sum := by decide
  have hdescent : baseEnd_1561465 < baseStart_1561465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561488 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 8]
def baseStart_1561488 : Nat := 118140960795 + 1561488 * 2 ^ 59
def prefixEnd_1561488 : Nat := 4983230072969 + 3 ^ 40 * 1561488 * 2
def baseEnd_1561488 : Nat := 801793880227891904718853

theorem tailTrace_1561488 : CollatzResearch.WordTrace tailWord_1561488 prefixEnd_1561488 801793880227891904718853 := by
  unfold tailWord_1561488
  simp only [CollatzResearch.WordTrace]
  refine ⟨28476073083501565881978559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37968097444668754509304745 28476073083501565881978559)
  ·
    refine ⟨42714109625252348822967839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28476073083501565881978559 42714109625252348822967839)
    ·
      refine ⟨64071164437878523234451759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42714109625252348822967839 64071164437878523234451759)
      ·
        refine ⟨96106746656817784851677639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64071164437878523234451759 96106746656817784851677639)
        ·
          refine ⟨144160119985226677277516459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96106746656817784851677639 144160119985226677277516459)
          ·
            refine ⟨216240179977840015916274689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144160119985226677277516459 216240179977840015916274689)
            ·
              refine ⟨162180134983380011937206017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216240179977840015916274689 162180134983380011937206017)
              ·
                refine ⟨121635101237535008952904513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162180134983380011937206017 121635101237535008952904513)
                ·
                  refine ⟨91226325928151256714678385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121635101237535008952904513 91226325928151256714678385)
                  ·
                    refine ⟨68419744446113442536008789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91226325928151256714678385 68419744446113442536008789)
                    ·
                      refine ⟨801793880227891904718853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 68419744446113442536008789 801793880227891904718853)
                      ·
                        rfl

theorem cell23_1561488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_1561488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561488 prefixEnd_1561488 := by exact prefixLift 1561488
  have htrace : WordTrace (prefixWord ++ tailWord_1561488) baseStart_1561488 baseEnd_1561488 := by
    simpa [prefixWord, tailWord_1561488, baseEnd_1561488] using wordTrace_append hprefix tailTrace_1561488
  have hstable : (prefixWord ++ tailWord_1561488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561488).length < 2 ^ (prefixWord ++ tailWord_1561488).sum := by decide
  have hdescent : baseEnd_1561488 < baseStart_1561488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561500 : List Nat := [2, 2, 3, 3, 3, 1, 1, 2, 2, 2, 2]
def baseStart_1561500 : Nat := 118140960795 + 1561500 * 2 ^ 59
def prefixEnd_1561500 : Nat := 4983230072969 + 3 ^ 40 * 1561500 * 2
def baseEnd_1561500 : Nat := 801800041995745857768799

theorem tailTrace_1561500 : CollatzResearch.WordTrace tailWord_1561500 prefixEnd_1561500 801800041995745857768799 := by
  unfold tailWord_1561500
  simp only [CollatzResearch.WordTrace]
  refine ⟨28476291921479828906696977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37968389228639771875595969 28476291921479828906696977)
  ·
    refine ⟨21357218941109871680022733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28476291921479828906696977 21357218941109871680022733)
    ·
      refine ⟨8008957102916201880008525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21357218941109871680022733 8008957102916201880008525)
      ·
        refine ⟨3003358913593575705003197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8008957102916201880008525 3003358913593575705003197)
        ·
          refine ⟨1126259592597590889376199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3003358913593575705003197 1126259592597590889376199)
          ·
            refine ⟨1689389388896386334064299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1126259592597590889376199 1689389388896386334064299)
            ·
              refine ⟨2534084083344579501096449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1689389388896386334064299 2534084083344579501096449)
              ·
                refine ⟨1900563062508434625822337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2534084083344579501096449 1900563062508434625822337)
                ·
                  refine ⟨1425422296881325969366753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1900563062508434625822337 1425422296881325969366753)
                  ·
                    refine ⟨1069066722660994477025065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1425422296881325969366753 1069066722660994477025065)
                    ·
                      refine ⟨801800041995745857768799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1069066722660994477025065 801800041995745857768799)
                      ·
                        rfl

theorem cell23_1561500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_1561500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561500 prefixEnd_1561500 := by exact prefixLift 1561500
  have htrace : WordTrace (prefixWord ++ tailWord_1561500) baseStart_1561500 baseEnd_1561500 := by
    simpa [prefixWord, tailWord_1561500, baseEnd_1561500] using wordTrace_append hprefix tailTrace_1561500
  have hstable : (prefixWord ++ tailWord_1561500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561500).length < 2 ^ (prefixWord ++ tailWord_1561500).sum := by decide
  have hdescent : baseEnd_1561500 < baseStart_1561500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561515 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 7, 4]
def baseStart_1561515 : Nat := 118140960795 + 1561515 * 2 ^ 59
def prefixEnd_1561515 : Nat := 4983230072969 + 3 ^ 40 * 1561515 * 2
def baseEnd_1561515 : Nat := 267269248068521099693743

theorem tailTrace_1561515 : CollatzResearch.WordTrace tailWord_1561515 prefixEnd_1561515 267269248068521099693743 := by
  unfold tailWord_1561515
  simp only [CollatzResearch.WordTrace]
  refine ⟨56953130937905315375189999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37968753958603543583459999 56953130937905315375189999)
  ·
    refine ⟨85429696406857973062784999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56953130937905315375189999 85429696406857973062784999)
    ·
      refine ⟨128144544610286959594177499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85429696406857973062784999 128144544610286959594177499)
      ·
        refine ⟨192216816915430439391266249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128144544610286959594177499 192216816915430439391266249)
        ·
          refine ⟨144162612686572829543449687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192216816915430439391266249 144162612686572829543449687)
          ·
            refine ⟨216243919029859244315174531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144162612686572829543449687 216243919029859244315174531)
            ·
              refine ⟨324365878544788866472761797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216243919029859244315174531 324365878544788866472761797)
              ·
                refine ⟨60818602227147912463642837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 324365878544788866472761797 60818602227147912463642837)
                ·
                  refine ⟨1425435989698779198366629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 60818602227147912463642837 1425435989698779198366629)
                  ·
                    refine ⟨267269248068521099693743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1425435989698779198366629 267269248068521099693743)
                    ·
                      rfl

theorem cell23_1561515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 4].length) (baseStart_1561515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561515 prefixEnd_1561515 := by exact prefixLift 1561515
  have htrace : WordTrace (prefixWord ++ tailWord_1561515) baseStart_1561515 baseEnd_1561515 := by
    simpa [prefixWord, tailWord_1561515, baseEnd_1561515] using wordTrace_append hprefix tailTrace_1561515
  have hstable : (prefixWord ++ tailWord_1561515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561515).length < 2 ^ (prefixWord ++ tailWord_1561515).sum := by decide
  have hdescent : baseEnd_1561515 < baseStart_1561515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
