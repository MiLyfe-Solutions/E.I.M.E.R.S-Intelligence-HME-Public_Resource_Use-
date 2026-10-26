import V185TrunkScan21Chunk103

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1262184 : List Nat := [2, 1, 4, 3, 3, 1, 2, 5]
def baseStart_1262184 : Nat := 118140960795 + 1262184 * 2 ^ 59
def prefixEnd_1262184 : Nat := 4983230072969 + 3 ^ 40 * 1262184 * 2
def baseEnd_1262184 : Nat := 96015861691051101184493

theorem tailTrace_1262184 : CollatzResearch.WordTrace tailWord_1262184 prefixEnd_1262184 96015861691051101184493 := by
  unfold tailWord_1262184
  simp only [CollatzResearch.WordTrace]
  refine ⟨23017816229665203355196803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30690421639553604473595737 23017816229665203355196803)
  ·
    refine ⟨34526724344497805032795205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23017816229665203355196803 34526724344497805032795205)
    ·
      refine ⟨6473760814593338443649101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34526724344497805032795205 6473760814593338443649101)
      ·
        refine ⟨2427660305472501916368413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6473760814593338443649101 2427660305472501916368413)
        ·
          refine ⟨910372614552188218638155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2427660305472501916368413 910372614552188218638155)
          ·
            refine ⟨1365558921828282327957233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 910372614552188218638155 1365558921828282327957233)
            ·
              refine ⟨1024169191371211745967925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1365558921828282327957233 1024169191371211745967925)
              ·
                refine ⟨96015861691051101184493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1024169191371211745967925 96015861691051101184493)
                ·
                  rfl

theorem cell21_1262184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 5].length) (baseStart_1262184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1262184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1262184 prefixEnd_1262184 := by exact prefixLift 1262184
  have htrace : WordTrace (prefixWord ++ tailWord_1262184) baseStart_1262184 baseEnd_1262184 := by
    simpa [prefixWord, tailWord_1262184, baseEnd_1262184] using wordTrace_append hprefix tailTrace_1262184
  have hstable : (prefixWord ++ tailWord_1262184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262184).length < 2 ^ (prefixWord ++ tailWord_1262184).sum := by decide
  have hdescent : baseEnd_1262184 < baseStart_1262184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262226 : List Nat := [3, 2, 3, 1, 2, 2, 2, 6]
def baseStart_1262226 : Nat := 118140960795 + 1262226 * 2 ^ 59
def prefixEnd_1262226 : Nat := 4983230072969 + 3 ^ 40 * 1262226 * 2
def baseEnd_1262226 : Nat := 96019056681790187951131

theorem tailTrace_1262226 : CollatzResearch.WordTrace tailWord_1262226 prefixEnd_1262226 96019056681790187951131 := by
  unfold tailWord_1262226
  simp only [CollatzResearch.WordTrace]
  refine ⟨11509291081294561970855633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30691442883452165255615021 11509291081294561970855633)
  ·
    refine ⟨8631968310970921478141725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11509291081294561970855633 8631968310970921478141725)
    ·
      refine ⟨3236988116614095554303147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8631968310970921478141725 3236988116614095554303147)
      ·
        refine ⟨4855482174921143331454721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3236988116614095554303147 4855482174921143331454721)
        ·
          refine ⟨3641611631190857498591041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4855482174921143331454721 3641611631190857498591041)
          ·
            refine ⟨2731208723393143123943281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3641611631190857498591041 2731208723393143123943281)
            ·
              refine ⟨2048406542544857342957461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2731208723393143123943281 2048406542544857342957461)
              ·
                refine ⟨96019056681790187951131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2048406542544857342957461 96019056681790187951131)
                ·
                  rfl

theorem cell21_1262226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_1262226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1262226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1262226 prefixEnd_1262226 := by exact prefixLift 1262226
  have htrace : WordTrace (prefixWord ++ tailWord_1262226) baseStart_1262226 baseEnd_1262226 := by
    simpa [prefixWord, tailWord_1262226, baseEnd_1262226] using wordTrace_append hprefix tailTrace_1262226
  have hstable : (prefixWord ++ tailWord_1262226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262226).length < 2 ^ (prefixWord ++ tailWord_1262226).sum := by decide
  have hdescent : baseEnd_1262226 < baseStart_1262226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262271 : List Nat := [1, 1, 2, 2, 2, 5, 2, 2, 4]
def baseStart_1262271 : Nat := 118140960795 + 1262271 * 2 ^ 59
def prefixEnd_1262271 : Nat := 4983230072969 + 3 ^ 40 * 1262271 * 2
def baseEnd_1262271 : Nat := 288067439658460485603301

theorem tailTrace_1262271 : CollatzResearch.WordTrace tailWord_1262271 prefixEnd_1262271 288067439658460485603301 := by
  unfold tailWord_1262271
  simp only [CollatzResearch.WordTrace]
  refine ⟨46038805610015220568810667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30692537073343480379207111 46038805610015220568810667)
  ·
    refine ⟨69058208415022830853216001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46038805610015220568810667 69058208415022830853216001)
    ·
      refine ⟨51793656311267123139912001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69058208415022830853216001 51793656311267123139912001)
      ·
        refine ⟨38845242233450342354934001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51793656311267123139912001 38845242233450342354934001)
        ·
          refine ⟨29133931675087756766200501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38845242233450342354934001 29133931675087756766200501)
          ·
            refine ⟨2731306094539477196831297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29133931675087756766200501 2731306094539477196831297)
            ·
              refine ⟨2048479570904607897623473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2731306094539477196831297 2048479570904607897623473)
              ·
                refine ⟨1536359678178455923217605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2048479570904607897623473 1536359678178455923217605)
                ·
                  refine ⟨288067439658460485603301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1536359678178455923217605 288067439658460485603301)
                  ·
                    rfl

theorem cell21_1262271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 4].length) (baseStart_1262271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1262271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1262271 prefixEnd_1262271 := by exact prefixLift 1262271
  have htrace : WordTrace (prefixWord ++ tailWord_1262271) baseStart_1262271 baseEnd_1262271 := by
    simpa [prefixWord, tailWord_1262271, baseEnd_1262271] using wordTrace_append hprefix tailTrace_1262271
  have hstable : (prefixWord ++ tailWord_1262271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262271).length < 2 ^ (prefixWord ++ tailWord_1262271).sum := by decide
  have hdescent : baseEnd_1262271 < baseStart_1262271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262398 : List Nat := [4, 2, 1, 2, 4, 1, 2, 1, 4]
def baseStart_1262398 : Nat := 118140960795 + 1262398 * 2 ^ 59
def prefixEnd_1262398 : Nat := 4983230072969 + 3 ^ 40 * 1262398 * 2
def baseEnd_1262398 : Nat := 288096422788736486986375

theorem tailTrace_1262398 : CollatzResearch.WordTrace tailWord_1262398 prefixEnd_1262398 288096422788736486986375 := by
  unfold tailWord_1262398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5755429710069390157335481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30695625120370080839122565 5755429710069390157335481)
  ·
    refine ⟨4316572282552042618001611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5755429710069390157335481 4316572282552042618001611)
    ·
      refine ⟨6474858423828063927002417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4316572282552042618001611 6474858423828063927002417)
      ·
        refine ⟨4856143817871047945251813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6474858423828063927002417 4856143817871047945251813)
        ·
          refine ⟨910526965850821489734715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4856143817871047945251813 910526965850821489734715)
          ·
            refine ⟨1365790448776232234602073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 910526965850821489734715 1365790448776232234602073)
            ·
              refine ⟨1024342836582174175951555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1365790448776232234602073 1024342836582174175951555)
              ·
                refine ⟨1536514254873261263927333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1024342836582174175951555 1536514254873261263927333)
                ·
                  refine ⟨288096422788736486986375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1536514254873261263927333 288096422788736486986375)
                  ·
                    rfl

theorem cell21_1262398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_1262398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1262398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1262398 prefixEnd_1262398 := by exact prefixLift 1262398
  have htrace : WordTrace (prefixWord ++ tailWord_1262398) baseStart_1262398 baseEnd_1262398 := by
    simpa [prefixWord, tailWord_1262398, baseEnd_1262398] using wordTrace_append hprefix tailTrace_1262398
  have hstable : (prefixWord ++ tailWord_1262398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262398).length < 2 ^ (prefixWord ++ tailWord_1262398).sum := by decide
  have hdescent : baseEnd_1262398 < baseStart_1262398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262454 : List Nat := [5, 1, 1, 3, 1, 1, 3, 6]
def baseStart_1262454 : Nat := 118140960795 + 1262454 * 2 ^ 59
def prefixEnd_1262454 : Nat := 4983230072969 + 3 ^ 40 * 1262454 * 2
def baseEnd_1262454 : Nat := 96036400917230944684309

theorem tailTrace_1262454 : CollatzResearch.WordTrace tailWord_1262454 prefixEnd_1262454 96036400917230944684309 := by
  unfold tailWord_1262454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2877842510522015176420151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30696986778901495215148277 2877842510522015176420151)
  ·
    refine ⟨4316763765783022764630227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2877842510522015176420151 4316763765783022764630227)
    ·
      refine ⟨6475145648674534146945341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4316763765783022764630227 6475145648674534146945341)
      ·
        refine ⟨2428179618252950305104503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6475145648674534146945341 2428179618252950305104503)
        ·
          refine ⟨3642269427379425457656755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2428179618252950305104503 3642269427379425457656755)
          ·
            refine ⟨5463404141069138186485133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3642269427379425457656755 5463404141069138186485133)
            ·
              refine ⟨2048776552900926819931925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5463404141069138186485133 2048776552900926819931925)
              ·
                refine ⟨96036400917230944684309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2048776552900926819931925 96036400917230944684309)
                ·
                  rfl

theorem cell21_1262454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_1262454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1262454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1262454 prefixEnd_1262454 := by exact prefixLift 1262454
  have htrace : WordTrace (prefixWord ++ tailWord_1262454) baseStart_1262454 baseEnd_1262454 := by
    simpa [prefixWord, tailWord_1262454, baseEnd_1262454] using wordTrace_append hprefix tailTrace_1262454
  have hstable : (prefixWord ++ tailWord_1262454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262454).length < 2 ^ (prefixWord ++ tailWord_1262454).sum := by decide
  have hdescent : baseEnd_1262454 < baseStart_1262454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262485 : List Nat := [1, 3, 2, 1, 1, 5, 2, 3, 3]
def baseStart_1262485 : Nat := 118140960795 + 1262485 * 2 ^ 59
def prefixEnd_1262485 : Nat := 4983230072969 + 3 ^ 40 * 1262485 * 2
def baseEnd_1262485 : Nat := 288116277374043669036197

theorem tailTrace_1262485 : CollatzResearch.WordTrace tailWord_1262485 prefixEnd_1262485 288116277374043669036197 := by
  unfold tailWord_1262485
  simp only [CollatzResearch.WordTrace]
  refine ⟨46046610831239935117100909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30697740554159956744733939 46046610831239935117100909)
  ·
    refine ⟨17267479061714975668912841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46046610831239935117100909 17267479061714975668912841)
    ·
      refine ⟨12950609296286231751684631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17267479061714975668912841 12950609296286231751684631)
      ·
        refine ⟨19425913944429347627526947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12950609296286231751684631 19425913944429347627526947)
        ·
          refine ⟨29138870916644021441290421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19425913944429347627526947 29138870916644021441290421)
          ·
            refine ⟨2731769148435377010120977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29138870916644021441290421 2731769148435377010120977)
            ·
              refine ⟨2048826861326532757590733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2731769148435377010120977 2048826861326532757590733)
              ·
                refine ⟨768310072997449784096525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2048826861326532757590733 768310072997449784096525)
                ·
                  refine ⟨288116277374043669036197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 768310072997449784096525 288116277374043669036197)
                  ·
                    rfl

theorem cell21_1262485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 3].length) (baseStart_1262485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1262485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1262485 prefixEnd_1262485 := by exact prefixLift 1262485
  have htrace : WordTrace (prefixWord ++ tailWord_1262485) baseStart_1262485 baseEnd_1262485 := by
    simpa [prefixWord, tailWord_1262485, baseEnd_1262485] using wordTrace_append hprefix tailTrace_1262485
  have hstable : (prefixWord ++ tailWord_1262485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262485).length < 2 ^ (prefixWord ++ tailWord_1262485).sum := by decide
  have hdescent : baseEnd_1262485 < baseStart_1262485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262575 : List Nat := [1, 1, 2, 1, 4, 3, 4, 1, 4]
def baseStart_1262575 : Nat := 118140960795 + 1262575 * 2 ^ 59
def prefixEnd_1262575 : Nat := 4983230072969 + 3 ^ 40 * 1262575 * 2
def baseEnd_1262575 : Nat := 288136816600223512536013

theorem tailTrace_1262575 : CollatzResearch.WordTrace tailWord_1262575 prefixEnd_1262575 288136816600223512536013 := by
  unfold tailWord_1262575
  simp only [CollatzResearch.WordTrace]
  refine ⟨46049893400913880487877179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30699928933942586991918119 46049893400913880487877179)
  ·
    refine ⟨69074840101370820731815769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46049893400913880487877179 69074840101370820731815769)
    ·
      refine ⟨51806130076028115548861827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69074840101370820731815769 51806130076028115548861827)
      ·
        refine ⟨77709195114042173323292741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51806130076028115548861827 77709195114042173323292741)
        ·
          refine ⟨14570474083882907498117389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77709195114042173323292741 14570474083882907498117389)
          ·
            refine ⟨5463927781456090311794021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14570474083882907498117389 5463927781456090311794021)
            ·
              refine ⟨1024486459023016933461379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5463927781456090311794021 1024486459023016933461379)
              ·
                refine ⟨1536729688534525400192069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1024486459023016933461379 1536729688534525400192069)
                ·
                  refine ⟨288136816600223512536013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1536729688534525400192069 288136816600223512536013)
                  ·
                    rfl

theorem cell21_1262575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 4].length) (baseStart_1262575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1262575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1262575 prefixEnd_1262575 := by exact prefixLift 1262575
  have htrace : WordTrace (prefixWord ++ tailWord_1262575) baseStart_1262575 baseEnd_1262575 := by
    simpa [prefixWord, tailWord_1262575, baseEnd_1262575] using wordTrace_append hprefix tailTrace_1262575
  have hstable : (prefixWord ++ tailWord_1262575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262575).length < 2 ^ (prefixWord ++ tailWord_1262575).sum := by decide
  have hdescent : baseEnd_1262575 < baseStart_1262575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262617 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 6]
def baseStart_1262617 : Nat := 118140960795 + 1262617 * 2 ^ 59
def prefixEnd_1262617 : Nat := 4983230072969 + 3 ^ 40 * 1262617 * 2
def baseEnd_1262617 : Nat := 288146401572440772835927

theorem tailTrace_1262617 : CollatzResearch.WordTrace tailWord_1262617 prefixEnd_1262617 288146401572440772835927 := by
  unfold tailWord_1262617
  simp only [CollatzResearch.WordTrace]
  refine ⟨46051425266761721660906105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30700950177841147773937403 46051425266761721660906105)
  ·
    refine ⟨34538568950071291245679579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46051425266761721660906105 34538568950071291245679579)
    ·
      refine ⟨51807853425106936868519369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34538568950071291245679579 51807853425106936868519369)
      ·
        refine ⟨38855890068830202651389527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51807853425106936868519369 38855890068830202651389527)
        ·
          refine ⟨58283835103245303977084291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38855890068830202651389527 58283835103245303977084291)
          ·
            refine ⟨87425752654867955965626437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58283835103245303977084291 87425752654867955965626437)
            ·
              refine ⟨16392328622787741743554957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87425752654867955965626437 16392328622787741743554957)
              ·
                refine ⟨6147123233545403153833109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16392328622787741743554957 6147123233545403153833109)
                ·
                  refine ⟨288146401572440772835927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6147123233545403153833109 288146401572440772835927)
                  ·
                    rfl

theorem cell21_1262617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_1262617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1262617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1262617 prefixEnd_1262617 := by exact prefixLift 1262617
  have htrace : WordTrace (prefixWord ++ tailWord_1262617) baseStart_1262617 baseEnd_1262617 := by
    simpa [prefixWord, tailWord_1262617, baseEnd_1262617] using wordTrace_append hprefix tailTrace_1262617
  have hstable : (prefixWord ++ tailWord_1262617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262617).length < 2 ^ (prefixWord ++ tailWord_1262617).sum := by decide
  have hdescent : baseEnd_1262617 < baseStart_1262617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262654 : List Nat := [4, 2, 1, 3, 1, 2, 2, 3, 3]
def baseStart_1262654 : Nat := 118140960795 + 1262654 * 2 ^ 59
def prefixEnd_1262654 : Nat := 4983230072969 + 3 ^ 40 * 1262654 * 2
def baseEnd_1262654 : Nat := 288154845476536930719185

theorem tailTrace_1262654 : CollatzResearch.WordTrace tailWord_1262654 prefixEnd_1262654 288154845476536930719185 := by
  unfold tailWord_1262654
  simp only [CollatzResearch.WordTrace]
  refine ⟨5756596845953459622500377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30701849845085117986668677 5756596845953459622500377)
  ·
    refine ⟨4317447634465094716875283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5756596845953459622500377 4317447634465094716875283)
    ·
      refine ⟨6476171451697642075312925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4317447634465094716875283 6476171451697642075312925)
      ·
        refine ⟨2428564294386615778242347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6476171451697642075312925 2428564294386615778242347)
        ·
          refine ⟨3642846441579923667363521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2428564294386615778242347 3642846441579923667363521)
          ·
            refine ⟨2732134831184942750522641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3642846441579923667363521 2732134831184942750522641)
            ·
              refine ⟨2049101123388707062891981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2732134831184942750522641 2049101123388707062891981)
              ·
                refine ⟨768412921270765148584493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2049101123388707062891981 768412921270765148584493)
                ·
                  refine ⟨288154845476536930719185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 768412921270765148584493 288154845476536930719185)
                  ·
                    rfl

theorem cell21_1262654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_1262654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1262654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1262654 prefixEnd_1262654 := by exact prefixLift 1262654
  have htrace : WordTrace (prefixWord ++ tailWord_1262654) baseStart_1262654 baseEnd_1262654 := by
    simpa [prefixWord, tailWord_1262654, baseEnd_1262654] using wordTrace_append hprefix tailTrace_1262654
  have hstable : (prefixWord ++ tailWord_1262654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262654).length < 2 ^ (prefixWord ++ tailWord_1262654).sum := by decide
  have hdescent : baseEnd_1262654 < baseStart_1262654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262685 : List Nat := [1, 4, 4, 1, 2, 1, 3, 1, 4]
def baseStart_1262685 : Nat := 118140960795 + 1262685 * 2 ^ 59
def prefixEnd_1262685 : Nat := 4983230072969 + 3 ^ 40 * 1262685 * 2
def baseEnd_1262685 : Nat := 288161920098887765702455

theorem tailTrace_1262685 : CollatzResearch.WordTrace tailWord_1262685 prefixEnd_1262685 288161920098887765702455 := by
  unfold tailWord_1262685
  simp only [CollatzResearch.WordTrace]
  refine ⟨46053905430515369274381509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30702603620343579516254339 46053905430515369274381509)
  ·
    refine ⟨8635107268221631738946533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46053905430515369274381509 8635107268221631738946533)
    ·
      refine ⟨1619082612791555951052475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8635107268221631738946533 1619082612791555951052475)
      ·
        refine ⟨2428623919187333926578713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1619082612791555951052475 2428623919187333926578713)
        ·
          refine ⟨1821467939390500444934035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2428623919187333926578713 1821467939390500444934035)
          ·
            refine ⟨2732201909085750667401053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1821467939390500444934035 2732201909085750667401053)
            ·
              refine ⟨1024575715907156500275395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2732201909085750667401053 1024575715907156500275395)
              ·
                refine ⟨1536863573860734750413093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1024575715907156500275395 1536863573860734750413093)
                ·
                  refine ⟨288161920098887765702455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1536863573860734750413093 288161920098887765702455)
                  ·
                    rfl

theorem cell21_1262685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_1262685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1262685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1262685 prefixEnd_1262685 := by exact prefixLift 1262685
  have htrace : WordTrace (prefixWord ++ tailWord_1262685) baseStart_1262685 baseEnd_1262685 := by
    simpa [prefixWord, tailWord_1262685, baseEnd_1262685] using wordTrace_append hprefix tailTrace_1262685
  have hstable : (prefixWord ++ tailWord_1262685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262685).length < 2 ^ (prefixWord ++ tailWord_1262685).sum := by decide
  have hdescent : baseEnd_1262685 < baseStart_1262685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262710 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_1262710 : Nat := 118140960795 + 1262710 * 2 ^ 59
def prefixEnd_1262710 : Nat := 4983230072969 + 3 ^ 40 * 1262710 * 2
def baseEnd_1262710 : Nat := 288167625439493277785737

theorem tailTrace_1262710 : CollatzResearch.WordTrace tailWord_1262710 prefixEnd_1262710 288167625439493277785737 := by
  unfold tailWord_1262710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2878426078464049909002599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30703211503616532362694389 2878426078464049909002599)
  ·
    refine ⟨4317639117696074863503899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2878426078464049909002599 4317639117696074863503899)
    ·
      refine ⟨6476458676544112295255849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4317639117696074863503899 6476458676544112295255849)
      ·
        refine ⟨4857344007408084221441887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6476458676544112295255849 4857344007408084221441887)
        ·
          refine ⟨7286016011112126332162831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4857344007408084221441887 7286016011112126332162831)
          ·
            refine ⟨10929024016668189498244247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7286016011112126332162831 10929024016668189498244247)
            ·
              refine ⟨16393536025002284247366371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10929024016668189498244247 16393536025002284247366371)
              ·
                refine ⟨24590304037503426371049557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16393536025002284247366371 24590304037503426371049557)
                ·
                  refine ⟨288167625439493277785737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24590304037503426371049557 288167625439493277785737)
                  ·
                    rfl

theorem cell21_1262710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_1262710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1262710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1262710 prefixEnd_1262710 := by exact prefixLift 1262710
  have htrace : WordTrace (prefixWord ++ tailWord_1262710) baseStart_1262710 baseEnd_1262710 := by
    simpa [prefixWord, tailWord_1262710, baseEnd_1262710] using wordTrace_append hprefix tailTrace_1262710
  have hstable : (prefixWord ++ tailWord_1262710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262710).length < 2 ^ (prefixWord ++ tailWord_1262710).sum := by decide
  have hdescent : baseEnd_1262710 < baseStart_1262710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262724 : List Nat := [2, 3, 2, 1, 2, 2, 9]
def baseStart_1262724 : Nat := 118140960795 + 1262724 * 2 ^ 59
def prefixEnd_1262724 : Nat := 4983230072969 + 3 ^ 40 * 1262724 * 2
def baseEnd_1262724 : Nat := 32018980047803596061375

theorem tailTrace_1262724 : CollatzResearch.WordTrace tailWord_1262724 prefixEnd_1262724 32018980047803596061375 := by
  unfold tailWord_1262724
  simp only [CollatzResearch.WordTrace]
  refine ⟨23027663938687039467525613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30703551918249385956700817 23027663938687039467525613)
  ·
    refine ⟨8635373977007639800322105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23027663938687039467525613 8635373977007639800322105)
    ·
      refine ⟨6476530482755729850241579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8635373977007639800322105 6476530482755729850241579)
      ·
        refine ⟨9714795724133594775362369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6476530482755729850241579 9714795724133594775362369)
        ·
          refine ⟨7286096793100196081521777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9714795724133594775362369 7286096793100196081521777)
          ·
            refine ⟨5464572594825147061141333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7286096793100196081521777 5464572594825147061141333)
            ·
              refine ⟨32018980047803596061375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5464572594825147061141333 32018980047803596061375)
              ·
                rfl

theorem cell21_1262724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 9].length) (baseStart_1262724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1262724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1262724 prefixEnd_1262724 := by exact prefixLift 1262724
  have htrace : WordTrace (prefixWord ++ tailWord_1262724) baseStart_1262724 baseEnd_1262724 := by
    simpa [prefixWord, tailWord_1262724, baseEnd_1262724] using wordTrace_append hprefix tailTrace_1262724
  have hstable : (prefixWord ++ tailWord_1262724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262724).length < 2 ^ (prefixWord ++ tailWord_1262724).sum := by decide
  have hdescent : baseEnd_1262724 < baseStart_1262724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262744 : List Nat := [2, 1, 2, 4, 2, 3, 2, 1, 4]
def baseStart_1262744 : Nat := 118140960795 + 1262744 * 2 ^ 59
def prefixEnd_1262744 : Nat := 4983230072969 + 3 ^ 40 * 1262744 * 2
def baseEnd_1262744 : Nat := 288175384702716774219001

theorem tailTrace_1262744 : CollatzResearch.WordTrace tailWord_1262744 prefixEnd_1262744 288175384702716774219001 := by
  unfold tailWord_1262744
  simp only [CollatzResearch.WordTrace]
  refine ⟨23028028668650811175389643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30704038224867748233852857 23028028668650811175389643)
  ·
    refine ⟨34542043002976216763084465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23028028668650811175389643 34542043002976216763084465)
    ·
      refine ⟨25906532252232162572313349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34542043002976216763084465 25906532252232162572313349)
      ·
        refine ⟨4857474797293530482308753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25906532252232162572313349 4857474797293530482308753)
        ·
          refine ⟨3643106097970147861731565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4857474797293530482308753 3643106097970147861731565)
          ·
            refine ⟨1366164786738805448149337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3643106097970147861731565 1366164786738805448149337)
            ·
              refine ⟨1024623590054104086112003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1366164786738805448149337 1024623590054104086112003)
              ·
                refine ⟨1536935385081156129168005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1024623590054104086112003 1536935385081156129168005)
                ·
                  refine ⟨288175384702716774219001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1536935385081156129168005 288175384702716774219001)
                  ·
                    rfl

theorem cell21_1262744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 4].length) (baseStart_1262744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1262744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1262744 prefixEnd_1262744 := by exact prefixLift 1262744
  have htrace : WordTrace (prefixWord ++ tailWord_1262744) baseStart_1262744 baseEnd_1262744 := by
    simpa [prefixWord, tailWord_1262744, baseEnd_1262744] using wordTrace_append hprefix tailTrace_1262744
  have hstable : (prefixWord ++ tailWord_1262744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262744).length < 2 ^ (prefixWord ++ tailWord_1262744).sum := by decide
  have hdescent : baseEnd_1262744 < baseStart_1262744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262817 : List Nat := [1, 2, 3, 1, 3, 3, 3, 5]
def baseStart_1262817 : Nat := 118140960795 + 1262817 * 2 ^ 59
def prefixEnd_1262817 : Nat := 4983230072969 + 3 ^ 40 * 1262817 * 2
def baseEnd_1262817 : Nat := 96064014765761623167395

theorem tailTrace_1262817 : CollatzResearch.WordTrace tailWord_1262817 prefixEnd_1262817 96064014765761623167395 := by
  unfold tailWord_1262817
  simp only [CollatzResearch.WordTrace]
  refine ⟨46058719866037155818186705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30705813244024770545457803 46058719866037155818186705)
  ·
    refine ⟨34544039899527866863640029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46058719866037155818186705 34544039899527866863640029)
    ·
      refine ⟨12954014962322950073865011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34544039899527866863640029 12954014962322950073865011)
      ·
        refine ⟨19431022443484425110797517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12954014962322950073865011 19431022443484425110797517)
        ·
          refine ⟨7286633416306659416549069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19431022443484425110797517 7286633416306659416549069)
          ·
            refine ⟨2732487531114997281205901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7286633416306659416549069 2732487531114997281205901)
            ·
              refine ⟨1024682824168123980452213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2732487531114997281205901 1024682824168123980452213)
              ·
                refine ⟨96064014765761623167395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1024682824168123980452213 96064014765761623167395)
                ·
                  rfl

theorem cell21_1262817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 5].length) (baseStart_1262817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1262817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1262817 prefixEnd_1262817 := by exact prefixLift 1262817
  have htrace : WordTrace (prefixWord ++ tailWord_1262817) baseStart_1262817 baseEnd_1262817 := by
    simpa [prefixWord, tailWord_1262817, baseEnd_1262817] using wordTrace_append hprefix tailTrace_1262817
  have hstable : (prefixWord ++ tailWord_1262817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262817).length < 2 ^ (prefixWord ++ tailWord_1262817).sum := by decide
  have hdescent : baseEnd_1262817 < baseStart_1262817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262882 : List Nat := [3, 3, 1, 1, 4, 2, 1, 3, 3]
def baseStart_1262882 : Nat := 118140960795 + 1262882 * 2 ^ 59
def prefixEnd_1262882 : Nat := 4983230072969 + 3 ^ 40 * 1262882 * 2
def baseEnd_1262882 : Nat := 288206878182859200918719

theorem tailTrace_1262882 : CollatzResearch.WordTrace tailWord_1262882 prefixEnd_1262882 288206878182859200918719 := by
  unfold tailWord_1262882
  simp only [CollatzResearch.WordTrace]
  refine ⟨11515272652700417979825725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30707393740534447946201933 11515272652700417979825725)
  ·
    refine ⟨4318227244762656742434647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11515272652700417979825725 4318227244762656742434647)
    ·
      refine ⟨6477340867143985113651971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4318227244762656742434647 6477340867143985113651971)
      ·
        refine ⟨9716011300715977670477957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6477340867143985113651971 9716011300715977670477957)
        ·
          refine ⟨1821752118884245813214617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9716011300715977670477957 1821752118884245813214617)
          ·
            refine ⟨1366314089163184359910963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1821752118884245813214617 1366314089163184359910963)
            ·
              refine ⟨2049471133744776539866445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1366314089163184359910963 2049471133744776539866445)
              ·
                refine ⟨768551675154291202449917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2049471133744776539866445 768551675154291202449917)
                ·
                  refine ⟨288206878182859200918719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 768551675154291202449917 288206878182859200918719)
                  ·
                    rfl

theorem cell21_1262882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_1262882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1262882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1262882 prefixEnd_1262882 := by exact prefixLift 1262882
  have htrace : WordTrace (prefixWord ++ tailWord_1262882) baseStart_1262882 baseEnd_1262882 := by
    simpa [prefixWord, tailWord_1262882, baseEnd_1262882] using wordTrace_append hprefix tailTrace_1262882
  have hstable : (prefixWord ++ tailWord_1262882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262882).length < 2 ^ (prefixWord ++ tailWord_1262882).sum := by decide
  have hdescent : baseEnd_1262882 < baseStart_1262882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262893 : List Nat := [1, 5, 3, 1, 1, 1, 9]
def baseStart_1262893 : Nat := 118140960795 + 1262893 * 2 ^ 59
def prefixEnd_1262893 : Nat := 4983230072969 + 3 ^ 40 * 1262893 * 2
def baseEnd_1262893 : Nat := 32023265392525069581707

theorem tailTrace_1262893 : CollatzResearch.WordTrace tailWord_1262893 prefixEnd_1262893 32023265392525069581707 := by
  unfold tailWord_1262893
  simp only [CollatzResearch.WordTrace]
  refine ⟨46061491813761820797953333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30707661209174547198635555 46061491813761820797953333)
  ·
    refine ⟨4318264857540170699808125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46061491813761820797953333 4318264857540170699808125)
    ·
      refine ⟨1619349321577564012428047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4318264857540170699808125 1619349321577564012428047)
      ·
        refine ⟨2429023982366346018642071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1619349321577564012428047 2429023982366346018642071)
        ·
          refine ⟨3643535973549519027963107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2429023982366346018642071 3643535973549519027963107)
          ·
            refine ⟨5465303960324278541944661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3643535973549519027963107 5465303960324278541944661)
            ·
              refine ⟨32023265392525069581707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5465303960324278541944661 32023265392525069581707)
              ·
                rfl

theorem cell21_1262893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 9].length) (baseStart_1262893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1262893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1262893 prefixEnd_1262893 := by exact prefixLift 1262893
  have htrace : WordTrace (prefixWord ++ tailWord_1262893) baseStart_1262893 baseEnd_1262893 := by
    simpa [prefixWord, tailWord_1262893, baseEnd_1262893] using wordTrace_append hprefix tailTrace_1262893
  have hstable : (prefixWord ++ tailWord_1262893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262893).length < 2 ^ (prefixWord ++ tailWord_1262893).sum := by decide
  have hdescent : baseEnd_1262893 < baseStart_1262893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262952 : List Nat := [2, 1, 4, 2, 3, 9]
def baseStart_1262952 : Nat := 118140960795 + 1262952 * 2 ^ 59
def prefixEnd_1262952 : Nat := 4983230072969 + 3 ^ 40 * 1262952 * 2
def baseEnd_1262952 : Nat := 10674920486539060546367

theorem tailTrace_1262952 : CollatzResearch.WordTrace tailWord_1262952 prefixEnd_1262952 10674920486539060546367 := by
  unfold tailWord_1262952
  simp only [CollatzResearch.WordTrace]
  refine ⟨23031821860274036937175555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30709095813698715916234073 23031821860274036937175555)
  ·
    refine ⟨34547732790411055405763333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23031821860274036937175555 34547732790411055405763333)
    ·
      refine ⟨6477699898202072888580625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34547732790411055405763333 6477699898202072888580625)
      ·
        refine ⟨4858274923651554666435469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6477699898202072888580625 4858274923651554666435469)
        ·
          refine ⟨1821853096369332999913301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4858274923651554666435469 1821853096369332999913301)
          ·
            refine ⟨10674920486539060546367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1821853096369332999913301 10674920486539060546367)
            ·
              rfl

theorem cell21_1262952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 9].length) (baseStart_1262952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1262952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1262952 prefixEnd_1262952 := by exact prefixLift 1262952
  have htrace : WordTrace (prefixWord ++ tailWord_1262952) baseStart_1262952 baseEnd_1262952 := by
    simpa [prefixWord, tailWord_1262952, baseEnd_1262952] using wordTrace_append hprefix tailTrace_1262952
  have hstable : (prefixWord ++ tailWord_1262952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262952).length < 2 ^ (prefixWord ++ tailWord_1262952).sum := by decide
  have hdescent : baseEnd_1262952 < baseStart_1262952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262958 : List Nat := [4, 1, 2, 4, 1, 1, 1, 4, 3]
def baseStart_1262958 : Nat := 118140960795 + 1262958 * 2 ^ 59
def prefixEnd_1262958 : Nat := 4983230072969 + 3 ^ 40 * 1262958 * 2
def baseEnd_1262958 : Nat := 288224222418299957651897

theorem tailTrace_1262958 : CollatzResearch.WordTrace tailWord_1262958 prefixEnd_1262958 288224222418299957651897 := by
  unfold tailWord_1262958
  simp only [CollatzResearch.WordTrace]
  refine ⟨5757982819815792112383691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30709241705684224599379685 5757982819815792112383691)
  ·
    refine ⟨8636974229723688168575537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5757982819815792112383691 8636974229723688168575537)
    ·
      refine ⟨6477730672292766126431653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8636974229723688168575537 6477730672292766126431653)
      ·
        refine ⟨1214574501054893648705935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6477730672292766126431653 1214574501054893648705935)
        ·
          refine ⟨1821861751582340473058903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1214574501054893648705935 1821861751582340473058903)
          ·
            refine ⟨2732792627373510709588355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1821861751582340473058903 2732792627373510709588355)
            ·
              refine ⟨4099188941060266064382533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2732792627373510709588355 4099188941060266064382533)
              ·
                refine ⟨768597926448799887071725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4099188941060266064382533 768597926448799887071725)
                ·
                  refine ⟨288224222418299957651897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 768597926448799887071725 288224222418299957651897)
                  ·
                    rfl

theorem cell21_1262958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_1262958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1262958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1262958 prefixEnd_1262958 := by exact prefixLift 1262958
  have htrace : WordTrace (prefixWord ++ tailWord_1262958) baseStart_1262958 baseEnd_1262958 := by
    simpa [prefixWord, tailWord_1262958, baseEnd_1262958] using wordTrace_append hprefix tailTrace_1262958
  have hstable : (prefixWord ++ tailWord_1262958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262958).length < 2 ^ (prefixWord ++ tailWord_1262958).sum := by decide
  have hdescent : baseEnd_1262958 < baseStart_1262958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262983 : List Nat := [1, 1, 4, 2, 2, 3, 1, 2, 5]
def baseStart_1262983 : Nat := 118140960795 + 1262983 * 2 ^ 59
def prefixEnd_1262983 : Nat := 4983230072969 + 3 ^ 40 * 1262983 * 2
def baseEnd_1262983 : Nat := 288229927758905469735179

theorem tailTrace_1262983 : CollatzResearch.WordTrace tailWord_1262983 prefixEnd_1262983 288229927758905469735179 := by
  unfold tailWord_1262983
  simp only [CollatzResearch.WordTrace]
  refine ⟨46064774383435766168729603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30709849588957177445819735 46064774383435766168729603)
  ·
    refine ⟨69097161575153649253094405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46064774383435766168729603 69097161575153649253094405)
    ·
      refine ⟨12955717795341309234955201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69097161575153649253094405 12955717795341309234955201)
      ·
        refine ⟨9716788346505981926216401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12955717795341309234955201 9716788346505981926216401)
        ·
          refine ⟨7287591259879486444662301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9716788346505981926216401 7287591259879486444662301)
          ·
            refine ⟨2732846722454807416748363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7287591259879486444662301 2732846722454807416748363)
            ·
              refine ⟨4099270083682211125122545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2732846722454807416748363 4099270083682211125122545)
              ·
                refine ⟨3074452562761658343841909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4099270083682211125122545 3074452562761658343841909)
                ·
                  refine ⟨288229927758905469735179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3074452562761658343841909 288229927758905469735179)
                  ·
                    rfl

theorem cell21_1262983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 5].length) (baseStart_1262983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1262983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1262983 prefixEnd_1262983 := by exact prefixLift 1262983
  have htrace : WordTrace (prefixWord ++ tailWord_1262983) baseStart_1262983 baseEnd_1262983 := by
    simpa [prefixWord, tailWord_1262983, baseEnd_1262983] using wordTrace_append hprefix tailTrace_1262983
  have hstable : (prefixWord ++ tailWord_1262983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262983).length < 2 ^ (prefixWord ++ tailWord_1262983).sum := by decide
  have hdescent : baseEnd_1262983 < baseStart_1262983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263011 : List Nat := [1, 1, 1, 4, 1, 3, 10]
def baseStart_1263011 : Nat := 118140960795 + 1263011 * 2 ^ 59
def prefixEnd_1263011 : Nat := 4983230072969 + 3 ^ 40 * 1263011 * 2
def baseEnd_1263011 : Nat := 32026257526709293696495

theorem tailTrace_1263011 : CollatzResearch.WordTrace tailWord_1263011 prefixEnd_1263011 32026257526709293696495 := by
  unfold tailWord_1263011
  simp only [CollatzResearch.WordTrace]
  refine ⟨46065795627334326950748887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30710530418222884633832591 46065795627334326950748887)
  ·
    refine ⟨69098693441001490426123331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46065795627334326950748887 69098693441001490426123331)
    ·
      refine ⟨103648040161502235639184997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69098693441001490426123331 103648040161502235639184997)
      ·
        refine ⟨19434007530281669182347187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103648040161502235639184997 19434007530281669182347187)
        ·
          refine ⟨29151011295422503773520781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19434007530281669182347187 29151011295422503773520781)
          ·
            refine ⟨10931629235783438915070293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29151011295422503773520781 10931629235783438915070293)
            ·
              refine ⟨32026257526709293696495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10931629235783438915070293 32026257526709293696495)
              ·
                rfl

theorem cell21_1263011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 10].length) (baseStart_1263011 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263011 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263011 prefixEnd_1263011 := by exact prefixLift 1263011
  have htrace : WordTrace (prefixWord ++ tailWord_1263011) baseStart_1263011 baseEnd_1263011 := by
    simpa [prefixWord, tailWord_1263011, baseEnd_1263011] using wordTrace_append hprefix tailTrace_1263011
  have hstable : (prefixWord ++ tailWord_1263011).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263011).length < 2 ^ (prefixWord ++ tailWord_1263011).sum := by decide
  have hdescent : baseEnd_1263011 < baseStart_1263011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263073 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 6]
def baseStart_1263073 : Nat := 118140960795 + 1263073 * 2 ^ 59
def prefixEnd_1263073 : Nat := 4983230072969 + 3 ^ 40 * 1263073 * 2
def baseEnd_1263073 : Nat := 288250466985085313234995

theorem tailTrace_1263073 : CollatzResearch.WordTrace tailWord_1263073 prefixEnd_1263073 288250466985085313234995 := by
  unfold tailWord_1263073
  simp only [CollatzResearch.WordTrace]
  refine ⟨46068056953109711539505873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30712037968739807693003915 46068056953109711539505873)
  ·
    refine ⟨34551042714832283654629405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46068056953109711539505873 34551042714832283654629405)
    ·
      refine ⟨12956641018062106370486027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34551042714832283654629405 12956641018062106370486027)
      ·
        refine ⟨19434961527093159555729041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12956641018062106370486027 19434961527093159555729041)
        ·
          refine ⟨14576221145319869666796781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19434961527093159555729041 14576221145319869666796781)
          ·
            refine ⟨5466082929494951125048793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14576221145319869666796781 5466082929494951125048793)
            ·
              refine ⟨4099562197121213343786595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5466082929494951125048793 4099562197121213343786595)
              ·
                refine ⟨6149343295681820015679893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4099562197121213343786595 6149343295681820015679893)
                ·
                  refine ⟨288250466985085313234995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6149343295681820015679893 288250466985085313234995)
                  ·
                    rfl

theorem cell21_1263073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_1263073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263073 prefixEnd_1263073 := by exact prefixLift 1263073
  have htrace : WordTrace (prefixWord ++ tailWord_1263073) baseStart_1263073 baseEnd_1263073 := by
    simpa [prefixWord, tailWord_1263073, baseEnd_1263073] using wordTrace_append hprefix tailTrace_1263073
  have hstable : (prefixWord ++ tailWord_1263073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263073).length < 2 ^ (prefixWord ++ tailWord_1263073).sum := by decide
  have hdescent : baseEnd_1263073 < baseStart_1263073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263087 : List Nat := [1, 1, 2, 1, 4, 1, 3, 8]
def baseStart_1263087 : Nat := 118140960795 + 1263087 * 2 ^ 59
def prefixEnd_1263087 : Nat := 4983230072969 + 3 ^ 40 * 1263087 * 2
def baseEnd_1263087 : Nat := 96084553991941466667211

theorem tailTrace_1263087 : CollatzResearch.WordTrace tailWord_1263087 prefixEnd_1263087 96084553991941466667211 := by
  unfold tailWord_1263087
  simp only [CollatzResearch.WordTrace]
  refine ⟨46068567575058991930515515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30712378383372661287010343 46068567575058991930515515)
  ·
    refine ⟨69102851362588487895773273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46068567575058991930515515 69102851362588487895773273)
    ·
      refine ⟨51827138521941365921829955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69102851362588487895773273 51827138521941365921829955)
      ·
        refine ⟨77740707782912048882744933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51827138521941365921829955 77740707782912048882744933)
        ·
          refine ⟨14576382709296009165514675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77740707782912048882744933 14576382709296009165514675)
          ·
            refine ⟨21864574063944013748272013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14576382709296009165514675 21864574063944013748272013)
            ·
              refine ⟨8199215273979005155602005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21864574063944013748272013 8199215273979005155602005)
              ·
                refine ⟨96084553991941466667211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8199215273979005155602005 96084553991941466667211)
                ·
                  rfl

theorem cell21_1263087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 8].length) (baseStart_1263087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263087 prefixEnd_1263087 := by exact prefixLift 1263087
  have htrace : WordTrace (prefixWord ++ tailWord_1263087) baseStart_1263087 baseEnd_1263087 := by
    simpa [prefixWord, tailWord_1263087, baseEnd_1263087] using wordTrace_append hprefix tailTrace_1263087
  have hstable : (prefixWord ++ tailWord_1263087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263087).length < 2 ^ (prefixWord ++ tailWord_1263087).sum := by decide
  have hdescent : baseEnd_1263087 < baseStart_1263087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263124 : List Nat := [2, 4, 3, 1, 2, 1, 2, 2, 4]
def baseStart_1263124 : Nat := 118140960795 + 1263124 * 2 ^ 59
def prefixEnd_1263124 : Nat := 4983230072969 + 3 ^ 40 * 1263124 * 2
def baseEnd_1263124 : Nat := 288262105879920557884891

theorem tailTrace_1263124 : CollatzResearch.WordTrace tailWord_1263124 prefixEnd_1263124 288262105879920557884891 := by
  unfold tailWord_1263124
  simp only [CollatzResearch.WordTrace]
  refine ⟨23034958537962473624806213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30713278050616631499741617 23034958537962473624806213)
  ·
    refine ⟨4319054725867963804651165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23034958537962473624806213 4319054725867963804651165)
    ·
      refine ⟨1619645522200486426744187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4319054725867963804651165 1619645522200486426744187)
      ·
        refine ⟨2429468283300729640116281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1619645522200486426744187 2429468283300729640116281)
        ·
          refine ⟨1822101212475547230087211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2429468283300729640116281 1822101212475547230087211)
          ·
            refine ⟨2733151818713320845130817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1822101212475547230087211 2733151818713320845130817)
            ·
              refine ⟨2049863864034990633848113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2733151818713320845130817 2049863864034990633848113)
              ·
                refine ⟨1537397898026242975386085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2049863864034990633848113 1537397898026242975386085)
                ·
                  refine ⟨288262105879920557884891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1537397898026242975386085 288262105879920557884891)
                  ·
                    rfl

theorem cell21_1263124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_1263124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263124 prefixEnd_1263124 := by exact prefixLift 1263124
  have htrace : WordTrace (prefixWord ++ tailWord_1263124) baseStart_1263124 baseEnd_1263124 := by
    simpa [prefixWord, tailWord_1263124, baseEnd_1263124] using wordTrace_append hprefix tailTrace_1263124
  have hstable : (prefixWord ++ tailWord_1263124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263124).length < 2 ^ (prefixWord ++ tailWord_1263124).sum := by decide
  have hdescent : baseEnd_1263124 < baseStart_1263124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263214 : List Nat := [4, 1, 2, 2, 3, 2, 2, 5]
def baseStart_1263214 : Nat := 118140960795 + 1263214 * 2 ^ 59
def prefixEnd_1263214 : Nat := 4983230072969 + 3 ^ 40 * 1263214 * 2
def baseEnd_1263214 : Nat := 96094215035366800461569

theorem tailTrace_1263214 : CollatzResearch.WordTrace tailWord_1263214 prefixEnd_1263214 96094215035366800461569 := by
  unfold tailWord_1263214
  simp only [CollatzResearch.WordTrace]
  refine ⟨5759149955699861577548587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30715466430399261746925797 5759149955699861577548587)
  ·
    refine ⟨8638724933549792366322881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5759149955699861577548587 8638724933549792366322881)
    ·
      refine ⟨6479043700162344274742161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8638724933549792366322881 6479043700162344274742161)
      ·
        refine ⟨4859282775121758206056621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6479043700162344274742161 4859282775121758206056621)
        ·
          refine ⟨1822231040670659327271233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4859282775121758206056621 1822231040670659327271233)
          ·
            refine ⟨1366673280502994495453425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1822231040670659327271233 1366673280502994495453425)
            ·
              refine ⟨1025004960377245871590069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1366673280502994495453425 1025004960377245871590069)
              ·
                refine ⟨96094215035366800461569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1025004960377245871590069 96094215035366800461569)
                ·
                  rfl

theorem cell21_1263214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_1263214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263214 prefixEnd_1263214 := by exact prefixLift 1263214
  have htrace : WordTrace (prefixWord ++ tailWord_1263214) baseStart_1263214 baseEnd_1263214 := by
    simpa [prefixWord, tailWord_1263214, baseEnd_1263214] using wordTrace_append hprefix tailTrace_1263214
  have hstable : (prefixWord ++ tailWord_1263214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263214).length < 2 ^ (prefixWord ++ tailWord_1263214).sum := by decide
  have hdescent : baseEnd_1263214 < baseStart_1263214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263239 : List Nat := [1, 1, 4, 2, 1, 3, 9]
def baseStart_1263239 : Nat := 118140960795 + 1263239 * 2 ^ 59
def prefixEnd_1263239 : Nat := 4983230072969 + 3 ^ 40 * 1263239 * 2
def baseEnd_1263239 : Nat := 32032038938522879274221

theorem tailTrace_1263239 : CollatzResearch.WordTrace tailWord_1263239 prefixEnd_1263239 32032038938522879274221 := by
  unfold tailWord_1263239
  simp only [CollatzResearch.WordTrace]
  refine ⟨46074111470508321890048771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30716074313672214593365847 46074111470508321890048771)
  ·
    refine ⟨69111167205762482835073157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46074111470508321890048771 69111167205762482835073157)
    ·
      refine ⟨12958343851080465531576217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69111167205762482835073157 12958343851080465531576217)
      ·
        refine ⟨9718757888310349148682163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12958343851080465531576217 9718757888310349148682163)
        ·
          refine ⟨14578136832465523723023245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9718757888310349148682163 14578136832465523723023245)
          ·
            refine ⟨5466801312174571396133717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14578136832465523723023245 5466801312174571396133717)
            ·
              refine ⟨32032038938522879274221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5466801312174571396133717 32032038938522879274221)
              ·
                rfl

theorem cell21_1263239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 9].length) (baseStart_1263239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263239 prefixEnd_1263239 := by exact prefixLift 1263239
  have htrace : WordTrace (prefixWord ++ tailWord_1263239) baseStart_1263239 baseEnd_1263239 := by
    simpa [prefixWord, tailWord_1263239, baseEnd_1263239] using wordTrace_append hprefix tailTrace_1263239
  have hstable : (prefixWord ++ tailWord_1263239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263239).length < 2 ^ (prefixWord ++ tailWord_1263239).sum := by decide
  have hdescent : baseEnd_1263239 < baseStart_1263239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263256 : List Nat := [2, 1, 2, 4, 1, 3, 2, 6]
def baseStart_1263256 : Nat := 118140960795 + 1263256 * 2 ^ 59
def prefixEnd_1263256 : Nat := 4983230072969 + 3 ^ 40 * 1263256 * 2
def baseEnd_1263256 : Nat := 96097410026105887228207

theorem tailTrace_1263256 : CollatzResearch.WordTrace tailWord_1263256 prefixEnd_1263256 96097410026105887228207 := by
  unfold tailWord_1263256
  simp only [CollatzResearch.WordTrace]
  refine ⟨23037365755723366896708811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30716487674297822528945081 23037365755723366896708811)
  ·
    refine ⟨34556048633585050345063217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23037365755723366896708811 34556048633585050345063217)
    ·
      refine ⟨25917036475188787758797413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34556048633585050345063217 25917036475188787758797413)
      ·
        refine ⟨4859444339097897704774515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25917036475188787758797413 4859444339097897704774515)
        ·
          refine ⟨7289166508646846557161773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4859444339097897704774515 7289166508646846557161773)
          ·
            refine ⟨2733437440742567458935665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7289166508646846557161773 2733437440742567458935665)
            ·
              refine ⟨2050078080556925594201749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2733437440742567458935665 2050078080556925594201749)
              ·
                refine ⟨96097410026105887228207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2050078080556925594201749 96097410026105887228207)
                ·
                  rfl

theorem cell21_1263256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 6].length) (baseStart_1263256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263256 prefixEnd_1263256 := by exact prefixLift 1263256
  have htrace : WordTrace (prefixWord ++ tailWord_1263256) baseStart_1263256 baseEnd_1263256 := by
    simpa [prefixWord, tailWord_1263256, baseEnd_1263256] using wordTrace_append hprefix tailTrace_1263256
  have hstable : (prefixWord ++ tailWord_1263256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263256).length < 2 ^ (prefixWord ++ tailWord_1263256).sum := by decide
  have hdescent : baseEnd_1263256 < baseStart_1263256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263332 : List Nat := [2, 3, 1, 1, 1, 3, 5, 5]
def baseStart_1263332 : Nat := 118140960795 + 1263332 * 2 ^ 59
def prefixEnd_1263332 : Nat := 4983230072969 + 3 ^ 40 * 1263332 * 2
def baseEnd_1263332 : Nat := 96103191437919472805933

theorem tailTrace_1263332 : CollatzResearch.WordTrace tailWord_1263332 prefixEnd_1263332 96103191437919472805933 := by
  unfold tailWord_1263332
  simp only [CollatzResearch.WordTrace]
  refine ⟨23038751729585699386592125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30718335639447599182122833 23038751729585699386592125)
  ·
    refine ⟨8639531898594637269972047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23038751729585699386592125 8639531898594637269972047)
    ·
      refine ⟨12959297847891955904958071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8639531898594637269972047 12959297847891955904958071)
      ·
        refine ⟨19438946771837933857437107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12959297847891955904958071 19438946771837933857437107)
        ·
          refine ⟨29158420157756900786155661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19438946771837933857437107 29158420157756900786155661)
          ·
            refine ⟨10934407559158837794808373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29158420157756900786155661 10934407559158837794808373)
            ·
              refine ⟨1025100708671141043263285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10934407559158837794808373 1025100708671141043263285)
              ·
                refine ⟨96103191437919472805933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1025100708671141043263285 96103191437919472805933)
                ·
                  rfl

theorem cell21_1263332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 5].length) (baseStart_1263332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263332 prefixEnd_1263332 := by exact prefixLift 1263332
  have htrace : WordTrace (prefixWord ++ tailWord_1263332) baseStart_1263332 baseEnd_1263332 := by
    simpa [prefixWord, tailWord_1263332, baseEnd_1263332] using wordTrace_append hprefix tailTrace_1263332
  have hstable : (prefixWord ++ tailWord_1263332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263332).length < 2 ^ (prefixWord ++ tailWord_1263332).sum := by decide
  have hdescent : baseEnd_1263332 < baseStart_1263332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263346 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 7]
def baseStart_1263346 : Nat := 118140960795 + 1263346 * 2 ^ 59
def prefixEnd_1263346 : Nat := 4983230072969 + 3 ^ 40 * 1263346 * 2
def baseEnd_1263346 : Nat := 288312769304497505184437

theorem tailTrace_1263346 : CollatzResearch.WordTrace tailWord_1263346 prefixEnd_1263346 288312769304497505184437 := by
  unfold tailWord_1263346
  simp only [CollatzResearch.WordTrace]
  refine ⟨11519503520280169791048473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30718676054080452776129261 11519503520280169791048473)
  ·
    refine ⟨8639627640210127343286355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11519503520280169791048473 8639627640210127343286355)
    ·
      refine ⟨12959441460315191014929533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8639627640210127343286355 12959441460315191014929533)
      ·
        refine ⟨4859790547618196630598575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12959441460315191014929533 4859790547618196630598575)
        ·
          refine ⟨7289685821427294945897863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4859790547618196630598575 7289685821427294945897863)
          ·
            refine ⟨10934528732140942418846795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7289685821427294945897863 10934528732140942418846795)
            ·
              refine ⟨16401793098211413628270193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10934528732140942418846795 16401793098211413628270193)
              ·
                refine ⟨12301344823658560221202645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16401793098211413628270193 12301344823658560221202645)
                ·
                  refine ⟨288312769304497505184437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12301344823658560221202645 288312769304497505184437)
                  ·
                    rfl

theorem cell21_1263346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_1263346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263346 prefixEnd_1263346 := by exact prefixLift 1263346
  have htrace : WordTrace (prefixWord ++ tailWord_1263346) baseStart_1263346 baseEnd_1263346 := by
    simpa [prefixWord, tailWord_1263346, baseEnd_1263346] using wordTrace_append hprefix tailTrace_1263346
  have hstable : (prefixWord ++ tailWord_1263346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263346).length < 2 ^ (prefixWord ++ tailWord_1263346).sum := by decide
  have hdescent : baseEnd_1263346 < baseStart_1263346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263360 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 6]
def baseStart_1263360 : Nat := 118140960795 + 1263360 * 2 ^ 59
def prefixEnd_1263360 : Nat := 4983230072969 + 3 ^ 40 * 1263360 * 2
def baseEnd_1263360 : Nat := 288315964295236591951075

theorem tailTrace_1263360 : CollatzResearch.WordTrace tailWord_1263360 prefixEnd_1263360 288315964295236591951075 := by
  unfold tailWord_1263360
  simp only [CollatzResearch.WordTrace]
  refine ⟨23039262351534979777601767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30719016468713306370135689 23039262351534979777601767)
  ·
    refine ⟨34558893527302469666402651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23039262351534979777601767 34558893527302469666402651)
    ·
      refine ⟨51838340290953704499603977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34558893527302469666402651 51838340290953704499603977)
      ·
        refine ⟨38878755218215278374702983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51838340290953704499603977 38878755218215278374702983)
        ·
          refine ⟨58318132827322917562054475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38878755218215278374702983 58318132827322917562054475)
          ·
            refine ⟨87477199240984376343081713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58318132827322917562054475 87477199240984376343081713)
            ·
              refine ⟨65607899430738282257311285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87477199240984376343081713 65607899430738282257311285)
              ·
                refine ⟨6150740571631713961622933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65607899430738282257311285 6150740571631713961622933)
                ·
                  refine ⟨288315964295236591951075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6150740571631713961622933 288315964295236591951075)
                  ·
                    rfl

theorem cell21_1263360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_1263360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263360 prefixEnd_1263360 := by exact prefixLift 1263360
  have htrace : WordTrace (prefixWord ++ tailWord_1263360) baseStart_1263360 baseEnd_1263360 := by
    simpa [prefixWord, tailWord_1263360, baseEnd_1263360] using wordTrace_append hprefix tailTrace_1263360
  have hstable : (prefixWord ++ tailWord_1263360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263360).length < 2 ^ (prefixWord ++ tailWord_1263360).sum := by decide
  have hdescent : baseEnd_1263360 < baseStart_1263360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263363 : List Nat := [1, 1, 1, 3, 2, 2, 4, 4, 3]
def baseStart_1263363 : Nat := 118140960795 + 1263363 * 2 ^ 59
def prefixEnd_1263363 : Nat := 4983230072969 + 3 ^ 40 * 1263363 * 2
def baseEnd_1263363 : Nat := 288316648936109253401069

theorem tailTrace_1263363 : CollatzResearch.WordTrace tailWord_1263363 prefixEnd_1263363 288316648936109253401069 := by
  unfold tailWord_1263363
  simp only [CollatzResearch.WordTrace]
  refine ⟨46078634122059091067562743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30719089414706060711708495 46078634122059091067562743)
  ·
    refine ⟨69117951183088636601344115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46078634122059091067562743 69117951183088636601344115)
    ·
      refine ⟨103676926774632954902016173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69117951183088636601344115 103676926774632954902016173)
      ·
        refine ⟨38878847540487358088256065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103676926774632954902016173 38878847540487358088256065)
        ·
          refine ⟨29159135655365518566192049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38878847540487358088256065 29159135655365518566192049)
          ·
            refine ⟨21869351741524138924644037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29159135655365518566192049 21869351741524138924644037)
            ·
              refine ⟨4100503451535776048370757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21869351741524138924644037 4100503451535776048370757)
              ·
                refine ⟨768844397162958009069517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4100503451535776048370757 768844397162958009069517)
                ·
                  refine ⟨288316648936109253401069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 768844397162958009069517 288316648936109253401069)
                  ·
                    rfl

theorem cell21_1263363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 3].length) (baseStart_1263363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263363 prefixEnd_1263363 := by exact prefixLift 1263363
  have htrace : WordTrace (prefixWord ++ tailWord_1263363) baseStart_1263363 baseEnd_1263363 := by
    simpa [prefixWord, tailWord_1263363, baseEnd_1263363] using wordTrace_append hprefix tailTrace_1263363
  have hstable : (prefixWord ++ tailWord_1263363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263363).length < 2 ^ (prefixWord ++ tailWord_1263363).sum := by decide
  have hdescent : baseEnd_1263363 < baseStart_1263363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263391 : List Nat := [1, 1, 2, 4, 2, 1, 3, 7]
def baseStart_1263391 : Nat := 118140960795 + 1263391 * 2 ^ 59
def prefixEnd_1263391 : Nat := 4983230072969 + 3 ^ 40 * 1263391 * 2
def baseEnd_1263391 : Nat := 96107679639195808978115

theorem tailTrace_1263391 : CollatzResearch.WordTrace tailWord_1263391 prefixEnd_1263391 96107679639195808978115 := by
  unfold tailWord_1263391
  simp only [CollatzResearch.WordTrace]
  refine ⟨46079655365957651849582027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30719770243971767899721351 46079655365957651849582027)
  ·
    refine ⟨69119483048936477774373041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46079655365957651849582027 69119483048936477774373041)
    ·
      refine ⟨51839612286702358330779781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69119483048936477774373041 51839612286702358330779781)
      ·
        refine ⟨9719927303756692187021209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51839612286702358330779781 9719927303756692187021209)
        ·
          refine ⟨7289945477817519140265907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9719927303756692187021209 7289945477817519140265907)
          ·
            refine ⟨10934918216726278710398861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7289945477817519140265907 10934918216726278710398861)
            ·
              refine ⟨4100594331272354516399573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10934918216726278710398861 4100594331272354516399573)
              ·
                refine ⟨96107679639195808978115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4100594331272354516399573 96107679639195808978115)
                ·
                  rfl

theorem cell21_1263391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 7].length) (baseStart_1263391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263391 prefixEnd_1263391 := by exact prefixLift 1263391
  have htrace : WordTrace (prefixWord ++ tailWord_1263391) baseStart_1263391 baseEnd_1263391 := by
    simpa [prefixWord, tailWord_1263391, baseEnd_1263391] using wordTrace_append hprefix tailTrace_1263391
  have hstable : (prefixWord ++ tailWord_1263391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263391).length < 2 ^ (prefixWord ++ tailWord_1263391).sum := by decide
  have hdescent : baseEnd_1263391 < baseStart_1263391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263414 : List Nat := [5, 1, 2, 2, 1, 2, 3, 2, 3]
def baseStart_1263414 : Nat := 118140960795 + 1263414 * 2 ^ 59
def prefixEnd_1263414 : Nat := 4983230072969 + 3 ^ 40 * 1263414 * 2
def baseEnd_1263414 : Nat := 288328287830944498050965

theorem tailTrace_1263414 : CollatzResearch.WordTrace tailWord_1263414 prefixEnd_1263414 288328287830944498050965 := by
  unfold tailWord_1263414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2880030890304645423604331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30720329496582884518446197 2880030890304645423604331)
  ·
    refine ⟨4320046335456968135406497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2880030890304645423604331 4320046335456968135406497)
    ·
      refine ⟨3240034751592726101554873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4320046335456968135406497 3240034751592726101554873)
      ·
        refine ⟨2430026063694544576166155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3240034751592726101554873 2430026063694544576166155)
        ·
          refine ⟨3645039095541816864249233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2430026063694544576166155 3645039095541816864249233)
          ·
            refine ⟨2733779321656362648186925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3645039095541816864249233 2733779321656362648186925)
            ·
              refine ⟨1025167245621135993070097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2733779321656362648186925 1025167245621135993070097)
              ·
                refine ⟨768875434215851994802573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1025167245621135993070097 768875434215851994802573)
                ·
                  refine ⟨288328287830944498050965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 768875434215851994802573 288328287830944498050965)
                  ·
                    rfl

theorem cell21_1263414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_1263414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263414 prefixEnd_1263414 := by exact prefixLift 1263414
  have htrace : WordTrace (prefixWord ++ tailWord_1263414) baseStart_1263414 baseEnd_1263414 := by
    simpa [prefixWord, tailWord_1263414, baseEnd_1263414] using wordTrace_append hprefix tailTrace_1263414
  have hstable : (prefixWord ++ tailWord_1263414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263414).length < 2 ^ (prefixWord ++ tailWord_1263414).sum := by decide
  have hdescent : baseEnd_1263414 < baseStart_1263414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263470 : List Nat := [4, 1, 2, 3, 1, 1, 1, 4, 4]
def baseStart_1263470 : Nat := 118140960795 + 1263470 * 2 ^ 59
def prefixEnd_1263470 : Nat := 4983230072969 + 3 ^ 40 * 1263470 * 2
def baseEnd_1263470 : Nat := 288341067793900845117517

theorem tailTrace_1263470 : CollatzResearch.WordTrace tailWord_1263470 prefixEnd_1263470 288341067793900845117517 := by
  unfold tailWord_1263470
  simp only [CollatzResearch.WordTrace]
  refine ⟨5760317091583931042713483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30721691155114298894471909 5760317091583931042713483)
  ·
    refine ⟨8640475637375896564070225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5760317091583931042713483 8640475637375896564070225)
    ·
      refine ⟨6480356728031922423052669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8640475637375896564070225 6480356728031922423052669)
      ·
        refine ⟨2430133773011970908644751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6480356728031922423052669 2430133773011970908644751)
        ·
          refine ⟨3645200659517956362967127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2430133773011970908644751 3645200659517956362967127)
          ·
            refine ⟨5467800989276934544450691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3645200659517956362967127 5467800989276934544450691)
            ·
              refine ⟨8201701483915401816676037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5467800989276934544450691 8201701483915401816676037)
              ·
                refine ⟨1537819028234137840626757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8201701483915401816676037 1537819028234137840626757)
                ·
                  refine ⟨288341067793900845117517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1537819028234137840626757 288341067793900845117517)
                  ·
                    rfl

theorem cell21_1263470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_1263470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263470 prefixEnd_1263470 := by exact prefixLift 1263470
  have htrace : WordTrace (prefixWord ++ tailWord_1263470) baseStart_1263470 baseEnd_1263470 := by
    simpa [prefixWord, tailWord_1263470, baseEnd_1263470] using wordTrace_append hprefix tailTrace_1263470
  have hstable : (prefixWord ++ tailWord_1263470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263470).length < 2 ^ (prefixWord ++ tailWord_1263470).sum := by decide
  have hdescent : baseEnd_1263470 < baseStart_1263470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263557 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 7]
def baseStart_1263557 : Nat := 118140960795 + 1263557 * 2 ^ 59
def prefixEnd_1263557 : Nat := 4983230072969 + 3 ^ 40 * 1263557 * 2
def baseEnd_1263557 : Nat := 288360922379208027167339

theorem tailTrace_1263557 : CollatzResearch.WordTrace tailWord_1263557 prefixEnd_1263557 288360922379208027167339 := by
  unfold tailWord_1263557
  simp only [CollatzResearch.WordTrace]
  refine ⟨46085709883356262200124925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30723806588904174800083283 46085709883356262200124925)
  ·
    refine ⟨17282141206258598325046847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46085709883356262200124925 17282141206258598325046847)
    ·
      refine ⟨25923211809387897487570271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17282141206258598325046847 25923211809387897487570271)
      ·
        refine ⟨38884817714081846231355407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25923211809387897487570271 38884817714081846231355407)
        ·
          refine ⟨58327226571122769347033111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38884817714081846231355407 58327226571122769347033111)
          ·
            refine ⟨87490839856684154020549667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58327226571122769347033111 87490839856684154020549667)
            ·
              refine ⟨131236259785026231030824501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87490839856684154020549667 131236259785026231030824501)
              ·
                refine ⟨12303399354846209159139797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 131236259785026231030824501 12303399354846209159139797)
                ·
                  refine ⟨288360922379208027167339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12303399354846209159139797 288360922379208027167339)
                  ·
                    rfl

theorem cell21_1263557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_1263557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263557 prefixEnd_1263557 := by exact prefixLift 1263557
  have htrace : WordTrace (prefixWord ++ tailWord_1263557) baseStart_1263557 baseEnd_1263557 := by
    simpa [prefixWord, tailWord_1263557, baseEnd_1263557] using wordTrace_append hprefix tailTrace_1263557
  have hstable : (prefixWord ++ tailWord_1263557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263557).length < 2 ^ (prefixWord ++ tailWord_1263557).sum := by decide
  have hdescent : baseEnd_1263557 < baseStart_1263557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263560 : List Nat := [2, 1, 3, 1, 4, 1, 4, 5]
def baseStart_1263560 : Nat := 118140960795 + 1263560 * 2 ^ 59
def prefixEnd_1263560 : Nat := 4983230072969 + 3 ^ 40 * 1263560 * 2
def baseEnd_1263560 : Nat := 96120535673360229539111

theorem tailTrace_1263560 : CollatzResearch.WordTrace tailWord_1263560 prefixEnd_1263560 96120535673360229539111 := by
  unfold tailWord_1263560
  simp only [CollatzResearch.WordTrace]
  refine ⟨23042909651172696856242067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30723879534896929141656089 23042909651172696856242067)
  ·
    refine ⟨34564364476759045284363101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23042909651172696856242067 34564364476759045284363101)
    ·
      refine ⟨12961636678784641981636163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34564364476759045284363101 12961636678784641981636163)
      ·
        refine ⟨19442455018176962972454245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12961636678784641981636163 19442455018176962972454245)
        ·
          refine ⟨3645460315908180557335171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19442455018176962972454245 3645460315908180557335171)
          ·
            refine ⟨5468190473862270836002757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3645460315908180557335171 5468190473862270836002757)
            ·
              refine ⟨1025285713849175781750517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5468190473862270836002757 1025285713849175781750517)
              ·
                refine ⟨96120535673360229539111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1025285713849175781750517 96120535673360229539111)
                ·
                  rfl

theorem cell21_1263560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 5].length) (baseStart_1263560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263560 prefixEnd_1263560 := by exact prefixLift 1263560
  have htrace : WordTrace (prefixWord ++ tailWord_1263560) baseStart_1263560 baseEnd_1263560 := by
    simpa [prefixWord, tailWord_1263560, baseEnd_1263560] using wordTrace_append hprefix tailTrace_1263560
  have hstable : (prefixWord ++ tailWord_1263560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263560).length < 2 ^ (prefixWord ++ tailWord_1263560).sum := by decide
  have hdescent : baseEnd_1263560 < baseStart_1263560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263588 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 6]
def baseStart_1263588 : Nat := 118140960795 + 1263588 * 2 ^ 59
def prefixEnd_1263588 : Nat := 4983230072969 + 3 ^ 40 * 1263588 * 2
def baseEnd_1263588 : Nat := 288367997001558862150609

theorem tailTrace_1263588 : CollatzResearch.WordTrace tailWord_1263588 prefixEnd_1263588 288367997001558862150609 := by
  unfold tailWord_1263588
  simp only [CollatzResearch.WordTrace]
  refine ⟨23043420273121977247251709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30724560364162636329668945 23043420273121977247251709)
  ·
    refine ⟨8641282602420741467719391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23043420273121977247251709 8641282602420741467719391)
    ·
      refine ⟨12961923903631112201579087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8641282602420741467719391 12961923903631112201579087)
      ·
        refine ⟨19442885855446668302368631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12961923903631112201579087 19442885855446668302368631)
        ·
          refine ⟨29164328783170002453552947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19442885855446668302368631 29164328783170002453552947)
          ·
            refine ⟨43746493174755003680329421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29164328783170002453552947 43746493174755003680329421)
            ·
              refine ⟨16404934940533126380123533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43746493174755003680329421 16404934940533126380123533)
              ·
                refine ⟨6151850602699922392546325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16404934940533126380123533 6151850602699922392546325)
                ·
                  refine ⟨288367997001558862150609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6151850602699922392546325 288367997001558862150609)
                  ·
                    rfl

theorem cell21_1263588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_1263588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263588 prefixEnd_1263588 := by exact prefixLift 1263588
  have htrace : WordTrace (prefixWord ++ tailWord_1263588) baseStart_1263588 baseEnd_1263588 := by
    simpa [prefixWord, tailWord_1263588, baseEnd_1263588] using wordTrace_append hprefix tailTrace_1263588
  have hstable : (prefixWord ++ tailWord_1263588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263588).length < 2 ^ (prefixWord ++ tailWord_1263588).sum := by decide
  have hdescent : baseEnd_1263588 < baseStart_1263588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263597 : List Nat := [1, 5, 1, 4, 2, 1, 2, 1, 4]
def baseStart_1263597 : Nat := 118140960795 + 1263597 * 2 ^ 59
def prefixEnd_1263597 : Nat := 4983230072969 + 3 ^ 40 * 1263597 * 2
def baseEnd_1263597 : Nat := 288370050924176846500591

theorem tailTrace_1263597 : CollatzResearch.WordTrace tailWord_1263597 prefixEnd_1263597 288370050924176846500591 := by
  unfold tailWord_1263597
  simp only [CollatzResearch.WordTrace]
  refine ⟨46087168803211349031581045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30724779202140899354387363 46087168803211349031581045)
  ·
    refine ⟨4320672075301063971710723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46087168803211349031581045 4320672075301063971710723)
    ·
      refine ⟨6481008112951595957566085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4320672075301063971710723 6481008112951595957566085)
      ·
        refine ⟨1215189021178424242043641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6481008112951595957566085 1215189021178424242043641)
        ·
          refine ⟨911391765883818181532731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1215189021178424242043641 911391765883818181532731)
          ·
            refine ⟨1367087648825727272299097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 911391765883818181532731 1367087648825727272299097)
            ·
              refine ⟨1025315736619295454224323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1367087648825727272299097 1025315736619295454224323)
              ·
                refine ⟨1537973604928943181336485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1025315736619295454224323 1537973604928943181336485)
                ·
                  refine ⟨288370050924176846500591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1537973604928943181336485 288370050924176846500591)
                  ·
                    rfl

theorem cell21_1263597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_1263597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263597 prefixEnd_1263597 := by exact prefixLift 1263597
  have htrace : WordTrace (prefixWord ++ tailWord_1263597) baseStart_1263597 baseEnd_1263597 := by
    simpa [prefixWord, tailWord_1263597, baseEnd_1263597] using wordTrace_append hprefix tailTrace_1263597
  have hstable : (prefixWord ++ tailWord_1263597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263597).length < 2 ^ (prefixWord ++ tailWord_1263597).sum := by decide
  have hdescent : baseEnd_1263597 < baseStart_1263597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263636 : List Nat := [2, 4, 3, 2, 10]
def baseStart_1263636 : Nat := 118140960795 + 1263636 * 2 ^ 59
def prefixEnd_1263636 : Nat := 4983230072969 + 3 ^ 40 * 1263636 * 2
def baseEnd_1263636 : Nat := 3560233966117548708031

theorem tailTrace_1263636 : CollatzResearch.WordTrace tailWord_1263636 prefixEnd_1263636 3560233966117548708031 := by
  unfold tailWord_1263636
  simp only [CollatzResearch.WordTrace]
  refine ⟨23044295625035029346125381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30725727500046705794833841 23044295625035029346125381)
  ·
    refine ⟨4320805429694068002398509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23044295625035029346125381 4320805429694068002398509)
    ·
      refine ⟨1620302036135275500899441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4320805429694068002398509 1620302036135275500899441)
      ·
        refine ⟨1215226527101456625674581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1620302036135275500899441 1215226527101456625674581)
        ·
          refine ⟨3560233966117548708031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1215226527101456625674581 3560233966117548708031)
          ·
            rfl

theorem cell21_1263636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 10].length) (baseStart_1263636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263636 prefixEnd_1263636 := by exact prefixLift 1263636
  have htrace : WordTrace (prefixWord ++ tailWord_1263636) baseStart_1263636 baseEnd_1263636 := by
    simpa [prefixWord, tailWord_1263636, baseEnd_1263636] using wordTrace_append hprefix tailTrace_1263636
  have hstable : (prefixWord ++ tailWord_1263636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263636).length < 2 ^ (prefixWord ++ tailWord_1263636).sum := by decide
  have hdescent : baseEnd_1263636 < baseStart_1263636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263650 : List Nat := [3, 3, 1, 1, 1, 2, 2, 3, 5]
def baseStart_1263650 : Nat := 118140960795 + 1263650 * 2 ^ 59
def prefixEnd_1263650 : Nat := 4983230072969 + 3 ^ 40 * 1263650 * 2
def baseEnd_1263650 : Nat := 288382146246260532117149

theorem tailTrace_1263650 : CollatzResearch.WordTrace tailWord_1263650 prefixEnd_1263650 288382146246260532117149 := by
  unfold tailWord_1263650
  simp only [CollatzResearch.WordTrace]
  refine ⟨11522275468004834770815101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30726067914679559388840269 11522275468004834770815101)
  ·
    refine ⟨4320853300501813039055663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11522275468004834770815101 4320853300501813039055663)
    ·
      refine ⟨6481279950752719558583495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4320853300501813039055663 6481279950752719558583495)
      ·
        refine ⟨9721919926129079337875243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6481279950752719558583495 9721919926129079337875243)
        ·
          refine ⟨14582879889193619006812865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9721919926129079337875243 14582879889193619006812865)
          ·
            refine ⟨10937159916895214255109649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14582879889193619006812865 10937159916895214255109649)
            ·
              refine ⟨8202869937671410691332237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10937159916895214255109649 8202869937671410691332237)
              ·
                refine ⟨3076076226626779009249589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8202869937671410691332237 3076076226626779009249589)
                ·
                  refine ⟨288382146246260532117149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3076076226626779009249589 288382146246260532117149)
                  ·
                    rfl

theorem cell21_1263650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_1263650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263650 prefixEnd_1263650 := by exact prefixLift 1263650
  have htrace : WordTrace (prefixWord ++ tailWord_1263650) baseStart_1263650 baseEnd_1263650 := by
    simpa [prefixWord, tailWord_1263650, baseEnd_1263650] using wordTrace_append hprefix tailTrace_1263650
  have hstable : (prefixWord ++ tailWord_1263650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263650).length < 2 ^ (prefixWord ++ tailWord_1263650).sum := by decide
  have hdescent : baseEnd_1263650 < baseStart_1263650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263726 : List Nat := [4, 1, 2, 2, 1, 1, 1, 4, 5]
def baseStart_1263726 : Nat := 118140960795 + 1263726 * 2 ^ 59
def prefixEnd_1263726 : Nat := 4983230072969 + 3 ^ 40 * 1263726 * 2
def baseEnd_1263726 : Nat := 288399490481701288850327

theorem tailTrace_1263726 : CollatzResearch.WordTrace tailWord_1263726 prefixEnd_1263726 288399490481701288850327 := by
  unfold tailWord_1263726
  simp only [CollatzResearch.WordTrace]
  refine ⟨5761484227468000507878379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30727915879829336042018021 5761484227468000507878379)
  ·
    refine ⟨8642226341202000761817569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5761484227468000507878379 8642226341202000761817569)
    ·
      refine ⟨6481669755901500571363177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8642226341202000761817569 6481669755901500571363177)
      ·
        refine ⟨4861252316926125428522383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6481669755901500571363177 4861252316926125428522383)
        ·
          refine ⟨7291878475389188142783575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4861252316926125428522383 7291878475389188142783575)
          ·
            refine ⟨10937817713083782214175363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7291878475389188142783575 10937817713083782214175363)
            ·
              refine ⟨16406726569625673321263045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10937817713083782214175363 16406726569625673321263045)
              ·
                refine ⟨3076261231804813747736821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16406726569625673321263045 3076261231804813747736821)
                ·
                  refine ⟨288399490481701288850327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3076261231804813747736821 288399490481701288850327)
                  ·
                    rfl

theorem cell21_1263726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_1263726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263726 prefixEnd_1263726 := by exact prefixLift 1263726
  have htrace : WordTrace (prefixWord ++ tailWord_1263726) baseStart_1263726 baseEnd_1263726 := by
    simpa [prefixWord, tailWord_1263726, baseEnd_1263726] using wordTrace_append hprefix tailTrace_1263726
  have hstable : (prefixWord ++ tailWord_1263726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263726).length < 2 ^ (prefixWord ++ tailWord_1263726).sum := by decide
  have hdescent : baseEnd_1263726 < baseStart_1263726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263740 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 6]
def baseStart_1263740 : Nat := 118140960795 + 1263740 * 2 ^ 59
def prefixEnd_1263740 : Nat := 4983230072969 + 3 ^ 40 * 1263740 * 2
def baseEnd_1263740 : Nat := 288402685472440375616965

theorem tailTrace_1263740 : CollatzResearch.WordTrace tailWord_1263740 prefixEnd_1263740 288402685472440375616965 := by
  unfold tailWord_1263740
  simp only [CollatzResearch.WordTrace]
  refine ⟨23046192220846642227018337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30728256294462189636024449 23046192220846642227018337)
  ·
    refine ⟨17284644165634981670263753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23046192220846642227018337 17284644165634981670263753)
    ·
      refine ⟨12963483124226236252697815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17284644165634981670263753 12963483124226236252697815)
      ·
        refine ⟨19445224686339354379046723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12963483124226236252697815 19445224686339354379046723)
        ·
          refine ⟨29167837029509031568570085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19445224686339354379046723 29167837029509031568570085)
          ·
            refine ⟨5468969443032943419106891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29167837029509031568570085 5468969443032943419106891)
            ·
              refine ⟨8203454164549415128660337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5468969443032943419106891 8203454164549415128660337)
              ·
                refine ⟨6152590623412061346495253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8203454164549415128660337 6152590623412061346495253)
                ·
                  refine ⟨288402685472440375616965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6152590623412061346495253 288402685472440375616965)
                  ·
                    rfl

theorem cell21_1263740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_1263740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263740 prefixEnd_1263740 := by exact prefixLift 1263740
  have htrace : WordTrace (prefixWord ++ tailWord_1263740) baseStart_1263740 baseEnd_1263740 := by
    simpa [prefixWord, tailWord_1263740, baseEnd_1263740] using wordTrace_append hprefix tailTrace_1263740
  have hstable : (prefixWord ++ tailWord_1263740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263740).length < 2 ^ (prefixWord ++ tailWord_1263740).sum := by decide
  have hdescent : baseEnd_1263740 < baseStart_1263740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263836 : List Nat := [2, 2, 5, 2, 1, 1, 1, 2, 5]
def baseStart_1263836 : Nat := 118140960795 + 1263836 * 2 ^ 59
def prefixEnd_1263836 : Nat := 4983230072969 + 3 ^ 40 * 1263836 * 2
def baseEnd_1263836 : Nat := 288424593980365542016769

theorem tailTrace_1263836 : CollatzResearch.WordTrace tailWord_1263836 prefixEnd_1263836 288424593980365542016769 := by
  unfold tailWord_1263836
  simp only [CollatzResearch.WordTrace]
  refine ⟨23047942924672746424765681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30730590566230328566354241 23047942924672746424765681)
  ·
    refine ⟨17285957193504559818574261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23047942924672746424765681 17285957193504559818574261)
    ·
      refine ⟨1620558486891052482991337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17285957193504559818574261 1620558486891052482991337)
      ·
        refine ⟨1215418865168289362243503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1620558486891052482991337 1215418865168289362243503)
        ·
          refine ⟨1823128297752434043365255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1215418865168289362243503 1823128297752434043365255)
          ·
            refine ⟨2734692446628651065047883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1823128297752434043365255 2734692446628651065047883)
            ·
              refine ⟨4102038669942976597571825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2734692446628651065047883 4102038669942976597571825)
              ·
                refine ⟨3076529002457232448178869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4102038669942976597571825 3076529002457232448178869)
                ·
                  refine ⟨288424593980365542016769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3076529002457232448178869 288424593980365542016769)
                  ·
                    rfl

theorem cell21_1263836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_1263836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263836 prefixEnd_1263836 := by exact prefixLift 1263836
  have htrace : WordTrace (prefixWord ++ tailWord_1263836) baseStart_1263836 baseEnd_1263836 := by
    simpa [prefixWord, tailWord_1263836, baseEnd_1263836] using wordTrace_append hprefix tailTrace_1263836
  have hstable : (prefixWord ++ tailWord_1263836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263836).length < 2 ^ (prefixWord ++ tailWord_1263836).sum := by decide
  have hdescent : baseEnd_1263836 < baseStart_1263836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263951 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 8]
def baseStart_1263951 : Nat := 118140960795 + 1263951 * 2 ^ 59
def prefixEnd_1263951 : Nat := 4983230072969 + 3 ^ 40 * 1263951 * 2
def baseEnd_1263951 : Nat := 288450838547150897599867

theorem tailTrace_1263951 : CollatzResearch.WordTrace tailWord_1263951 prefixEnd_1263951 288450838547150897599867 := by
  unfold tailWord_1263951
  simp only [CollatzResearch.WordTrace]
  refine ⟨46100080243928867489967707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30733386829285911659978471 46100080243928867489967707)
  ·
    refine ⟨69150120365893301234951561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46100080243928867489967707 69150120365893301234951561)
    ·
      refine ⟨51862590274419975926213671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69150120365893301234951561 51862590274419975926213671)
      ·
        refine ⟨77793885411629963889320507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51862590274419975926213671 77793885411629963889320507)
        ·
          refine ⟨116690828117444945833980761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77793885411629963889320507 116690828117444945833980761)
          ·
            refine ⟨87518121088083709375485571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116690828117444945833980761 87518121088083709375485571)
            ·
              refine ⟨131277181632125564063228357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87518121088083709375485571 131277181632125564063228357)
              ·
                refine ⟨24614471556023543261855317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131277181632125564063228357 24614471556023543261855317)
                ·
                  refine ⟨288450838547150897599867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24614471556023543261855317 288450838547150897599867)
                  ·
                    rfl

theorem cell21_1263951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 8].length) (baseStart_1263951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263951 prefixEnd_1263951 := by exact prefixLift 1263951
  have htrace : WordTrace (prefixWord ++ tailWord_1263951) baseStart_1263951 baseEnd_1263951 := by
    simpa [prefixWord, tailWord_1263951, baseEnd_1263951] using wordTrace_append hprefix tailTrace_1263951
  have hstable : (prefixWord ++ tailWord_1263951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263951).length < 2 ^ (prefixWord ++ tailWord_1263951).sum := by decide
  have hdescent : baseEnd_1263951 < baseStart_1263951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263982 : List Nat := [4, 1, 2, 14]
def baseStart_1263982 : Nat := 118140960795 + 1263982 * 2 ^ 59
def prefixEnd_1263982 : Nat := 4983230072969 + 3 ^ 40 * 1263982 * 2
def baseEnd_1263982 : Nat := 1187069601520583261659

theorem tailTrace_1263982 : CollatzResearch.WordTrace tailWord_1263982 prefixEnd_1263982 1187069601520583261659 := by
  unfold tailWord_1263982
  simp only [CollatzResearch.WordTrace]
  refine ⟨5762651363352069973043275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30734140604544373189564133 5762651363352069973043275)
  ·
    refine ⟨8643977045028104959564913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5762651363352069973043275 8643977045028104959564913)
    ·
      refine ⟨6482982783771078719673685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8643977045028104959564913 6482982783771078719673685)
      ·
        refine ⟨1187069601520583261659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 6482982783771078719673685 1187069601520583261659)
        ·
          rfl

theorem cell21_1263982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 14].length) (baseStart_1263982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1263982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1263982 prefixEnd_1263982 := by exact prefixLift 1263982
  have htrace : WordTrace (prefixWord ++ tailWord_1263982) baseStart_1263982 baseEnd_1263982 := by
    simpa [prefixWord, tailWord_1263982, baseEnd_1263982] using wordTrace_append hprefix tailTrace_1263982
  have hstable : (prefixWord ++ tailWord_1263982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263982).length < 2 ^ (prefixWord ++ tailWord_1263982).sum := by decide
  have hdescent : baseEnd_1263982 < baseStart_1263982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264098 : List Nat := [3, 3, 3, 2, 1, 1, 3, 2, 3]
def baseStart_1264098 : Nat := 118140960795 + 1264098 * 2 ^ 59
def prefixEnd_1264098 : Nat := 4983230072969 + 3 ^ 40 * 1264098 * 2
def baseEnd_1264098 : Nat := 288484385949911308649567

theorem tailTrace_1264098 : CollatzResearch.WordTrace tailWord_1264098 prefixEnd_1264098 288484385949911308649567 := by
  unfold tailWord_1264098
  simp only [CollatzResearch.WordTrace]
  refine ⟨11526360443599077898892237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30736961182930874397045965 11526360443599077898892237)
  ·
    refine ⟨4322385166349654212084589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11526360443599077898892237 4322385166349654212084589)
    ·
      refine ⟨1620894437381120329531721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4322385166349654212084589 1620894437381120329531721)
      ·
        refine ⟨1215670828035840247148791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1620894437381120329531721 1215670828035840247148791)
        ·
          refine ⟨1823506242053760370723187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1215670828035840247148791 1823506242053760370723187)
          ·
            refine ⟨2735259363080640556084781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1823506242053760370723187 2735259363080640556084781)
            ·
              refine ⟨1025722261155240208531793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2735259363080640556084781 1025722261155240208531793)
              ·
                refine ⟨769291695866430156398845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1025722261155240208531793 769291695866430156398845)
                ·
                  refine ⟨288484385949911308649567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 769291695866430156398845 288484385949911308649567)
                  ·
                    rfl

theorem cell21_1264098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_1264098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264098 prefixEnd_1264098 := by exact prefixLift 1264098
  have htrace : WordTrace (prefixWord ++ tailWord_1264098) baseStart_1264098 baseEnd_1264098 := by
    simpa [prefixWord, tailWord_1264098, baseEnd_1264098] using wordTrace_append hprefix tailTrace_1264098
  have hstable : (prefixWord ++ tailWord_1264098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264098).length < 2 ^ (prefixWord ++ tailWord_1264098).sum := by decide
  have hdescent : baseEnd_1264098 < baseStart_1264098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264106 : List Nat := [3, 1, 3, 1, 3, 1, 3, 1, 5]
def baseStart_1264106 : Nat := 118140960795 + 1264106 * 2 ^ 59
def prefixEnd_1264106 : Nat := 4983230072969 + 3 ^ 40 * 1264106 * 2
def baseEnd_1264106 : Nat := 288486211658905072516217

theorem tailTrace_1264106 : CollatzResearch.WordTrace tailWord_1264106 prefixEnd_1264106 288486211658905072516217 := by
  unfold tailWord_1264106
  simp only [CollatzResearch.WordTrace]
  refine ⟨11526433389591832240465043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30737155705578219307906781 11526433389591832240465043)
  ·
    refine ⟨17289650084387748360697565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11526433389591832240465043 17289650084387748360697565)
    ·
      refine ⟨6483618781645405635261587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17289650084387748360697565 6483618781645405635261587)
      ·
        refine ⟨9725428172468108452892381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6483618781645405635261587 9725428172468108452892381)
        ·
          refine ⟨3647035564675540669834643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9725428172468108452892381 3647035564675540669834643)
          ·
            refine ⟨5470553347013311004751965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3647035564675540669834643 5470553347013311004751965)
            ·
              refine ⟨2051457505129991626781987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5470553347013311004751965 2051457505129991626781987)
              ·
                refine ⟨3077186257694987440172981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2051457505129991626781987 3077186257694987440172981)
                ·
                  refine ⟨288486211658905072516217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3077186257694987440172981 288486211658905072516217)
                  ·
                    rfl

theorem cell21_1264106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_1264106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264106 prefixEnd_1264106 := by exact prefixLift 1264106
  have htrace : WordTrace (prefixWord ++ tailWord_1264106) baseStart_1264106 baseEnd_1264106 := by
    simpa [prefixWord, tailWord_1264106, baseEnd_1264106] using wordTrace_append hprefix tailTrace_1264106
  have hstable : (prefixWord ++ tailWord_1264106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264106).length < 2 ^ (prefixWord ++ tailWord_1264106).sum := by decide
  have hdescent : baseEnd_1264106 < baseStart_1264106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264120 : List Nat := [2, 1, 2, 1, 1, 4, 3, 3, 4]
def baseStart_1264120 : Nat := 118140960795 + 1264120 * 2 ^ 59
def prefixEnd_1264120 : Nat := 4983230072969 + 3 ^ 40 * 1264120 * 2
def baseEnd_1264120 : Nat := 288489406649644159282855

theorem tailTrace_1264120 : CollatzResearch.WordTrace tailWord_1264120 prefixEnd_1264120 288489406649644159282855 := by
  unfold tailWord_1264120
  simp only [CollatzResearch.WordTrace]
  refine ⟨23053122090158304676434907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30737496120211072901913209 23053122090158304676434907)
  ·
    refine ⟨34579683135237457014652361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23053122090158304676434907 34579683135237457014652361)
    ·
      refine ⟨25934762351428092760989271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34579683135237457014652361 25934762351428092760989271)
      ·
        refine ⟨38902143527142139141483907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25934762351428092760989271 38902143527142139141483907)
        ·
          refine ⟨58353215290713208712225861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38902143527142139141483907 58353215290713208712225861)
          ·
            refine ⟨10941227867008726633542349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58353215290713208712225861 10941227867008726633542349)
            ·
              refine ⟨4102960450128272487578381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10941227867008726633542349 4102960450128272487578381)
              ·
                refine ⟨1538610168798102182841893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4102960450128272487578381 1538610168798102182841893)
                ·
                  refine ⟨288489406649644159282855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1538610168798102182841893 288489406649644159282855)
                  ·
                    rfl

theorem cell21_1264120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 4].length) (baseStart_1264120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264120 prefixEnd_1264120 := by exact prefixLift 1264120
  have htrace : WordTrace (prefixWord ++ tailWord_1264120) baseStart_1264120 baseEnd_1264120 := by
    simpa [prefixWord, tailWord_1264120, baseEnd_1264120] using wordTrace_append hprefix tailTrace_1264120
  have hstable : (prefixWord ++ tailWord_1264120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264120).length < 2 ^ (prefixWord ++ tailWord_1264120).sum := by decide
  have hdescent : baseEnd_1264120 < baseStart_1264120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264151 : List Nat := [1, 1, 3, 6, 1, 9]
def baseStart_1264151 : Nat := 118140960795 + 1264151 * 2 ^ 59
def prefixEnd_1264151 : Nat := 4983230072969 + 3 ^ 40 * 1264151 * 2
def baseEnd_1264151 : Nat := 10685054861925740528375

theorem tailTrace_1264151 : CollatzResearch.WordTrace tailWord_1264151 prefixEnd_1264151 10685054861925740528375 := by
  unfold tailWord_1264151
  simp only [CollatzResearch.WordTrace]
  refine ⟨46107374843204301647248307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30738249895469534431498871 46107374843204301647248307)
  ·
    refine ⟨69161062264806452470872461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46107374843204301647248307 69161062264806452470872461)
    ·
      refine ⟨25935398349302419676577173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69161062264806452470872461 25935398349302419676577173)
      ·
        refine ⟨1215721797623550922339555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25935398349302419676577173 1215721797623550922339555)
        ·
          refine ⟨1823582696435326383509333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1215721797623550922339555 1823582696435326383509333)
          ·
            refine ⟨10685054861925740528375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1823582696435326383509333 10685054861925740528375)
            ·
              rfl

theorem cell21_1264151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 9].length) (baseStart_1264151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264151 prefixEnd_1264151 := by exact prefixLift 1264151
  have htrace : WordTrace (prefixWord ++ tailWord_1264151) baseStart_1264151 baseEnd_1264151 := by
    simpa [prefixWord, tailWord_1264151, baseEnd_1264151] using wordTrace_append hprefix tailTrace_1264151
  have hstable : (prefixWord ++ tailWord_1264151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264151).length < 2 ^ (prefixWord ++ tailWord_1264151).sum := by decide
  have hdescent : baseEnd_1264151 < baseStart_1264151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264168 : List Nat := [2, 1, 5, 2, 1, 3, 1, 6]
def baseStart_1264168 : Nat := 118140960795 + 1264168 * 2 ^ 59
def prefixEnd_1264168 : Nat := 4983230072969 + 3 ^ 40 * 1264168 * 2
def baseEnd_1264168 : Nat := 96166786967868914160919

theorem tailTrace_1264168 : CollatzResearch.WordTrace tailWord_1264168 prefixEnd_1264168 96166786967868914160919 := by
  unfold tailWord_1264168
  simp only [CollatzResearch.WordTrace]
  refine ⟨23053997442071356775308579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30738663256095142367078105 23053997442071356775308579)
  ·
    refine ⟨34580996163107035162962869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23053997442071356775308579 34580996163107035162962869)
    ·
      refine ⟨3241968390291284546527769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34580996163107035162962869 3241968390291284546527769)
      ·
        refine ⟨2431476292718463409895827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3241968390291284546527769 2431476292718463409895827)
        ·
          refine ⟨3647214439077695114843741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2431476292718463409895827 3647214439077695114843741)
          ·
            refine ⟨1367705414654135668066403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3647214439077695114843741 1367705414654135668066403)
            ·
              refine ⟨2051558121981203502099605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1367705414654135668066403 2051558121981203502099605)
              ·
                refine ⟨96166786967868914160919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2051558121981203502099605 96166786967868914160919)
                ·
                  rfl

theorem cell21_1264168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 6].length) (baseStart_1264168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264168 prefixEnd_1264168 := by exact prefixLift 1264168
  have htrace : WordTrace (prefixWord ++ tailWord_1264168) baseStart_1264168 baseEnd_1264168 := by
    simpa [prefixWord, tailWord_1264168, baseEnd_1264168] using wordTrace_append hprefix tailTrace_1264168
  have hstable : (prefixWord ++ tailWord_1264168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264168).length < 2 ^ (prefixWord ++ tailWord_1264168).sum := by decide
  have hdescent : baseEnd_1264168 < baseStart_1264168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264182 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_1264182 : Nat := 118140960795 + 1264182 * 2 ^ 59
def prefixEnd_1264182 : Nat := 4983230072969 + 3 ^ 40 * 1264182 * 2
def baseEnd_1264182 : Nat := 288503555894345829249395

theorem tailTrace_1264182 : CollatzResearch.WordTrace tailWord_1264182 prefixEnd_1264182 288503555894345829249395 := by
  unfold tailWord_1264182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2881781594130749621351675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30739003670727995961084533 2881781594130749621351675)
  ·
    refine ⟨4322672391196124432027513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2881781594130749621351675 4322672391196124432027513)
    ·
      refine ⟨3242004293397093324020635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4322672391196124432027513 3242004293397093324020635)
      ·
        refine ⟨4863006440095639986030953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3242004293397093324020635 4863006440095639986030953)
        ·
          refine ⟨3647254830071729989523215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4863006440095639986030953 3647254830071729989523215)
          ·
            refine ⟨5470882245107594984284823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3647254830071729989523215 5470882245107594984284823)
            ·
              refine ⟨8206323367661392476427235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5470882245107594984284823 8206323367661392476427235)
              ·
                refine ⟨12309485051492088714640853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8206323367661392476427235 12309485051492088714640853)
                ·
                  refine ⟨288503555894345829249395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12309485051492088714640853 288503555894345829249395)
                  ·
                    rfl

theorem cell21_1264182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_1264182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264182 prefixEnd_1264182 := by exact prefixLift 1264182
  have htrace : WordTrace (prefixWord ++ tailWord_1264182) baseStart_1264182 baseEnd_1264182 := by
    simpa [prefixWord, tailWord_1264182, baseEnd_1264182] using wordTrace_append hprefix tailTrace_1264182
  have hstable : (prefixWord ++ tailWord_1264182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264182).length < 2 ^ (prefixWord ++ tailWord_1264182).sum := by decide
  have hdescent : baseEnd_1264182 < baseStart_1264182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264199 : List Nat := [1, 1, 4, 1, 4, 2, 2, 3, 3]
def baseStart_1264199 : Nat := 118140960795 + 1264199 * 2 ^ 59
def prefixEnd_1264199 : Nat := 4983230072969 + 3 ^ 40 * 1264199 * 2
def baseEnd_1264199 : Nat := 288507435525957577466027

theorem tailTrace_1264199 : CollatzResearch.WordTrace tailWord_1264199 prefixEnd_1264199 288507435525957577466027 := by
  unfold tailWord_1264199
  simp only [CollatzResearch.WordTrace]
  refine ⟨46109125547030405844995651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30739417031353603896663767 46109125547030405844995651)
  ·
    refine ⟨69163688320545608767493477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46109125547030405844995651 69163688320545608767493477)
    ·
      refine ⟨12968191560102301643905027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69163688320545608767493477 12968191560102301643905027)
      ·
        refine ⟨19452287340153452465857541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12968191560102301643905027 19452287340153452465857541)
        ·
          refine ⟨3647303876278772337348289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19452287340153452465857541 3647303876278772337348289)
          ·
            refine ⟨2735477907209079253011217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3647303876278772337348289 2735477907209079253011217)
            ·
              refine ⟨2051608430406809439758413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2735477907209079253011217 2051608430406809439758413)
              ·
                refine ⟨769353161402553539909405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2051608430406809439758413 769353161402553539909405)
                ·
                  refine ⟨288507435525957577466027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 769353161402553539909405 288507435525957577466027)
                  ·
                    rfl

theorem cell21_1264199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 3].length) (baseStart_1264199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264199 prefixEnd_1264199 := by exact prefixLift 1264199
  have htrace : WordTrace (prefixWord ++ tailWord_1264199) baseStart_1264199 baseEnd_1264199 := by
    simpa [prefixWord, tailWord_1264199, baseEnd_1264199] using wordTrace_append hprefix tailTrace_1264199
  have hstable : (prefixWord ++ tailWord_1264199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264199).length < 2 ^ (prefixWord ++ tailWord_1264199).sum := by decide
  have hdescent : baseEnd_1264199 < baseStart_1264199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264210 : List Nat := [3, 2, 2, 1, 2, 1, 10]
def baseStart_1264210 : Nat := 118140960795 + 1264210 * 2 ^ 59
def prefixEnd_1264210 : Nat := 4983230072969 + 3 ^ 40 * 1264210 * 2
def baseEnd_1264210 : Nat := 32056660652869333642519

theorem tailTrace_1264210 : CollatzResearch.WordTrace tailWord_1264210 prefixEnd_1264210 32056660652869333642519 := by
  unfold tailWord_1264210
  simp only [CollatzResearch.WordTrace]
  refine ⟨11527381687497638680911521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30739684499993703149097389 11527381687497638680911521)
  ·
    refine ⟨8645536265623229010683641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11527381687497638680911521 8645536265623229010683641)
    ·
      refine ⟨6484152199217421758012731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8645536265623229010683641 6484152199217421758012731)
      ·
        refine ⟨9726228298826132637019097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6484152199217421758012731 9726228298826132637019097)
        ·
          refine ⟨7294671224119599477764323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9726228298826132637019097 7294671224119599477764323)
          ·
            refine ⟨10942006836179399216646485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7294671224119599477764323 10942006836179399216646485)
            ·
              refine ⟨32056660652869333642519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10942006836179399216646485 32056660652869333642519)
              ·
                rfl

theorem cell21_1264210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 10].length) (baseStart_1264210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264210 prefixEnd_1264210 := by exact prefixLift 1264210
  have htrace : WordTrace (prefixWord ++ tailWord_1264210) baseStart_1264210 baseEnd_1264210 := by
    simpa [prefixWord, tailWord_1264210, baseEnd_1264210] using wordTrace_append hprefix tailTrace_1264210
  have hstable : (prefixWord ++ tailWord_1264210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264210).length < 2 ^ (prefixWord ++ tailWord_1264210).sum := by decide
  have hdescent : baseEnd_1264210 < baseStart_1264210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264289 : List Nat := [1, 2, 3, 3, 3, 1, 1, 3, 4]
def baseStart_1264289 : Nat := 118140960795 + 1264289 * 2 ^ 59
def prefixEnd_1264289 : Nat := 4983230072969 + 3 ^ 40 * 1264289 * 2
def baseEnd_1264289 : Nat := 288527974752137420965843

theorem tailTrace_1264289 : CollatzResearch.WordTrace tailWord_1264289 prefixEnd_1264289 288527974752137420965843 := by
  unfold tailWord_1264289
  simp only [CollatzResearch.WordTrace]
  refine ⟨46112408116704351215771921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30741605411136234143847947 46112408116704351215771921)
  ·
    refine ⟨34584306087528263411828941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46112408116704351215771921 34584306087528263411828941)
    ·
      refine ⟨12969114782823098779435853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34584306087528263411828941 12969114782823098779435853)
      ·
        refine ⟨4863418043558662042288445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12969114782823098779435853 4863418043558662042288445)
        ·
          refine ⟨1823781766334498265858167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4863418043558662042288445 1823781766334498265858167)
          ·
            refine ⟨2735672649501747398787251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1823781766334498265858167 2735672649501747398787251)
            ·
              refine ⟨4103508974252621098180877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2735672649501747398787251 4103508974252621098180877)
              ·
                refine ⟨1538815865344732911817829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4103508974252621098180877 1538815865344732911817829)
                ·
                  refine ⟨288527974752137420965843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1538815865344732911817829 288527974752137420965843)
                  ·
                    rfl

theorem cell21_1264289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 4].length) (baseStart_1264289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264289 prefixEnd_1264289 := by exact prefixLift 1264289
  have htrace : WordTrace (prefixWord ++ tailWord_1264289) baseStart_1264289 baseEnd_1264289 := by
    simpa [prefixWord, tailWord_1264289, baseEnd_1264289] using wordTrace_append hprefix tailTrace_1264289
  have hstable : (prefixWord ++ tailWord_1264289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264289).length < 2 ^ (prefixWord ++ tailWord_1264289).sum := by decide
  have hdescent : baseEnd_1264289 < baseStart_1264289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264376 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 7]
def baseStart_1264376 : Nat := 118140960795 + 1264376 * 2 ^ 59
def prefixEnd_1264376 : Nat := 4983230072969 + 3 ^ 40 * 1264376 * 2
def baseEnd_1264376 : Nat := 288547829337444603015665

theorem tailTrace_1264376 : CollatzResearch.WordTrace tailWord_1264376 prefixEnd_1264376 288547829337444603015665 := by
  unfold tailWord_1264376
  simp only [CollatzResearch.WordTrace]
  refine ⟨23057790633694582537094491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30743720844926110049459321 23057790633694582537094491)
  ·
    refine ⟨34586685950541873805641737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23057790633694582537094491 34586685950541873805641737)
    ·
      refine ⟨25940014462906405354231303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34586685950541873805641737 25940014462906405354231303)
      ·
        refine ⟨38910021694359608031346955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25940014462906405354231303 38910021694359608031346955)
        ·
          refine ⟨58365032541539412047020433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38910021694359608031346955 58365032541539412047020433)
          ·
            refine ⟨43773774406154559035265325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58365032541539412047020433 43773774406154559035265325)
            ·
              refine ⟨16415165402307959638224497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43773774406154559035265325 16415165402307959638224497)
              ·
                refine ⟨12311374051730969728668373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16415165402307959638224497 12311374051730969728668373)
                ·
                  refine ⟨288547829337444603015665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12311374051730969728668373 288547829337444603015665)
                  ·
                    rfl

theorem cell21_1264376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_1264376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264376 prefixEnd_1264376 := by exact prefixLift 1264376
  have htrace : WordTrace (prefixWord ++ tailWord_1264376) baseStart_1264376 baseEnd_1264376 := by
    simpa [prefixWord, tailWord_1264376, baseEnd_1264376] using wordTrace_append hprefix tailTrace_1264376
  have hstable : (prefixWord ++ tailWord_1264376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264376).length < 2 ^ (prefixWord ++ tailWord_1264376).sum := by decide
  have hdescent : baseEnd_1264376 < baseStart_1264376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264382 : List Nat := [4, 2, 2, 1, 2, 3, 1, 2, 4]
def baseStart_1264382 : Nat := 118140960795 + 1264382 * 2 ^ 59
def prefixEnd_1264382 : Nat := 4983230072969 + 3 ^ 40 * 1264382 * 2
def baseEnd_1264382 : Nat := 288549198619189925915653

theorem tailTrace_1264382 : CollatzResearch.WordTrace tailWord_1264382 prefixEnd_1264382 288549198619189925915653 := by
  unfold tailWord_1264382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5764475013170928512363425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30743866736911618732604933 5764475013170928512363425)
  ·
    refine ⟨4323356259878196384272569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5764475013170928512363425 4323356259878196384272569)
    ·
      refine ⟨3242517194908647288204427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4323356259878196384272569 3242517194908647288204427)
      ·
        refine ⟨4863775792362970932306641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3242517194908647288204427 4863775792362970932306641)
        ·
          refine ⟨3647831844272228199229981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4863775792362970932306641 3647831844272228199229981)
          ·
            refine ⟨1367936941602085574711243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3647831844272228199229981 1367936941602085574711243)
            ·
              refine ⟨2051905412403128362066865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1367936941602085574711243 2051905412403128362066865)
              ·
                refine ⟨1538929059302346271550149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2051905412403128362066865 1538929059302346271550149)
                ·
                  refine ⟨288549198619189925915653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1538929059302346271550149 288549198619189925915653)
                  ·
                    rfl

theorem cell21_1264382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_1264382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264382 prefixEnd_1264382 := by exact prefixLift 1264382
  have htrace : WordTrace (prefixWord ++ tailWord_1264382) baseStart_1264382 baseEnd_1264382 := by
    simpa [prefixWord, tailWord_1264382, baseEnd_1264382] using wordTrace_append hprefix tailTrace_1264382
  have hstable : (prefixWord ++ tailWord_1264382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264382).length < 2 ^ (prefixWord ++ tailWord_1264382).sum := by decide
  have hdescent : baseEnd_1264382 < baseStart_1264382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264413 : List Nat := [1, 4, 2, 4, 1, 2, 2, 5]
def baseStart_1264413 : Nat := 118140960795 + 1264413 * 2 ^ 59
def prefixEnd_1264413 : Nat := 4983230072969 + 3 ^ 40 * 1264413 * 2
def baseEnd_1264413 : Nat := 96185424413846920299641

theorem tailTrace_1264413 : CollatzResearch.WordTrace tailWord_1264413 prefixEnd_1264413 96185424413846920299641 := by
  unfold tailWord_1264413
  simp only [CollatzResearch.WordTrace]
  refine ⟨46116930768255120393285893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30744620512170080262190595 46116930768255120393285893)
  ·
    refine ⟨8646924519047835073741105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46116930768255120393285893 8646924519047835073741105)
    ·
      refine ⟨6485193389285876305305829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8646924519047835073741105 6485193389285876305305829)
      ·
        refine ⟨1215973760491101807244843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6485193389285876305305829 1215973760491101807244843)
        ·
          refine ⟨1823960640736652710867265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1215973760491101807244843 1823960640736652710867265)
          ·
            refine ⟨1367970480552489533150449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1823960640736652710867265 1367970480552489533150449)
            ·
              refine ⟨1025977860414367149862837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1367970480552489533150449 1025977860414367149862837)
              ·
                refine ⟨96185424413846920299641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1025977860414367149862837 96185424413846920299641)
                ·
                  rfl

theorem cell21_1264413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 5].length) (baseStart_1264413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264413 prefixEnd_1264413 := by exact prefixLift 1264413
  have htrace : WordTrace (prefixWord ++ tailWord_1264413) baseStart_1264413 baseEnd_1264413 := by
    simpa [prefixWord, tailWord_1264413, baseEnd_1264413] using wordTrace_append hprefix tailTrace_1264413
  have hstable : (prefixWord ++ tailWord_1264413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264413).length < 2 ^ (prefixWord ++ tailWord_1264413).sum := by decide
  have hdescent : baseEnd_1264413 < baseStart_1264413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264497 : List Nat := [1, 2, 2, 2, 1, 13]
def baseStart_1264497 : Nat := 118140960795 + 1264497 * 2 ^ 59
def prefixEnd_1264497 : Nat := 4983230072969 + 3 ^ 40 * 1264497 * 2
def baseEnd_1264497 : Nat := 10687979377258343759213

theorem tailTrace_1264497 : CollatzResearch.WordTrace tailWord_1264497 prefixEnd_1264497 10687979377258343759213 := by
  unfold tailWord_1264497
  simp only [CollatzResearch.WordTrace]
  refine ⟨46119994499950802739343745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30746662999967201826229163 46119994499950802739343745)
  ·
    refine ⟨34589995874963102054507809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46119994499950802739343745 34589995874963102054507809)
    ·
      refine ⟨25942496906222326540880857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34589995874963102054507809 25942496906222326540880857)
      ·
        refine ⟨19456872679666744905660643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25942496906222326540880857 19456872679666744905660643)
        ·
          refine ⟨29185309019500117358490965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19456872679666744905660643 29185309019500117358490965)
          ·
            refine ⟨10687979377258343759213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 29185309019500117358490965 10687979377258343759213)
            ·
              rfl

theorem cell21_1264497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 13].length) (baseStart_1264497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264497 prefixEnd_1264497 := by exact prefixLift 1264497
  have htrace : WordTrace (prefixWord ++ tailWord_1264497) baseStart_1264497 baseEnd_1264497 := by
    simpa [prefixWord, tailWord_1264497, baseEnd_1264497] using wordTrace_append hprefix tailTrace_1264497
  have hstable : (prefixWord ++ tailWord_1264497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264497).length < 2 ^ (prefixWord ++ tailWord_1264497).sum := by decide
  have hdescent : baseEnd_1264497 < baseStart_1264497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264559 : List Nat := [1, 1, 2, 1, 2, 2, 2, 6, 4]
def baseStart_1264559 : Nat := 118140960795 + 1264559 * 2 ^ 59
def prefixEnd_1264559 : Nat := 4983230072969 + 3 ^ 40 * 1264559 * 2
def baseEnd_1264559 : Nat := 288589592430676951465291

theorem tailTrace_1264559 : CollatzResearch.WordTrace tailWord_1264559 prefixEnd_1264559 288589592430676951465291 := by
  unfold tailWord_1264559
  simp only [CollatzResearch.WordTrace]
  refine ⟨46122255825726187328100731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30748170550484124885400487 46122255825726187328100731)
  ·
    refine ⟨69183383738589280992151097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46122255825726187328100731 69183383738589280992151097)
    ·
      refine ⟨51887537803941960744113323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69183383738589280992151097 51887537803941960744113323)
      ·
        refine ⟨77831306705912941116169985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51887537803941960744113323 77831306705912941116169985)
        ·
          refine ⟨58373480029434705837127489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77831306705912941116169985 58373480029434705837127489)
          ·
            refine ⟨43780110022076029377845617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58373480029434705837127489 43780110022076029377845617)
            ·
              refine ⟨32835082516557022033384213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43780110022076029377845617 32835082516557022033384213)
              ·
                refine ⟨1539144492963610407814885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32835082516557022033384213 1539144492963610407814885)
                ·
                  refine ⟨288589592430676951465291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1539144492963610407814885 288589592430676951465291)
                  ·
                    rfl

theorem cell21_1264559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 4].length) (baseStart_1264559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264559 prefixEnd_1264559 := by exact prefixLift 1264559
  have htrace : WordTrace (prefixWord ++ tailWord_1264559) baseStart_1264559 baseEnd_1264559 := by
    simpa [prefixWord, tailWord_1264559, baseEnd_1264559] using wordTrace_append hprefix tailTrace_1264559
  have hstable : (prefixWord ++ tailWord_1264559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264559).length < 2 ^ (prefixWord ++ tailWord_1264559).sum := by decide
  have hdescent : baseEnd_1264559 < baseStart_1264559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264582 : List Nat := [6, 1, 3, 1, 1, 1, 1, 7]
def baseStart_1264582 : Nat := 118140960795 + 1264582 * 2 ^ 59
def prefixEnd_1264582 : Nat := 4983230072969 + 3 ^ 40 * 1264582 * 2
def baseEnd_1264582 : Nat := 96198280448011340860637

theorem tailTrace_1264582 : CollatzResearch.WordTrace tailWord_1264582 prefixEnd_1264582 96198280448011340860637 := by
  unfold tailWord_1264582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1441346709520089445505875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30748729803095241504125333 1441346709520089445505875)
  ·
    refine ⟨2162020064280134168258813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1441346709520089445505875 2162020064280134168258813)
    ·
      refine ⟨810757524105050313097055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2162020064280134168258813 810757524105050313097055)
      ·
        refine ⟨1216136286157575469645583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 810757524105050313097055 1216136286157575469645583)
        ·
          refine ⟨1824204429236363204468375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1216136286157575469645583 1824204429236363204468375)
          ·
            refine ⟨2736306643854544806702563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1824204429236363204468375 2736306643854544806702563)
            ·
              refine ⟨4104459965781817210053845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2736306643854544806702563 4104459965781817210053845)
              ·
                refine ⟨96198280448011340860637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4104459965781817210053845 96198280448011340860637)
                ·
                  rfl

theorem cell21_1264582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_1264582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264582 prefixEnd_1264582 := by exact prefixLift 1264582
  have htrace : WordTrace (prefixWord ++ tailWord_1264582) baseStart_1264582 baseEnd_1264582 := by
    simpa [prefixWord, tailWord_1264582, baseEnd_1264582] using wordTrace_append hprefix tailTrace_1264582
  have hstable : (prefixWord ++ tailWord_1264582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264582).length < 2 ^ (prefixWord ++ tailWord_1264582).sum := by decide
  have hdescent : baseEnd_1264582 < baseStart_1264582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264590 : List Nat := [4, 1, 1, 1, 2, 4, 1, 7]
def baseStart_1264590 : Nat := 118140960795 + 1264590 * 2 ^ 59
def prefixEnd_1264590 : Nat := 4983230072969 + 3 ^ 40 * 1264590 * 2
def baseEnd_1264590 : Nat := 96198889017675928816187

theorem tailTrace_1264590 : CollatzResearch.WordTrace tailWord_1264590 prefixEnd_1264590 96198889017675928816187 := by
  unfold tailWord_1264590
  simp only [CollatzResearch.WordTrace]
  refine ⟨5765423311076734952809903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30748924325742586414986149 5765423311076734952809903)
  ·
    refine ⟨8648134966615102429214855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5765423311076734952809903 8648134966615102429214855)
    ·
      refine ⟨12972202449922653643822283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8648134966615102429214855 12972202449922653643822283)
      ·
        refine ⟨19458303674883980465733425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12972202449922653643822283 19458303674883980465733425)
        ·
          refine ⟨14593727756162985349300069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19458303674883980465733425 14593727756162985349300069)
          ·
            refine ⟨2736323954280559752993763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14593727756162985349300069 2736323954280559752993763)
            ·
              refine ⟨4104485931420839629490645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2736323954280559752993763 4104485931420839629490645)
              ·
                refine ⟨96198889017675928816187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4104485931420839629490645 96198889017675928816187)
                ·
                  rfl

theorem cell21_1264590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_1264590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264590 prefixEnd_1264590 := by exact prefixLift 1264590
  have htrace : WordTrace (prefixWord ++ tailWord_1264590) baseStart_1264590 baseEnd_1264590 := by
    simpa [prefixWord, tailWord_1264590, baseEnd_1264590] using wordTrace_append hprefix tailTrace_1264590
  have hstable : (prefixWord ++ tailWord_1264590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264590).length < 2 ^ (prefixWord ++ tailWord_1264590).sum := by decide
  have hdescent : baseEnd_1264590 < baseStart_1264590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264607 : List Nat := [1, 1, 2, 3, 6, 1, 7]
def baseStart_1264607 : Nat := 118140960795 + 1264607 * 2 ^ 59
def prefixEnd_1264607 : Nat := 4983230072969 + 3 ^ 40 * 1264607 * 2
def baseEnd_1264607 : Nat := 32066727409404392740577

theorem tailTrace_1264607 : CollatzResearch.WordTrace tailWord_1264607 prefixEnd_1264607 32066727409404392740577 := by
  unfold tailWord_1264607
  simp only [CollatzResearch.WordTrace]
  refine ⟨46124006529552291525848075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30749337686368194350565383 46124006529552291525848075)
  ·
    refine ⟨69186009794328437288772113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46124006529552291525848075 69186009794328437288772113)
    ·
      refine ⟨51889507345746327966579085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69186009794328437288772113 51889507345746327966579085)
      ·
        refine ⟨19458565254654872987467157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51889507345746327966579085 19458565254654872987467157)
        ·
          refine ⟨912120246311947171287523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19458565254654872987467157 912120246311947171287523)
          ·
            refine ⟨1368180369467920756931285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912120246311947171287523 1368180369467920756931285)
            ·
              refine ⟨32066727409404392740577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1368180369467920756931285 32066727409404392740577)
              ·
                rfl

theorem cell21_1264607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 7].length) (baseStart_1264607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264607 prefixEnd_1264607 := by exact prefixLift 1264607
  have htrace : WordTrace (prefixWord ++ tailWord_1264607) baseStart_1264607 baseEnd_1264607 := by
    simpa [prefixWord, tailWord_1264607, baseEnd_1264607] using wordTrace_append hprefix tailTrace_1264607
  have hstable : (prefixWord ++ tailWord_1264607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264607).length < 2 ^ (prefixWord ++ tailWord_1264607).sum := by decide
  have hdescent : baseEnd_1264607 < baseStart_1264607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264669 : List Nat := [1, 4, 2, 2, 3, 1, 2, 2, 4]
def baseStart_1264669 : Nat := 118140960795 + 1264669 * 2 ^ 59
def prefixEnd_1264669 : Nat := 4983230072969 + 3 ^ 40 * 1264669 * 2
def baseEnd_1264669 : Nat := 288614695929341204631733

theorem tailTrace_1264669 : CollatzResearch.WordTrace tailWord_1264669 prefixEnd_1264669 288614695929341204631733 := by
  unfold tailWord_1264669
  simp only [CollatzResearch.WordTrace]
  refine ⟨46126267855327676114605061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30750845236885117409736707 46126267855327676114605061)
  ·
    refine ⟨8648675222873939271488449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46126267855327676114605061 8648675222873939271488449)
    ·
      refine ⟨6486506417155454453616337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8648675222873939271488449 6486506417155454453616337)
      ·
        refine ⟨4864879812866590840212253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6486506417155454453616337 4864879812866590840212253)
        ·
          refine ⟨1824329929824971565079595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4864879812866590840212253 1824329929824971565079595)
          ·
            refine ⟨2736494894737457347619393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1824329929824971565079595 2736494894737457347619393)
            ·
              refine ⟨2052371171053093010714545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2736494894737457347619393 2052371171053093010714545)
              ·
                refine ⟨1539278378289819758035909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2052371171053093010714545 1539278378289819758035909)
                ·
                  refine ⟨288614695929341204631733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1539278378289819758035909 288614695929341204631733)
                  ·
                    rfl

theorem cell21_1264669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_1264669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264669 prefixEnd_1264669 := by exact prefixLift 1264669
  have htrace : WordTrace (prefixWord ++ tailWord_1264669) baseStart_1264669 baseEnd_1264669 := by
    simpa [prefixWord, tailWord_1264669, baseEnd_1264669] using wordTrace_append hprefix tailTrace_1264669
  have hstable : (prefixWord ++ tailWord_1264669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264669).length < 2 ^ (prefixWord ++ tailWord_1264669).sum := by decide
  have hdescent : baseEnd_1264669 < baseStart_1264669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264697 : List Nat := [1, 2, 1, 5, 2, 2, 1, 2, 5]
def baseStart_1264697 : Nat := 118140960795 + 1264697 * 2 ^ 59
def prefixEnd_1264697 : Nat := 4983230072969 + 3 ^ 40 * 1264697 * 2
def baseEnd_1264697 : Nat := 288621085910819378165009

theorem tailTrace_1264697 : CollatzResearch.WordTrace tailWord_1264697 prefixEnd_1264697 288621085910819378165009 := by
  unfold tailWord_1264697
  simp only [CollatzResearch.WordTrace]
  refine ⟨46127289099226236896624345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30751526066150824597749563 46127289099226236896624345)
  ·
    refine ⟨34595466824419677672468259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46127289099226236896624345 34595466824419677672468259)
    ·
      refine ⟨51893200236629516508702389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34595466824419677672468259 51893200236629516508702389)
      ·
        refine ⟨4864987522184017172690849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51893200236629516508702389 4864987522184017172690849)
        ·
          refine ⟨3648740641638012879518137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4864987522184017172690849 3648740641638012879518137)
          ·
            refine ⟨2736555481228509659638603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3648740641638012879518137 2736555481228509659638603)
            ·
              refine ⟨4104833221842764489457905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2736555481228509659638603 4104833221842764489457905)
              ·
                refine ⟨3078624916382073367093429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4104833221842764489457905 3078624916382073367093429)
                ·
                  refine ⟨288621085910819378165009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3078624916382073367093429 288621085910819378165009)
                  ·
                    rfl

theorem cell21_1264697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 5].length) (baseStart_1264697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264697 prefixEnd_1264697 := by exact prefixLift 1264697
  have htrace : WordTrace (prefixWord ++ tailWord_1264697) baseStart_1264697 baseEnd_1264697 := by
    simpa [prefixWord, tailWord_1264697, baseEnd_1264697] using wordTrace_append hprefix tailTrace_1264697
  have hstable : (prefixWord ++ tailWord_1264697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264697).length < 2 ^ (prefixWord ++ tailWord_1264697).sum := by decide
  have hdescent : baseEnd_1264697 < baseStart_1264697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264725 : List Nat := [1, 3, 2, 2, 1, 2, 10]
def baseStart_1264725 : Nat := 118140960795 + 1264725 * 2 ^ 59
def prefixEnd_1264725 : Nat := 4983230072969 + 3 ^ 40 * 1264725 * 2
def baseEnd_1264725 : Nat := 32069719543588616855365

theorem tailTrace_1264725 : CollatzResearch.WordTrace tailWord_1264725 prefixEnd_1264725 32069719543588616855365 := by
  unfold tailWord_1264725
  simp only [CollatzResearch.WordTrace]
  refine ⟨46128310343124797678643629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30752206895416531785762419 46128310343124797678643629)
  ·
    refine ⟨17298116378671799129491361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46128310343124797678643629 17298116378671799129491361)
    ·
      refine ⟨12973587284003849347118521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17298116378671799129491361 12973587284003849347118521)
      ·
        refine ⟨9730190463002887010338891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12973587284003849347118521 9730190463002887010338891)
        ·
          refine ⟨14595285694504330515508337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9730190463002887010338891 14595285694504330515508337)
          ·
            refine ⟨10946464270878247886631253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14595285694504330515508337 10946464270878247886631253)
            ·
              refine ⟨32069719543588616855365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10946464270878247886631253 32069719543588616855365)
              ·
                rfl

theorem cell21_1264725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 10].length) (baseStart_1264725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264725 prefixEnd_1264725 := by exact prefixLift 1264725
  have htrace : WordTrace (prefixWord ++ tailWord_1264725) baseStart_1264725 baseEnd_1264725 := by
    simpa [prefixWord, tailWord_1264725, baseEnd_1264725] using wordTrace_append hprefix tailTrace_1264725
  have hstable : (prefixWord ++ tailWord_1264725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264725).length < 2 ^ (prefixWord ++ tailWord_1264725).sum := by decide
  have hdescent : baseEnd_1264725 < baseStart_1264725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264804 : List Nat := [2, 3, 1, 2, 3, 2, 1, 3, 4]
def baseStart_1264804 : Nat := 118140960795 + 1264804 * 2 ^ 59
def prefixEnd_1264804 : Nat := 4983230072969 + 3 ^ 40 * 1264804 * 2
def baseEnd_1264804 : Nat := 288645504768610969881457

theorem tailTrace_1264804 : CollatzResearch.WordTrace tailWord_1264804 prefixEnd_1264804 288645504768610969881457 := by
  unfold tailWord_1264804
  simp only [CollatzResearch.WordTrace]
  refine ⟨23065595854919297085384733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30754127806559062780512977 23065595854919297085384733)
  ·
    refine ⟨8649598445594736407019275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23065595854919297085384733 8649598445594736407019275)
    ·
      refine ⟨12974397668392104610528913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8649598445594736407019275 12974397668392104610528913)
      ·
        refine ⟨9730798251294078457896685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12974397668392104610528913 9730798251294078457896685)
        ·
          refine ⟨3649049344235279421711257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9730798251294078457896685 3649049344235279421711257)
          ·
            refine ⟨2736787008176459566283443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3649049344235279421711257 2736787008176459566283443)
            ·
              refine ⟨4105180512264689349425165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2736787008176459566283443 4105180512264689349425165)
              ·
                refine ⟨1539442692099258506034437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4105180512264689349425165 1539442692099258506034437)
                ·
                  refine ⟨288645504768610969881457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1539442692099258506034437 288645504768610969881457)
                  ·
                    rfl

theorem cell21_1264804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_1264804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264804 prefixEnd_1264804 := by exact prefixLift 1264804
  have htrace : WordTrace (prefixWord ++ tailWord_1264804) baseStart_1264804 baseEnd_1264804 := by
    simpa [prefixWord, tailWord_1264804, baseEnd_1264804] using wordTrace_append hprefix tailTrace_1264804
  have hstable : (prefixWord ++ tailWord_1264804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264804).length < 2 ^ (prefixWord ++ tailWord_1264804).sum := by decide
  have hdescent : baseEnd_1264804 < baseStart_1264804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264852 : List Nat := [2, 4, 1, 4, 1, 2, 1, 6]
def baseStart_1264852 : Nat := 118140960795 + 1264852 * 2 ^ 59
def prefixEnd_1264852 : Nat := 4983230072969 + 3 ^ 40 * 1264852 * 2
def baseEnd_1264852 : Nat := 96218819674191184360453

theorem tailTrace_1264852 : CollatzResearch.WordTrace tailWord_1264852 prefixEnd_1264852 96218819674191184360453 := by
  unfold tailWord_1264852
  simp only [CollatzResearch.WordTrace]
  refine ⟨23066471206832349184258405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30755294942443132245677873 23066471206832349184258405)
  ·
    refine ⟨4324963351281065472048451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23066471206832349184258405 4324963351281065472048451)
    ·
      refine ⟨6487445026921598208072677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4324963351281065472048451 6487445026921598208072677)
      ·
        refine ⟨1216395942547799664013627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6487445026921598208072677 1216395942547799664013627)
        ·
          refine ⟨1824593913821699496020441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1216395942547799664013627 1824593913821699496020441)
          ·
            refine ⟨1368445435366274622015331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1824593913821699496020441 1368445435366274622015331)
            ·
              refine ⟨2052668153049411933022997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1368445435366274622015331 2052668153049411933022997)
              ·
                refine ⟨96218819674191184360453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2052668153049411933022997 96218819674191184360453)
                ·
                  rfl

theorem cell21_1264852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 6].length) (baseStart_1264852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264852 prefixEnd_1264852 := by exact prefixLift 1264852
  have htrace : WordTrace (prefixWord ++ tailWord_1264852) baseStart_1264852 baseEnd_1264852 := by
    simpa [prefixWord, tailWord_1264852, baseEnd_1264852] using wordTrace_append hprefix tailTrace_1264852
  have hstable : (prefixWord ++ tailWord_1264852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264852).length < 2 ^ (prefixWord ++ tailWord_1264852).sum := by decide
  have hdescent : baseEnd_1264852 < baseStart_1264852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264863 : List Nat := [1, 1, 2, 3, 2, 1, 4, 3, 4]
def baseStart_1264863 : Nat := 118140960795 + 1264863 * 2 ^ 59
def prefixEnd_1264863 : Nat := 4983230072969 + 3 ^ 40 * 1264863 * 2
def baseEnd_1264863 : Nat := 288658969372439978398003

theorem tailTrace_1264863 : CollatzResearch.WordTrace tailWord_1264863 prefixEnd_1264863 288658969372439978398003 := by
  unfold tailWord_1264863
  simp only [CollatzResearch.WordTrace]
  refine ⟨46133343616624847247167243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30755562411083231498111495 46133343616624847247167243)
  ·
    refine ⟨69200015424937270870750865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46133343616624847247167243 69200015424937270870750865)
    ·
      refine ⟨51900011568702953153063149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69200015424937270870750865 51900011568702953153063149)
      ·
        refine ⟨19462504338263607432398681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51900011568702953153063149 19462504338263607432398681)
        ·
          refine ⟨14596878253697705574299011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19462504338263607432398681 14596878253697705574299011)
          ·
            refine ⟨21895317380546558361448517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14596878253697705574299011 21895317380546558361448517)
            ·
              refine ⟨4105372008852479692771597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21895317380546558361448517 4105372008852479692771597)
              ·
                refine ⟨1539514503319679884789349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4105372008852479692771597 1539514503319679884789349)
                ·
                  refine ⟨288658969372439978398003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1539514503319679884789349 288658969372439978398003)
                  ·
                    rfl

theorem cell21_1264863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 4].length) (baseStart_1264863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264863 prefixEnd_1264863 := by exact prefixLift 1264863
  have htrace : WordTrace (prefixWord ++ tailWord_1264863) baseStart_1264863 baseEnd_1264863 := by
    simpa [prefixWord, tailWord_1264863, baseEnd_1264863] using wordTrace_append hprefix tailTrace_1264863
  have hstable : (prefixWord ++ tailWord_1264863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264863).length < 2 ^ (prefixWord ++ tailWord_1264863).sum := by decide
  have hdescent : baseEnd_1264863 < baseStart_1264863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264894 : List Nat := [4, 2, 2, 1, 1, 3, 8]
def baseStart_1264894 : Nat := 118140960795 + 1264894 * 2 ^ 59
def prefixEnd_1264894 : Nat := 4983230072969 + 3 ^ 40 * 1264894 * 2
def baseEnd_1264894 : Nat := 32074004888310090375697

theorem tailTrace_1264894 : CollatzResearch.WordTrace tailWord_1264894 prefixEnd_1264894 32074004888310090375697 := by
  unfold tailWord_1264894
  simp only [CollatzResearch.WordTrace]
  refine ⟨5766809284939067442693217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30756316186341693027697157 5766809284939067442693217)
  ·
    refine ⟨4325106963704300582019913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5766809284939067442693217 4325106963704300582019913)
    ·
      refine ⟨3243830222778225436514935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4325106963704300582019913 3243830222778225436514935)
      ·
        refine ⟨4865745334167338154772403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3243830222778225436514935 4865745334167338154772403)
        ·
          refine ⟨7298618001251007232158605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4865745334167338154772403 7298618001251007232158605)
          ·
            refine ⟨2736981750469127712059477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7298618001251007232158605 2736981750469127712059477)
            ·
              refine ⟨32074004888310090375697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2736981750469127712059477 32074004888310090375697)
              ·
                rfl

theorem cell21_1264894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 8].length) (baseStart_1264894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264894 prefixEnd_1264894 := by exact prefixLift 1264894
  have htrace : WordTrace (prefixWord ++ tailWord_1264894) baseStart_1264894 baseEnd_1264894 := by
    simpa [prefixWord, tailWord_1264894, baseEnd_1264894] using wordTrace_append hprefix tailTrace_1264894
  have hstable : (prefixWord ++ tailWord_1264894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264894).length < 2 ^ (prefixWord ++ tailWord_1264894).sum := by decide
  have hdescent : baseEnd_1264894 < baseStart_1264894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264908 : List Nat := [2, 2, 1, 2, 2, 3, 1, 3, 5]
def baseStart_1264908 : Nat := 118140960795 + 1264908 * 2 ^ 59
def prefixEnd_1264908 : Nat := 4983230072969 + 3 ^ 40 * 1264908 * 2
def baseEnd_1264908 : Nat := 288669238985529900147911

theorem tailTrace_1264908 : CollatzResearch.WordTrace tailWord_1264908 prefixEnd_1264908 288669238985529900147911 := by
  unfold tailWord_1264908
  simp only [CollatzResearch.WordTrace]
  refine ⟨23067492450730909966277689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30756656600974546621703585 23067492450730909966277689)
  ·
    refine ⟨17300619338048182474708267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23067492450730909966277689 17300619338048182474708267)
    ·
      refine ⟨25950929007072273712062401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17300619338048182474708267 25950929007072273712062401)
      ·
        refine ⟨19463196755304205284046801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25950929007072273712062401 19463196755304205284046801)
        ·
          refine ⟨14597397566478153963035101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19463196755304205284046801 14597397566478153963035101)
          ·
            refine ⟨5474024087429307736138163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14597397566478153963035101 5474024087429307736138163)
            ·
              refine ⟨8211036131143961604207245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5474024087429307736138163 8211036131143961604207245)
              ·
                refine ⟨3079138549178985601577717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8211036131143961604207245 3079138549178985601577717)
                ·
                  refine ⟨288669238985529900147911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3079138549178985601577717 288669238985529900147911)
                  ·
                    rfl

theorem cell21_1264908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_1264908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264908 prefixEnd_1264908 := by exact prefixLift 1264908
  have htrace : WordTrace (prefixWord ++ tailWord_1264908) baseStart_1264908 baseEnd_1264908 := by
    simpa [prefixWord, tailWord_1264908, baseEnd_1264908] using wordTrace_append hprefix tailTrace_1264908
  have hstable : (prefixWord ++ tailWord_1264908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264908).length < 2 ^ (prefixWord ++ tailWord_1264908).sum := by decide
  have hdescent : baseEnd_1264908 < baseStart_1264908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264925 : List Nat := [1, 4, 2, 3, 1, 1, 2, 2, 5]
def baseStart_1264925 : Nat := 118140960795 + 1264925 * 2 ^ 59
def prefixEnd_1264925 : Nat := 4983230072969 + 3 ^ 40 * 1264925 * 2
def baseEnd_1264925 : Nat := 288673118617141648364543

theorem tailTrace_1264925 : CollatzResearch.WordTrace tailWord_1264925 prefixEnd_1264925 288673118617141648364543 := by
  unfold tailWord_1264925
  simp only [CollatzResearch.WordTrace]
  refine ⟨46135604942400231835924229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30757069961600154557282819 46135604942400231835924229)
  ·
    refine ⟨8650425926700043469235793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46135604942400231835924229 8650425926700043469235793)
    ·
      refine ⟨6487819445025032601926845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8650425926700043469235793 6487819445025032601926845)
      ·
        refine ⟨2432932291884387225722567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6487819445025032601926845 2432932291884387225722567)
        ·
          refine ⟨3649398437826580838583851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2432932291884387225722567 3649398437826580838583851)
          ·
            refine ⟨5474097656739871257875777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3649398437826580838583851 5474097656739871257875777)
            ·
              refine ⟨4105573242554903443406833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5474097656739871257875777 4105573242554903443406833)
              ·
                refine ⟨3079179931916177582555125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4105573242554903443406833 3079179931916177582555125)
                ·
                  refine ⟨288673118617141648364543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3079179931916177582555125 288673118617141648364543)
                  ·
                    rfl

theorem cell21_1264925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_1264925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264925 prefixEnd_1264925 := by exact prefixLift 1264925
  have htrace : WordTrace (prefixWord ++ tailWord_1264925) baseStart_1264925 baseEnd_1264925 := by
    simpa [prefixWord, tailWord_1264925, baseEnd_1264925] using wordTrace_append hprefix tailTrace_1264925
  have hstable : (prefixWord ++ tailWord_1264925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264925).length < 2 ^ (prefixWord ++ tailWord_1264925).sum := by decide
  have hdescent : baseEnd_1264925 < baseStart_1264925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264928 : List Nat := [2, 1, 1, 5, 4, 1, 2, 5]
def baseStart_1264928 : Nat := 118140960795 + 1264928 * 2 ^ 59
def prefixEnd_1264928 : Nat := 4983230072969 + 3 ^ 40 * 1264928 * 2
def baseEnd_1264928 : Nat := 96224601086004769938179

theorem tailTrace_1264928 : CollatzResearch.WordTrace tailWord_1264928 prefixEnd_1264928 96224601086004769938179 := by
  unfold tailWord_1264928
  simp only [CollatzResearch.WordTrace]
  refine ⟨23067857180694681674141719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30757142907592908898855625 23067857180694681674141719)
  ·
    refine ⟨34601785771042022511212579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23067857180694681674141719 34601785771042022511212579)
    ·
      refine ⟨51902678656563033766818869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34601785771042022511212579 51902678656563033766818869)
      ·
        refine ⟨4865876124052784415639269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51902678656563033766818869 4865876124052784415639269)
        ·
          refine ⟨912351773259897077932363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4865876124052784415639269 912351773259897077932363)
          ·
            refine ⟨1368527659889845616898545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912351773259897077932363 1368527659889845616898545)
            ·
              refine ⟨1026395744917384212673909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1368527659889845616898545 1026395744917384212673909)
              ·
                refine ⟨96224601086004769938179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1026395744917384212673909 96224601086004769938179)
                ·
                  rfl

theorem cell21_1264928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 5].length) (baseStart_1264928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1264928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1264928 prefixEnd_1264928 := by exact prefixLift 1264928
  have htrace : WordTrace (prefixWord ++ tailWord_1264928) baseStart_1264928 baseEnd_1264928 := by
    simpa [prefixWord, tailWord_1264928, baseEnd_1264928] using wordTrace_append hprefix tailTrace_1264928
  have hstable : (prefixWord ++ tailWord_1264928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264928).length < 2 ^ (prefixWord ++ tailWord_1264928).sum := by decide
  have hdescent : baseEnd_1264928 < baseStart_1264928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265015 : List Nat := [1, 1, 3, 1, 1, 2, 6, 2, 4]
def baseStart_1265015 : Nat := 118140960795 + 1265015 * 2 ^ 59
def prefixEnd_1265015 : Nat := 4983230072969 + 3 ^ 40 * 1265015 * 2
def baseEnd_1265015 : Nat := 288693657843321491864359

theorem tailTrace_1265015 : CollatzResearch.WordTrace tailWord_1265015 prefixEnd_1265015 288693657843321491864359 := by
  unfold tailWord_1265015
  simp only [CollatzResearch.WordTrace]
  refine ⟨46138887512074177206700499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30759258341382784804466999 46138887512074177206700499)
  ·
    refine ⟨69208331268111265810050749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46138887512074177206700499 69208331268111265810050749)
    ·
      refine ⟨25953124225541724678769031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69208331268111265810050749 25953124225541724678769031)
      ·
        refine ⟨38929686338312587018153547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25953124225541724678769031 38929686338312587018153547)
        ·
          refine ⟨58394529507468880527230321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38929686338312587018153547 58394529507468880527230321)
          ·
            refine ⟨43795897130601660395422741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58394529507468880527230321 43795897130601660395422741)
            ·
              refine ⟨2052932677996952831035441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43795897130601660395422741 2052932677996952831035441)
              ·
                refine ⟨1539699508497714623276581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2052932677996952831035441 1539699508497714623276581)
                ·
                  refine ⟨288693657843321491864359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1539699508497714623276581 288693657843321491864359)
                  ·
                    rfl

theorem cell21_1265015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 4].length) (baseStart_1265015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1265015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1265015 prefixEnd_1265015 := by exact prefixLift 1265015
  have htrace : WordTrace (prefixWord ++ tailWord_1265015) baseStart_1265015 baseEnd_1265015 := by
    simpa [prefixWord, tailWord_1265015, baseEnd_1265015] using wordTrace_append hprefix tailTrace_1265015
  have hstable : (prefixWord ++ tailWord_1265015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265015).length < 2 ^ (prefixWord ++ tailWord_1265015).sum := by decide
  have hdescent : baseEnd_1265015 < baseStart_1265015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265029 : List Nat := [1, 3, 1, 1, 3, 1, 5, 6]
def baseStart_1265029 : Nat := 118140960795 + 1265029 * 2 ^ 59
def prefixEnd_1265029 : Nat := 4983230072969 + 3 ^ 40 * 1265029 * 2
def baseEnd_1265029 : Nat := 96232284278020192876999

theorem tailTrace_1265029 : CollatzResearch.WordTrace tailWord_1265029 prefixEnd_1265029 96232284278020192876999 := by
  unfold tailWord_1265029
  simp only [CollatzResearch.WordTrace]
  refine ⟨46139398134023457597710141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30759598756015638398473427 46139398134023457597710141)
  ·
    refine ⟨17302274300258796599141303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46139398134023457597710141 17302274300258796599141303)
    ·
      refine ⟨25953411450388194898711955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17302274300258796599141303 25953411450388194898711955)
      ·
        refine ⟨38930117175582292348067933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25953411450388194898711955 38930117175582292348067933)
        ·
          refine ⟨14598793940843359630525475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38930117175582292348067933 14598793940843359630525475)
          ·
            refine ⟨21898190911265039445788213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14598793940843359630525475 21898190911265039445788213)
            ·
              refine ⟨2052955397931097448042645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21898190911265039445788213 2052955397931097448042645)
              ·
                refine ⟨96232284278020192876999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2052955397931097448042645 96232284278020192876999)
                ·
                  rfl

theorem cell21_1265029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 6].length) (baseStart_1265029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1265029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1265029 prefixEnd_1265029 := by exact prefixLift 1265029
  have htrace : WordTrace (prefixWord ++ tailWord_1265029) baseStart_1265029 baseEnd_1265029 := by
    simpa [prefixWord, tailWord_1265029, baseEnd_1265029] using wordTrace_append hprefix tailTrace_1265029
  have hstable : (prefixWord ++ tailWord_1265029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265029).length < 2 ^ (prefixWord ++ tailWord_1265029).sum := by decide
  have hdescent : baseEnd_1265029 < baseStart_1265029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265077 : List Nat := [1, 3, 3, 2, 2, 2, 2, 1, 5]
def baseStart_1265077 : Nat := 118140960795 + 1265077 * 2 ^ 59
def prefixEnd_1265077 : Nat := 4983230072969 + 3 ^ 40 * 1265077 * 2
def baseEnd_1265077 : Nat := 288707807088023161830899

theorem tailTrace_1265077 : CollatzResearch.WordTrace tailWord_1265077 prefixEnd_1265077 288707807088023161830899 := by
  unfold tailWord_1265077
  simp only [CollatzResearch.WordTrace]
  refine ⟨46141148837849561795457485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30760765891899707863638323 46141148837849561795457485)
  ·
    refine ⟨17302930814193585673296557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46141148837849561795457485 17302930814193585673296557)
    ·
      refine ⟨6488599055322594627486209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17302930814193585673296557 6488599055322594627486209)
      ·
        refine ⟨4866449291491945970614657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6488599055322594627486209 4866449291491945970614657)
        ·
          refine ⟨3649836968618959477960993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4866449291491945970614657 3649836968618959477960993)
          ·
            refine ⟨2737377726464219608470745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3649836968618959477960993 2737377726464219608470745)
            ·
              refine ⟨2053033294848164706353059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2737377726464219608470745 2053033294848164706353059)
              ·
                refine ⟨3079549942272247059529589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2053033294848164706353059 3079549942272247059529589)
                ·
                  refine ⟨288707807088023161830899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3079549942272247059529589 288707807088023161830899)
                  ·
                    rfl

theorem cell21_1265077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_1265077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1265077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1265077 prefixEnd_1265077 := by exact prefixLift 1265077
  have htrace : WordTrace (prefixWord ++ tailWord_1265077) baseStart_1265077 baseEnd_1265077 := by
    simpa [prefixWord, tailWord_1265077, baseEnd_1265077] using wordTrace_append hprefix tailTrace_1265077
  have hstable : (prefixWord ++ tailWord_1265077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265077).length < 2 ^ (prefixWord ++ tailWord_1265077).sum := by decide
  have hdescent : baseEnd_1265077 < baseStart_1265077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265136 : List Nat := [2, 1, 1, 1, 3, 4, 3, 1, 5]
def baseStart_1265136 : Nat := 118140960795 + 1265136 * 2 ^ 59
def prefixEnd_1265136 : Nat := 4983230072969 + 3 ^ 40 * 1265136 * 2
def baseEnd_1265136 : Nat := 288721271691852170347445

theorem tailTrace_1265136 : CollatzResearch.WordTrace tailWord_1265136 prefixEnd_1265136 288721271691852170347445 := by
  unfold tailWord_1265136
  simp only [CollatzResearch.WordTrace]
  refine ⟨23071650372317907435927631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30762200496423876581236841 23071650372317907435927631)
  ·
    refine ⟨34607475558476861153891447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23071650372317907435927631 34607475558476861153891447)
    ·
      refine ⟨51911213337715291730837171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34607475558476861153891447 51911213337715291730837171)
      ·
        refine ⟨77866820006572937596255757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51911213337715291730837171 77866820006572937596255757)
        ·
          refine ⟨29200057502464851598595909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77866820006572937596255757 29200057502464851598595909)
          ·
            refine ⟨5475010781712159674736733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29200057502464851598595909 5475010781712159674736733)
            ·
              refine ⟨2053129043142059878026275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5475010781712159674736733 2053129043142059878026275)
              ·
                refine ⟨3079693564713089817039413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2053129043142059878026275 3079693564713089817039413)
                ·
                  refine ⟨288721271691852170347445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3079693564713089817039413 288721271691852170347445)
                  ·
                    rfl

theorem cell21_1265136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 5].length) (baseStart_1265136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1265136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1265136 prefixEnd_1265136 := by exact prefixLift 1265136
  have htrace : WordTrace (prefixWord ++ tailWord_1265136) baseStart_1265136 baseEnd_1265136 := by
    simpa [prefixWord, tailWord_1265136, baseEnd_1265136] using wordTrace_append hprefix tailTrace_1265136
  have hstable : (prefixWord ++ tailWord_1265136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265136).length < 2 ^ (prefixWord ++ tailWord_1265136).sum := by decide
  have hdescent : baseEnd_1265136 < baseStart_1265136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265184 : List Nat := [2, 1, 1, 6, 1, 2, 2, 2, 4]
def baseStart_1265184 : Nat := 118140960795 + 1265184 * 2 ^ 59
def prefixEnd_1265184 : Nat := 4983230072969 + 3 ^ 40 * 1265184 * 2
def baseEnd_1265184 : Nat := 288732225945814753547347

theorem tailTrace_1265184 : CollatzResearch.WordTrace tailWord_1265184 prefixEnd_1265184 288732225945814753547347 := by
  unfold tailWord_1265184
  simp only [CollatzResearch.WordTrace]
  refine ⟨23072525724230959534801303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30763367632307946046401737 23072525724230959534801303)
  ·
    refine ⟨34608788586346439302201955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23072525724230959534801303 34608788586346439302201955)
    ·
      refine ⟨51913182879519658953302933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34608788586346439302201955 51913182879519658953302933)
      ·
        refine ⟨2433430447477484013436075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51913182879519658953302933 2433430447477484013436075)
        ·
          refine ⟨3650145671216226020154113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2433430447477484013436075 3650145671216226020154113)
          ·
            refine ⟨2737609253412169515115585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3650145671216226020154113 2737609253412169515115585)
            ·
              refine ⟨2053206940059127136336689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2737609253412169515115585 2053206940059127136336689)
              ·
                refine ⟨1539905205044345352252517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2053206940059127136336689 1539905205044345352252517)
                ·
                  refine ⟨288732225945814753547347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1539905205044345352252517 288732225945814753547347)
                  ·
                    rfl

theorem cell21_1265184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 4].length) (baseStart_1265184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1265184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1265184 prefixEnd_1265184 := by exact prefixLift 1265184
  have htrace : WordTrace (prefixWord ++ tailWord_1265184) baseStart_1265184 baseEnd_1265184 := by
    simpa [prefixWord, tailWord_1265184, baseEnd_1265184] using wordTrace_append hprefix tailTrace_1265184
  have hstable : (prefixWord ++ tailWord_1265184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265184).length < 2 ^ (prefixWord ++ tailWord_1265184).sum := by decide
  have hdescent : baseEnd_1265184 < baseStart_1265184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265187 : List Nat := [1, 1, 1, 4, 5, 2, 2, 2, 3]
def baseStart_1265187 : Nat := 118140960795 + 1265187 * 2 ^ 59
def prefixEnd_1265187 : Nat := 4983230072969 + 3 ^ 40 * 1265187 * 2
def baseEnd_1265187 : Nat := 288732910586687414997341

theorem tailTrace_1265187 : CollatzResearch.WordTrace tailWord_1265187 prefixEnd_1265187 288732910586687414997341 := by
  unfold tailWord_1265187
  simp only [CollatzResearch.WordTrace]
  refine ⟨46145160867451050581961815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30763440578300700387974543 46145160867451050581961815)
  ·
    refine ⟨69217741301176575872942723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46145160867451050581961815 69217741301176575872942723)
    ·
      refine ⟨103826611951764863809414085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69217741301176575872942723 103826611951764863809414085)
      ·
        refine ⟨19467489740955911964265141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103826611951764863809414085 19467489740955911964265141)
        ·
          refine ⟨1825077163214616746649857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19467489740955911964265141 1825077163214616746649857)
          ·
            refine ⟨1368807872410962559987393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1825077163214616746649857 1368807872410962559987393)
            ·
              refine ⟨1026605904308221919990545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1368807872410962559987393 1026605904308221919990545)
              ·
                refine ⟨769954428231166439992909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1026605904308221919990545 769954428231166439992909)
                ·
                  refine ⟨288732910586687414997341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 769954428231166439992909 288732910586687414997341)
                  ·
                    rfl

theorem cell21_1265187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 3].length) (baseStart_1265187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1265187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1265187 prefixEnd_1265187 := by exact prefixLift 1265187
  have htrace : WordTrace (prefixWord ++ tailWord_1265187) baseStart_1265187 baseEnd_1265187 := by
    simpa [prefixWord, tailWord_1265187, baseEnd_1265187] using wordTrace_append hprefix tailTrace_1265187
  have hstable : (prefixWord ++ tailWord_1265187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265187).length < 2 ^ (prefixWord ++ tailWord_1265187).sum := by decide
  have hdescent : baseEnd_1265187 < baseStart_1265187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265198 : List Nat := [4, 1, 3, 1, 2, 1, 3, 6]
def baseStart_1265198 : Nat := 118140960795 + 1265198 * 2 ^ 59
def prefixEnd_1265198 : Nat := 4983230072969 + 3 ^ 40 * 1265198 * 2
def baseEnd_1265198 : Nat := 96245140312184613437995

theorem tailTrace_1265198 : CollatzResearch.WordTrace tailWord_1265198 prefixEnd_1265198 96245140312184613437995 := by
  unfold tailWord_1265198
  simp only [CollatzResearch.WordTrace]
  refine ⟨5768195258801399932576531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30763708046940799640408165 5768195258801399932576531)
  ·
    refine ⟨8652292888202099898864797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5768195258801399932576531 8652292888202099898864797)
    ·
      refine ⟨3244609833075787462074299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8652292888202099898864797 3244609833075787462074299)
      ·
        refine ⟨4866914749613681193111449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3244609833075787462074299 4866914749613681193111449)
        ·
          refine ⟨3650186062210260894833587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4866914749613681193111449 3650186062210260894833587)
          ·
            refine ⟨5475279093315391342250381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3650186062210260894833587 5475279093315391342250381)
            ·
              refine ⟨2053229659993271753343893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5475279093315391342250381 2053229659993271753343893)
              ·
                refine ⟨96245140312184613437995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2053229659993271753343893 96245140312184613437995)
                ·
                  rfl

theorem cell21_1265198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_1265198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1265198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1265198 prefixEnd_1265198 := by exact prefixLift 1265198
  have htrace : WordTrace (prefixWord ++ tailWord_1265198) baseStart_1265198 baseEnd_1265198 := by
    simpa [prefixWord, tailWord_1265198, baseEnd_1265198] using wordTrace_append hprefix tailTrace_1265198
  have hstable : (prefixWord ++ tailWord_1265198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265198).length < 2 ^ (prefixWord ++ tailWord_1265198).sum := by decide
  have hdescent : baseEnd_1265198 < baseStart_1265198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265226 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 6]
def baseStart_1265226 : Nat := 118140960795 + 1265226 * 2 ^ 59
def prefixEnd_1265226 : Nat := 4983230072969 + 3 ^ 40 * 1265226 * 2
def baseEnd_1265226 : Nat := 288741810918032013847261

theorem tailTrace_1265226 : CollatzResearch.WordTrace tailWord_1265226 prefixEnd_1265226 288741810918032013847261 := by
  unfold tailWord_1265226
  simp only [CollatzResearch.WordTrace]
  refine ⟨11536645828577440060657883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30764388876206506828421021 11536645828577440060657883)
  ·
    refine ⟨17304968742866160090986825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11536645828577440060657883 17304968742866160090986825)
    ·
      refine ⟨12978726557149620068240119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17304968742866160090986825 12978726557149620068240119)
      ·
        refine ⟨19468089835724430102360179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12978726557149620068240119 19468089835724430102360179)
        ·
          refine ⟨29202134753586645153540269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19468089835724430102360179 29202134753586645153540269)
          ·
            refine ⟨10950800532594991932577601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29202134753586645153540269 10950800532594991932577601)
            ·
              refine ⟨8213100399446243949433201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10950800532594991932577601 8213100399446243949433201)
              ·
                refine ⟨6159825299584682962074901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8213100399446243949433201 6159825299584682962074901)
                ·
                  refine ⟨288741810918032013847261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6159825299584682962074901 288741810918032013847261)
                  ·
                    rfl

theorem cell21_1265226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_1265226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1265226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1265226 prefixEnd_1265226 := by exact prefixLift 1265226
  have htrace : WordTrace (prefixWord ++ tailWord_1265226) baseStart_1265226 baseEnd_1265226 := by
    simpa [prefixWord, tailWord_1265226, baseEnd_1265226] using wordTrace_append hprefix tailTrace_1265226
  have hstable : (prefixWord ++ tailWord_1265226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265226).length < 2 ^ (prefixWord ++ tailWord_1265226).sum := by decide
  have hdescent : baseEnd_1265226 < baseStart_1265226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265356 : List Nat := [2, 2, 1, 5, 3, 1, 2, 2, 3]
def baseStart_1265356 : Nat := 118140960795 + 1265356 * 2 ^ 59
def prefixEnd_1265356 : Nat := 4983230072969 + 3 ^ 40 * 1265356 * 2
def baseEnd_1265356 : Nat := 288771478689180676680329

theorem tailTrace_1265356 : CollatzResearch.WordTrace tailWord_1265356 prefixEnd_1265356 288771478689180676680329 := by
  unfold tailWord_1265356
  simp only [CollatzResearch.WordTrace]
  refine ⟨23075662401919396222431961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30767549869225861629909281 23075662401919396222431961)
  ·
    refine ⟨17306746801439547166823971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23075662401919396222431961 17306746801439547166823971)
    ·
      refine ⟨25960120202159320750235957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17306746801439547166823971 25960120202159320750235957)
      ·
        refine ⟨2433761268952436320334621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25960120202159320750235957 2433761268952436320334621)
        ·
          refine ⟨912660475857163620125483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2433761268952436320334621 912660475857163620125483)
          ·
            refine ⟨1368990713785745430188225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912660475857163620125483 1368990713785745430188225)
            ·
              refine ⟨1026743035339309072641169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1368990713785745430188225 1026743035339309072641169)
              ·
                refine ⟨770057276504481804480877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1026743035339309072641169 770057276504481804480877)
                ·
                  refine ⟨288771478689180676680329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 770057276504481804480877 288771478689180676680329)
                  ·
                    rfl

theorem cell21_1265356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 3].length) (baseStart_1265356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1265356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1265356 prefixEnd_1265356 := by exact prefixLift 1265356
  have htrace : WordTrace (prefixWord ++ tailWord_1265356) baseStart_1265356 baseEnd_1265356 := by
    simpa [prefixWord, tailWord_1265356, baseEnd_1265356] using wordTrace_append hprefix tailTrace_1265356
  have hstable : (prefixWord ++ tailWord_1265356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265356).length < 2 ^ (prefixWord ++ tailWord_1265356).sum := by decide
  have hdescent : baseEnd_1265356 < baseStart_1265356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265398 : List Nat := [5, 1, 1, 1, 1, 4, 2, 3, 3]
def baseStart_1265398 : Nat := 118140960795 + 1265398 * 2 ^ 59
def prefixEnd_1265398 : Nat := 4983230072969 + 3 ^ 40 * 1265398 * 2
def baseEnd_1265398 : Nat := 288781063661397936980243

theorem tailTrace_1265398 : CollatzResearch.WordTrace tailWord_1265398 prefixEnd_1265398 288781063661397936980243 := by
  unfold tailWord_1265398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2884553541855414601118303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30768571113124422411928565 2884553541855414601118303)
  ·
    refine ⟨4326830312783121901677455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2884553541855414601118303 4326830312783121901677455)
    ·
      refine ⟨6490245469174682852516183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4326830312783121901677455 6490245469174682852516183)
      ·
        refine ⟨9735368203762024278774275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6490245469174682852516183 9735368203762024278774275)
        ·
          refine ⟨14603052305643036418161413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9735368203762024278774275 14603052305643036418161413)
          ·
            refine ⟨2738072307308069328405265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14603052305643036418161413 2738072307308069328405265)
            ·
              refine ⟨2053554230481051996303949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2738072307308069328405265 2053554230481051996303949)
              ·
                refine ⟨770082836430394498613981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2053554230481051996303949 770082836430394498613981)
                ·
                  refine ⟨288781063661397936980243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 770082836430394498613981 288781063661397936980243)
                  ·
                    rfl

theorem cell21_1265398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_1265398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1265398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1265398 prefixEnd_1265398 := by exact prefixLift 1265398
  have htrace : WordTrace (prefixWord ++ tailWord_1265398) baseStart_1265398 baseEnd_1265398 := by
    simpa [prefixWord, tailWord_1265398, baseEnd_1265398] using wordTrace_append hprefix tailTrace_1265398
  have hstable : (prefixWord ++ tailWord_1265398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265398).length < 2 ^ (prefixWord ++ tailWord_1265398).sum := by decide
  have hdescent : baseEnd_1265398 < baseStart_1265398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265412 : List Nat := [2, 3, 2, 2, 1, 4, 1, 2, 4]
def baseStart_1265412 : Nat := 118140960795 + 1265412 * 2 ^ 59
def prefixEnd_1265412 : Nat := 4983230072969 + 3 ^ 40 * 1265412 * 2
def baseEnd_1265412 : Nat := 288784258652137023746881

theorem tailTrace_1265412 : CollatzResearch.WordTrace tailWord_1265412 prefixEnd_1265412 288784258652137023746881 := by
  unfold tailWord_1265412
  simp only [CollatzResearch.WordTrace]
  refine ⟨23076683645817957004451245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30768911527757276005934993 23076683645817957004451245)
  ·
    refine ⟨8653756367181733876669217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23076683645817957004451245 8653756367181733876669217)
    ·
      refine ⟨6490317275386300407501913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8653756367181733876669217 6490317275386300407501913)
      ·
        refine ⟨4867737956539725305626435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6490317275386300407501913 4867737956539725305626435)
        ·
          refine ⟨7301606934809587958439653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4867737956539725305626435 7301606934809587958439653)
          ·
            refine ⟨1369051300276797742207435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7301606934809587958439653 1369051300276797742207435)
            ·
              refine ⟨2053576950415196613311153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369051300276797742207435 2053576950415196613311153)
              ·
                refine ⟨1540182712811397459983365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2053576950415196613311153 1540182712811397459983365)
                ·
                  refine ⟨288784258652137023746881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1540182712811397459983365 288784258652137023746881)
                  ·
                    rfl

theorem cell21_1265412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_1265412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1265412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1265412 prefixEnd_1265412 := by exact prefixLift 1265412
  have htrace : WordTrace (prefixWord ++ tailWord_1265412) baseStart_1265412 baseEnd_1265412 := by
    simpa [prefixWord, tailWord_1265412, baseEnd_1265412] using wordTrace_append hprefix tailTrace_1265412
  have hstable : (prefixWord ++ tailWord_1265412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265412).length < 2 ^ (prefixWord ++ tailWord_1265412).sum := by decide
  have hdescent : baseEnd_1265412 < baseStart_1265412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265457 : List Nat := [1, 2, 2, 3, 2, 2, 3, 3, 3]
def baseStart_1265457 : Nat := 118140960795 + 1265457 * 2 ^ 59
def prefixEnd_1265457 : Nat := 4983230072969 + 3 ^ 40 * 1265457 * 2
def baseEnd_1265457 : Nat := 288794528265226945496789

theorem tailTrace_1265457 : CollatzResearch.WordTrace tailWord_1265457 prefixEnd_1265457 288794528265226945496789 := by
  unfold tailWord_1265457
  simp only [CollatzResearch.WordTrace]
  refine ⟨46155008576472886694290625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30770005717648591129527083 46155008576472886694290625)
  ·
    refine ⟨34616256432354665020717969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46155008576472886694290625 34616256432354665020717969)
    ·
      refine ⟨25962192324265998765538477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34616256432354665020717969 25962192324265998765538477)
      ·
        refine ⟨9735822121599749537076929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25962192324265998765538477 9735822121599749537076929)
        ·
          refine ⟨7301866591199812152807697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9735822121599749537076929 7301866591199812152807697)
          ·
            refine ⟨5476399943399859114605773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7301866591199812152807697 5476399943399859114605773)
            ·
              refine ⟨2053649978774947167977165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5476399943399859114605773 2053649978774947167977165)
              ·
                refine ⟨770118742040605187991437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2053649978774947167977165 770118742040605187991437)
                ·
                  refine ⟨288794528265226945496789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 770118742040605187991437 288794528265226945496789)
                  ·
                    rfl

theorem cell21_1265457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 3].length) (baseStart_1265457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1265457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1265457 prefixEnd_1265457 := by exact prefixLift 1265457
  have htrace : WordTrace (prefixWord ++ tailWord_1265457) baseStart_1265457 baseEnd_1265457 := by
    simpa [prefixWord, tailWord_1265457, baseEnd_1265457] using wordTrace_append hprefix tailTrace_1265457
  have hstable : (prefixWord ++ tailWord_1265457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265457).length < 2 ^ (prefixWord ++ tailWord_1265457).sum := by decide
  have hdescent : baseEnd_1265457 < baseStart_1265457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265468 : List Nat := [2, 2, 2, 2, 1, 1, 11]
def baseStart_1265468 : Nat := 118140960795 + 1265468 * 2 ^ 59
def prefixEnd_1265468 : Nat := 4983230072969 + 3 ^ 40 * 1265468 * 2
def baseEnd_1265468 : Nat := 32088559846121485645937

theorem tailTrace_1265468 : CollatzResearch.WordTrace tailWord_1265468 prefixEnd_1265468 32088559846121485645937 := by
  unfold tailWord_1265468
  simp only [CollatzResearch.WordTrace]
  refine ⟨23077704889716517786470529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30770273186288690381960705 23077704889716517786470529)
  ·
    refine ⟨17308278667287388339852897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23077704889716517786470529 17308278667287388339852897)
    ·
      refine ⟨12981209000465541254889673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17308278667287388339852897 12981209000465541254889673)
      ·
        refine ⟨9735906750349155941167255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12981209000465541254889673 9735906750349155941167255)
        ·
          refine ⟨14603860125523733911750883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9735906750349155941167255 14603860125523733911750883)
          ·
            refine ⟨21905790188285600867626325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14603860125523733911750883 21905790188285600867626325)
            ·
              refine ⟨32088559846121485645937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 21905790188285600867626325 32088559846121485645937)
              ·
                rfl

theorem cell21_1265468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 11].length) (baseStart_1265468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1265468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1265468 prefixEnd_1265468 := by exact prefixLift 1265468
  have htrace : WordTrace (prefixWord ++ tailWord_1265468) baseStart_1265468 baseEnd_1265468 := by
    simpa [prefixWord, tailWord_1265468, baseEnd_1265468] using wordTrace_append hprefix tailTrace_1265468
  have hstable : (prefixWord ++ tailWord_1265468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265468).length < 2 ^ (prefixWord ++ tailWord_1265468).sum := by decide
  have hdescent : baseEnd_1265468 < baseStart_1265468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265513 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 8]
def baseStart_1265513 : Nat := 118140960795 + 1265513 * 2 ^ 59
def prefixEnd_1265513 : Nat := 4983230072969 + 3 ^ 40 * 1265513 * 2
def baseEnd_1265513 : Nat := 288807308228183292563341

theorem tailTrace_1265513 : CollatzResearch.WordTrace tailWord_1265513 prefixEnd_1265513 288807308228183292563341 := by
  unfold tailWord_1265513
  simp only [CollatzResearch.WordTrace]
  refine ⟨46157051064270008258329193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30771367376180005505552795 46157051064270008258329193)
  ·
    refine ⟨34617788298202506193746895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46157051064270008258329193 34617788298202506193746895)
    ·
      refine ⟨51926682447303759290620343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34617788298202506193746895 51926682447303759290620343)
      ·
        refine ⟨77890023670955638935930515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51926682447303759290620343 77890023670955638935930515)
        ·
          refine ⟨116835035506433458403895773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77890023670955638935930515 116835035506433458403895773)
          ·
            refine ⟨43813138314912546901460915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116835035506433458403895773 43813138314912546901460915)
            ·
              refine ⟨65719707472368820352191373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43813138314912546901460915 65719707472368820352191373)
              ·
                refine ⟨24644890302138307632071765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65719707472368820352191373 24644890302138307632071765)
                ·
                  refine ⟨288807308228183292563341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24644890302138307632071765 288807308228183292563341)
                  ·
                    rfl

theorem cell21_1265513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_1265513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1265513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1265513 prefixEnd_1265513 := by exact prefixLift 1265513
  have htrace : WordTrace (prefixWord ++ tailWord_1265513) baseStart_1265513 baseEnd_1265513 := by
    simpa [prefixWord, tailWord_1265513, baseEnd_1265513] using wordTrace_append hprefix tailTrace_1265513
  have hstable : (prefixWord ++ tailWord_1265513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265513).length < 2 ^ (prefixWord ++ tailWord_1265513).sum := by decide
  have hdescent : baseEnd_1265513 < baseStart_1265513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265530 : List Nat := [3, 1, 1, 1, 1, 1, 5, 4, 4]
def baseStart_1265530 : Nat := 118140960795 + 1265530 * 2 ^ 59
def prefixEnd_1265530 : Nat := 4983230072969 + 3 ^ 40 * 1265530 * 2
def baseEnd_1265530 : Nat := 288811187859795040779973

theorem tailTrace_1265530 : CollatzResearch.WordTrace tailWord_1265530 prefixEnd_1265530 288811187859795040779973 := by
  unfold tailWord_1265530
  simp only [CollatzResearch.WordTrace]
  refine ⟨11539417776302105040424511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30771780736805613441132029 11539417776302105040424511)
  ·
    refine ⟨17309126664453157560636767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11539417776302105040424511 17309126664453157560636767)
    ·
      refine ⟨25963689996679736340955151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17309126664453157560636767 25963689996679736340955151)
      ·
        refine ⟨38945534995019604511432727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25963689996679736340955151 38945534995019604511432727)
        ·
          refine ⟨58418302492529406767149091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38945534995019604511432727 58418302492529406767149091)
          ·
            refine ⟨87627453738794110150723637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58418302492529406767149091 87627453738794110150723637)
            ·
              refine ⟨8215073788011947826630341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87627453738794110150723637 8215073788011947826630341)
              ·
                refine ⟨1540326335252240217493189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8215073788011947826630341 1540326335252240217493189)
                ·
                  refine ⟨288811187859795040779973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1540326335252240217493189 288811187859795040779973)
                  ·
                    rfl

theorem cell21_1265530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_1265530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1265530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1265530 prefixEnd_1265530 := by exact prefixLift 1265530
  have htrace : WordTrace (prefixWord ++ tailWord_1265530) baseStart_1265530 baseEnd_1265530 := by
    simpa [prefixWord, tailWord_1265530, baseEnd_1265530] using wordTrace_append hprefix tailTrace_1265530
  have hstable : (prefixWord ++ tailWord_1265530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265530).length < 2 ^ (prefixWord ++ tailWord_1265530).sum := by decide
  have hdescent : baseEnd_1265530 < baseStart_1265530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265592 : List Nat := [2, 1, 2, 1, 2, 3, 1, 6, 3]
def baseStart_1265592 : Nat := 118140960795 + 1265592 * 2 ^ 59
def prefixEnd_1265592 : Nat := 4983230072969 + 3 ^ 40 * 1265592 * 2
def baseEnd_1265592 : Nat := 288825337104496710746513

theorem tailTrace_1265592 : CollatzResearch.WordTrace tailWord_1265592 prefixEnd_1265592 288825337104496710746513 := by
  unfold tailWord_1265592
  simp only [CollatzResearch.WordTrace]
  refine ⟨23079966215491902375227515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30773288287322536500303353 23079966215491902375227515)
  ·
    refine ⟨34619949323237853562841273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23079966215491902375227515 34619949323237853562841273)
    ·
      refine ⟨25964961992428390172130955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34619949323237853562841273 25964961992428390172130955)
      ·
        refine ⟨38947442988642585258196433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25964961992428390172130955 38947442988642585258196433)
        ·
          refine ⟨29210582241481938943647325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38947442988642585258196433 29210582241481938943647325)
          ·
            refine ⟨10953968340555727103867747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29210582241481938943647325 10953968340555727103867747)
            ·
              refine ⟨16430952510833590655801621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10953968340555727103867747 16430952510833590655801621)
              ·
                refine ⟨770200898945324561990701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16430952510833590655801621 770200898945324561990701)
                ·
                  refine ⟨288825337104496710746513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 770200898945324561990701 288825337104496710746513)
                  ·
                    rfl

theorem cell21_1265592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 3].length) (baseStart_1265592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1265592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1265592 prefixEnd_1265592 := by exact prefixLift 1265592
  have htrace : WordTrace (prefixWord ++ tailWord_1265592) baseStart_1265592 baseEnd_1265592 := by
    simpa [prefixWord, tailWord_1265592, baseEnd_1265592] using wordTrace_append hprefix tailTrace_1265592
  have hstable : (prefixWord ++ tailWord_1265592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265592).length < 2 ^ (prefixWord ++ tailWord_1265592).sum := by decide
  have hdescent : baseEnd_1265592 < baseStart_1265592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265626 : List Nat := [3, 1, 1, 2, 5, 2, 1, 3, 3]
def baseStart_1265626 : Nat := 118140960795 + 1265626 * 2 ^ 59
def prefixEnd_1265626 : Nat := 4983230072969 + 3 ^ 40 * 1265626 * 2
def baseEnd_1265626 : Nat := 288833096367720207179777

theorem tailTrace_1265626 : CollatzResearch.WordTrace tailWord_1265626 prefixEnd_1265626 288833096367720207179777 := by
  unfold tailWord_1265626
  simp only [CollatzResearch.WordTrace]
  refine ⟨11540293128215157139298183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30774115008573752371461821 11540293128215157139298183)
  ·
    refine ⟨17310439692322735708947275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11540293128215157139298183 17310439692322735708947275)
    ·
      refine ⟨25965659538484103563420913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17310439692322735708947275 25965659538484103563420913)
      ·
        refine ⟨19474244653863077672565685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25965659538484103563420913 19474244653863077672565685)
        ·
          refine ⟨1825710436299663531803033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19474244653863077672565685 1825710436299663531803033)
          ·
            refine ⟨1369282827224747648852275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1825710436299663531803033 1369282827224747648852275)
            ·
              refine ⟨2053924240837121473278413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369282827224747648852275 2053924240837121473278413)
              ·
                refine ⟨770221590313920552479405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2053924240837121473278413 770221590313920552479405)
                ·
                  refine ⟨288833096367720207179777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 770221590313920552479405 288833096367720207179777)
                  ·
                    rfl

theorem cell21_1265626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 3].length) (baseStart_1265626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1265626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1265626 prefixEnd_1265626 := by exact prefixLift 1265626
  have htrace : WordTrace (prefixWord ++ tailWord_1265626) baseStart_1265626 baseEnd_1265626 := by
    simpa [prefixWord, tailWord_1265626, baseEnd_1265626] using wordTrace_append hprefix tailTrace_1265626
  have hstable : (prefixWord ++ tailWord_1265626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265626).length < 2 ^ (prefixWord ++ tailWord_1265626).sum := by decide
  have hdescent : baseEnd_1265626 < baseStart_1265626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265654 : List Nat := [5, 1, 1, 1, 4, 1, 2, 6]
def baseStart_1265654 : Nat := 118140960795 + 1265654 * 2 ^ 59
def prefixEnd_1265654 : Nat := 4983230072969 + 3 ^ 40 * 1265654 * 2
def baseEnd_1265654 : Nat := 96279828783066126904351

theorem tailTrace_1265654 : CollatzResearch.WordTrace tailWord_1265654 prefixEnd_1265654 96279828783066126904351 := by
  unfold tailWord_1265654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2885137109797449333700751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30774795837839459559474677 2885137109797449333700751)
  ·
    refine ⟨4327705664696174000551127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2885137109797449333700751 4327705664696174000551127)
    ·
      refine ⟨6491558497044261000826691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4327705664696174000551127 6491558497044261000826691)
      ·
        refine ⟨9737337745566391501240037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6491558497044261000826691 9737337745566391501240037)
        ·
          refine ⟨1825750827293698406482507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9737337745566391501240037 1825750827293698406482507)
          ·
            refine ⟨2738626240940547609723761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1825750827293698406482507 2738626240940547609723761)
            ·
              refine ⟨2053969680705410707292821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2738626240940547609723761 2053969680705410707292821)
              ·
                refine ⟨96279828783066126904351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2053969680705410707292821 96279828783066126904351)
                ·
                  rfl

theorem cell21_1265654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_1265654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1265654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1265654 prefixEnd_1265654 := by exact prefixLift 1265654
  have htrace : WordTrace (prefixWord ++ tailWord_1265654) baseStart_1265654 baseEnd_1265654 := by
    simpa [prefixWord, tailWord_1265654, baseEnd_1265654] using wordTrace_append hprefix tailTrace_1265654
  have hstable : (prefixWord ++ tailWord_1265654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265654).length < 2 ^ (prefixWord ++ tailWord_1265654).sum := by decide
  have hdescent : baseEnd_1265654 < baseStart_1265654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265713 : List Nat := [1, 2, 2, 3, 1, 5, 1, 6]
def baseStart_1265713 : Nat := 118140960795 + 1265713 * 2 ^ 59
def prefixEnd_1265713 : Nat := 4983230072969 + 3 ^ 40 * 1265713 * 2
def baseEnd_1265713 : Nat := 96284316984342463076533

theorem tailTrace_1265713 : CollatzResearch.WordTrace tailWord_1265713 prefixEnd_1265713 96284316984342463076533 := by
  unfold tailWord_1265713
  simp only [CollatzResearch.WordTrace]
  refine ⟨46164345663545442415609793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30776230442363628277073195 46164345663545442415609793)
  ·
    refine ⟨34623259247659081811707345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46164345663545442415609793 34623259247659081811707345)
    ·
      refine ⟨25967444435744311358780509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34623259247659081811707345 25967444435744311358780509)
      ·
        refine ⟨9737791663404116759542691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25967444435744311358780509 9737791663404116759542691)
        ·
          refine ⟨14606687495106175139314037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9737791663404116759542691 14606687495106175139314037)
          ·
            refine ⟨1369376952666203919310691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14606687495106175139314037 1369376952666203919310691)
            ·
              refine ⟨2054065428999305878966037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369376952666203919310691 2054065428999305878966037)
              ·
                refine ⟨96284316984342463076533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2054065428999305878966037 96284316984342463076533)
                ·
                  rfl

theorem cell21_1265713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 6].length) (baseStart_1265713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1265713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1265713 prefixEnd_1265713 := by exact prefixLift 1265713
  have htrace : WordTrace (prefixWord ++ tailWord_1265713) baseStart_1265713 baseEnd_1265713 := by
    simpa [prefixWord, tailWord_1265713, baseEnd_1265713] using wordTrace_append hprefix tailTrace_1265713
  have hstable : (prefixWord ++ tailWord_1265713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265713).length < 2 ^ (prefixWord ++ tailWord_1265713).sum := by decide
  have hdescent : baseEnd_1265713 < baseStart_1265713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265775 : List Nat := [1, 1, 2, 1, 3, 5, 3, 1, 4]
def baseStart_1265775 : Nat := 118140960795 + 1265775 * 2 ^ 59
def prefixEnd_1265775 : Nat := 4983230072969 + 3 ^ 40 * 1265775 * 2
def baseEnd_1265775 : Nat := 288867100197729059196139

theorem tailTrace_1265775 : CollatzResearch.WordTrace tailWord_1265775 prefixEnd_1265775 288867100197729059196139 := by
  unfold tailWord_1265775
  simp only [CollatzResearch.WordTrace]
  refine ⟨46166606989320827004366779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30777737992880551336244519 46166606989320827004366779)
  ·
    refine ⟨69249910483981240506550169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46166606989320827004366779 69249910483981240506550169)
    ·
      refine ⟨51937432862985930379912627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69249910483981240506550169 51937432862985930379912627)
      ·
        refine ⟨77906149294478895569868941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51937432862985930379912627 77906149294478895569868941)
        ·
          refine ⟨29214805985429585838700853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77906149294478895569868941 29214805985429585838700853)
          ·
            refine ⟨2738888061134023672378205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29214805985429585838700853 2738888061134023672378205)
            ·
              refine ⟨1027083022925258877141827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2738888061134023672378205 1027083022925258877141827)
              ·
                refine ⟨1540624534387888315712741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1027083022925258877141827 1540624534387888315712741)
                ·
                  refine ⟨288867100197729059196139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1540624534387888315712741 288867100197729059196139)
                  ·
                    rfl

theorem cell21_1265775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 4].length) (baseStart_1265775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1265775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1265775 prefixEnd_1265775 := by exact prefixLift 1265775
  have htrace : WordTrace (prefixWord ++ tailWord_1265775) baseStart_1265775 baseEnd_1265775 := by
    simpa [prefixWord, tailWord_1265775, baseEnd_1265775] using wordTrace_append hprefix tailTrace_1265775
  have hstable : (prefixWord ++ tailWord_1265775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265775).length < 2 ^ (prefixWord ++ tailWord_1265775).sum := by decide
  have hdescent : baseEnd_1265775 < baseStart_1265775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265789 : List Nat := [1, 4, 1, 1, 3, 2, 4, 5]
def baseStart_1265789 : Nat := 118140960795 + 1265789 * 2 ^ 59
def prefixEnd_1265789 : Nat := 4983230072969 + 3 ^ 40 * 1265789 * 2
def baseEnd_1265789 : Nat := 96290098396156048654259

theorem tailTrace_1265789 : CollatzResearch.WordTrace tailWord_1265789 prefixEnd_1265789 96290098396156048654259 := by
  unfold tailWord_1265789
  simp only [CollatzResearch.WordTrace]
  refine ⟨46167117611270107395376421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30778078407513404930250947 46167117611270107395376421)
  ·
    refine ⟨8656334552113145136633079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46167117611270107395376421 8656334552113145136633079)
    ·
      refine ⟨12984501828169717704949619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8656334552113145136633079 12984501828169717704949619)
      ·
        refine ⟨19476752742254576557424429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12984501828169717704949619 19476752742254576557424429)
        ·
          refine ⟨7303782278345466209034161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19476752742254576557424429 7303782278345466209034161)
          ·
            refine ⟨5477836708759099656775621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7303782278345466209034161 5477836708759099656775621)
            ·
              refine ⟨1027094382892331185645429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5477836708759099656775621 1027094382892331185645429)
              ·
                refine ⟨96290098396156048654259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1027094382892331185645429 96290098396156048654259)
                ·
                  rfl

theorem cell21_1265789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 5].length) (baseStart_1265789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1265789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1265789 prefixEnd_1265789 := by exact prefixLift 1265789
  have htrace : WordTrace (prefixWord ++ tailWord_1265789) baseStart_1265789 baseEnd_1265789 := by
    simpa [prefixWord, tailWord_1265789, baseEnd_1265789] using wordTrace_append hprefix tailTrace_1265789
  have hstable : (prefixWord ++ tailWord_1265789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265789).length < 2 ^ (prefixWord ++ tailWord_1265789).sum := by decide
  have hdescent : baseEnd_1265789 < baseStart_1265789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265806 : List Nat := [4, 1, 1, 3, 4, 1, 7]
def baseStart_1265806 : Nat := 118140960795 + 1265806 * 2 ^ 59
def prefixEnd_1265806 : Nat := 4983230072969 + 3 ^ 40 * 1265806 * 2
def baseEnd_1265806 : Nat := 32097130535564432686601

theorem tailTrace_1265806 : CollatzResearch.WordTrace tailWord_1265806 prefixEnd_1265806 32097130535564432686601 := by
  unfold tailWord_1265806
  simp only [CollatzResearch.WordTrace]
  refine ⟨5770967206526064912343159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30778491768139012865830181 5770967206526064912343159)
  ·
    refine ⟨8656450809789097368514739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5770967206526064912343159 8656450809789097368514739)
    ·
      refine ⟨12984676214683646052772109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8656450809789097368514739 12984676214683646052772109)
      ·
        refine ⟨4869253580506367269789541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12984676214683646052772109 4869253580506367269789541)
        ·
          refine ⟨912985046344943863085539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4869253580506367269789541 912985046344943863085539)
          ·
            refine ⟨1369477569517415794628309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912985046344943863085539 1369477569517415794628309)
            ·
              refine ⟨32097130535564432686601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1369477569517415794628309 32097130535564432686601)
              ·
                rfl

theorem cell21_1265806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 7].length) (baseStart_1265806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1265806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1265806 prefixEnd_1265806 := by exact prefixLift 1265806
  have htrace : WordTrace (prefixWord ++ tailWord_1265806) baseStart_1265806 baseEnd_1265806 := by
    simpa [prefixWord, tailWord_1265806, baseEnd_1265806] using wordTrace_append hprefix tailTrace_1265806
  have hstable : (prefixWord ++ tailWord_1265806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265806).length < 2 ^ (prefixWord ++ tailWord_1265806).sum := by decide
  have hdescent : baseEnd_1265806 < baseStart_1265806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265868 : List Nat := [2, 2, 1, 6, 1, 1, 2, 2, 4]
def baseStart_1265868 : Nat := 118140960795 + 1265868 * 2 ^ 59
def prefixEnd_1265868 : Nat := 4983230072969 + 3 ^ 40 * 1265868 * 2
def baseEnd_1265868 : Nat := 288888324064781564145949

theorem tailTrace_1265868 : CollatzResearch.WordTrace tailWord_1265868 prefixEnd_1265868 288888324064781564145949 := by
  unfold tailWord_1265868
  simp only [CollatzResearch.WordTrace]
  refine ⟨23084999488991951943751129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30779999318655935925001505 23084999488991951943751129)
  ·
    refine ⟨17313749616743963957813347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23084999488991951943751129 17313749616743963957813347)
    ·
      refine ⟨25970624425115945936720021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17313749616743963957813347 25970624425115945936720021)
      ·
        refine ⟨1217373019927309965783751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25970624425115945936720021 1217373019927309965783751)
        ·
          refine ⟨1826059529890964948675627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1217373019927309965783751 1826059529890964948675627)
          ·
            refine ⟨2739089294836447423013441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1826059529890964948675627 2739089294836447423013441)
            ·
              refine ⟨2054316971127335567260081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2739089294836447423013441 2054316971127335567260081)
              ·
                refine ⟨1540737728345501675445061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2054316971127335567260081 1540737728345501675445061)
                ·
                  refine ⟨288888324064781564145949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1540737728345501675445061 288888324064781564145949)
                  ·
                    rfl

theorem cell21_1265868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_1265868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1265868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1265868 prefixEnd_1265868 := by exact prefixLift 1265868
  have htrace : WordTrace (prefixWord ++ tailWord_1265868) baseStart_1265868 baseEnd_1265868 := by
    simpa [prefixWord, tailWord_1265868, baseEnd_1265868] using wordTrace_append hprefix tailTrace_1265868
  have hstable : (prefixWord ++ tailWord_1265868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265868).length < 2 ^ (prefixWord ++ tailWord_1265868).sum := by decide
  have hdescent : baseEnd_1265868 < baseStart_1265868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265927 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 6]
def baseStart_1265927 : Nat := 118140960795 + 1265927 * 2 ^ 59
def prefixEnd_1265927 : Nat := 4983230072969 + 3 ^ 40 * 1265927 * 2
def baseEnd_1265927 : Nat := 288901788668610572662495

theorem tailTrace_1265927 : CollatzResearch.WordTrace tailWord_1265927 prefixEnd_1265927 288901788668610572662495 := by
  unfold tailWord_1265927
  simp only [CollatzResearch.WordTrace]
  refine ⟨46172150884770156963900035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30781433923180104642600023 46172150884770156963900035)
  ·
    refine ⟨69258226327155235445850053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46172150884770156963900035 69258226327155235445850053)
    ·
      refine ⟨12985917436341606646096885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69258226327155235445850053 12985917436341606646096885)
      ·
        refine ⟨1217429759657025623071583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12985917436341606646096885 1217429759657025623071583)
        ·
          refine ⟨1826144639485538434607375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1217429759657025623071583 1826144639485538434607375)
          ·
            refine ⟨2739216959228307651911063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1826144639485538434607375 2739216959228307651911063)
            ·
              refine ⟨4108825438842461477866595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2739216959228307651911063 4108825438842461477866595)
              ·
                refine ⟨6163238158263692216799893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4108825438842461477866595 6163238158263692216799893)
                ·
                  refine ⟨288901788668610572662495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6163238158263692216799893 288901788668610572662495)
                  ·
                    rfl

theorem cell21_1265927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 6].length) (baseStart_1265927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1265927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1265927 prefixEnd_1265927 := by exact prefixLift 1265927
  have htrace : WordTrace (prefixWord ++ tailWord_1265927) baseStart_1265927 baseEnd_1265927 := by
    simpa [prefixWord, tailWord_1265927, baseEnd_1265927] using wordTrace_append hprefix tailTrace_1265927
  have hstable : (prefixWord ++ tailWord_1265927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265927).length < 2 ^ (prefixWord ++ tailWord_1265927).sum := by decide
  have hdescent : baseEnd_1265927 < baseStart_1265927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266000 : List Nat := [2, 1, 1, 1, 1, 7, 2, 6]
def baseStart_1266000 : Nat := 118140960795 + 1266000 * 2 ^ 59
def prefixEnd_1266000 : Nat := 4983230072969 + 3 ^ 40 * 1266000 * 2
def baseEnd_1266000 : Nat := 96306149421059555981893

theorem tailTrace_1266000 : CollatzResearch.WordTrace tailWord_1266000 prefixEnd_1266000 96306149421059555981893 := by
  unfold tailWord_1266000
  simp only [CollatzResearch.WordTrace]
  refine ⟨23087406706752845215653727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30783208942337126954204969 23087406706752845215653727)
  ·
    refine ⟨34631110060129267823480591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23087406706752845215653727 34631110060129267823480591)
    ·
      refine ⟨51946665090193901735220887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34631110060129267823480591 51946665090193901735220887)
      ·
        refine ⟨77919997635290852602831331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51946665090193901735220887 77919997635290852602831331)
        ·
          refine ⟨116879996452936278904246997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77919997635290852602831331 116879996452936278904246997)
          ·
            refine ⟨2739374916865694036818289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 116879996452936278904246997 2739374916865694036818289)
            ·
              refine ⟨2054531187649270527613717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2739374916865694036818289 2054531187649270527613717)
              ·
                refine ⟨96306149421059555981893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2054531187649270527613717 96306149421059555981893)
                ·
                  rfl

theorem cell21_1266000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 6].length) (baseStart_1266000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1266000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1266000 prefixEnd_1266000 := by exact prefixLift 1266000
  have htrace : WordTrace (prefixWord ++ tailWord_1266000) baseStart_1266000 baseEnd_1266000 := by
    simpa [prefixWord, tailWord_1266000, baseEnd_1266000] using wordTrace_append hprefix tailTrace_1266000
  have hstable : (prefixWord ++ tailWord_1266000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266000).length < 2 ^ (prefixWord ++ tailWord_1266000).sum := by decide
  have hdescent : baseEnd_1266000 < baseStart_1266000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266093 : List Nat := [1, 5, 2, 2, 2, 1, 8]
def baseStart_1266093 : Nat := 118140960795 + 1266093 * 2 ^ 59
def prefixEnd_1266093 : Nat := 4983230072969 + 3 ^ 40 * 1266093 * 2
def baseEnd_1266093 : Nat := 32104408014470130321721

theorem tailTrace_1266093 : CollatzResearch.WordTrace tailWord_1266093 prefixEnd_1266093 32104408014470130321721 := by
  unfold tailWord_1266093
  simp only [CollatzResearch.WordTrace]
  refine ⟨46178205402168767314442933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30785470268112511542961955 46178205402168767314442933)
  ·
    refine ⟨4329206756453321935729025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46178205402168767314442933 4329206756453321935729025)
    ·
      refine ⟨3246905067339991451796769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4329206756453321935729025 3246905067339991451796769)
      ·
        refine ⟨2435178800504993588847577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3246905067339991451796769 2435178800504993588847577)
        ·
          refine ⟨1826384100378745191635683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2435178800504993588847577 1826384100378745191635683)
          ·
            refine ⟨2739576150568117787453525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1826384100378745191635683 2739576150568117787453525)
            ·
              refine ⟨32104408014470130321721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2739576150568117787453525 32104408014470130321721)
              ·
                rfl

theorem cell21_1266093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 8].length) (baseStart_1266093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1266093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1266093 prefixEnd_1266093 := by exact prefixLift 1266093
  have htrace : WordTrace (prefixWord ++ tailWord_1266093) baseStart_1266093 baseEnd_1266093 := by
    simpa [prefixWord, tailWord_1266093, baseEnd_1266093] using wordTrace_append hprefix tailTrace_1266093
  have hstable : (prefixWord ++ tailWord_1266093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266093).length < 2 ^ (prefixWord ++ tailWord_1266093).sum := by decide
  have hdescent : baseEnd_1266093 < baseStart_1266093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266121 : List Nat := [1, 2, 1, 1, 2, 1, 4, 5, 4]
def baseStart_1266121 : Nat := 118140960795 + 1266121 * 2 ^ 59
def prefixEnd_1266121 : Nat := 4983230072969 + 3 ^ 40 * 1266121 * 2
def baseEnd_1266121 : Nat := 288946062111709346428765

theorem tailTrace_1266121 : CollatzResearch.WordTrace tailWord_1266121 prefixEnd_1266121 288946062111709346428765 := by
  unfold tailWord_1266121
  simp only [CollatzResearch.WordTrace]
  refine ⟨46179226646067328096462217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30786151097378218730974811 46179226646067328096462217)
  ·
    refine ⟨34634419984550496072346663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46179226646067328096462217 34634419984550496072346663)
    ·
      refine ⟨51951629976825744108519995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34634419984550496072346663 51951629976825744108519995)
      ·
        refine ⟨77927444965238616162779993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51951629976825744108519995 77927444965238616162779993)
        ·
          refine ⟨58445583723928962122084995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77927444965238616162779993 58445583723928962122084995)
          ·
            refine ⟨87668375585893443183127493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58445583723928962122084995 87668375585893443183127493)
            ·
              refine ⟨16437820422355020596836405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87668375585893443183127493 16437820422355020596836405)
              ·
                refine ⟨1541045664595783180953413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16437820422355020596836405 1541045664595783180953413)
                ·
                  refine ⟨288946062111709346428765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1541045664595783180953413 288946062111709346428765)
                  ·
                    rfl

theorem cell21_1266121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 4].length) (baseStart_1266121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1266121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1266121 prefixEnd_1266121 := by exact prefixLift 1266121
  have htrace : WordTrace (prefixWord ++ tailWord_1266121) baseStart_1266121 baseEnd_1266121 := by
    simpa [prefixWord, tailWord_1266121, baseEnd_1266121] using wordTrace_append hprefix tailTrace_1266121
  have hstable : (prefixWord ++ tailWord_1266121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266121).length < 2 ^ (prefixWord ++ tailWord_1266121).sum := by decide
  have hdescent : baseEnd_1266121 < baseStart_1266121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266152 : List Nat := [2, 1, 4, 1, 1, 5, 7]
def baseStart_1266152 : Nat := 118140960795 + 1266152 * 2 ^ 59
def prefixEnd_1266152 : Nat := 4983230072969 + 3 ^ 40 * 1266152 * 2
def baseEnd_1266152 : Nat := 32105904081562242379115

theorem tailTrace_1266152 : CollatzResearch.WordTrace tailWord_1266152 prefixEnd_1266152 32105904081562242379115 := by
  unfold tailWord_1266152
  simp only [CollatzResearch.WordTrace]
  refine ⟨23090178654477510195420355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30786904872636680260560473 23090178654477510195420355)
  ·
    refine ⟨34635267981716265293130533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23090178654477510195420355 34635267981716265293130533)
    ·
      refine ⟨6494112746571799742461975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34635267981716265293130533 6494112746571799742461975)
      ·
        refine ⟨9741169119857699613692963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6494112746571799742461975 9741169119857699613692963)
        ·
          refine ⟨14611753679786549420539445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9741169119857699613692963 14611753679786549420539445)
          ·
            refine ⟨1369851907479989008175573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14611753679786549420539445 1369851907479989008175573)
            ·
              refine ⟨32105904081562242379115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1369851907479989008175573 32105904081562242379115)
              ·
                rfl

theorem cell21_1266152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 7].length) (baseStart_1266152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1266152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1266152 prefixEnd_1266152 := by exact prefixLift 1266152
  have htrace : WordTrace (prefixWord ++ tailWord_1266152) baseStart_1266152 baseEnd_1266152 := by
    simpa [prefixWord, tailWord_1266152, baseEnd_1266152] using wordTrace_append hprefix tailTrace_1266152
  have hstable : (prefixWord ++ tailWord_1266152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266152).length < 2 ^ (prefixWord ++ tailWord_1266152).sum := by decide
  have hdescent : baseEnd_1266152 < baseStart_1266152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266211 : List Nat := [1, 1, 1, 4, 4, 10]
def baseStart_1266211 : Nat := 118140960795 + 1266211 * 2 ^ 59
def prefixEnd_1266211 : Nat := 4983230072969 + 3 ^ 40 * 1266211 * 2
def baseEnd_1266211 : Nat := 10702466716218118145503

theorem tailTrace_1266211 : CollatzResearch.WordTrace tailWord_1266211 prefixEnd_1266211 10702466716218118145503 := by
  unfold tailWord_1266211
  simp only [CollatzResearch.WordTrace]
  refine ⟨46182509215741273467238487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30788339477160848978158991 46182509215741273467238487)
  ·
    refine ⟨69273763823611910200857731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46182509215741273467238487 69273763823611910200857731)
    ·
      refine ⟨103910645735417865301286597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69273763823611910200857731 103910645735417865301286597)
      ·
        refine ⟨19483246075390849743991237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103910645735417865301286597 19483246075390849743991237)
        ·
          refine ⟨3653108639135784326998357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19483246075390849743991237 3653108639135784326998357)
          ·
            refine ⟨10702466716218118145503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3653108639135784326998357 10702466716218118145503)
            ·
              rfl

theorem cell21_1266211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 10].length) (baseStart_1266211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1266211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1266211 prefixEnd_1266211 := by exact prefixLift 1266211
  have htrace : WordTrace (prefixWord ++ tailWord_1266211) baseStart_1266211 baseEnd_1266211 := by
    simpa [prefixWord, tailWord_1266211, baseEnd_1266211] using wordTrace_append hprefix tailTrace_1266211
  have hstable : (prefixWord ++ tailWord_1266211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266211).length < 2 ^ (prefixWord ++ tailWord_1266211).sum := by decide
  have hdescent : baseEnd_1266211 < baseStart_1266211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266273 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 6]
def baseStart_1266273 : Nat := 118140960795 + 1266273 * 2 ^ 59
def prefixEnd_1266273 : Nat := 4983230072969 + 3 ^ 40 * 1266273 * 2
def baseEnd_1266273 : Nat := 288980750582590859895121

theorem tailTrace_1266273 : CollatzResearch.WordTrace tailWord_1266273 prefixEnd_1266273 288980750582590859895121 := by
  unfold tailWord_1266273
  simp only [CollatzResearch.WordTrace]
  refine ⟨46184770541516658055995473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30789847027677772037330315 46184770541516658055995473)
  ·
    refine ⟨34638577906137493541996605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46184770541516658055995473 34638577906137493541996605)
    ·
      refine ⟨12989466714801560078248727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34638577906137493541996605 12989466714801560078248727)
      ·
        refine ⟨19484200072202340117373091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12989466714801560078248727 19484200072202340117373091)
        ·
          refine ⟨29226300108303510176059637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19484200072202340117373091 29226300108303510176059637)
          ·
            refine ⟨2739965635153454079005591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29226300108303510176059637 2739965635153454079005591)
            ·
              refine ⟨4109948452730181118508387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2739965635153454079005591 4109948452730181118508387)
              ·
                refine ⟨6164922679095271677762581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4109948452730181118508387 6164922679095271677762581)
                ·
                  refine ⟨288980750582590859895121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6164922679095271677762581 288980750582590859895121)
                  ·
                    rfl

theorem cell21_1266273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 6].length) (baseStart_1266273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1266273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1266273 prefixEnd_1266273 := by exact prefixLift 1266273
  have htrace : WordTrace (prefixWord ++ tailWord_1266273) baseStart_1266273 baseEnd_1266273 := by
    simpa [prefixWord, tailWord_1266273, baseEnd_1266273] using wordTrace_append hprefix tailTrace_1266273
  have hstable : (prefixWord ++ tailWord_1266273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266273).length < 2 ^ (prefixWord ++ tailWord_1266273).sum := by decide
  have hdescent : baseEnd_1266273 < baseStart_1266273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266304 : List Nat := [2, 1, 1, 2, 1, 5, 4, 5]
def baseStart_1266304 : Nat := 118140960795 + 1266304 * 2 ^ 59
def prefixEnd_1266304 : Nat := 4983230072969 + 3 ^ 40 * 1266304 * 2
def baseEnd_1266304 : Nat := 96329275068313898292797

theorem tailTrace_1266304 : CollatzResearch.WordTrace tailWord_1266304 prefixEnd_1266304 96329275068313898292797 := by
  unfold tailWord_1266304
  simp only [CollatzResearch.WordTrace]
  refine ⟨23092950602202175175186983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30790600802936233566915977 23092950602202175175186983)
  ·
    refine ⟨34639425903303262762780475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23092950602202175175186983 34639425903303262762780475)
    ·
      refine ⟨51959138854954894144170713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34639425903303262762780475 51959138854954894144170713)
      ·
        refine ⟨38969354141216170608128035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51959138854954894144170713 38969354141216170608128035)
        ·
          refine ⟨58454031211824255912192053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38969354141216170608128035 58454031211824255912192053)
          ·
            refine ⟨5480065426108523991768005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58454031211824255912192053 5480065426108523991768005)
            ·
              refine ⟨1027512267395348248456501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5480065426108523991768005 1027512267395348248456501)
              ·
                refine ⟨96329275068313898292797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1027512267395348248456501 96329275068313898292797)
                ·
                  rfl

theorem cell21_1266304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 5].length) (baseStart_1266304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1266304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1266304 prefixEnd_1266304 := by exact prefixLift 1266304
  have htrace : WordTrace (prefixWord ++ tailWord_1266304) baseStart_1266304 baseEnd_1266304 := by
    simpa [prefixWord, tailWord_1266304, baseEnd_1266304] using wordTrace_append hprefix tailTrace_1266304
  have hstable : (prefixWord ++ tailWord_1266304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266304).length < 2 ^ (prefixWord ++ tailWord_1266304).sum := by decide
  have hdescent : baseEnd_1266304 < baseStart_1266304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266386 : List Nat := [3, 2, 2, 2, 3, 2, 2, 2, 3]
def baseStart_1266386 : Nat := 118140960795 + 1266386 * 2 ^ 59
def prefixEnd_1266386 : Nat := 4983230072969 + 3 ^ 40 * 1266386 * 2
def baseEnd_1266386 : Nat := 289006538722127774511557

theorem tailTrace_1266386 : CollatzResearch.WordTrace tailWord_1266386 prefixEnd_1266386 289006538722127774511557 := by
  unfold tailWord_1266386
  simp only [CollatzResearch.WordTrace]
  refine ⟨11547222997526819588714753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30792594660071518903239341 11547222997526819588714753)
  ·
    refine ⟨8660417248145114691536065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11547222997526819588714753 8660417248145114691536065)
    ·
      refine ⟨6495312936108836018652049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8660417248145114691536065 6495312936108836018652049)
      ·
        refine ⟨4871484702081627013989037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6495312936108836018652049 4871484702081627013989037)
        ·
          refine ⟨1826806763280610130245889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4871484702081627013989037 1826806763280610130245889)
          ·
            refine ⟨1370105072460457597684417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1826806763280610130245889 1370105072460457597684417)
            ·
              refine ⟨1027578804345343198263313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1370105072460457597684417 1027578804345343198263313)
              ·
                refine ⟨770684103259007398697485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1027578804345343198263313 770684103259007398697485)
                ·
                  refine ⟨289006538722127774511557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 770684103259007398697485 289006538722127774511557)
                  ·
                    rfl

theorem cell21_1266386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_1266386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1266386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1266386 prefixEnd_1266386 := by exact prefixLift 1266386
  have htrace : WordTrace (prefixWord ++ tailWord_1266386) baseStart_1266386 baseEnd_1266386 := by
    simpa [prefixWord, tailWord_1266386, baseEnd_1266386] using wordTrace_append hprefix tailTrace_1266386
  have hstable : (prefixWord ++ tailWord_1266386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266386).length < 2 ^ (prefixWord ++ tailWord_1266386).sum := by decide
  have hdescent : baseEnd_1266386 < baseStart_1266386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266394 : List Nat := [3, 1, 1, 2, 2, 2, 2, 3, 5]
def baseStart_1266394 : Nat := 118140960795 + 1266394 * 2 ^ 59
def prefixEnd_1266394 : Nat := 4983230072969 + 3 ^ 40 * 1266394 * 2
def baseEnd_1266394 : Nat := 289008364431121538378207

theorem tailTrace_1266394 : CollatzResearch.WordTrace tailWord_1266394 prefixEnd_1266394 289008364431121538378207 := by
  unfold tailWord_1266394
  simp only [CollatzResearch.WordTrace]
  refine ⟨11547295943519573930287559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30792789182718863814100157 11547295943519573930287559)
  ·
    refine ⟨17320943915279360895431339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11547295943519573930287559 17320943915279360895431339)
    ·
      refine ⟨25981415872919041343147009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17320943915279360895431339 25981415872919041343147009)
      ·
        refine ⟨19486061904689281007360257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25981415872919041343147009 19486061904689281007360257)
        ·
          refine ⟨14614546428516960755520193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19486061904689281007360257 14614546428516960755520193)
          ·
            refine ⟨10960909821387720566640145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14614546428516960755520193 10960909821387720566640145)
            ·
              refine ⟨8220682366040790424980109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10960909821387720566640145 8220682366040790424980109)
              ·
                refine ⟨3082755887265296409367541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8220682366040790424980109 3082755887265296409367541)
                ·
                  refine ⟨289008364431121538378207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3082755887265296409367541 289008364431121538378207)
                  ·
                    rfl

theorem cell21_1266394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_1266394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1266394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1266394 prefixEnd_1266394 := by exact prefixLift 1266394
  have htrace : WordTrace (prefixWord ++ tailWord_1266394) baseStart_1266394 baseEnd_1266394 := by
    simpa [prefixWord, tailWord_1266394, baseEnd_1266394] using wordTrace_append hprefix tailTrace_1266394
  have hstable : (prefixWord ++ tailWord_1266394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266394).length < 2 ^ (prefixWord ++ tailWord_1266394).sum := by decide
  have hdescent : baseEnd_1266394 < baseStart_1266394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266428 : List Nat := [2, 2, 2, 1, 3, 3, 2, 3, 3]
def baseStart_1266428 : Nat := 118140960795 + 1266428 * 2 ^ 59
def prefixEnd_1266428 : Nat := 4983230072969 + 3 ^ 40 * 1266428 * 2
def baseEnd_1266428 : Nat := 289016123694345034811471

theorem tailTrace_1266428 : CollatzResearch.WordTrace tailWord_1266428 prefixEnd_1266428 289016123694345034811471 := by
  unfold tailWord_1266428
  simp only [CollatzResearch.WordTrace]
  refine ⟨23095211927977559763943969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30793615903970079685258625 23095211927977559763943969)
  ·
    refine ⟨17321408945983169822957977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23095211927977559763943969 17321408945983169822957977)
    ·
      refine ⟨12991056709487377367218483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17321408945983169822957977 12991056709487377367218483)
      ·
        refine ⟨19486585064231066050827725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12991056709487377367218483 19486585064231066050827725)
        ·
          refine ⟨7307469399086649769060397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19486585064231066050827725 7307469399086649769060397)
          ·
            refine ⟨2740301024657493663397649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7307469399086649769060397 2740301024657493663397649)
            ·
              refine ⟨2055225768493120247548237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2740301024657493663397649 2055225768493120247548237)
              ·
                refine ⟨770709663184920092830589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2055225768493120247548237 770709663184920092830589)
                ·
                  refine ⟨289016123694345034811471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 770709663184920092830589 289016123694345034811471)
                  ·
                    rfl

theorem cell21_1266428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 3].length) (baseStart_1266428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1266428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1266428 prefixEnd_1266428 := by exact prefixLift 1266428
  have htrace : WordTrace (prefixWord ++ tailWord_1266428) baseStart_1266428 baseEnd_1266428 := by
    simpa [prefixWord, tailWord_1266428, baseEnd_1266428] using wordTrace_append hprefix tailTrace_1266428
  have hstable : (prefixWord ++ tailWord_1266428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266428).length < 2 ^ (prefixWord ++ tailWord_1266428).sum := by decide
  have hdescent : baseEnd_1266428 < baseStart_1266428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266504 : List Nat := [2, 1, 3, 1, 1, 3, 5, 2, 3]
def baseStart_1266504 : Nat := 118140960795 + 1266504 * 2 ^ 59
def prefixEnd_1266504 : Nat := 4983230072969 + 3 ^ 40 * 1266504 * 2
def baseEnd_1266504 : Nat := 289033467929785791544649

theorem tailTrace_1266504 : CollatzResearch.WordTrace tailWord_1266504 prefixEnd_1266504 289033467929785791544649 := by
  unfold tailWord_1266504
  simp only [CollatzResearch.WordTrace]
  refine ⟨23096597901839892253827283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30795463869119856338436377 23096597901839892253827283)
  ·
    refine ⟨34644896852759838380740925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23096597901839892253827283 34644896852759838380740925)
    ·
      refine ⟨12991836319784939392777847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34644896852759838380740925 12991836319784939392777847)
      ·
        refine ⟨19487754479677409089166771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12991836319784939392777847 19487754479677409089166771)
        ·
          refine ⟨29231631719516113633750157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19487754479677409089166771 29231631719516113633750157)
          ·
            refine ⟨10961861894818542612656309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29231631719516113633750157 10961861894818542612656309)
            ·
              refine ⟨1027674552639238369936529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10961861894818542612656309 1027674552639238369936529)
              ·
                refine ⟨770755914479428777452397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1027674552639238369936529 770755914479428777452397)
                ·
                  refine ⟨289033467929785791544649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 770755914479428777452397 289033467929785791544649)
                  ·
                    rfl

theorem cell21_1266504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 3].length) (baseStart_1266504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1266504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1266504 prefixEnd_1266504 := by exact prefixLift 1266504
  have htrace : WordTrace (prefixWord ++ tailWord_1266504) baseStart_1266504 baseEnd_1266504 := by
    simpa [prefixWord, tailWord_1266504, baseEnd_1266504] using wordTrace_append hprefix tailTrace_1266504
  have hstable : (prefixWord ++ tailWord_1266504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266504).length < 2 ^ (prefixWord ++ tailWord_1266504).sum := by decide
  have hdescent : baseEnd_1266504 < baseStart_1266504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266563 : List Nat := [1, 1, 1, 3, 4, 1, 3, 4, 3]
def baseStart_1266563 : Nat := 118140960795 + 1266563 * 2 ^ 59
def prefixEnd_1266563 : Nat := 4983230072969 + 3 ^ 40 * 1266563 * 2
def baseEnd_1266563 : Nat := 289046932533614800061195

theorem tailTrace_1266563 : CollatzResearch.WordTrace tailWord_1266563 prefixEnd_1266563 289046932533614800061195 := by
  unfold tailWord_1266563
  simp only [CollatzResearch.WordTrace]
  refine ⟨46195347710466037584052343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30796898473644025056034895 46195347710466037584052343)
  ·
    refine ⟨69293021565699056376078515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46195347710466037584052343 69293021565699056376078515)
    ·
      refine ⟨103939532348548584564117773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69293021565699056376078515 103939532348548584564117773)
      ·
        refine ⟨38977324630705719211544165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103939532348548584564117773 38977324630705719211544165)
        ·
          refine ⟨7308248368257322352164531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38977324630705719211544165 7308248368257322352164531)
          ·
            refine ⟨10962372552385983528246797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7308248368257322352164531 10962372552385983528246797)
            ·
              refine ⟨4110889707144743823092549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10962372552385983528246797 4110889707144743823092549)
              ·
                refine ⟨770791820089639466829853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4110889707144743823092549 770791820089639466829853)
                ·
                  refine ⟨289046932533614800061195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 770791820089639466829853 289046932533614800061195)
                  ·
                    rfl

theorem cell21_1266563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 3].length) (baseStart_1266563 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1266563 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1266563 prefixEnd_1266563 := by exact prefixLift 1266563
  have htrace : WordTrace (prefixWord ++ tailWord_1266563) baseStart_1266563 baseEnd_1266563 := by
    simpa [prefixWord, tailWord_1266563, baseEnd_1266563] using wordTrace_append hprefix tailTrace_1266563
  have hstable : (prefixWord ++ tailWord_1266563).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266563).length < 2 ^ (prefixWord ++ tailWord_1266563).sum := by decide
  have hdescent : baseEnd_1266563 < baseStart_1266563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266614 : List Nat := [5, 1, 4, 1, 1, 1, 2, 1, 5]
def baseStart_1266614 : Nat := 118140960795 + 1266614 * 2 ^ 59
def prefixEnd_1266614 : Nat := 4983230072969 + 3 ^ 40 * 1266614 * 2
def baseEnd_1266614 : Nat := 289058571428450044711091

theorem tailTrace_1266614 : CollatzResearch.WordTrace tailWord_1266614 prefixEnd_1266614 289058571428450044711091 := by
  unfold tailWord_1266614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2887325489580079580884931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30798138555520848862772597 2887325489580079580884931)
  ·
    refine ⟨4330988234370119371327397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2887325489580079580884931 4330988234370119371327397)
    ·
      refine ⟨812060293944397382123887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4330988234370119371327397 812060293944397382123887)
      ·
        refine ⟨1218090440916596073185831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 812060293944397382123887 1218090440916596073185831)
        ·
          refine ⟨1827135661374894109778747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1218090440916596073185831 1827135661374894109778747)
          ·
            refine ⟨2740703492062341164668121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1827135661374894109778747 2740703492062341164668121)
            ·
              refine ⟨2055527619046755873501091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2740703492062341164668121 2055527619046755873501091)
              ·
                refine ⟨3083291428570133810251637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2055527619046755873501091 3083291428570133810251637)
                ·
                  refine ⟨289058571428450044711091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3083291428570133810251637 289058571428450044711091)
                  ·
                    rfl

theorem cell21_1266614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_1266614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1266614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1266614 prefixEnd_1266614 := by exact prefixLift 1266614
  have htrace : WordTrace (prefixWord ++ tailWord_1266614) baseStart_1266614 baseEnd_1266614 := by
    simpa [prefixWord, tailWord_1266614, baseEnd_1266614] using wordTrace_append hprefix tailTrace_1266614
  have hstable : (prefixWord ++ tailWord_1266614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266614).length < 2 ^ (prefixWord ++ tailWord_1266614).sum := by decide
  have hdescent : baseEnd_1266614 < baseStart_1266614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266628 : List Nat := [2, 3, 3, 3, 1, 1, 3, 1, 4]
def baseStart_1266628 : Nat := 118140960795 + 1266628 * 2 ^ 59
def prefixEnd_1266628 : Nat := 4983230072969 + 3 ^ 40 * 1266628 * 2
def baseEnd_1266628 : Nat := 289061766419189131477729

theorem tailTrace_1266628 : CollatzResearch.WordTrace tailWord_1266628 prefixEnd_1266628 289061766419189131477729 := by
  unfold tailWord_1266628
  simp only [CollatzResearch.WordTrace]
  refine ⟨23098859227615276842584269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30798478970153702456779025 23098859227615276842584269)
  ·
    refine ⟨8662072210355728815969101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23098859227615276842584269 8662072210355728815969101)
    ·
      refine ⟨3248277078883398305988413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8662072210355728815969101 3248277078883398305988413)
      ·
        refine ⟨1218103904581274364745655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3248277078883398305988413 1218103904581274364745655)
        ·
          refine ⟨1827155856871911547118483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1218103904581274364745655 1827155856871911547118483)
          ·
            refine ⟨2740733785307867320677725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1827155856871911547118483 2740733785307867320677725)
            ·
              refine ⟨1027775169490450245254147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2740733785307867320677725 1027775169490450245254147)
              ·
                refine ⟨1541662754235675367881221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1027775169490450245254147 1541662754235675367881221)
                ·
                  refine ⟨289061766419189131477729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1541662754235675367881221 289061766419189131477729)
                  ·
                    rfl

theorem cell21_1266628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_1266628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1266628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1266628 prefixEnd_1266628 := by exact prefixLift 1266628
  have htrace : WordTrace (prefixWord ++ tailWord_1266628) baseStart_1266628 baseEnd_1266628 := by
    simpa [prefixWord, tailWord_1266628, baseEnd_1266628] using wordTrace_append hprefix tailTrace_1266628
  have hstable : (prefixWord ++ tailWord_1266628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266628).length < 2 ^ (prefixWord ++ tailWord_1266628).sum := by decide
  have hdescent : baseEnd_1266628 < baseStart_1266628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266653 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 6]
def baseStart_1266653 : Nat := 118140960795 + 1266653 * 2 ^ 59
def prefixEnd_1266653 : Nat := 4983230072969 + 3 ^ 40 * 1266653 * 2
def baseEnd_1266653 : Nat := 289067471759794643561011

theorem tailTrace_1266653 : CollatzResearch.WordTrace tailWord_1266653 prefixEnd_1266653 289067471759794643561011 := by
  unfold tailWord_1266653
  simp only [CollatzResearch.WordTrace]
  refine ⟨46198630280139982954828613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30799086853426655303219075 46198630280139982954828613)
  ·
    refine ⟨8662243177526246804030365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46198630280139982954828613 8662243177526246804030365)
    ·
      refine ⟨3248341191572342551511387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8662243177526246804030365 3248341191572342551511387)
      ·
        refine ⟨4872511787358513827267081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3248341191572342551511387 4872511787358513827267081)
        ·
          refine ⟨3654383840518885370450311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4872511787358513827267081 3654383840518885370450311)
          ·
            refine ⟨5481575760778328055675467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3654383840518885370450311 5481575760778328055675467)
            ·
              refine ⟨8222363641167492083513201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5481575760778328055675467 8222363641167492083513201)
              ·
                refine ⟨6166772730875619062634901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8222363641167492083513201 6166772730875619062634901)
                ·
                  refine ⟨289067471759794643561011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6166772730875619062634901 289067471759794643561011)
                  ·
                    rfl

theorem cell21_1266653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_1266653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1266653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1266653 prefixEnd_1266653 := by exact prefixLift 1266653
  have htrace : WordTrace (prefixWord ++ tailWord_1266653) baseStart_1266653 baseEnd_1266653 := by
    simpa [prefixWord, tailWord_1266653, baseEnd_1266653] using wordTrace_append hprefix tailTrace_1266653
  have hstable : (prefixWord ++ tailWord_1266653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266653).length < 2 ^ (prefixWord ++ tailWord_1266653).sum := by decide
  have hdescent : baseEnd_1266653 < baseStart_1266653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266757 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 7]
def baseStart_1266757 : Nat := 118140960795 + 1266757 * 2 ^ 59
def prefixEnd_1266757 : Nat := 4983230072969 + 3 ^ 40 * 1266757 * 2
def baseEnd_1266757 : Nat := 289091205976713573827465

theorem tailTrace_1266757 : CollatzResearch.WordTrace tailWord_1266757 prefixEnd_1266757 289091205976713573827465 := by
  unfold tailWord_1266757
  simp only [CollatzResearch.WordTrace]
  refine ⟨46202423471763208716614525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30801615647842139144409683 46202423471763208716614525)
  ·
    refine ⟨17325908801911203268730447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46202423471763208716614525 17325908801911203268730447)
    ·
      refine ⟨25988863202866804903095671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17325908801911203268730447 25988863202866804903095671)
      ·
        refine ⟨38983294804300207354643507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25988863202866804903095671 38983294804300207354643507)
        ·
          refine ⟨58474942206450311031965261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38983294804300207354643507 58474942206450311031965261)
          ·
            refine ⟨21928103327418866636986973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58474942206450311031965261 21928103327418866636986973)
            ·
              refine ⟨8223038747782074988870115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21928103327418866636986973 8223038747782074988870115)
              ·
                refine ⟨12334558121673112483305173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8223038747782074988870115 12334558121673112483305173)
                ·
                  refine ⟨289091205976713573827465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12334558121673112483305173 289091205976713573827465)
                  ·
                    rfl

theorem cell21_1266757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_1266757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1266757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1266757 prefixEnd_1266757 := by exact prefixLift 1266757
  have htrace : WordTrace (prefixWord ++ tailWord_1266757) baseStart_1266757 baseEnd_1266757 := by
    simpa [prefixWord, tailWord_1266757, baseEnd_1266757] using wordTrace_append hprefix tailTrace_1266757
  have hstable : (prefixWord ++ tailWord_1266757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266757).length < 2 ^ (prefixWord ++ tailWord_1266757).sum := by decide
  have hdescent : baseEnd_1266757 < baseStart_1266757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266791 : List Nat := [1, 1, 5, 1, 1, 3, 2, 4, 3]
def baseStart_1266791 : Nat := 118140960795 + 1266791 * 2 ^ 59
def prefixEnd_1266791 : Nat := 4983230072969 + 3 ^ 40 * 1266791 * 2
def baseEnd_1266791 : Nat := 289098965239937070260729

theorem tailTrace_1266791 : CollatzResearch.WordTrace tailWord_1266791 prefixEnd_1266791 289098965239937070260729 := by
  unfold tailWord_1266791
  simp only [CollatzResearch.WordTrace]
  refine ⟨46203663553640032523352227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30802442369093355015568151 46203663553640032523352227)
  ·
    refine ⟨69305495330460048785028341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46203663553640032523352227 69305495330460048785028341)
    ·
      refine ⟨6497390187230629573596407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69305495330460048785028341 6497390187230629573596407)
      ·
        refine ⟨9746085280845944360394611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6497390187230629573596407 9746085280845944360394611)
        ·
          refine ⟨14619127921268916540591917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9746085280845944360394611 14619127921268916540591917)
          ·
            refine ⟨5482172970475843702721969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14619127921268916540591917 5482172970475843702721969)
            ·
              refine ⟨4111629727856882777041477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5482172970475843702721969 4111629727856882777041477)
              ·
                refine ⟨770930573973165520695277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4111629727856882777041477 770930573973165520695277)
                ·
                  refine ⟨289098965239937070260729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 770930573973165520695277 289098965239937070260729)
                  ·
                    rfl

theorem cell21_1266791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 3].length) (baseStart_1266791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1266791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1266791 prefixEnd_1266791 := by exact prefixLift 1266791
  have htrace : WordTrace (prefixWord ++ tailWord_1266791) baseStart_1266791 baseEnd_1266791 := by
    simpa [prefixWord, tailWord_1266791, baseEnd_1266791] using wordTrace_append hprefix tailTrace_1266791
  have hstable : (prefixWord ++ tailWord_1266791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266791).length < 2 ^ (prefixWord ++ tailWord_1266791).sum := by decide
  have hdescent : baseEnd_1266791 < baseStart_1266791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266864 : List Nat := [2, 1, 1, 1, 2, 1, 2, 7, 4]
def baseStart_1266864 : Nat := 118140960795 + 1266864 * 2 ^ 59
def prefixEnd_1266864 : Nat := 4983230072969 + 3 ^ 40 * 1266864 * 2
def baseEnd_1266864 : Nat := 289115624834505165543913

theorem tailTrace_1266864 : CollatzResearch.WordTrace tailWord_1266864 prefixEnd_1266864 289115624834505165543913 := by
  unfold tailWord_1266864
  simp only [CollatzResearch.WordTrace]
  refine ⟨23103163041187782995379823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30804217388250377327173097 23103163041187782995379823)
  ·
    refine ⟨34654744561781674493069735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23103163041187782995379823 34654744561781674493069735)
    ·
      refine ⟨51982116842672511739604603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34654744561781674493069735 51982116842672511739604603)
      ·
        refine ⟨77973175264008767609406905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51982116842672511739604603 77973175264008767609406905)
        ·
          refine ⟨58479881448006575707055179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77973175264008767609406905 58479881448006575707055179)
          ·
            refine ⟨87719822172009863560582769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58479881448006575707055179 87719822172009863560582769)
            ·
              refine ⟨65789866629007397670437077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87719822172009863560582769 65789866629007397670437077)
              ·
                refine ⟨1541949999117360882900869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 65789866629007397670437077 1541949999117360882900869)
                ·
                  refine ⟨289115624834505165543913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1541949999117360882900869 289115624834505165543913)
                  ·
                    rfl

theorem cell21_1266864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 4].length) (baseStart_1266864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1266864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1266864 prefixEnd_1266864 := by exact prefixLift 1266864
  have htrace : WordTrace (prefixWord ++ tailWord_1266864) baseStart_1266864 baseEnd_1266864 := by
    simpa [prefixWord, tailWord_1266864, baseEnd_1266864] using wordTrace_append hprefix tailTrace_1266864
  have hstable : (prefixWord ++ tailWord_1266864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266864).length < 2 ^ (prefixWord ++ tailWord_1266864).sum := by decide
  have hdescent : baseEnd_1266864 < baseStart_1266864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266901 : List Nat := [1, 3, 2, 4, 1, 3, 2, 2, 3]
def baseStart_1266901 : Nat := 118140960795 + 1266901 * 2 ^ 59
def prefixEnd_1266901 : Nat := 4983230072969 + 3 ^ 40 * 1266901 * 2
def baseEnd_1266901 : Nat := 289124068738601323427171

theorem tailTrace_1266901 : CollatzResearch.WordTrace tailWord_1266901 prefixEnd_1266901 289124068738601323427171 := by
  unfold tailWord_1266901
  simp only [CollatzResearch.WordTrace]
  refine ⟨46207675583241521309856557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30805117055494347539904371 46207675583241521309856557)
  ·
    refine ⟨17327878343715570491196209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46207675583241521309856557 17327878343715570491196209)
    ·
      refine ⟨12995908757786677868397157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17327878343715570491196209 12995908757786677868397157)
      ·
        refine ⟨2436732892085002100324467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12995908757786677868397157 2436732892085002100324467)
        ·
          refine ⟨3655099338127503150486701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2436732892085002100324467 3655099338127503150486701)
          ·
            refine ⟨1370662251797813681432513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3655099338127503150486701 1370662251797813681432513)
            ·
              refine ⟨1027996688848360261074385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1370662251797813681432513 1027996688848360261074385)
              ·
                refine ⟨770997516636270195805789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1027996688848360261074385 770997516636270195805789)
                ·
                  refine ⟨289124068738601323427171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 770997516636270195805789 289124068738601323427171)
                  ·
                    rfl

theorem cell21_1266901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 3].length) (baseStart_1266901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1266901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1266901 prefixEnd_1266901 := by exact prefixLift 1266901
  have htrace : WordTrace (prefixWord ++ tailWord_1266901) baseStart_1266901 baseEnd_1266901 := by
    simpa [prefixWord, tailWord_1266901, baseEnd_1266901] using wordTrace_append hprefix tailTrace_1266901
  have hstable : (prefixWord ++ tailWord_1266901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266901).length < 2 ^ (prefixWord ++ tailWord_1266901).sum := by decide
  have hdescent : baseEnd_1266901 < baseStart_1266901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266943 : List Nat := [1, 1, 2, 2, 1, 6, 2, 3, 3]
def baseStart_1266943 : Nat := 118140960795 + 1266943 * 2 ^ 59
def prefixEnd_1266943 : Nat := 4983230072969 + 3 ^ 40 * 1266943 * 2
def baseEnd_1266943 : Nat := 289133653710818583727085

theorem tailTrace_1266943 : CollatzResearch.WordTrace tailWord_1266943 prefixEnd_1266943 289133653710818583727085 := by
  unfold tailWord_1266943
  simp only [CollatzResearch.WordTrace]
  refine ⟨46209207449089362482885483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30806138299392908321923655 46209207449089362482885483)
  ·
    refine ⟨69313811173634043724328225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46209207449089362482885483 69313811173634043724328225)
    ·
      refine ⟨51985358380225532793246169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69313811173634043724328225 51985358380225532793246169)
      ·
        refine ⟨38989018785169149594934627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51985358380225532793246169 38989018785169149594934627)
        ·
          refine ⟨58483528177753724392401941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38989018785169149594934627 58483528177753724392401941)
          ·
            refine ⟨2741415383332205830893841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58483528177753724392401941 2741415383332205830893841)
            ·
              refine ⟨2056061537499154373170381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2741415383332205830893841 2056061537499154373170381)
              ·
                refine ⟨771023076562182889938893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2056061537499154373170381 771023076562182889938893)
                ·
                  refine ⟨289133653710818583727085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 771023076562182889938893 289133653710818583727085)
                  ·
                    rfl

theorem cell21_1266943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 3].length) (baseStart_1266943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1266943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1266943 prefixEnd_1266943 := by exact prefixLift 1266943
  have htrace : WordTrace (prefixWord ++ tailWord_1266943) baseStart_1266943 baseEnd_1266943 := by
    simpa [prefixWord, tailWord_1266943, baseEnd_1266943] using wordTrace_append hprefix tailTrace_1266943
  have hstable : (prefixWord ++ tailWord_1266943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266943).length < 2 ^ (prefixWord ++ tailWord_1266943).sum := by decide
  have hdescent : baseEnd_1266943 < baseStart_1266943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267005 : List Nat := [1, 4, 1, 5, 2, 1, 7]
def baseStart_1267005 : Nat := 118140960795 + 1267005 * 2 ^ 59
def prefixEnd_1267005 : Nat := 4983230072969 + 3 ^ 40 * 1267005 * 2
def baseEnd_1267005 : Nat := 32127533661724472632625

theorem tailTrace_1267005 : CollatzResearch.WordTrace tailWord_1267005 prefixEnd_1267005 32127533661724472632625 := by
  unfold tailWord_1267005
  simp only [CollatzResearch.WordTrace]
  refine ⟨46211468774864747071642469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30807645849909831381094979 46211468774864747071642469)
  ·
    refine ⟨8664650395287140075932963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46211468774864747071642469 8664650395287140075932963)
    ·
      refine ⟨12996975592930710113899445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8664650395287140075932963 12996975592930710113899445)
      ·
        refine ⟨1218466461837254073178073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12996975592930710113899445 1218466461837254073178073)
        ·
          refine ⟨913849846377940554883555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1218466461837254073178073 913849846377940554883555)
          ·
            refine ⟨1370774769566910832325333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913849846377940554883555 1370774769566910832325333)
            ·
              refine ⟨32127533661724472632625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1370774769566910832325333 32127533661724472632625)
              ·
                rfl

theorem cell21_1267005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 7].length) (baseStart_1267005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1267005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1267005 prefixEnd_1267005 := by exact prefixLift 1267005
  have htrace : WordTrace (prefixWord ++ tailWord_1267005) baseStart_1267005 baseEnd_1267005 := by
    simpa [prefixWord, tailWord_1267005, baseEnd_1267005] using wordTrace_append hprefix tailTrace_1267005
  have hstable : (prefixWord ++ tailWord_1267005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267005).length < 2 ^ (prefixWord ++ tailWord_1267005).sum := by decide
  have hdescent : baseEnd_1267005 < baseStart_1267005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267016 : List Nat := [2, 1, 3, 1, 1, 2, 1, 6, 4]
def baseStart_1267016 : Nat := 118140960795 + 1267016 * 2 ^ 59
def prefixEnd_1267016 : Nat := 4983230072969 + 3 ^ 40 * 1267016 * 2
def baseEnd_1267016 : Nat := 289150313305386679010269

theorem tailTrace_1267016 : CollatzResearch.WordTrace tailWord_1267016 prefixEnd_1267016 289150313305386679010269 := by
  unfold tailWord_1267016
  simp only [CollatzResearch.WordTrace]
  refine ⟨23105934988912447975146451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30807913318549930633528601 23105934988912447975146451)
  ·
    refine ⟨34658902483368671962719677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23105934988912447975146451 34658902483368671962719677)
    ·
      refine ⟨12997088431263251986019879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34658902483368671962719677 12997088431263251986019879)
      ·
        refine ⟨19495632646894877979029819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12997088431263251986019879 19495632646894877979029819)
        ·
          refine ⟨29243448970342316968544729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19495632646894877979029819 29243448970342316968544729)
          ·
            refine ⟨21932586727756737726408547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29243448970342316968544729 21932586727756737726408547)
            ·
              refine ⟨32898880091635106589612821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21932586727756737726408547 32898880091635106589612821)
              ·
                refine ⟨1542135004295395621388101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32898880091635106589612821 1542135004295395621388101)
                ·
                  refine ⟨289150313305386679010269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1542135004295395621388101 289150313305386679010269)
                  ·
                    rfl

theorem cell21_1267016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 4].length) (baseStart_1267016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1267016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1267016 prefixEnd_1267016 := by exact prefixLift 1267016
  have htrace : WordTrace (prefixWord ++ tailWord_1267016) baseStart_1267016 baseEnd_1267016 := by
    simpa [prefixWord, tailWord_1267016, baseEnd_1267016] using wordTrace_append hprefix tailTrace_1267016
  have hstable : (prefixWord ++ tailWord_1267016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267016).length < 2 ^ (prefixWord ++ tailWord_1267016).sum := by decide
  have hdescent : baseEnd_1267016 < baseStart_1267016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267033 : List Nat := [1, 2, 1, 2, 2, 2, 6, 1, 4]
def baseStart_1267033 : Nat := 118140960795 + 1267033 * 2 ^ 59
def prefixEnd_1267033 : Nat := 4983230072969 + 3 ^ 40 * 1267033 * 2
def baseEnd_1267033 : Nat := 289154192936998427226901

theorem tailTrace_1267033 : CollatzResearch.WordTrace tailWord_1267033 prefixEnd_1267033 289154192936998427226901 := by
  unfold tailWord_1267033
  simp only [CollatzResearch.WordTrace]
  refine ⟨46212490018763307853661753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30808326679175538569107835 46212490018763307853661753)
  ·
    refine ⟨34659367514072480890246315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46212490018763307853661753 34659367514072480890246315)
    ·
      refine ⟨51989051271108721335369473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34659367514072480890246315 51989051271108721335369473)
      ·
        refine ⟨38991788453331541001527105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51989051271108721335369473 38991788453331541001527105)
        ·
          refine ⟨29243841339998655751145329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38991788453331541001527105 29243841339998655751145329)
          ·
            refine ⟨21932881004998991813358997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29243841339998655751145329 21932881004998991813358997)
            ·
              refine ⟨1028103797109327741251203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21932881004998991813358997 1028103797109327741251203)
              ·
                refine ⟨1542155695663991611876805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1028103797109327741251203 1542155695663991611876805)
                ·
                  refine ⟨289154192936998427226901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1542155695663991611876805 289154192936998427226901)
                  ·
                    rfl

theorem cell21_1267033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 4].length) (baseStart_1267033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1267033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1267033 prefixEnd_1267033 := by exact prefixLift 1267033
  have htrace : WordTrace (prefixWord ++ tailWord_1267033) baseStart_1267033 baseEnd_1267033 := by
    simpa [prefixWord, tailWord_1267033, baseEnd_1267033] using wordTrace_append hprefix tailTrace_1267033
  have hstable : (prefixWord ++ tailWord_1267033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267033).length < 2 ^ (prefixWord ++ tailWord_1267033).sum := by decide
  have hdescent : baseEnd_1267033 < baseStart_1267033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267171 : List Nat := [1, 1, 1, 6, 2, 1, 3, 3, 3]
def baseStart_1267171 : Nat := 118140960795 + 1267171 * 2 ^ 59
def prefixEnd_1267171 : Nat := 4983230072969 + 3 ^ 40 * 1267171 * 2
def baseEnd_1267171 : Nat := 289185686417140853926619

theorem tailTrace_1267171 : CollatzResearch.WordTrace tailWord_1267171 prefixEnd_1267171 289185686417140853926619 := by
  unfold tailWord_1267171
  simp only [CollatzResearch.WordTrace]
  refine ⟨46217523292263357422185367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30811682194842238281456911 46217523292263357422185367)
  ·
    refine ⟨69326284938395036133278051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46217523292263357422185367 69326284938395036133278051)
    ·
      refine ⟨103989427407592554199917077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69326284938395036133278051 103989427407592554199917077)
      ·
        refine ⟨4874504409730900978121113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 103989427407592554199917077 4874504409730900978121113)
        ·
          refine ⟨3655878307298175733590835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4874504409730900978121113 3655878307298175733590835)
          ·
            refine ⟨5483817460947263600386253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3655878307298175733590835 5483817460947263600386253)
            ·
              refine ⟨2056431547855223850144845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5483817460947263600386253 2056431547855223850144845)
              ·
                refine ⟨771161830445708943804317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2056431547855223850144845 771161830445708943804317)
                ·
                  refine ⟨289185686417140853926619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 771161830445708943804317 289185686417140853926619)
                  ·
                    rfl

theorem cell21_1267171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 3].length) (baseStart_1267171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1267171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1267171 prefixEnd_1267171 := by exact prefixLift 1267171
  have htrace : WordTrace (prefixWord ++ tailWord_1267171) baseStart_1267171 baseEnd_1267171 := by
    simpa [prefixWord, tailWord_1267171, baseEnd_1267171] using wordTrace_append hprefix tailTrace_1267171
  have hstable : (prefixWord ++ tailWord_1267171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267171).length < 2 ^ (prefixWord ++ tailWord_1267171).sum := by decide
  have hdescent : baseEnd_1267171 < baseStart_1267171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267202 : List Nat := [3, 4, 1, 2, 1, 2, 1, 3, 4]
def baseStart_1267202 : Nat := 118140960795 + 1267202 * 2 ^ 59
def prefixEnd_1267202 : Nat := 4983230072969 + 3 ^ 40 * 1267202 * 2
def baseEnd_1267202 : Nat := 289192761039491688909889

theorem tailTrace_1267202 : CollatzResearch.WordTrace tailWord_1267202 prefixEnd_1267202 289192761039491688909889 := by
  unfold tailWord_1267202
  simp only [CollatzResearch.WordTrace]
  refine ⟨11554663488787762429140965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30812435970100699811042573 11554663488787762429140965)
  ·
    refine ⟨2166499404147705455463931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11554663488787762429140965 2166499404147705455463931)
    ·
      refine ⟨3249749106221558183195897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2166499404147705455463931 3249749106221558183195897)
      ·
        refine ⟨2437311829666168637396923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3249749106221558183195897 2437311829666168637396923)
        ·
          refine ⟨3655967744499252956095385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2437311829666168637396923 3655967744499252956095385)
          ·
            refine ⟨2741975808374439717071539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3655967744499252956095385 2741975808374439717071539)
            ·
              refine ⟨4112963712561659575607309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2741975808374439717071539 4112963712561659575607309)
              ·
                refine ⟨1542361392210622340852741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4112963712561659575607309 1542361392210622340852741)
                ·
                  refine ⟨289192761039491688909889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1542361392210622340852741 289192761039491688909889)
                  ·
                    rfl

theorem cell21_1267202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_1267202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1267202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1267202 prefixEnd_1267202 := by exact prefixLift 1267202
  have htrace : WordTrace (prefixWord ++ tailWord_1267202) baseStart_1267202 baseEnd_1267202 := by
    simpa [prefixWord, tailWord_1267202, baseEnd_1267202] using wordTrace_append hprefix tailTrace_1267202
  have hstable : (prefixWord ++ tailWord_1267202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267202).length < 2 ^ (prefixWord ++ tailWord_1267202).sum := by decide
  have hdescent : baseEnd_1267202 < baseStart_1267202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267306 : List Nat := [3, 1, 3, 2, 1, 3, 2, 1, 5]
def baseStart_1267306 : Nat := 118140960795 + 1267306 * 2 ^ 59
def prefixEnd_1267306 : Nat := 4983230072969 + 3 ^ 40 * 1267306 * 2
def baseEnd_1267306 : Nat := 289216495256410619176343

theorem tailTrace_1267306 : CollatzResearch.WordTrace tailWord_1267306 prefixEnd_1267306 289216495256410619176343 := by
  unfold tailWord_1267306
  simp only [CollatzResearch.WordTrace]
  refine ⟨11555611786693568869587443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30814964764516183652233181 11555611786693568869587443)
  ·
    refine ⟨17333417680040353304381165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11555611786693568869587443 17333417680040353304381165)
    ·
      refine ⟨6500031630015132489142937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17333417680040353304381165 6500031630015132489142937)
      ·
        refine ⟨4875023722511349366857203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6500031630015132489142937 4875023722511349366857203)
        ·
          refine ⟨7312535583767024050285805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4875023722511349366857203 7312535583767024050285805)
          ·
            refine ⟨2742200843912634018857177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7312535583767024050285805 2742200843912634018857177)
            ·
              refine ⟨2056650632934475514142883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2742200843912634018857177 2056650632934475514142883)
              ·
                refine ⟨3084975949401713271214325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2056650632934475514142883 3084975949401713271214325)
                ·
                  refine ⟨289216495256410619176343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3084975949401713271214325 289216495256410619176343)
                  ·
                    rfl

theorem cell21_1267306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_1267306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1267306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1267306 prefixEnd_1267306 := by exact prefixLift 1267306
  have htrace : WordTrace (prefixWord ++ tailWord_1267306) baseStart_1267306 baseEnd_1267306 := by
    simpa [prefixWord, tailWord_1267306, baseEnd_1267306] using wordTrace_append hprefix tailTrace_1267306
  have hstable : (prefixWord ++ tailWord_1267306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267306).length < 2 ^ (prefixWord ++ tailWord_1267306).sum := by decide
  have hdescent : baseEnd_1267306 < baseStart_1267306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267365 : List Nat := [1, 3, 1, 2, 1, 2, 5, 1, 5]
def baseStart_1267365 : Nat := 118140960795 + 1267365 * 2 ^ 59
def prefixEnd_1267365 : Nat := 4983230072969 + 3 ^ 40 * 1267365 * 2
def baseEnd_1267365 : Nat := 289229959860239627692889

theorem tailTrace_1267365 : CollatzResearch.WordTrace tailWord_1267365 prefixEnd_1267365 289229959860239627692889 := by
  unfold tailWord_1267365
  simp only [CollatzResearch.WordTrace]
  refine ⟨46224599053560528554747549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30816399369040352369831699 46224599053560528554747549)
  ·
    refine ⟨17334224645085198208030331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46224599053560528554747549 17334224645085198208030331)
    ·
      refine ⟨26001336967627797312045497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17334224645085198208030331 26001336967627797312045497)
      ·
        refine ⟨19501002725720847984034123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26001336967627797312045497 19501002725720847984034123)
        ·
          refine ⟨29251504088581271976051185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19501002725720847984034123 29251504088581271976051185)
          ·
            refine ⟨21938628066435953982038389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29251504088581271976051185 21938628066435953982038389)
            ·
              refine ⟨2056746381228370685816099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21938628066435953982038389 2056746381228370685816099)
              ·
                refine ⟨3085119571842556028724149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2056746381228370685816099 3085119571842556028724149)
                ·
                  refine ⟨289229959860239627692889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3085119571842556028724149 289229959860239627692889)
                  ·
                    rfl

theorem cell21_1267365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_1267365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1267365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1267365 prefixEnd_1267365 := by exact prefixLift 1267365
  have htrace : WordTrace (prefixWord ++ tailWord_1267365) baseStart_1267365 baseEnd_1267365 := by
    simpa [prefixWord, tailWord_1267365, baseEnd_1267365] using wordTrace_append hprefix tailTrace_1267365
  have hstable : (prefixWord ++ tailWord_1267365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267365).length < 2 ^ (prefixWord ++ tailWord_1267365).sum := by decide
  have hdescent : baseEnd_1267365 < baseStart_1267365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267410 : List Nat := [3, 2, 2, 2, 2, 10]
def baseStart_1267410 : Nat := 118140960795 + 1267410 * 2 ^ 59
def prefixEnd_1267410 : Nat := 4983230072969 + 3 ^ 40 * 1267410 * 2
def baseEnd_1267410 : Nat := 10712601091604798127511

theorem tailTrace_1267410 : CollatzResearch.WordTrace tailWord_1267410 prefixEnd_1267410 10712601091604798127511 := by
  unfold tailWord_1267410
  simp only [CollatzResearch.WordTrace]
  refine ⟨11556560084599375310033921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30817493558931667493423789 11556560084599375310033921)
  ·
    refine ⟨8667420063449531482525441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11556560084599375310033921 8667420063449531482525441)
    ·
      refine ⟨6500565047587148611894081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8667420063449531482525441 6500565047587148611894081)
      ·
        refine ⟨4875423785690361458920561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6500565047587148611894081 4875423785690361458920561)
        ·
          refine ⟨3656567839267771094190421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4875423785690361458920561 3656567839267771094190421)
          ·
            refine ⟨10712601091604798127511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3656567839267771094190421 10712601091604798127511)
            ·
              rfl

theorem cell21_1267410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 10].length) (baseStart_1267410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1267410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1267410 prefixEnd_1267410 := by exact prefixLift 1267410
  have htrace : WordTrace (prefixWord ++ tailWord_1267410) baseStart_1267410 baseEnd_1267410 := by
    simpa [prefixWord, tailWord_1267410, baseEnd_1267410] using wordTrace_append hprefix tailTrace_1267410
  have hstable : (prefixWord ++ tailWord_1267410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267410).length < 2 ^ (prefixWord ++ tailWord_1267410).sum := by decide
  have hdescent : baseEnd_1267410 < baseStart_1267410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267441 : List Nat := [1, 2, 2, 2, 2, 4, 1, 2, 5]
def baseStart_1267441 : Nat := 118140960795 + 1267441 * 2 ^ 59
def prefixEnd_1267441 : Nat := 4983230072969 + 3 ^ 40 * 1267441 * 2
def baseEnd_1267441 : Nat := 289247304095680384426067

theorem tailTrace_1267441 : CollatzResearch.WordTrace tailWord_1267441 prefixEnd_1267441 289247304095680384426067 := by
  unfold tailWord_1267441
  simp only [CollatzResearch.WordTrace]
  refine ⟨46227371001285193534514177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30818247334190129023009451 46227371001285193534514177)
  ·
    refine ⟨34670528250963895150885633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46227371001285193534514177 34670528250963895150885633)
    ·
      refine ⟨26002896188222921363164225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34670528250963895150885633 26002896188222921363164225)
      ·
        refine ⟨19502172141167191022373169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26002896188222921363164225 19502172141167191022373169)
        ·
          refine ⟨14626629105875393266779877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19502172141167191022373169 14626629105875393266779877)
          ·
            refine ⟨2742492957351636237521227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14626629105875393266779877 2742492957351636237521227)
            ·
              refine ⟨4113739436027454356281841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2742492957351636237521227 4113739436027454356281841)
              ·
                refine ⟨3085304577020590767211381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4113739436027454356281841 3085304577020590767211381)
                ·
                  refine ⟨289247304095680384426067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3085304577020590767211381 289247304095680384426067)
                  ·
                    rfl

theorem cell21_1267441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 5].length) (baseStart_1267441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1267441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1267441 prefixEnd_1267441 := by exact prefixLift 1267441
  have htrace : WordTrace (prefixWord ++ tailWord_1267441) baseStart_1267441 baseEnd_1267441 := by
    simpa [prefixWord, tailWord_1267441, baseEnd_1267441] using wordTrace_append hprefix tailTrace_1267441
  have hstable : (prefixWord ++ tailWord_1267441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267441).length < 2 ^ (prefixWord ++ tailWord_1267441).sum := by decide
  have hdescent : baseEnd_1267441 < baseStart_1267441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267489 : List Nat := [1, 2, 3, 2, 1, 4, 3, 1, 4]
def baseStart_1267489 : Nat := 118140960795 + 1267489 * 2 ^ 59
def prefixEnd_1267489 : Nat := 4983230072969 + 3 ^ 40 * 1267489 * 2
def baseEnd_1267489 : Nat := 289258258349642967625969

theorem tailTrace_1267489 : CollatzResearch.WordTrace tailWord_1267489 prefixEnd_1267489 289258258349642967625969 := by
  unfold tailWord_1267489
  simp only [CollatzResearch.WordTrace]
  refine ⟨46229121705111297732261521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30819414470074198488174347 46229121705111297732261521)
  ·
    refine ⟨34671841278833473299196141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46229121705111297732261521 34671841278833473299196141)
    ·
      refine ⟨13001940479562552487198553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34671841278833473299196141 13001940479562552487198553)
      ·
        refine ⟨9751455359671914365398915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13001940479562552487198553 9751455359671914365398915)
        ·
          refine ⟨14627183039507871548098373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9751455359671914365398915 14627183039507871548098373)
          ·
            refine ⟨2742596819907725915268445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14627183039507871548098373 2742596819907725915268445)
            ·
              refine ⟨1028473807465397218225667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2742596819907725915268445 1028473807465397218225667)
              ·
                refine ⟨1542710711198095827338501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1028473807465397218225667 1542710711198095827338501)
                ·
                  refine ⟨289258258349642967625969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1542710711198095827338501 289258258349642967625969)
                  ·
                    rfl

theorem cell21_1267489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 4].length) (baseStart_1267489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1267489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1267489 prefixEnd_1267489 := by exact prefixLift 1267489
  have htrace : WordTrace (prefixWord ++ tailWord_1267489) baseStart_1267489 baseEnd_1267489 := by
    simpa [prefixWord, tailWord_1267489, baseEnd_1267489] using wordTrace_append hprefix tailTrace_1267489
  have hstable : (prefixWord ++ tailWord_1267489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267489).length < 2 ^ (prefixWord ++ tailWord_1267489).sum := by decide
  have hdescent : baseEnd_1267489 < baseStart_1267489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267582 : List Nat := [4, 2, 3, 1, 1, 2, 2, 2, 4]
def baseStart_1267582 : Nat := 118140960795 + 1267582 * 2 ^ 59
def prefixEnd_1267582 : Nat := 4983230072969 + 3 ^ 40 * 1267582 * 2
def baseEnd_1267582 : Nat := 289279482216695472575779

theorem tailTrace_1267582 : CollatzResearch.WordTrace tailWord_1267582 prefixEnd_1267582 289279482216695472575779 := by
  unfold tailWord_1267582
  simp only [CollatzResearch.WordTrace]
  refine ⟨5779064211721796826924625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30821675795849583076931333 5779064211721796826924625)
  ·
    refine ⟨4334298158791347620193469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5779064211721796826924625 4334298158791347620193469)
    ·
      refine ⟨1625361809546755357572551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4334298158791347620193469 1625361809546755357572551)
      ·
        refine ⟨2438042714320133036358827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1625361809546755357572551 2438042714320133036358827)
        ·
          refine ⟨3657064071480199554538241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2438042714320133036358827 3657064071480199554538241)
          ·
            refine ⟨2742798053610149665903681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3657064071480199554538241 2742798053610149665903681)
            ·
              refine ⟨2057098540207612249427761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2742798053610149665903681 2057098540207612249427761)
              ·
                refine ⟨1542823905155709187070821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2057098540207612249427761 1542823905155709187070821)
                ·
                  refine ⟨289279482216695472575779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1542823905155709187070821 289279482216695472575779)
                  ·
                    rfl

theorem cell21_1267582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_1267582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1267582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1267582 prefixEnd_1267582 := by exact prefixLift 1267582
  have htrace : WordTrace (prefixWord ++ tailWord_1267582) baseStart_1267582 baseEnd_1267582 := by
    simpa [prefixWord, tailWord_1267582, baseEnd_1267582] using wordTrace_append hprefix tailTrace_1267582
  have hstable : (prefixWord ++ tailWord_1267582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267582).length < 2 ^ (prefixWord ++ tailWord_1267582).sum := by decide
  have hdescent : baseEnd_1267582 < baseStart_1267582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267585 : List Nat := [1, 2, 4, 4, 1, 2, 2, 2, 3]
def baseStart_1267585 : Nat := 118140960795 + 1267585 * 2 ^ 59
def prefixEnd_1267585 : Nat := 4983230072969 + 3 ^ 40 * 1267585 * 2
def baseEnd_1267585 : Nat := 289280166857568134025773

theorem tailTrace_1267585 : CollatzResearch.WordTrace tailWord_1267585 prefixEnd_1267585 289280166857568134025773 := by
  unfold tailWord_1267585
  simp only [CollatzResearch.WordTrace]
  refine ⟨46232623112763506127756209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30821748741842337418504139 46232623112763506127756209)
  ·
    refine ⟨34674467334572629595817157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46232623112763506127756209 34674467334572629595817157)
    ·
      refine ⟨6501462625232368049215717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34674467334572629595817157 6501462625232368049215717)
      ·
        refine ⟨1219024242231069009227947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6501462625232368049215717 1219024242231069009227947)
        ·
          refine ⟨1828536363346603513841921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1219024242231069009227947 1828536363346603513841921)
          ·
            refine ⟨1371402272509952635381441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1828536363346603513841921 1371402272509952635381441)
            ·
              refine ⟨1028551704382464476536081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1371402272509952635381441 1028551704382464476536081)
              ·
                refine ⟨771413778286848357402061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1028551704382464476536081 771413778286848357402061)
                ·
                  refine ⟨289280166857568134025773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 771413778286848357402061 289280166857568134025773)
                  ·
                    rfl

theorem cell21_1267585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 3].length) (baseStart_1267585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1267585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1267585 prefixEnd_1267585 := by exact prefixLift 1267585
  have htrace : WordTrace (prefixWord ++ tailWord_1267585) baseStart_1267585 baseEnd_1267585 := by
    simpa [prefixWord, tailWord_1267585, baseEnd_1267585] using wordTrace_append hprefix tailTrace_1267585
  have hstable : (prefixWord ++ tailWord_1267585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267585).length < 2 ^ (prefixWord ++ tailWord_1267585).sum := by decide
  have hdescent : baseEnd_1267585 < baseStart_1267585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267621 : List Nat := [1, 3, 1, 2, 1, 1, 1, 11]
def baseStart_1267621 : Nat := 118140960795 + 1267621 * 2 ^ 59
def prefixEnd_1267621 : Nat := 4983230072969 + 3 ^ 40 * 1267621 * 2
def baseEnd_1267621 : Nat := 96429460849346690475233

theorem tailTrace_1267621 : CollatzResearch.WordTrace tailWord_1267621 prefixEnd_1267621 96429460849346690475233 := by
  unfold tailWord_1267621
  simp only [CollatzResearch.WordTrace]
  refine ⟨46233936140633084276066717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30822624093755389517377811 46233936140633084276066717)
  ·
    refine ⟨17337726052737406603525019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46233936140633084276066717 17337726052737406603525019)
    ·
      refine ⟨26006589079106109905287529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17337726052737406603525019 26006589079106109905287529)
      ·
        refine ⟨19504941809329582428965647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26006589079106109905287529 19504941809329582428965647)
        ·
          refine ⟨29257412713994373643448471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19504941809329582428965647 29257412713994373643448471)
          ·
            refine ⟨43886119070991560465172707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29257412713994373643448471 43886119070991560465172707)
            ·
              refine ⟨65829178606487340697759061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43886119070991560465172707 65829178606487340697759061)
              ·
                refine ⟨96429460849346690475233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 65829178606487340697759061 96429460849346690475233)
                ·
                  rfl

theorem cell21_1267621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 11].length) (baseStart_1267621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1267621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1267621 prefixEnd_1267621 := by exact prefixLift 1267621
  have htrace : WordTrace (prefixWord ++ tailWord_1267621) baseStart_1267621 baseEnd_1267621 := by
    simpa [prefixWord, tailWord_1267621, baseEnd_1267621] using wordTrace_append hprefix tailTrace_1267621
  have hstable : (prefixWord ++ tailWord_1267621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267621).length < 2 ^ (prefixWord ++ tailWord_1267621).sum := by decide
  have hdescent : baseEnd_1267621 < baseStart_1267621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267669 : List Nat := [1, 3, 2, 3, 2, 1, 2, 2, 5]
def baseStart_1267669 : Nat := 118140960795 + 1267669 * 2 ^ 59
def prefixEnd_1267669 : Nat := 4983230072969 + 3 ^ 40 * 1267669 * 2
def baseEnd_1267669 : Nat := 289299336802002654625601

theorem tailTrace_1267669 : CollatzResearch.WordTrace tailWord_1267669 prefixEnd_1267669 289299336802002654625601 := by
  unfold tailWord_1267669
  simp only [CollatzResearch.WordTrace]
  refine ⟨46235686844459188473814061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30823791229639458982542707 46235686844459188473814061)
  ·
    refine ⟨17338382566672195677680273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46235686844459188473814061 17338382566672195677680273)
    ·
      refine ⟨13003786925004146758260205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17338382566672195677680273 13003786925004146758260205)
      ·
        refine ⟨4876420096876555034347577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13003786925004146758260205 4876420096876555034347577)
        ·
          refine ⟨3657315072657416275760683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4876420096876555034347577 3657315072657416275760683)
          ·
            refine ⟨5485972608986124413641025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3657315072657416275760683 5485972608986124413641025)
            ·
              refine ⟨4114479456739593310230769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5485972608986124413641025 4114479456739593310230769)
              ·
                refine ⟨3085859592554694982673077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4114479456739593310230769 3085859592554694982673077)
                ·
                  refine ⟨289299336802002654625601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3085859592554694982673077 289299336802002654625601)
                  ·
                    rfl

theorem cell21_1267669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_1267669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1267669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1267669 prefixEnd_1267669 := by exact prefixLift 1267669
  have htrace : WordTrace (prefixWord ++ tailWord_1267669) baseStart_1267669 baseEnd_1267669 := by
    simpa [prefixWord, tailWord_1267669, baseEnd_1267669] using wordTrace_append hprefix tailTrace_1267669
  have hstable : (prefixWord ++ tailWord_1267669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267669).length < 2 ^ (prefixWord ++ tailWord_1267669).sum := by decide
  have hdescent : baseEnd_1267669 < baseStart_1267669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267683 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 6]
def baseStart_1267683 : Nat := 118140960795 + 1267683 * 2 ^ 59
def prefixEnd_1267683 : Nat := 4983230072969 + 3 ^ 40 * 1267683 * 2
def baseEnd_1267683 : Nat := 289302531792741741392239

theorem tailTrace_1267683 : CollatzResearch.WordTrace tailWord_1267683 prefixEnd_1267683 289302531792741741392239 := by
  unfold tailWord_1267683
  simp only [CollatzResearch.WordTrace]
  refine ⟨46236197466408468864823703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30824131644272312576549135 46236197466408468864823703)
  ·
    refine ⟨69354296199612703297235555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46236197466408468864823703 69354296199612703297235555)
    ·
      refine ⟨104031444299419054945853333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69354296199612703297235555 104031444299419054945853333)
      ·
        refine ⟨4876473951535268200586875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 104031444299419054945853333 4876473951535268200586875)
        ·
          refine ⟨7314710927302902300880313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4876473951535268200586875 7314710927302902300880313)
          ·
            refine ⟨5486033195477176725660235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7314710927302902300880313 5486033195477176725660235)
            ·
              refine ⟨8229049793215765088490353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5486033195477176725660235 8229049793215765088490353)
              ·
                refine ⟨6171787344911823816367765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8229049793215765088490353 6171787344911823816367765)
                ·
                  refine ⟨289302531792741741392239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6171787344911823816367765 289302531792741741392239)
                  ·
                    rfl

theorem cell21_1267683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 6].length) (baseStart_1267683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1267683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1267683 prefixEnd_1267683 := by exact prefixLift 1267683
  have htrace : WordTrace (prefixWord ++ tailWord_1267683) baseStart_1267683 baseEnd_1267683 := by
    simpa [prefixWord, tailWord_1267683, baseEnd_1267683] using wordTrace_append hprefix tailTrace_1267683
  have hstable : (prefixWord ++ tailWord_1267683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267683).length < 2 ^ (prefixWord ++ tailWord_1267683).sum := by decide
  have hdescent : baseEnd_1267683 < baseStart_1267683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267717 : List Nat := [1, 3, 1, 1, 2, 6, 2, 1, 4]
def baseStart_1267717 : Nat := 118140960795 + 1267717 * 2 ^ 59
def prefixEnd_1267717 : Nat := 4983230072969 + 3 ^ 40 * 1267717 * 2
def baseEnd_1267717 : Nat := 289310291055965237825503

theorem tailTrace_1267717 : CollatzResearch.WordTrace tailWord_1267717 prefixEnd_1267717 289310291055965237825503 := by
  unfold tailWord_1267717
  simp only [CollatzResearch.WordTrace]
  refine ⟨46237437548285292671561405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30824958365523528447707603 46237437548285292671561405)
  ·
    refine ⟨17339039080606984751835527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46237437548285292671561405 17339039080606984751835527)
    ·
      refine ⟨26008558620910477127753291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17339039080606984751835527 26008558620910477127753291)
      ·
        refine ⟨39012837931365715691629937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26008558620910477127753291 39012837931365715691629937)
        ·
          refine ⟨29259628448524286768722453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39012837931365715691629937 29259628448524286768722453)
          ·
            refine ⟨1371545083524575942283865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29259628448524286768722453 1371545083524575942283865)
            ·
              refine ⟨1028658812643431956712899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1371545083524575942283865 1028658812643431956712899)
              ·
                refine ⟨1542988218965147935069349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1028658812643431956712899 1542988218965147935069349)
                ·
                  refine ⟨289310291055965237825503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1542988218965147935069349 289310291055965237825503)
                  ·
                    rfl

theorem cell21_1267717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_1267717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1267717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1267717 prefixEnd_1267717 := by exact prefixLift 1267717
  have htrace : WordTrace (prefixWord ++ tailWord_1267717) baseStart_1267717 baseEnd_1267717 := by
    simpa [prefixWord, tailWord_1267717, baseEnd_1267717] using wordTrace_append hprefix tailTrace_1267717
  have hstable : (prefixWord ++ tailWord_1267717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267717).length < 2 ^ (prefixWord ++ tailWord_1267717).sum := by decide
  have hdescent : baseEnd_1267717 < baseStart_1267717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267762 : List Nat := [3, 2, 1, 1, 2, 4, 1, 4, 3]
def baseStart_1267762 : Nat := 118140960795 + 1267762 * 2 ^ 59
def prefixEnd_1267762 : Nat := 4983230072969 + 3 ^ 40 * 1267762 * 2
def baseEnd_1267762 : Nat := 289320560669055159575411

theorem tailTrace_1267762 : CollatzResearch.WordTrace tailWord_1267762 prefixEnd_1267762 289320560669055159575411 := by
  unfold tailWord_1267762
  simp only [CollatzResearch.WordTrace]
  refine ⟨11559769708280566339237385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30826052555414843571299693 11559769708280566339237385)
  ·
    refine ⟨8669827281210424754428039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11559769708280566339237385 8669827281210424754428039)
    ·
      refine ⟨13004740921815637131642059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8669827281210424754428039 13004740921815637131642059)
      ·
        refine ⟨19507111382723455697463089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13004740921815637131642059 19507111382723455697463089)
        ·
          refine ⟨14630333537042591773097317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19507111382723455697463089 14630333537042591773097317)
          ·
            refine ⟨2743187538195485957455747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14630333537042591773097317 2743187538195485957455747)
            ·
              refine ⟨4114781307293228936183621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2743187538195485957455747 4114781307293228936183621)
              ·
                refine ⟨771521495117480425534429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4114781307293228936183621 771521495117480425534429)
                ·
                  refine ⟨289320560669055159575411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 771521495117480425534429 289320560669055159575411)
                  ·
                    rfl

theorem cell21_1267762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_1267762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1267762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1267762 prefixEnd_1267762 := by exact prefixLift 1267762
  have htrace : WordTrace (prefixWord ++ tailWord_1267762) baseStart_1267762 baseEnd_1267762 := by
    simpa [prefixWord, tailWord_1267762, baseEnd_1267762] using wordTrace_append hprefix tailTrace_1267762
  have hstable : (prefixWord ++ tailWord_1267762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267762).length < 2 ^ (prefixWord ++ tailWord_1267762).sum := by decide
  have hdescent : baseEnd_1267762 < baseStart_1267762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267810 : List Nat := [3, 3, 2, 2, 2, 2, 1, 2, 4]
def baseStart_1267810 : Nat := 118140960795 + 1267810 * 2 ^ 59
def prefixEnd_1267810 : Nat := 4983230072969 + 3 ^ 40 * 1267810 * 2
def baseEnd_1267810 : Nat := 289331514923017742775313

theorem tailTrace_1267810 : CollatzResearch.WordTrace tailWord_1267810 prefixEnd_1267810 289331514923017742775313 := by
  unfold tailWord_1267810
  simp only [CollatzResearch.WordTrace]
  refine ⟨11560207384237092388674221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30827219691298913036464589 11560207384237092388674221)
  ·
    refine ⟨4335077769088909645752833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11560207384237092388674221 4335077769088909645752833)
    ·
      refine ⟨3251308326816682234314625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4335077769088909645752833 3251308326816682234314625)
      ·
        refine ⟨2438481245112511675735969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3251308326816682234314625 2438481245112511675735969)
        ·
          refine ⟨1828860933834383756801977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2438481245112511675735969 1828860933834383756801977)
          ·
            refine ⟨1371645700375787817601483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1828860933834383756801977 1371645700375787817601483)
            ·
              refine ⟨2057468550563681726402225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1371645700375787817601483 2057468550563681726402225)
              ·
                refine ⟨1543101412922761294801669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2057468550563681726402225 1543101412922761294801669)
                ·
                  refine ⟨289331514923017742775313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1543101412922761294801669 289331514923017742775313)
                  ·
                    rfl

theorem cell21_1267810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_1267810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1267810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1267810 prefixEnd_1267810 := by exact prefixLift 1267810
  have htrace : WordTrace (prefixWord ++ tailWord_1267810) baseStart_1267810 baseEnd_1267810 := by
    simpa [prefixWord, tailWord_1267810, baseEnd_1267810] using wordTrace_append hprefix tailTrace_1267810
  have hstable : (prefixWord ++ tailWord_1267810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267810).length < 2 ^ (prefixWord ++ tailWord_1267810).sum := by decide
  have hdescent : baseEnd_1267810 < baseStart_1267810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267821 : List Nat := [1, 5, 1, 1, 2, 1, 4, 1, 5]
def baseStart_1267821 : Nat := 118140960795 + 1267821 * 2 ^ 59
def prefixEnd_1267821 : Nat := 4983230072969 + 3 ^ 40 * 1267821 * 2
def baseEnd_1267821 : Nat := 289334025272884168091957

theorem tailTrace_1267821 : CollatzResearch.WordTrace tailWord_1267821 prefixEnd_1267821 289334025272884168091957 := by
  unfold tailWord_1267821
  simp only [CollatzResearch.WordTrace]
  refine ⟨46241230739908518433347317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30827487159939012288898211 46241230739908518433347317)
  ·
    refine ⟨4335115381866423603126311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46241230739908518433347317 4335115381866423603126311)
    ·
      refine ⟨6502673072799635404689467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4335115381866423603126311 6502673072799635404689467)
      ·
        refine ⟨9754009609199453107034201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6502673072799635404689467 9754009609199453107034201)
        ·
          refine ⟨7315507206899589830275651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9754009609199453107034201 7315507206899589830275651)
          ·
            refine ⟨10973260810349384745413477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7315507206899589830275651 10973260810349384745413477)
            ·
              refine ⟨2057486401940509639765027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10973260810349384745413477 2057486401940509639765027)
              ·
                refine ⟨3086229602910764459647541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2057486401940509639765027 3086229602910764459647541)
                ·
                  refine ⟨289334025272884168091957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3086229602910764459647541 289334025272884168091957)
                  ·
                    rfl

theorem cell21_1267821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_1267821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1267821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1267821 prefixEnd_1267821 := by exact prefixLift 1267821
  have htrace : WordTrace (prefixWord ++ tailWord_1267821) baseStart_1267821 baseEnd_1267821 := by
    simpa [prefixWord, tailWord_1267821, baseEnd_1267821] using wordTrace_append hprefix tailTrace_1267821
  have hstable : (prefixWord ++ tailWord_1267821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267821).length < 2 ^ (prefixWord ++ tailWord_1267821).sum := by decide
  have hdescent : baseEnd_1267821 < baseStart_1267821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267849 : List Nat := [1, 2, 1, 1, 4, 2, 3, 7]
def baseStart_1267849 : Nat := 118140960795 + 1267849 * 2 ^ 59
def prefixEnd_1267849 : Nat := 4983230072969 + 3 ^ 40 * 1267849 * 2
def baseEnd_1267849 : Nat := 96446805084787447208411

theorem tailTrace_1267849 : CollatzResearch.WordTrace tailWord_1267849 prefixEnd_1267849 96446805084787447208411 := by
  unfold tailWord_1267849
  simp only [CollatzResearch.WordTrace]
  refine ⟨46242251983807079215366601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30828167989204719476911067 46242251983807079215366601)
  ·
    refine ⟨34681688987855309411524951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46242251983807079215366601 34681688987855309411524951)
    ·
      refine ⟨52022533481782964117287427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34681688987855309411524951 52022533481782964117287427)
      ·
        refine ⟨78033800222674446175931141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52022533481782964117287427 78033800222674446175931141)
        ·
          refine ⟨14631337541751458657987089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78033800222674446175931141 14631337541751458657987089)
          ·
            refine ⟨10973503156313593993490317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14631337541751458657987089 10973503156313593993490317)
            ·
              refine ⟨4115063683617597747558869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10973503156313593993490317 4115063683617597747558869)
              ·
                refine ⟨96446805084787447208411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4115063683617597747558869 96446805084787447208411)
                ·
                  rfl

theorem cell21_1267849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 7].length) (baseStart_1267849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1267849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1267849 prefixEnd_1267849 := by exact prefixLift 1267849
  have htrace : WordTrace (prefixWord ++ tailWord_1267849) baseStart_1267849 baseEnd_1267849 := by
    simpa [prefixWord, tailWord_1267849, baseEnd_1267849] using wordTrace_append hprefix tailTrace_1267849
  have hstable : (prefixWord ++ tailWord_1267849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267849).length < 2 ^ (prefixWord ++ tailWord_1267849).sum := by decide
  have hdescent : baseEnd_1267849 < baseStart_1267849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267886 : List Nat := [4, 1, 4, 2, 1, 1, 1, 3, 4]
def baseStart_1267886 : Nat := 118140960795 + 1267886 * 2 ^ 59
def prefixEnd_1267886 : Nat := 4983230072969 + 3 ^ 40 * 1267886 * 2
def baseEnd_1267886 : Nat := 289348859158458499508491

theorem tailTrace_1267886 : CollatzResearch.WordTrace tailWord_1267886 prefixEnd_1267886 289348859158458499508491 := by
  unfold tailWord_1267886
  simp only [CollatzResearch.WordTrace]
  refine ⟨5780450185584129316807939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30829067656448689689642341 5780450185584129316807939)
  ·
    refine ⟨8670675278376193975211909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5780450185584129316807939 8670675278376193975211909)
    ·
      refine ⟨1625751614695536370352233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8670675278376193975211909 1625751614695536370352233)
      ·
        refine ⟨1219313711021652277764175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1625751614695536370352233 1219313711021652277764175)
        ·
          refine ⟨1828970566532478416646263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1219313711021652277764175 1828970566532478416646263)
          ·
            refine ⟨2743455849798717624969395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1828970566532478416646263 2743455849798717624969395)
            ·
              refine ⟨4115183774698076437454093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2743455849798717624969395 4115183774698076437454093)
              ·
                refine ⟨1543193915511778664045285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4115183774698076437454093 1543193915511778664045285)
                ·
                  refine ⟨289348859158458499508491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1543193915511778664045285 289348859158458499508491)
                  ·
                    rfl

theorem cell21_1267886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_1267886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1267886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1267886 prefixEnd_1267886 := by exact prefixLift 1267886
  have htrace : WordTrace (prefixWord ++ tailWord_1267886) baseStart_1267886 baseEnd_1267886 := by
    simpa [prefixWord, tailWord_1267886, baseEnd_1267886] using wordTrace_append hprefix tailTrace_1267886
  have hstable : (prefixWord ++ tailWord_1267886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267886).length < 2 ^ (prefixWord ++ tailWord_1267886).sum := by decide
  have hdescent : baseEnd_1267886 < baseStart_1267886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267925 : List Nat := [1, 3, 2, 4, 11]
def baseStart_1267925 : Nat := 118140960795 + 1267925 * 2 ^ 59
def prefixEnd_1267925 : Nat := 4983230072969 + 3 ^ 40 * 1267925 * 2
def baseEnd_1267925 : Nat := 3572318018392630843931

theorem tailTrace_1267925 : CollatzResearch.WordTrace tailWord_1267925 prefixEnd_1267925 3572318018392630843931 := by
  unfold tailWord_1267925
  simp only [CollatzResearch.WordTrace]
  refine ⟨46245023931531744195133229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30830015954354496130088819 46245023931531744195133229)
  ·
    refine ⟨17341883974324404073174961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46245023931531744195133229 17341883974324404073174961)
    ·
      refine ⟨13006412980743303054881221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17341883974324404073174961 13006412980743303054881221)
      ·
        refine ⟨2438702433889369322790229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13006412980743303054881221 2438702433889369322790229)
        ·
          refine ⟨3572318018392630843931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2438702433889369322790229 3572318018392630843931)
          ·
            rfl

theorem cell21_1267925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 11].length) (baseStart_1267925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1267925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1267925 prefixEnd_1267925 := by exact prefixLift 1267925
  have htrace : WordTrace (prefixWord ++ tailWord_1267925) baseStart_1267925 baseEnd_1267925 := by
    simpa [prefixWord, tailWord_1267925, baseEnd_1267925] using wordTrace_append hprefix tailTrace_1267925
  have hstable : (prefixWord ++ tailWord_1267925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267925).length < 2 ^ (prefixWord ++ tailWord_1267925).sum := by decide
  have hdescent : baseEnd_1267925 < baseStart_1267925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267928 : List Nat := [2, 1, 2, 2, 4, 2, 2, 2, 4]
def baseStart_1267928 : Nat := 118140960795 + 1267928 * 2 ^ 59
def prefixEnd_1267928 : Nat := 4983230072969 + 3 ^ 40 * 1267928 * 2
def baseEnd_1267928 : Nat := 289358444130675759808405

theorem tailTrace_1267928 : CollatzResearch.WordTrace tailWord_1267928 prefixEnd_1267928 289358444130675759808405 := by
  unfold tailWord_1267928
  simp only [CollatzResearch.WordTrace]
  refine ⟨23122566675260437853746219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30830088900347250471661625 23122566675260437853746219)
  ·
    refine ⟨34683850012890656780619329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23122566675260437853746219 34683850012890656780619329)
    ·
      refine ⟨26012887509667992585464497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34683850012890656780619329 26012887509667992585464497)
      ·
        refine ⟨19509665632250994439098373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26012887509667992585464497 19509665632250994439098373)
        ·
          refine ⟨3658062306047061457330945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19509665632250994439098373 3658062306047061457330945)
          ·
            refine ⟨2743546729535296092998209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3658062306047061457330945 2743546729535296092998209)
            ·
              refine ⟨2057660047151472069748657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2743546729535296092998209 2057660047151472069748657)
              ·
                refine ⟨1543245035363604052311493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2057660047151472069748657 1543245035363604052311493)
                ·
                  refine ⟨289358444130675759808405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1543245035363604052311493 289358444130675759808405)
                  ·
                    rfl

theorem cell21_1267928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 4].length) (baseStart_1267928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1267928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1267928 prefixEnd_1267928 := by exact prefixLift 1267928
  have htrace : WordTrace (prefixWord ++ tailWord_1267928) baseStart_1267928 baseEnd_1267928 := by
    simpa [prefixWord, tailWord_1267928, baseEnd_1267928] using wordTrace_append hprefix tailTrace_1267928
  have hstable : (prefixWord ++ tailWord_1267928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267928).length < 2 ^ (prefixWord ++ tailWord_1267928).sum := by decide
  have hdescent : baseEnd_1267928 < baseStart_1267928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268018 : List Nat := [3, 2, 1, 1, 5, 1, 1, 7]
def baseStart_1268018 : Nat := 118140960795 + 1268018 * 2 ^ 59
def prefixEnd_1268018 : Nat := 4983230072969 + 3 ^ 40 * 1268018 * 2
def baseEnd_1268018 : Nat := 96459661118951867769407

theorem tailTrace_1268018 : CollatzResearch.WordTrace tailWord_1268018 prefixEnd_1268018 96459661118951867769407 := by
  unfold tailWord_1268018
  simp only [CollatzResearch.WordTrace]
  refine ⟨11562103980048705269567177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30832277280129880718845805 11562103980048705269567177)
  ·
    refine ⟨8671577985036528952175383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11562103980048705269567177 8671577985036528952175383)
    ·
      refine ⟨13007366977554793428263075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8671577985036528952175383 13007366977554793428263075)
      ·
        refine ⟨19511050466332190142394613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13007366977554793428263075 19511050466332190142394613)
        ·
          refine ⟨1829160981218642825849495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19511050466332190142394613 1829160981218642825849495)
          ·
            refine ⟨2743741471827964238774243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1829160981218642825849495 2743741471827964238774243)
            ·
              refine ⟨4115612207741946358161365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2743741471827964238774243 4115612207741946358161365)
              ·
                refine ⟨96459661118951867769407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4115612207741946358161365 96459661118951867769407)
                ·
                  rfl

theorem cell21_1268018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_1268018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268018 prefixEnd_1268018 := by exact prefixLift 1268018
  have htrace : WordTrace (prefixWord ++ tailWord_1268018) baseStart_1268018 baseEnd_1268018 := by
    simpa [prefixWord, tailWord_1268018, baseEnd_1268018] using wordTrace_append hprefix tailTrace_1268018
  have hstable : (prefixWord ++ tailWord_1268018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268018).length < 2 ^ (prefixWord ++ tailWord_1268018).sum := by decide
  have hdescent : baseEnd_1268018 < baseStart_1268018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268049 : List Nat := [1, 2, 2, 1, 4, 4, 1, 1, 5]
def baseStart_1268049 : Nat := 118140960795 + 1268049 * 2 ^ 59
def prefixEnd_1268049 : Nat := 4983230072969 + 3 ^ 40 * 1268049 * 2
def baseEnd_1268049 : Nat := 289386057979206438291491

theorem tailTrace_1268049 : CollatzResearch.WordTrace tailWord_1268049 prefixEnd_1268049 289386057979206438291491 := by
  unfold tailWord_1268049
  simp only [CollatzResearch.WordTrace]
  refine ⟨46249546583082513372647201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30833031055388342248431467 46249546583082513372647201)
  ·
    refine ⟨34687159937311885029485401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46249546583082513372647201 34687159937311885029485401)
    ·
      refine ⟨26015369952983913772114051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34687159937311885029485401 26015369952983913772114051)
      ·
        refine ⟨39023054929475870658171077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26015369952983913772114051 39023054929475870658171077)
        ·
          refine ⟨7316822799276725748407077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39023054929475870658171077 7316822799276725748407077)
          ·
            refine ⟨1371904274864386077826327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7316822799276725748407077 1371904274864386077826327)
            ·
              refine ⟨2057856412296579116739491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1371904274864386077826327 2057856412296579116739491)
              ·
                refine ⟨3086784618444868675109237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2057856412296579116739491 3086784618444868675109237)
                ·
                  refine ⟨289386057979206438291491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3086784618444868675109237 289386057979206438291491)
                  ·
                    rfl

theorem cell21_1268049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 5].length) (baseStart_1268049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268049 prefixEnd_1268049 := by exact prefixLift 1268049
  have htrace : WordTrace (prefixWord ++ tailWord_1268049) baseStart_1268049 baseEnd_1268049 := by
    simpa [prefixWord, tailWord_1268049, baseEnd_1268049] using wordTrace_append hprefix tailTrace_1268049
  have hstable : (prefixWord ++ tailWord_1268049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268049).length < 2 ^ (prefixWord ++ tailWord_1268049).sum := by decide
  have hdescent : baseEnd_1268049 < baseStart_1268049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268077 : List Nat := [1, 5, 1, 1, 1, 2, 1, 9]
def baseStart_1268077 : Nat := 118140960795 + 1268077 * 2 ^ 59
def prefixEnd_1268077 : Nat := 4983230072969 + 3 ^ 40 * 1268077 * 2
def baseEnd_1268077 : Nat := 96464149320228203941589

theorem tailTrace_1268077 : CollatzResearch.WordTrace tailWord_1268077 prefixEnd_1268077 96464149320228203941589 := by
  unfold tailWord_1268077
  simp only [CollatzResearch.WordTrace]
  refine ⟨46250567826981074154666485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30833711884654049436444323 46250567826981074154666485)
  ·
    refine ⟨4335990733779475701999983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46250567826981074154666485 4335990733779475701999983)
    ·
      refine ⟨6503986100669213552999975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4335990733779475701999983 6503986100669213552999975)
      ·
        refine ⟨9755979151003820329499963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6503986100669213552999975 9755979151003820329499963)
        ·
          refine ⟨14633968726505730494249945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9755979151003820329499963 14633968726505730494249945)
          ·
            refine ⟨10975476544879297870687459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14633968726505730494249945 10975476544879297870687459)
            ·
              refine ⟨16463214817318946806031189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10975476544879297870687459 16463214817318946806031189)
              ·
                refine ⟨96464149320228203941589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16463214817318946806031189 96464149320228203941589)
                ·
                  rfl

theorem cell21_1268077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 9].length) (baseStart_1268077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268077 prefixEnd_1268077 := by exact prefixLift 1268077
  have htrace : WordTrace (prefixWord ++ tailWord_1268077) baseStart_1268077 baseEnd_1268077 := by
    simpa [prefixWord, tailWord_1268077, baseEnd_1268077] using wordTrace_append hprefix tailTrace_1268077
  have hstable : (prefixWord ++ tailWord_1268077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268077).length < 2 ^ (prefixWord ++ tailWord_1268077).sum := by decide
  have hdescent : baseEnd_1268077 < baseStart_1268077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268125 : List Nat := [1, 4, 2, 1, 4, 1, 1, 2, 5]
def baseStart_1268125 : Nat := 118140960795 + 1268125 * 2 ^ 59
def prefixEnd_1268125 : Nat := 4983230072969 + 3 ^ 40 * 1268125 * 2
def baseEnd_1268125 : Nat := 289403402214647195024669

theorem tailTrace_1268125 : CollatzResearch.WordTrace tailWord_1268125 prefixEnd_1268125 289403402214647195024669 := by
  unfold tailWord_1268125
  simp only [CollatzResearch.WordTrace]
  refine ⟨46252318530807178352413829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30834879020538118901609219 46252318530807178352413829)
  ·
    refine ⟨8672309724526345941077593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46252318530807178352413829 8672309724526345941077593)
    ·
      refine ⟨6504232293394759455808195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8672309724526345941077593 6504232293394759455808195)
      ·
        refine ⟨9756348440092139183712293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6504232293394759455808195 9756348440092139183712293)
        ·
          refine ⟨1829315332517276096946055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9756348440092139183712293 1829315332517276096946055)
          ·
            refine ⟨2743972998775914145419083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1829315332517276096946055 2743972998775914145419083)
            ·
              refine ⟨4115959498163871218128625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2743972998775914145419083 4115959498163871218128625)
              ·
                refine ⟨3086969623622903413596469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4115959498163871218128625 3086969623622903413596469)
                ·
                  refine ⟨289403402214647195024669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3086969623622903413596469 289403402214647195024669)
                  ·
                    rfl

theorem cell21_1268125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_1268125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268125 prefixEnd_1268125 := by exact prefixLift 1268125
  have htrace : WordTrace (prefixWord ++ tailWord_1268125) baseStart_1268125 baseEnd_1268125 := by
    simpa [prefixWord, tailWord_1268125, baseEnd_1268125] using wordTrace_append hprefix tailTrace_1268125
  have hstable : (prefixWord ++ tailWord_1268125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268125).length < 2 ^ (prefixWord ++ tailWord_1268125).sum := by decide
  have hdescent : baseEnd_1268125 < baseStart_1268125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268153 : List Nat := [1, 2, 1, 4, 3, 2, 8]
def baseStart_1268153 : Nat := 118140960795 + 1268153 * 2 ^ 59
def prefixEnd_1268153 : Nat := 4983230072969 + 3 ^ 40 * 1268153 * 2
def baseEnd_1268153 : Nat := 32156643577347263173105

theorem tailTrace_1268153 : CollatzResearch.WordTrace tailWord_1268153 prefixEnd_1268153 32156643577347263173105 := by
  unfold tailWord_1268153
  simp only [CollatzResearch.WordTrace]
  refine ⟨46253339774705739134433113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30835559849803826089622075 46253339774705739134433113)
  ·
    refine ⟨34690004831029304350824835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46253339774705739134433113 34690004831029304350824835)
    ·
      refine ⟨52035007246543956526237253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34690004831029304350824835 52035007246543956526237253)
      ·
        refine ⟨9756563858726991848669485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52035007246543956526237253 9756563858726991848669485)
        ·
          refine ⟨3658711447022621943251057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9756563858726991848669485 3658711447022621943251057)
          ·
            refine ⟨2744033585266966457438293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3658711447022621943251057 2744033585266966457438293)
            ·
              refine ⟨32156643577347263173105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2744033585266966457438293 32156643577347263173105)
              ·
                rfl

theorem cell21_1268153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 8].length) (baseStart_1268153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268153 prefixEnd_1268153 := by exact prefixLift 1268153
  have htrace : WordTrace (prefixWord ++ tailWord_1268153) baseStart_1268153 baseEnd_1268153 := by
    simpa [prefixWord, tailWord_1268153, baseEnd_1268153] using wordTrace_append hprefix tailTrace_1268153
  have hstable : (prefixWord ++ tailWord_1268153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268153).length < 2 ^ (prefixWord ++ tailWord_1268153).sum := by decide
  have hdescent : baseEnd_1268153 < baseStart_1268153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268156 : List Nat := [2, 2, 2, 4, 1, 1, 3, 2, 4]
def baseStart_1268156 : Nat := 118140960795 + 1268156 * 2 ^ 59
def prefixEnd_1268156 : Nat := 4983230072969 + 3 ^ 40 * 1268156 * 2
def baseEnd_1268156 : Nat := 289410476836998030007939

theorem tailTrace_1268156 : CollatzResearch.WordTrace tailWord_1268156 prefixEnd_1268156 289410476836998030007939 := by
  unfold tailWord_1268156
  simp only [CollatzResearch.WordTrace]
  refine ⟨23126724596847435323396161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30835632795796580431194881 23126724596847435323396161)
  ·
    refine ⟨17345043447635576492547121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23126724596847435323396161 17345043447635576492547121)
    ·
      refine ⟨13008782585726682369410341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17345043447635576492547121 13008782585726682369410341)
      ·
        refine ⟨2439146734823752944264439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13008782585726682369410341 2439146734823752944264439)
        ·
          refine ⟨3658720102235629416396659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2439146734823752944264439 3658720102235629416396659)
          ·
            refine ⟨5488080153353444124594989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3658720102235629416396659 5488080153353444124594989)
            ·
              refine ⟨2058030057507541546723121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5488080153353444124594989 2058030057507541546723121)
              ·
                refine ⟨1543522543130656160042341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2058030057507541546723121 1543522543130656160042341)
                ·
                  refine ⟨289410476836998030007939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1543522543130656160042341 289410476836998030007939)
                  ·
                    rfl

theorem cell21_1268156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_1268156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268156 prefixEnd_1268156 := by exact prefixLift 1268156
  have htrace : WordTrace (prefixWord ++ tailWord_1268156) baseStart_1268156 baseEnd_1268156 := by
    simpa [prefixWord, tailWord_1268156, baseEnd_1268156] using wordTrace_append hprefix tailTrace_1268156
  have hstable : (prefixWord ++ tailWord_1268156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268156).length < 2 ^ (prefixWord ++ tailWord_1268156).sum := by decide
  have hdescent : baseEnd_1268156 < baseStart_1268156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268243 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 7]
def baseStart_1268243 : Nat := 118140960795 + 1268243 * 2 ^ 59
def prefixEnd_1268243 : Nat := 4983230072969 + 3 ^ 40 * 1268243 * 2
def baseEnd_1268243 : Nat := 289430331422305212057761

theorem tailTrace_1268243 : CollatzResearch.WordTrace tailWord_1268243 prefixEnd_1268243 289430331422305212057761 := by
  unfold tailWord_1268243
  simp only [CollatzResearch.WordTrace]
  refine ⟨46256622344379684505209383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30837748229586456336806255 46256622344379684505209383)
  ·
    refine ⟨69384933516569526757814075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46256622344379684505209383 69384933516569526757814075)
    ·
      refine ⟨104077400274854290136721113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69384933516569526757814075 104077400274854290136721113)
      ·
        refine ⟨78058050206140717602540835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104077400274854290136721113 78058050206140717602540835)
        ·
          refine ⟨117087075309211076403811253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78058050206140717602540835 117087075309211076403811253)
          ·
            refine ⟨10976913310238538412857305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117087075309211076403811253 10976913310238538412857305)
            ·
              refine ⟨8232684982678903809642979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10976913310238538412857305 8232684982678903809642979)
              ·
                refine ⟨12349027474018355714464469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8232684982678903809642979 12349027474018355714464469)
                ·
                  refine ⟨289430331422305212057761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12349027474018355714464469 289430331422305212057761)
                  ·
                    rfl

theorem cell21_1268243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 7].length) (baseStart_1268243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268243 prefixEnd_1268243 := by exact prefixLift 1268243
  have htrace : WordTrace (prefixWord ++ tailWord_1268243) baseStart_1268243 baseEnd_1268243 := by
    simpa [prefixWord, tailWord_1268243, baseEnd_1268243] using wordTrace_append hprefix tailTrace_1268243
  have hstable : (prefixWord ++ tailWord_1268243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268243).length < 2 ^ (prefixWord ++ tailWord_1268243).sum := by decide
  have hdescent : baseEnd_1268243 < baseStart_1268243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268263 : List Nat := [1, 1, 7, 2, 2, 8]
def baseStart_1268263 : Nat := 118140960795 + 1268263 * 2 ^ 59
def prefixEnd_1268263 : Nat := 4983230072969 + 3 ^ 40 * 1268263 * 2
def baseEnd_1268263 : Nat := 10719810951658874878681

theorem tailTrace_1268263 : CollatzResearch.WordTrace tailWord_1268263 prefixEnd_1268263 10719810951658874878681 := by
  unfold tailWord_1268263
  simp only [CollatzResearch.WordTrace]
  refine ⟨46257351804307227920937443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30838234536204818613958295 46257351804307227920937443)
  ·
    refine ⟨69386027706460841881406165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46257351804307227920937443 69386027706460841881406165)
    ·
      refine ⟨1626235024370175981595457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 69386027706460841881406165 1626235024370175981595457)
      ·
        refine ⟨1219676268277631986196593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1626235024370175981595457 1219676268277631986196593)
        ·
          refine ⟨914757201208223989647445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1219676268277631986196593 914757201208223989647445)
          ·
            refine ⟨10719810951658874878681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 914757201208223989647445 10719810951658874878681)
            ·
              rfl

theorem cell21_1268263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 8].length) (baseStart_1268263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268263 prefixEnd_1268263 := by exact prefixLift 1268263
  have htrace : WordTrace (prefixWord ++ tailWord_1268263) baseStart_1268263 baseEnd_1268263 := by
    simpa [prefixWord, tailWord_1268263, baseEnd_1268263] using wordTrace_append hprefix tailTrace_1268263
  have hstable : (prefixWord ++ tailWord_1268263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268263).length < 2 ^ (prefixWord ++ tailWord_1268263).sum := by decide
  have hdescent : baseEnd_1268263 < baseStart_1268263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268274 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 6]
def baseStart_1268274 : Nat := 118140960795 + 1268274 * 2 ^ 59
def prefixEnd_1268274 : Nat := 4983230072969 + 3 ^ 40 * 1268274 * 2
def baseEnd_1268274 : Nat := 289437406044656047041031

theorem tailTrace_1268274 : CollatzResearch.WordTrace tailWord_1268274 prefixEnd_1268274 289437406044656047041031 := by
  unfold tailWord_1268274
  simp only [CollatzResearch.WordTrace]
  refine ⟨11564438251816844199896969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30838502004844917866391917 11564438251816844199896969)
  ·
    refine ⟨8673328688862633149922727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11564438251816844199896969 8673328688862633149922727)
    ·
      refine ⟨13009993033293949724884091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8673328688862633149922727 13009993033293949724884091)
      ·
        refine ⟨19514989549940924587326137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13009993033293949724884091 19514989549940924587326137)
        ·
          refine ⟨14636242162455693440494603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19514989549940924587326137 14636242162455693440494603)
          ·
            refine ⟨21954363243683540160741905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14636242162455693440494603 21954363243683540160741905)
            ·
              refine ⟨16465772432762655120556429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21954363243683540160741905 16465772432762655120556429)
              ·
                refine ⟨6174664662285995670208661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16465772432762655120556429 6174664662285995670208661)
                ·
                  refine ⟨289437406044656047041031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6174664662285995670208661 289437406044656047041031)
                  ·
                    rfl

theorem cell21_1268274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_1268274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268274 prefixEnd_1268274 := by exact prefixLift 1268274
  have htrace : WordTrace (prefixWord ++ tailWord_1268274) baseStart_1268274 baseEnd_1268274 := by
    simpa [prefixWord, tailWord_1268274, baseEnd_1268274] using wordTrace_append hprefix tailTrace_1268274
  have hstable : (prefixWord ++ tailWord_1268274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268274).length < 2 ^ (prefixWord ++ tailWord_1268274).sum := by decide
  have hdescent : baseEnd_1268274 < baseStart_1268274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268277 : List Nat := [1, 3, 3, 1, 1, 2, 3, 4, 3]
def baseStart_1268277 : Nat := 118140960795 + 1268277 * 2 ^ 59
def prefixEnd_1268277 : Nat := 4983230072969 + 3 ^ 40 * 1268277 * 2
def baseEnd_1268277 : Nat := 289438090685528708491025

theorem tailTrace_1268277 : CollatzResearch.WordTrace tailWord_1268277 prefixEnd_1268277 289438090685528708491025 := by
  unfold tailWord_1268277
  simp only [CollatzResearch.WordTrace]
  refine ⟨46257862426256508311947085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30838574950837672207964723 46257862426256508311947085)
  ·
    refine ⟨17346698409846190616980157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46257862426256508311947085 17346698409846190616980157)
    ·
      refine ⟨6505011903692321481367559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17346698409846190616980157 6505011903692321481367559)
      ·
        refine ⟨9757517855538482222051339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6505011903692321481367559 9757517855538482222051339)
        ·
          refine ⟨14636276783307723333077009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9757517855538482222051339 14636276783307723333077009)
          ·
            refine ⟨10977207587480792499807757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14636276783307723333077009 10977207587480792499807757)
            ·
              refine ⟨4116452845305297187427909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10977207587480792499807757 4116452845305297187427909)
              ·
                refine ⟨771834908494743222642733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4116452845305297187427909 771834908494743222642733)
                ·
                  refine ⟨289438090685528708491025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 771834908494743222642733 289438090685528708491025)
                  ·
                    rfl

theorem cell21_1268277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 3].length) (baseStart_1268277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268277 prefixEnd_1268277 := by exact prefixLift 1268277
  have htrace : WordTrace (prefixWord ++ tailWord_1268277) baseStart_1268277 baseEnd_1268277 := by
    simpa [prefixWord, tailWord_1268277, baseEnd_1268277] using wordTrace_append hprefix tailTrace_1268277
  have hstable : (prefixWord ++ tailWord_1268277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268277).length < 2 ^ (prefixWord ++ tailWord_1268277).sum := by decide
  have hdescent : baseEnd_1268277 < baseStart_1268277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268294 : List Nat := [6, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_1268294 : Nat := 118140960795 + 1268294 * 2 ^ 59
def prefixEnd_1268294 : Nat := 4983230072969 + 3 ^ 40 * 1268294 * 2
def baseEnd_1268294 : Nat := 289441970317140456707657

theorem tailTrace_1268294 : CollatzResearch.WordTrace tailWord_1268294 prefixEnd_1268294 289441970317140456707657 := by
  unfold tailWord_1268294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1445577577099841256728623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30838988311463280143543957 1445577577099841256728623)
  ·
    refine ⟨2168366365649761885092935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1445577577099841256728623 2168366365649761885092935)
    ·
      refine ⟨3252549548474642827639403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2168366365649761885092935 3252549548474642827639403)
      ·
        refine ⟨4878824322711964241459105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3252549548474642827639403 4878824322711964241459105)
        ·
          refine ⟨3659118242033973181094329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4878824322711964241459105 3659118242033973181094329)
          ·
            refine ⟨2744338681525479885820747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3659118242033973181094329 2744338681525479885820747)
            ·
              refine ⟨4116508022288219828731121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2744338681525479885820747 4116508022288219828731121)
              ·
                refine ⟨3087381016716164871548341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4116508022288219828731121 3087381016716164871548341)
                ·
                  refine ⟨289441970317140456707657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3087381016716164871548341 289441970317140456707657)
                  ·
                    rfl

theorem cell21_1268294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_1268294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268294 prefixEnd_1268294 := by exact prefixLift 1268294
  have htrace : WordTrace (prefixWord ++ tailWord_1268294) baseStart_1268294 baseEnd_1268294 := by
    simpa [prefixWord, tailWord_1268294, baseEnd_1268294] using wordTrace_append hprefix tailTrace_1268294
  have hstable : (prefixWord ++ tailWord_1268294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268294).length < 2 ^ (prefixWord ++ tailWord_1268294).sum := by decide
  have hdescent : baseEnd_1268294 < baseStart_1268294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268325 : List Nat := [1, 3, 1, 3, 5, 1, 1, 2, 4]
def baseStart_1268325 : Nat := 118140960795 + 1268325 * 2 ^ 59
def prefixEnd_1268325 : Nat := 4983230072969 + 3 ^ 40 * 1268325 * 2
def baseEnd_1268325 : Nat := 289449044939491291690927

theorem tailTrace_1268325 : CollatzResearch.WordTrace tailWord_1268325 prefixEnd_1268325 289449044939491291690927 := by
  unfold tailWord_1268325
  simp only [CollatzResearch.WordTrace]
  refine ⟨46259613130082612509694429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30839742086721741673129619 46259613130082612509694429)
  ·
    refine ⟨17347354923780979691135411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46259613130082612509694429 17347354923780979691135411)
    ·
      refine ⟨26021032385671469536703117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17347354923780979691135411 26021032385671469536703117)
      ·
        refine ⟨9757887144626801076263669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26021032385671469536703117 9757887144626801076263669)
        ·
          refine ⟨914801919808762600899719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9757887144626801076263669 914801919808762600899719)
          ·
            refine ⟨1372202879713143901349579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 914801919808762600899719 1372202879713143901349579)
            ·
              refine ⟨2058304319569715852024369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1372202879713143901349579 2058304319569715852024369)
              ·
                refine ⟨1543728239677286889018277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2058304319569715852024369 1543728239677286889018277)
                ·
                  refine ⟨289449044939491291690927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1543728239677286889018277 289449044939491291690927)
                  ·
                    rfl

theorem cell21_1268325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 4].length) (baseStart_1268325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268325 prefixEnd_1268325 := by exact prefixLift 1268325
  have htrace : WordTrace (prefixWord ++ tailWord_1268325) baseStart_1268325 baseEnd_1268325 := by
    simpa [prefixWord, tailWord_1268325, baseEnd_1268325] using wordTrace_append hprefix tailTrace_1268325
  have hstable : (prefixWord ++ tailWord_1268325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268325).length < 2 ^ (prefixWord ++ tailWord_1268325).sum := by decide
  have hdescent : baseEnd_1268325 < baseStart_1268325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268370 : List Nat := [3, 2, 3, 1, 2, 1, 3, 3, 3]
def baseStart_1268370 : Nat := 118140960795 + 1268370 * 2 ^ 59
def prefixEnd_1268370 : Nat := 4983230072969 + 3 ^ 40 * 1268370 * 2
def baseEnd_1268370 : Nat := 289459314552581213440835

theorem tailTrace_1268370 : CollatzResearch.WordTrace tailWord_1268370 prefixEnd_1268370 289459314552581213440835 := by
  unfold tailWord_1268370
  simp only [CollatzResearch.WordTrace]
  refine ⟨11565313603729896298770641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30840836276613056796721709 11565313603729896298770641)
  ·
    refine ⟨8673985202797422224077981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11565313603729896298770641 8673985202797422224077981)
    ·
      refine ⟨3252744451049033334029243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8673985202797422224077981 3252744451049033334029243)
      ·
        refine ⟨4879116676573550001043865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3252744451049033334029243 4879116676573550001043865)
        ·
          refine ⟨3659337507430162500782899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4879116676573550001043865 3659337507430162500782899)
          ·
            refine ⟨5489006261145243751174349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3659337507430162500782899 5489006261145243751174349)
            ·
              refine ⟨2058377347929466406690381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5489006261145243751174349 2058377347929466406690381)
              ·
                refine ⟨771891505473549902508893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2058377347929466406690381 771891505473549902508893)
                ·
                  refine ⟨289459314552581213440835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 771891505473549902508893 289459314552581213440835)
                  ·
                    rfl

theorem cell21_1268370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_1268370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268370 prefixEnd_1268370 := by exact prefixLift 1268370
  have htrace : WordTrace (prefixWord ++ tailWord_1268370) baseStart_1268370 baseEnd_1268370 := by
    simpa [prefixWord, tailWord_1268370, baseEnd_1268370] using wordTrace_append hprefix tailTrace_1268370
  have hstable : (prefixWord ++ tailWord_1268370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268370).length < 2 ^ (prefixWord ++ tailWord_1268370).sum := by decide
  have hdescent : baseEnd_1268370 < baseStart_1268370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268398 : List Nat := [4, 1, 4, 1, 1, 1, 1, 8]
def baseStart_1268398 : Nat := 118140960795 + 1268398 * 2 ^ 59
def prefixEnd_1268398 : Nat := 4983230072969 + 3 ^ 40 * 1268398 * 2
def baseEnd_1268398 : Nat := 96488568178019795658037

theorem tailTrace_1268398 : CollatzResearch.WordTrace tailWord_1268398 prefixEnd_1268398 96488568178019795658037 := by
  unfold tailWord_1268398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5782784457352268247137731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30841517105878763984734565 5782784457352268247137731)
  ·
    refine ⟨8674176686028402370706597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5782784457352268247137731 8674176686028402370706597)
    ·
      refine ⟨1626408128630325444507487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8674176686028402370706597 1626408128630325444507487)
      ·
        refine ⟨2439612192945488166761231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1626408128630325444507487 2439612192945488166761231)
        ·
          refine ⟨3659418289418232250141847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2439612192945488166761231 3659418289418232250141847)
          ·
            refine ⟨5489127434127348375212771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3659418289418232250141847 5489127434127348375212771)
            ·
              refine ⟨8233691151191022562819157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5489127434127348375212771 8233691151191022562819157)
              ·
                refine ⟨96488568178019795658037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8233691151191022562819157 96488568178019795658037)
                ·
                  rfl

theorem cell21_1268398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_1268398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268398 prefixEnd_1268398 := by exact prefixLift 1268398
  have htrace : WordTrace (prefixWord ++ tailWord_1268398) baseStart_1268398 baseEnd_1268398 := by
    simpa [prefixWord, tailWord_1268398, baseEnd_1268398] using wordTrace_append hprefix tailTrace_1268398
  have hstable : (prefixWord ++ tailWord_1268398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268398).length < 2 ^ (prefixWord ++ tailWord_1268398).sum := by decide
  have hdescent : baseEnd_1268398 < baseStart_1268398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268440 : List Nat := [2, 1, 2, 2, 3, 11]
def baseStart_1268440 : Nat := 118140960795 + 1268440 * 2 ^ 59
def prefixEnd_1268440 : Nat := 4983230072969 + 3 ^ 40 * 1268440 * 2
def baseEnd_1268440 : Nat := 10721307018750986936075

theorem tailTrace_1268440 : CollatzResearch.WordTrace tailWord_1268440 prefixEnd_1268440 10721307018750986936075 := by
  unfold tailWord_1268440
  simp only [CollatzResearch.WordTrace]
  refine ⟨23131903762332993575065387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30842538349777324766753849 23131903762332993575065387)
  ·
    refine ⟨34697855643499490362598081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23131903762332993575065387 34697855643499490362598081)
    ·
      refine ⟨26023391732624617771948561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34697855643499490362598081 26023391732624617771948561)
      ·
        refine ⟨19517543799468463328961421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26023391732624617771948561 19517543799468463328961421)
        ·
          refine ⟨7319078924800673748360533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19517543799468463328961421 7319078924800673748360533)
          ·
            refine ⟨10721307018750986936075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7319078924800673748360533 10721307018750986936075)
            ·
              rfl

theorem cell21_1268440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 11].length) (baseStart_1268440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268440 prefixEnd_1268440 := by exact prefixLift 1268440
  have htrace : WordTrace (prefixWord ++ tailWord_1268440) baseStart_1268440 baseEnd_1268440 := by
    simpa [prefixWord, tailWord_1268440, baseEnd_1268440] using wordTrace_append hprefix tailTrace_1268440
  have hstable : (prefixWord ++ tailWord_1268440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268440).length < 2 ^ (prefixWord ++ tailWord_1268440).sum := by decide
  have hdescent : baseEnd_1268440 < baseStart_1268440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268525 : List Nat := [1, 5, 3, 2, 2, 1, 2, 5]
def baseStart_1268525 : Nat := 118140960795 + 1268525 * 2 ^ 59
def prefixEnd_1268525 : Nat := 4983230072969 + 3 ^ 40 * 1268525 * 2
def baseEnd_1268525 : Nat := 96498229221445129452395

theorem tailTrace_1268525 : CollatzResearch.WordTrace tailWord_1268525 prefixEnd_1268525 96498229221445129452395 := by
  unfold tailWord_1268525
  simp only [CollatzResearch.WordTrace]
  refine ⟨46266907729358046666975029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30844605152905364444650019 46266907729358046666975029)
  ·
    refine ⟨4337522599627316875028909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46266907729358046666975029 4337522599627316875028909)
    ·
      refine ⟨1626570974860243828135841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4337522599627316875028909 1626570974860243828135841)
      ·
        refine ⟨1219928231145182871101881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1626570974860243828135841 1219928231145182871101881)
        ·
          refine ⟨914946173358887153326411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1219928231145182871101881 914946173358887153326411)
          ·
            refine ⟨1372419260038330729989617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 914946173358887153326411 1372419260038330729989617)
            ·
              refine ⟨1029314445028748047492213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1372419260038330729989617 1029314445028748047492213)
              ·
                refine ⟨96498229221445129452395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1029314445028748047492213 96498229221445129452395)
                ·
                  rfl

theorem cell21_1268525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 5].length) (baseStart_1268525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268525 prefixEnd_1268525 := by exact prefixLift 1268525
  have htrace : WordTrace (prefixWord ++ tailWord_1268525) baseStart_1268525 baseEnd_1268525 := by
    simpa [prefixWord, tailWord_1268525, baseEnd_1268525] using wordTrace_append hprefix tailTrace_1268525
  have hstable : (prefixWord ++ tailWord_1268525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268525).length < 2 ^ (prefixWord ++ tailWord_1268525).sum := by decide
  have hdescent : baseEnd_1268525 < baseStart_1268525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268533 : List Nat := [1, 3, 3, 1, 3, 2, 1, 7]
def baseStart_1268533 : Nat := 118140960795 + 1268533 * 2 ^ 59
def prefixEnd_1268533 : Nat := 4983230072969 + 3 ^ 40 * 1268533 * 2
def baseEnd_1268533 : Nat := 96498837791109717407945

theorem tailTrace_1268533 : CollatzResearch.WordTrace tailWord_1268533 prefixEnd_1268533 96498837791109717407945 := by
  unfold tailWord_1268533
  simp only [CollatzResearch.WordTrace]
  refine ⟨46267199513329064033266253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30844799675552709355510835 46267199513329064033266253)
  ·
    refine ⟨17350199817498399012474845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46267199513329064033266253 17350199817498399012474845)
    ·
      refine ⟨6506324931561899629678067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17350199817498399012474845 6506324931561899629678067)
      ·
        refine ⟨9759487397342849444517101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6506324931561899629678067 9759487397342849444517101)
        ·
          refine ⟨3659807774003568541693913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9759487397342849444517101 3659807774003568541693913)
          ·
            refine ⟨2744855830502676406270435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3659807774003568541693913 2744855830502676406270435)
            ·
              refine ⟨4117283745754014609405653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2744855830502676406270435 4117283745754014609405653)
              ·
                refine ⟨96498837791109717407945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4117283745754014609405653 96498837791109717407945)
                ·
                  rfl

theorem cell21_1268533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 7].length) (baseStart_1268533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268533 prefixEnd_1268533 := by exact prefixLift 1268533
  have htrace : WordTrace (prefixWord ++ tailWord_1268533) baseStart_1268533 baseEnd_1268533 := by
    simpa [prefixWord, tailWord_1268533, baseEnd_1268533] using wordTrace_append hprefix tailTrace_1268533
  have hstable : (prefixWord ++ tailWord_1268533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268533).length < 2 ^ (prefixWord ++ tailWord_1268533).sum := by decide
  have hdescent : baseEnd_1268533 < baseStart_1268533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268592 : List Nat := [2, 1, 1, 1, 4, 1, 4, 7]
def baseStart_1268592 : Nat := 118140960795 + 1268592 * 2 ^ 59
def prefixEnd_1268592 : Nat := 4983230072969 + 3 ^ 40 * 1268592 * 2
def baseEnd_1268592 : Nat := 96503325992386053580127

theorem tailTrace_1268592 : CollatzResearch.WordTrace tailWord_1268592 prefixEnd_1268592 96503325992386053580127 := by
  unfold tailWord_1268592
  simp only [CollatzResearch.WordTrace]
  refine ⟨23134675710057658554832015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30846234280076878073109353 23134675710057658554832015)
  ·
    refine ⟨34702013565086487832248023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23134675710057658554832015 34702013565086487832248023)
    ·
      refine ⟨52053020347629731748372035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34702013565086487832248023 52053020347629731748372035)
      ·
        refine ⟨78079530521444597622558053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52053020347629731748372035 78079530521444597622558053)
        ·
          refine ⟨14639911972770862054229635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78079530521444597622558053 14639911972770862054229635)
          ·
            refine ⟨21959867959156293081344453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14639911972770862054229635 21959867959156293081344453)
            ·
              refine ⟨4117475242341804952752085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21959867959156293081344453 4117475242341804952752085)
              ·
                refine ⟨96503325992386053580127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4117475242341804952752085 96503325992386053580127)
                ·
                  rfl

theorem cell21_1268592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 7].length) (baseStart_1268592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268592 prefixEnd_1268592 := by exact prefixLift 1268592
  have htrace : WordTrace (prefixWord ++ tailWord_1268592) baseStart_1268592 baseEnd_1268592 := by
    simpa [prefixWord, tailWord_1268592, baseEnd_1268592] using wordTrace_append hprefix tailTrace_1268592
  have hstable : (prefixWord ++ tailWord_1268592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268592).length < 2 ^ (prefixWord ++ tailWord_1268592).sum := by decide
  have hdescent : baseEnd_1268592 < baseStart_1268592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268744 : List Nat := [2, 1, 3, 2, 1, 3, 1, 8]
def baseStart_1268744 : Nat := 118140960795 + 1268744 * 2 ^ 59
def prefixEnd_1268744 : Nat := 4983230072969 + 3 ^ 40 * 1268744 * 2
def baseEnd_1268744 : Nat := 96514888816013224735579

theorem tailTrace_1268744 : CollatzResearch.WordTrace tailWord_1268744 prefixEnd_1268744 96514888816013224735579 := by
  unfold tailWord_1268744
  simp only [CollatzResearch.WordTrace]
  refine ⟨23137447657782323534598643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30849930210376431379464857 23137447657782323534598643)
  ·
    refine ⟨34706171486673485301897965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23137447657782323534598643 34706171486673485301897965)
    ·
      refine ⟨13014814307502556988211737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34706171486673485301897965 13014814307502556988211737)
      ·
        refine ⟨9761110730626917741158803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13014814307502556988211737 9761110730626917741158803)
        ·
          refine ⟨14641666095940376611738205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9761110730626917741158803 14641666095940376611738205)
          ·
            refine ⟨5490624785977641229401827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14641666095940376611738205 5490624785977641229401827)
            ·
              refine ⟨8235937178966461844102741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5490624785977641229401827 8235937178966461844102741)
              ·
                refine ⟨96514888816013224735579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8235937178966461844102741 96514888816013224735579)
                ·
                  rfl

theorem cell21_1268744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 8].length) (baseStart_1268744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268744 prefixEnd_1268744 := by exact prefixLift 1268744
  have htrace : WordTrace (prefixWord ++ tailWord_1268744) baseStart_1268744 baseEnd_1268744 := by
    simpa [prefixWord, tailWord_1268744, baseEnd_1268744] using wordTrace_append hprefix tailTrace_1268744
  have hstable : (prefixWord ++ tailWord_1268744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268744).length < 2 ^ (prefixWord ++ tailWord_1268744).sum := by decide
  have hdescent : baseEnd_1268744 < baseStart_1268744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268747 : List Nat := [1, 1, 1, 1, 6, 2, 4, 1, 4]
def baseStart_1268747 : Nat := 118140960795 + 1268747 * 2 ^ 59
def prefixEnd_1268747 : Nat := 4983230072969 + 3 ^ 40 * 1268747 * 2
def baseEnd_1268747 : Nat := 289545351088912335656731

theorem tailTrace_1268747 : CollatzResearch.WordTrace tailWord_1268747 prefixEnd_1268747 289545351088912335656731 := by
  unfold tailWord_1268747
  simp only [CollatzResearch.WordTrace]
  refine ⟨46275004734553778581556495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30850003156369185721037663 46275004734553778581556495)
  ·
    refine ⟨69412507101830667872334743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46275004734553778581556495 69412507101830667872334743)
    ·
      refine ⟨104118760652746001808502115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69412507101830667872334743 104118760652746001808502115)
      ·
        refine ⟨156178140979119002712753173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104118760652746001808502115 156178140979119002712753173)
        ·
          refine ⟨7320850358396203252160305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 156178140979119002712753173 7320850358396203252160305)
          ·
            refine ⟨5490637768797152439120229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7320850358396203252160305 5490637768797152439120229)
            ·
              refine ⟨1029494581649466082335043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5490637768797152439120229 1029494581649466082335043)
              ·
                refine ⟨1544241872474199123502565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1029494581649466082335043 1544241872474199123502565)
                ·
                  refine ⟨289545351088912335656731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1544241872474199123502565 289545351088912335656731)
                  ·
                    rfl

theorem cell21_1268747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 4].length) (baseStart_1268747 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268747 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268747 prefixEnd_1268747 := by exact prefixLift 1268747
  have htrace : WordTrace (prefixWord ++ tailWord_1268747) baseStart_1268747 baseEnd_1268747 := by
    simpa [prefixWord, tailWord_1268747, baseEnd_1268747] using wordTrace_append hprefix tailTrace_1268747
  have hstable : (prefixWord ++ tailWord_1268747).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268747).length < 2 ^ (prefixWord ++ tailWord_1268747).sum := by decide
  have hdescent : baseEnd_1268747 < baseStart_1268747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268820 : List Nat := [2, 4, 1, 1, 1, 1, 2, 9]
def baseStart_1268820 : Nat := 118140960795 + 1268820 * 2 ^ 59
def prefixEnd_1268820 : Nat := 4983230072969 + 3 ^ 40 * 1268820 * 2
def baseEnd_1268820 : Nat := 96520670227826810313305

theorem tailTrace_1268820 : CollatzResearch.WordTrace tailWord_1268820 prefixEnd_1268820 96520670227826810313305 := by
  unfold tailWord_1268820
  simp only [CollatzResearch.WordTrace]
  refine ⟨23138833631644656024481957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30851778175526208032642609 23138833631644656024481957)
  ·
    refine ⟨4338531305933373004590367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23138833631644656024481957 4338531305933373004590367)
    ·
      refine ⟨6507796958900059506885551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4338531305933373004590367 6507796958900059506885551)
      ·
        refine ⟨9761695438350089260328327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6507796958900059506885551 9761695438350089260328327)
        ·
          refine ⟨14642543157525133890492491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9761695438350089260328327 14642543157525133890492491)
          ·
            refine ⟨21963814736287700835738737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14642543157525133890492491 21963814736287700835738737)
            ·
              refine ⟨16472861052215775626804053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21963814736287700835738737 16472861052215775626804053)
              ·
                refine ⟨96520670227826810313305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16472861052215775626804053 96520670227826810313305)
                ·
                  rfl

theorem cell21_1268820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 9].length) (baseStart_1268820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268820 prefixEnd_1268820 := by exact prefixLift 1268820
  have htrace : WordTrace (prefixWord ++ tailWord_1268820) baseStart_1268820 baseEnd_1268820 := by
    simpa [prefixWord, tailWord_1268820, baseEnd_1268820] using wordTrace_append hprefix tailTrace_1268820
  have hstable : (prefixWord ++ tailWord_1268820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268820).length < 2 ^ (prefixWord ++ tailWord_1268820).sum := by decide
  have hdescent : baseEnd_1268820 < baseStart_1268820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268882 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 6]
def baseStart_1268882 : Nat := 118140960795 + 1268882 * 2 ^ 59
def prefixEnd_1268882 : Nat := 4983230072969 + 3 ^ 40 * 1268882 * 2
def baseEnd_1268882 : Nat := 289576159928182100906455

theorem tailTrace_1268882 : CollatzResearch.WordTrace tailWord_1268882 prefixEnd_1268882 289576159928182100906455 := by
  unfold tailWord_1268882
  simp only [CollatzResearch.WordTrace]
  refine ⟨11569982147266174159430225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30853285726043131091813933 11569982147266174159430225)
  ·
    refine ⟨8677486610449630619572669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11569982147266174159430225 8677486610449630619572669)
    ·
      refine ⟨3254057478918611482339751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8677486610449630619572669 3254057478918611482339751)
      ·
        refine ⟨4881086218377917223509627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3254057478918611482339751 4881086218377917223509627)
        ·
          refine ⟨7321629327566875835264441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4881086218377917223509627 7321629327566875835264441)
          ·
            refine ⟨5491221995675156876448331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7321629327566875835264441 5491221995675156876448331)
            ·
              refine ⟨8236832993512735314672497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5491221995675156876448331 8236832993512735314672497)
              ·
                refine ⟨6177624745134551486004373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8236832993512735314672497 6177624745134551486004373)
                ·
                  refine ⟨289576159928182100906455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6177624745134551486004373 289576159928182100906455)
                  ·
                    rfl

theorem cell21_1268882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_1268882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268882 prefixEnd_1268882 := by exact prefixLift 1268882
  have htrace : WordTrace (prefixWord ++ tailWord_1268882) baseStart_1268882 baseEnd_1268882 := by
    simpa [prefixWord, tailWord_1268882, baseEnd_1268882] using wordTrace_append hprefix tailTrace_1268882
  have hstable : (prefixWord ++ tailWord_1268882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268882).length < 2 ^ (prefixWord ++ tailWord_1268882).sum := by decide
  have hdescent : baseEnd_1268882 < baseStart_1268882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268913 : List Nat := [1, 2, 2, 5, 1, 2, 2, 6]
def baseStart_1268913 : Nat := 118140960795 + 1268913 * 2 ^ 59
def prefixEnd_1268913 : Nat := 4983230072969 + 3 ^ 40 * 1268913 * 2
def baseEnd_1268913 : Nat := 96527744850177645296575

theorem tailTrace_1268913 : CollatzResearch.WordTrace tailWord_1268913 prefixEnd_1268913 96527744850177645296575 := by
  unfold tailWord_1268913
  simp only [CollatzResearch.WordTrace]
  refine ⟨46281059251952388932099393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30854039501301592621399595 46281059251952388932099393)
  ·
    refine ⟨34710794438964291699074545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46281059251952388932099393 34710794438964291699074545)
    ·
      refine ⟨26033095829223218774305909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34710794438964291699074545 26033095829223218774305909)
      ·
        refine ⟨2440602733989676760091179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26033095829223218774305909 2440602733989676760091179)
        ·
          refine ⟨3660904100984515140136769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2440602733989676760091179 3660904100984515140136769)
          ·
            refine ⟨2745678075738386355102577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3660904100984515140136769 2745678075738386355102577)
            ·
              refine ⟨2059258556803789766326933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2745678075738386355102577 2059258556803789766326933)
              ·
                refine ⟨96527744850177645296575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2059258556803789766326933 96527744850177645296575)
                ·
                  rfl

theorem cell21_1268913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 6].length) (baseStart_1268913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268913 prefixEnd_1268913 := by exact prefixLift 1268913
  have htrace : WordTrace (prefixWord ++ tailWord_1268913) baseStart_1268913 baseEnd_1268913 := by
    simpa [prefixWord, tailWord_1268913, baseEnd_1268913] using wordTrace_append hprefix tailTrace_1268913
  have hstable : (prefixWord ++ tailWord_1268913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268913).length < 2 ^ (prefixWord ++ tailWord_1268913).sum := by decide
  have hdescent : baseEnd_1268913 < baseStart_1268913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268961 : List Nat := [1, 2, 3, 1, 3, 2, 4, 2, 3]
def baseStart_1268961 : Nat := 118140960795 + 1268961 * 2 ^ 59
def prefixEnd_1268961 : Nat := 4983230072969 + 3 ^ 40 * 1268961 * 2
def baseEnd_1268961 : Nat := 289594188804495519089627

theorem tailTrace_1268961 : CollatzResearch.WordTrace tailWord_1268961 prefixEnd_1268961 289594188804495519089627 := by
  unfold tailWord_1268961
  simp only [CollatzResearch.WordTrace]
  refine ⟨46282809955778493129846737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30855206637185662086564491 46282809955778493129846737)
  ·
    refine ⟨34712107466833869847385053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46282809955778493129846737 34712107466833869847385053)
    ·
      refine ⟨13017040300062701192769395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34712107466833869847385053 13017040300062701192769395)
      ·
        refine ⟨19525560450094051789154093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13017040300062701192769395 19525560450094051789154093)
        ·
          refine ⟨7322085168785269420932785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19525560450094051789154093 7322085168785269420932785)
          ·
            refine ⟨5491563876588952065699589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7322085168785269420932785 5491563876588952065699589)
            ·
              refine ⟨1029668226860428512318673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5491563876588952065699589 1029668226860428512318673)
              ·
                refine ⟨772251170145321384239005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1029668226860428512318673 772251170145321384239005)
                ·
                  refine ⟨289594188804495519089627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 772251170145321384239005 289594188804495519089627)
                  ·
                    rfl

theorem cell21_1268961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 3].length) (baseStart_1268961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268961 prefixEnd_1268961 := by exact prefixLift 1268961
  have htrace : WordTrace (prefixWord ++ tailWord_1268961) baseStart_1268961 baseEnd_1268961 := by
    simpa [prefixWord, tailWord_1268961, baseEnd_1268961] using wordTrace_append hprefix tailTrace_1268961
  have hstable : (prefixWord ++ tailWord_1268961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268961).length < 2 ^ (prefixWord ++ tailWord_1268961).sum := by decide
  have hdescent : baseEnd_1268961 < baseStart_1268961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268972 : List Nat := [2, 2, 1, 1, 2, 4, 3, 6]
def baseStart_1268972 : Nat := 118140960795 + 1268972 * 2 ^ 59
def prefixEnd_1268972 : Nat := 4983230072969 + 3 ^ 40 * 1268972 * 2
def baseEnd_1268972 : Nat := 96532233051453981468757

theorem tailTrace_1268972 : CollatzResearch.WordTrace tailWord_1268972 prefixEnd_1268972 96532233051453981468757 := by
  unfold tailWord_1268972
  simp only [CollatzResearch.WordTrace]
  refine ⟨23141605579369321004248585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30855474105825761338998113 23141605579369321004248585)
  ·
    refine ⟨17356204184526990753186439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23141605579369321004248585 17356204184526990753186439)
    ·
      refine ⟨26034306276790486129779659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17356204184526990753186439 26034306276790486129779659)
      ·
        refine ⟨39051459415185729194669489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26034306276790486129779659 39051459415185729194669489)
        ·
          refine ⟨29288594561389296896002117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39051459415185729194669489 29288594561389296896002117)
          ·
            refine ⟨5491611480260493168000397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29288594561389296896002117 5491611480260493168000397)
            ·
              refine ⟨2059354305097684938000149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5491611480260493168000397 2059354305097684938000149)
              ·
                refine ⟨96532233051453981468757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2059354305097684938000149 96532233051453981468757)
                ·
                  rfl

theorem cell21_1268972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 6].length) (baseStart_1268972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1268972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1268972 prefixEnd_1268972 := by exact prefixLift 1268972
  have htrace : WordTrace (prefixWord ++ tailWord_1268972) baseStart_1268972 baseEnd_1268972 := by
    simpa [prefixWord, tailWord_1268972, baseEnd_1268972] using wordTrace_append hprefix tailTrace_1268972
  have hstable : (prefixWord ++ tailWord_1268972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268972).length < 2 ^ (prefixWord ++ tailWord_1268972).sum := by decide
  have hdescent : baseEnd_1268972 < baseStart_1268972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269020 : List Nat := [2, 2, 3, 1, 1, 1, 4, 4, 3]
def baseStart_1269020 : Nat := 118140960795 + 1269020 * 2 ^ 59
def prefixEnd_1269020 : Nat := 4983230072969 + 3 ^ 40 * 1269020 * 2
def baseEnd_1269020 : Nat := 289607653408324527606173

theorem tailTrace_1269020 : CollatzResearch.WordTrace tailWord_1269020 prefixEnd_1269020 289607653408324527606173 := by
  unfold tailWord_1269020
  simp only [CollatzResearch.WordTrace]
  refine ⟨23142480931282373103122257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30856641241709830804163009 23142480931282373103122257)
  ·
    refine ⟨17356860698461779827341693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23142480931282373103122257 17356860698461779827341693)
    ·
      refine ⟨6508822761923167435253135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17356860698461779827341693 6508822761923167435253135)
      ·
        refine ⟨9763234142884751152879703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6508822761923167435253135 9763234142884751152879703)
        ·
          refine ⟨14644851214327126729319555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9763234142884751152879703 14644851214327126729319555)
          ·
            refine ⟨21967276821490690093979333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14644851214327126729319555 21967276821490690093979333)
            ·
              refine ⟨4118864404029504392621125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21967276821490690093979333 4118864404029504392621125)
              ·
                refine ⟨772287075755532073616461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4118864404029504392621125 772287075755532073616461)
                ·
                  refine ⟨289607653408324527606173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 772287075755532073616461 289607653408324527606173)
                  ·
                    rfl

theorem cell21_1269020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 3].length) (baseStart_1269020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1269020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1269020 prefixEnd_1269020 := by exact prefixLift 1269020
  have htrace : WordTrace (prefixWord ++ tailWord_1269020) baseStart_1269020 baseEnd_1269020 := by
    simpa [prefixWord, tailWord_1269020, baseEnd_1269020] using wordTrace_append hprefix tailTrace_1269020
  have hstable : (prefixWord ++ tailWord_1269020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269020).length < 2 ^ (prefixWord ++ tailWord_1269020).sum := by decide
  have hdescent : baseEnd_1269020 < baseStart_1269020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269079 : List Nat := [1, 1, 3, 2, 3, 2, 3, 1, 5]
def baseStart_1269079 : Nat := 118140960795 + 1269079 * 2 ^ 59
def prefixEnd_1269079 : Nat := 4983230072969 + 3 ^ 40 * 1269079 * 2
def baseEnd_1269079 : Nat := 289621118012153536122719

theorem tailTrace_1269079 : CollatzResearch.WordTrace tailWord_1269079 prefixEnd_1269079 289621118012153536122719 := by
  unfold tailWord_1269079
  simp only [CollatzResearch.WordTrace]
  refine ⟨46287113769350999282642291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30858075846233999521761527 46287113769350999282642291)
  ·
    refine ⟨69430670654026498923963437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46287113769350999282642291 69430670654026498923963437)
    ·
      refine ⟨26036501495259937096486289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69430670654026498923963437 26036501495259937096486289)
      ·
        refine ⟨19527376121444952822364717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26036501495259937096486289 19527376121444952822364717)
        ·
          refine ⟨7322766045541857308386769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19527376121444952822364717 7322766045541857308386769)
          ·
            refine ⟨5492074534156392981290077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7322766045541857308386769 5492074534156392981290077)
            ·
              refine ⟨2059527950308647367983779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5492074534156392981290077 2059527950308647367983779)
              ·
                refine ⟨3089291925462971051975669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2059527950308647367983779 3089291925462971051975669)
                ·
                  refine ⟨289621118012153536122719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3089291925462971051975669 289621118012153536122719)
                  ·
                    rfl

theorem cell21_1269079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 5].length) (baseStart_1269079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1269079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1269079 prefixEnd_1269079 := by exact prefixLift 1269079
  have htrace : WordTrace (prefixWord ++ tailWord_1269079) baseStart_1269079 baseEnd_1269079 := by
    simpa [prefixWord, tailWord_1269079, baseEnd_1269079] using wordTrace_append hprefix tailTrace_1269079
  have hstable : (prefixWord ++ tailWord_1269079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269079).length < 2 ^ (prefixWord ++ tailWord_1269079).sum := by decide
  have hdescent : baseEnd_1269079 < baseStart_1269079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269085 : List Nat := [1, 4, 5, 1, 1, 1, 1, 3, 4]
def baseStart_1269085 : Nat := 118140960795 + 1269085 * 2 ^ 59
def prefixEnd_1269085 : Nat := 4983230072969 + 3 ^ 40 * 1269085 * 2
def baseEnd_1269085 : Nat := 289622487293898859022707

theorem tailTrace_1269085 : CollatzResearch.WordTrace tailWord_1269085 prefixEnd_1269085 289622487293898859022707 := by
  unfold tailWord_1269085
  simp only [CollatzResearch.WordTrace]
  refine ⟨46287332607329262307360709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30858221738219508204907139 46287332607329262307360709)
  ·
    refine ⟨8678874863874236682630133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46287332607329262307360709 8678874863874236682630133)
    ·
      refine ⟨813644518488209688996575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8678874863874236682630133 813644518488209688996575)
      ·
        refine ⟨1220466777732314533494863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 813644518488209688996575 1220466777732314533494863)
        ·
          refine ⟨1830700166598471800242295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1220466777732314533494863 1830700166598471800242295)
          ·
            refine ⟨2746050249897707700363443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1830700166598471800242295 2746050249897707700363443)
            ·
              refine ⟨4119075374846561550545165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2746050249897707700363443 4119075374846561550545165)
              ·
                refine ⟨1544653265567460581454437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4119075374846561550545165 1544653265567460581454437)
                ·
                  refine ⟨289622487293898859022707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1544653265567460581454437 289622487293898859022707)
                  ·
                    rfl

theorem cell21_1269085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_1269085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1269085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1269085 prefixEnd_1269085 := by exact prefixLift 1269085
  have htrace : WordTrace (prefixWord ++ tailWord_1269085) baseStart_1269085 baseEnd_1269085 := by
    simpa [prefixWord, tailWord_1269085, baseEnd_1269085] using wordTrace_append hprefix tailTrace_1269085
  have hstable : (prefixWord ++ tailWord_1269085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269085).length < 2 ^ (prefixWord ++ tailWord_1269085).sum := by decide
  have hdescent : baseEnd_1269085 < baseStart_1269085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269169 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 6]
def baseStart_1269169 : Nat := 118140960795 + 1269169 * 2 ^ 59
def prefixEnd_1269169 : Nat := 4983230072969 + 3 ^ 40 * 1269169 * 2
def baseEnd_1269169 : Nat := 289641657238333379622535

theorem tailTrace_1269169 : CollatzResearch.WordTrace tailWord_1269169 prefixEnd_1269169 289641657238333379622535 := by
  unfold tailWord_1269169
  simp only [CollatzResearch.WordTrace]
  refine ⟨46290396339024944653418561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30860264226016629768945707 46290396339024944653418561)
  ·
    refine ⟨34717797254268708490063921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46290396339024944653418561 34717797254268708490063921)
    ·
      refine ⟨26038347940701531367547941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34717797254268708490063921 26038347940701531367547941)
      ·
        refine ⟨4882190238881537131415239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26038347940701531367547941 4882190238881537131415239)
        ·
          refine ⟨7323285358322305697122859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4882190238881537131415239 7323285358322305697122859)
          ·
            refine ⟨10984928037483458545684289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7323285358322305697122859 10984928037483458545684289)
            ·
              refine ⟨8238696028112593909263217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10984928037483458545684289 8238696028112593909263217)
              ·
                refine ⟨6179022021084445431947413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8238696028112593909263217 6179022021084445431947413)
                ·
                  refine ⟨289641657238333379622535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6179022021084445431947413 289641657238333379622535)
                  ·
                    rfl

theorem cell21_1269169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_1269169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1269169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1269169 prefixEnd_1269169 := by exact prefixLift 1269169
  have htrace : WordTrace (prefixWord ++ tailWord_1269169) baseStart_1269169 baseEnd_1269169 := by
    simpa [prefixWord, tailWord_1269169, baseEnd_1269169] using wordTrace_append hprefix tailTrace_1269169
  have hstable : (prefixWord ++ tailWord_1269169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269169).length < 2 ^ (prefixWord ++ tailWord_1269169).sum := by decide
  have hdescent : baseEnd_1269169 < baseStart_1269169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269217 : List Nat := [1, 2, 3, 1, 2, 5, 2, 5]
def baseStart_1269217 : Nat := 118140960795 + 1269217 * 2 ^ 59
def prefixEnd_1269217 : Nat := 4983230072969 + 3 ^ 40 * 1269217 * 2
def baseEnd_1269217 : Nat := 96550870497431987607479

theorem tailTrace_1269217 : CollatzResearch.WordTrace tailWord_1269217 prefixEnd_1269217 96550870497431987607479 := by
  unfold tailWord_1269217
  simp only [CollatzResearch.WordTrace]
  refine ⟨46292147042851048851165905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30861431361900699234110603 46292147042851048851165905)
  ·
    refine ⟨34719110282138286638374429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46292147042851048851165905 34719110282138286638374429)
    ·
      refine ⟨13019666355801857489390411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34719110282138286638374429 13019666355801857489390411)
      ·
        refine ⟨19529499533702786234085617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13019666355801857489390411 19529499533702786234085617)
        ·
          refine ⟨14647124650277089675564213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19529499533702786234085617 14647124650277089675564213)
          ·
            refine ⟨1373167935963477157084145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14647124650277089675564213 1373167935963477157084145)
            ·
              refine ⟨1029875951972607867813109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1373167935963477157084145 1029875951972607867813109)
              ·
                refine ⟨96550870497431987607479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1029875951972607867813109 96550870497431987607479)
                ·
                  rfl

theorem cell21_1269217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 5].length) (baseStart_1269217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1269217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1269217 prefixEnd_1269217 := by exact prefixLift 1269217
  have htrace : WordTrace (prefixWord ++ tailWord_1269217) baseStart_1269217 baseEnd_1269217 := by
    simpa [prefixWord, tailWord_1269217, baseEnd_1269217] using wordTrace_append hprefix tailTrace_1269217
  have hstable : (prefixWord ++ tailWord_1269217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269217).length < 2 ^ (prefixWord ++ tailWord_1269217).sum := by decide
  have hdescent : baseEnd_1269217 < baseStart_1269217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269245 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 6]
def baseStart_1269245 : Nat := 118140960795 + 1269245 * 2 ^ 59
def prefixEnd_1269245 : Nat := 4983230072969 + 3 ^ 40 * 1269245 * 2
def baseEnd_1269245 : Nat := 289659001473774136355713

theorem tailTrace_1269245 : CollatzResearch.WordTrace tailWord_1269245 prefixEnd_1269245 289659001473774136355713 := by
  unfold tailWord_1269245
  simp only [CollatzResearch.WordTrace]
  refine ⟨46293168286749609633185189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30862112191166406422123459 46293168286749609633185189)
  ·
    refine ⟨8679969053765551806222223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46293168286749609633185189 8679969053765551806222223)
    ·
      refine ⟨13019953580648327709333335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8679969053765551806222223 13019953580648327709333335)
      ·
        refine ⟨19529930370972491564000003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13019953580648327709333335 19529930370972491564000003)
        ·
          refine ⟨29294895556458737346000005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19529930370972491564000003 29294895556458737346000005)
          ·
            refine ⟨5492792916836013252375001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29294895556458737346000005 5492792916836013252375001)
            ·
              refine ⟨4119594687627009939281251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5492792916836013252375001 4119594687627009939281251)
              ·
                refine ⟨6179392031440514908921877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4119594687627009939281251 6179392031440514908921877)
                ·
                  refine ⟨289659001473774136355713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6179392031440514908921877 289659001473774136355713)
                  ·
                    rfl

theorem cell21_1269245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_1269245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1269245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1269245 prefixEnd_1269245 := by exact prefixLift 1269245
  have htrace : WordTrace (prefixWord ++ tailWord_1269245) baseStart_1269245 baseEnd_1269245 := by
    simpa [prefixWord, tailWord_1269245, baseEnd_1269245] using wordTrace_append hprefix tailTrace_1269245
  have hstable : (prefixWord ++ tailWord_1269245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269245).length < 2 ^ (prefixWord ++ tailWord_1269245).sum := by decide
  have hdescent : baseEnd_1269245 < baseStart_1269245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269352 : List Nat := [2, 1, 4, 3, 1, 2, 8]
def baseStart_1269352 : Nat := 118140960795 + 1269352 * 2 ^ 59
def prefixEnd_1269352 : Nat := 4983230072969 + 3 ^ 40 * 1269352 * 2
def baseEnd_1269352 : Nat := 32187046703507303119129

theorem tailTrace_1269352 : CollatzResearch.WordTrace tailWord_1269352 prefixEnd_1269352 32187046703507303119129 := by
  unfold tailWord_1269352
  simp only [CollatzResearch.WordTrace]
  refine ⟨23148535448680983453665155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30864713931574644604886873 23148535448680983453665155)
  ·
    refine ⟨34722803173021475180497733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23148535448680983453665155 34722803173021475180497733)
    ·
      refine ⟨6510525594941526596343325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34722803173021475180497733 6510525594941526596343325)
      ·
        refine ⟨2441447098103072473628747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6510525594941526596343325 2441447098103072473628747)
        ·
          refine ⟨3662170647154608710443121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2441447098103072473628747 3662170647154608710443121)
          ·
            refine ⟨2746627985365956532832341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3662170647154608710443121 2746627985365956532832341)
            ·
              refine ⟨32187046703507303119129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2746627985365956532832341 32187046703507303119129)
              ·
                rfl

theorem cell21_1269352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 8].length) (baseStart_1269352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1269352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1269352 prefixEnd_1269352 := by exact prefixLift 1269352
  have htrace : WordTrace (prefixWord ++ tailWord_1269352) baseStart_1269352 baseEnd_1269352 := by
    simpa [prefixWord, tailWord_1269352, baseEnd_1269352] using wordTrace_append hprefix tailTrace_1269352
  have hstable : (prefixWord ++ tailWord_1269352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269352).length < 2 ^ (prefixWord ++ tailWord_1269352).sum := by decide
  have hdescent : baseEnd_1269352 < baseStart_1269352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269400 : List Nat := [2, 1, 2, 4, 1, 2, 3, 3, 3]
def baseStart_1269400 : Nat := 118140960795 + 1269400 * 2 ^ 59
def prefixEnd_1269400 : Nat := 4983230072969 + 3 ^ 40 * 1269400 * 2
def baseEnd_1269400 : Nat := 289694374585528311272063

theorem tailTrace_1269400 : CollatzResearch.WordTrace tailWord_1269400 prefixEnd_1269400 289694374585528311272063 := by
  unfold tailWord_1269400
  simp only [CollatzResearch.WordTrace]
  refine ⟨23149410800594035552538827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30865881067458714070051769 23149410800594035552538827)
  ·
    refine ⟨34724116200891053328808241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23149410800594035552538827 34724116200891053328808241)
    ·
      refine ⟨26043087150668289996606181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34724116200891053328808241 26043087150668289996606181)
      ·
        refine ⟨4883078840750304374363659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26043087150668289996606181 4883078840750304374363659)
        ·
          refine ⟨7324618261125456561545489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4883078840750304374363659 7324618261125456561545489)
          ·
            refine ⟨5493463695844092421159117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7324618261125456561545489 5493463695844092421159117)
            ·
              refine ⟨2060048885941534657934669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5493463695844092421159117 2060048885941534657934669)
              ·
                refine ⟨772518332228075496725501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2060048885941534657934669 772518332228075496725501)
                ·
                  refine ⟨289694374585528311272063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 772518332228075496725501 289694374585528311272063)
                  ·
                    rfl

theorem cell21_1269400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 3].length) (baseStart_1269400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1269400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1269400 prefixEnd_1269400 := by exact prefixLift 1269400
  have htrace : WordTrace (prefixWord ++ tailWord_1269400) baseStart_1269400 baseEnd_1269400 := by
    simpa [prefixWord, tailWord_1269400, baseEnd_1269400] using wordTrace_append hprefix tailTrace_1269400
  have hstable : (prefixWord ++ tailWord_1269400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269400).length < 2 ^ (prefixWord ++ tailWord_1269400).sum := by decide
  have hdescent : baseEnd_1269400 < baseStart_1269400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269431 : List Nat := [1, 1, 3, 1, 5, 3, 2, 1, 4]
def baseStart_1269431 : Nat := 118140960795 + 1269431 * 2 ^ 59
def prefixEnd_1269431 : Nat := 4983230072969 + 3 ^ 40 * 1269431 * 2
def baseEnd_1269431 : Nat := 289701449207879146255333

theorem tailTrace_1269431 : CollatzResearch.WordTrace tailWord_1269431 prefixEnd_1269431 289701449207879146255333 := by
  unfold tailWord_1269431
  simp only [CollatzResearch.WordTrace]
  refine ⟨46299952264075763399456147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30866634842717175599637431 46299952264075763399456147)
  ·
    refine ⟨69449928396113645099184221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46299952264075763399456147 69449928396113645099184221)
    ·
      refine ⟨26043723148542616912194083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69449928396113645099184221 26043723148542616912194083)
      ·
        refine ⟨39065584722813925368291125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26043723148542616912194083 39065584722813925368291125)
        ·
          refine ⟨3662398567763805503277293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39065584722813925368291125 3662398567763805503277293)
          ·
            refine ⟨1373399462911427063728985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3662398567763805503277293 1373399462911427063728985)
            ·
              refine ⟨1030049597183570297796739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1373399462911427063728985 1030049597183570297796739)
              ·
                refine ⟨1545074395775355446695109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1030049597183570297796739 1545074395775355446695109)
                ·
                  refine ⟨289701449207879146255333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1545074395775355446695109 289701449207879146255333)
                  ·
                    rfl

theorem cell21_1269431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 4].length) (baseStart_1269431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1269431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1269431 prefixEnd_1269431 := by exact prefixLift 1269431
  have htrace : WordTrace (prefixWord ++ tailWord_1269431) baseStart_1269431 baseEnd_1269431 := by
    simpa [prefixWord, tailWord_1269431, baseEnd_1269431] using wordTrace_append hprefix tailTrace_1269431
  have hstable : (prefixWord ++ tailWord_1269431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269431).length < 2 ^ (prefixWord ++ tailWord_1269431).sum := by decide
  have hdescent : baseEnd_1269431 < baseStart_1269431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269456 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 6]
def baseStart_1269456 : Nat := 118140960795 + 1269456 * 2 ^ 59
def prefixEnd_1269456 : Nat := 4983230072969 + 3 ^ 40 * 1269456 * 2
def baseEnd_1269456 : Nat := 289707154548484658338615

theorem tailTrace_1269456 : CollatzResearch.WordTrace tailWord_1269456 prefixEnd_1269456 289707154548484658338615 := by
  unfold tailWord_1269456
  simp only [CollatzResearch.WordTrace]
  refine ⟨23150432044492596334558111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30867242725990128446077481 23150432044492596334558111)
  ·
    refine ⟨34725648066738894501837167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23150432044492596334558111 34725648066738894501837167)
    ·
      refine ⟨52088472100108341752755751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34725648066738894501837167 52088472100108341752755751)
      ·
        refine ⟨78132708150162512629133627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52088472100108341752755751 78132708150162512629133627)
        ·
          refine ⟨117199062225243768943700441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78132708150162512629133627 117199062225243768943700441)
          ·
            refine ⟨87899296668932826707775331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117199062225243768943700441 87899296668932826707775331)
            ·
              refine ⟨131848945003399240061662997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87899296668932826707775331 131848945003399240061662997)
              ·
                refine ⟨6180419297034339377890453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 131848945003399240061662997 6180419297034339377890453)
                ·
                  refine ⟨289707154548484658338615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6180419297034339377890453 289707154548484658338615)
                  ·
                    rfl

theorem cell21_1269456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_1269456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1269456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1269456 prefixEnd_1269456 := by exact prefixLift 1269456
  have htrace : WordTrace (prefixWord ++ tailWord_1269456) baseStart_1269456 baseEnd_1269456 := by
    simpa [prefixWord, tailWord_1269456, baseEnd_1269456] using wordTrace_append hprefix tailTrace_1269456
  have hstable : (prefixWord ++ tailWord_1269456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269456).length < 2 ^ (prefixWord ++ tailWord_1269456).sum := by decide
  have hdescent : baseEnd_1269456 < baseStart_1269456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269462 : List Nat := [5, 2, 1, 3, 2, 8]
def baseStart_1269462 : Nat := 118140960795 + 1269462 * 2 ^ 59
def prefixEnd_1269462 : Nat := 4983230072969 + 3 ^ 40 * 1269462 * 2
def baseEnd_1269462 : Nat := 10729945327045554860689

theorem tailTrace_1269462 : CollatzResearch.WordTrace tailWord_1269462 prefixEnd_1269462 10729945327045554860689 := by
  unfold tailWord_1269462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2893817682935215980864665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30867388617975637129223093 2893817682935215980864665)
  ·
    refine ⟨2170363262201411985648499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2893817682935215980864665 2170363262201411985648499)
    ·
      refine ⟨3255544893302117978472749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2170363262201411985648499 3255544893302117978472749)
      ·
        refine ⟨1220829334988294241927281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3255544893302117978472749 1220829334988294241927281)
        ·
          refine ⟨915622001241220681445461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1220829334988294241927281 915622001241220681445461)
          ·
            refine ⟨10729945327045554860689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 915622001241220681445461 10729945327045554860689)
            ·
              rfl

theorem cell21_1269462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 8].length) (baseStart_1269462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1269462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1269462 prefixEnd_1269462 := by exact prefixLift 1269462
  have htrace : WordTrace (prefixWord ++ tailWord_1269462) baseStart_1269462 baseEnd_1269462 := by
    simpa [prefixWord, tailWord_1269462, baseEnd_1269462] using wordTrace_append hprefix tailTrace_1269462
  have hstable : (prefixWord ++ tailWord_1269462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269462).length < 2 ^ (prefixWord ++ tailWord_1269462).sum := by decide
  have hdescent : baseEnd_1269462 < baseStart_1269462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269524 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 6]
def baseStart_1269524 : Nat := 118140960795 + 1269524 * 2 ^ 59
def prefixEnd_1269524 : Nat := 4983230072969 + 3 ^ 40 * 1269524 * 2
def baseEnd_1269524 : Nat := 289722673074931651205143

theorem tailTrace_1269524 : CollatzResearch.WordTrace tailWord_1269524 prefixEnd_1269524 289722673074931651205143 := by
  unfold tailWord_1269524
  simp only [CollatzResearch.WordTrace]
  refine ⟨23151672126369420141295813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30868896168492560188394417 23151672126369420141295813)
  ·
    refine ⟨4340938523694266276492965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23151672126369420141295813 4340938523694266276492965)
    ·
      refine ⟨813925973192674926842431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4340938523694266276492965 813925973192674926842431)
      ·
        refine ⟨1220888959789012390263647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 813925973192674926842431 1220888959789012390263647)
        ·
          refine ⟨1831333439683518585395471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1220888959789012390263647 1831333439683518585395471)
          ·
            refine ⟨2747000159525277878093207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1831333439683518585395471 2747000159525277878093207)
            ·
              refine ⟨4120500239287916817139811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2747000159525277878093207 4120500239287916817139811)
              ·
                refine ⟨6180750358931875225709717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4120500239287916817139811 6180750358931875225709717)
                ·
                  refine ⟨289722673074931651205143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6180750358931875225709717 289722673074931651205143)
                  ·
                    rfl

theorem cell21_1269524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_1269524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1269524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1269524 prefixEnd_1269524 := by exact prefixLift 1269524
  have htrace : WordTrace (prefixWord ++ tailWord_1269524) baseStart_1269524 baseEnd_1269524 := by
    simpa [prefixWord, tailWord_1269524, baseEnd_1269524] using wordTrace_append hprefix tailTrace_1269524
  have hstable : (prefixWord ++ tailWord_1269524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269524).length < 2 ^ (prefixWord ++ tailWord_1269524).sum := by decide
  have hdescent : baseEnd_1269524 < baseStart_1269524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269535 : List Nat := [1, 1, 2, 4, 2, 1, 1, 6, 3]
def baseStart_1269535 : Nat := 118140960795 + 1269535 * 2 ^ 59
def prefixEnd_1269535 : Nat := 4983230072969 + 3 ^ 40 * 1269535 * 2
def baseEnd_1269535 : Nat := 289725183424798076521787

theorem tailTrace_1269535 : CollatzResearch.WordTrace tailWord_1269535 prefixEnd_1269535 289725183424798076521787 := by
  unfold tailWord_1269535
  simp only [CollatzResearch.WordTrace]
  refine ⟨46303745455698989161242059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30869163637132659440828039 46303745455698989161242059)
  ·
    refine ⟨69455618183548483741863089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46303745455698989161242059 69455618183548483741863089)
    ·
      refine ⟨52091713637661362806397317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69455618183548483741863089 52091713637661362806397317)
      ·
        refine ⟨9767196307061505526199497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52091713637661362806397317 9767196307061505526199497)
        ·
          refine ⟨7325397230296129144649623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9767196307061505526199497 7325397230296129144649623)
          ·
            refine ⟨10988095845444193716974435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7325397230296129144649623 10988095845444193716974435)
            ·
              refine ⟨16482143768166290575461653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10988095845444193716974435 16482143768166290575461653)
              ·
                refine ⟨772600489132794870724765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16482143768166290575461653 772600489132794870724765)
                ·
                  refine ⟨289725183424798076521787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 772600489132794870724765 289725183424798076521787)
                  ·
                    rfl

theorem cell21_1269535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 3].length) (baseStart_1269535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1269535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1269535 prefixEnd_1269535 := by exact prefixLift 1269535
  have htrace : WordTrace (prefixWord ++ tailWord_1269535) baseStart_1269535 baseEnd_1269535 := by
    simpa [prefixWord, tailWord_1269535, baseEnd_1269535] using wordTrace_append hprefix tailTrace_1269535
  have hstable : (prefixWord ++ tailWord_1269535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269535).length < 2 ^ (prefixWord ++ tailWord_1269535).sum := by decide
  have hdescent : baseEnd_1269535 < baseStart_1269535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269580 : List Nat := [2, 2, 1, 3, 4, 2, 7]
def baseStart_1269580 : Nat := 118140960795 + 1269580 * 2 ^ 59
def prefixEnd_1269580 : Nat := 4983230072969 + 3 ^ 40 * 1269580 * 2
def baseEnd_1269580 : Nat := 32192828115320888696855

theorem tailTrace_1269580 : CollatzResearch.WordTrace tailWord_1269580 prefixEnd_1269580 32192828115320888696855 := by
  unfold tailWord_1269580
  simp only [CollatzResearch.WordTrace]
  refine ⟨23152693370267980923315097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30870257827023974564420129 23152693370267980923315097)
  ·
    refine ⟨17364520027700985692486323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23152693370267980923315097 17364520027700985692486323)
    ·
      refine ⟨26046780041551478538729485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17364520027700985692486323 26046780041551478538729485)
      ·
        refine ⟨9767542515581804452023557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26046780041551478538729485 9767542515581804452023557)
        ·
          refine ⟨1831414221671588334754417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9767542515581804452023557 1831414221671588334754417)
          ·
            refine ⟨1373560666253691251065813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1831414221671588334754417 1373560666253691251065813)
            ·
              refine ⟨32192828115320888696855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1373560666253691251065813 32192828115320888696855)
              ·
                rfl

theorem cell21_1269580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 7].length) (baseStart_1269580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1269580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1269580 prefixEnd_1269580 := by exact prefixLift 1269580
  have htrace : WordTrace (prefixWord ++ tailWord_1269580) baseStart_1269580 baseEnd_1269580 := by
    simpa [prefixWord, tailWord_1269580, baseEnd_1269580] using wordTrace_append hprefix tailTrace_1269580
  have hstable : (prefixWord ++ tailWord_1269580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269580).length < 2 ^ (prefixWord ++ tailWord_1269580).sum := by decide
  have hdescent : baseEnd_1269580 < baseStart_1269580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269639 : List Nat := [1, 1, 4, 2, 4, 9]
def baseStart_1269639 : Nat := 118140960795 + 1269639 * 2 ^ 59
def prefixEnd_1269639 : Nat := 4983230072969 + 3 ^ 40 * 1269639 * 2
def baseEnd_1269639 : Nat := 10731441394137666918083

theorem tailTrace_1269639 : CollatzResearch.WordTrace tailWord_1269639 prefixEnd_1269639 10731441394137666918083 := by
  unfold tailWord_1269639
  simp only [CollatzResearch.WordTrace]
  refine ⟨46307538647322214923027971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30871692431548143282018647 46307538647322214923027971)
  ·
    refine ⟨69461307970983322384541957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46307538647322214923027971 69461307970983322384541957)
    ·
      refine ⟨13023995244559372947101617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69461307970983322384541957 13023995244559372947101617)
      ·
        refine ⟨9767996433419529710326213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13023995244559372947101617 9767996433419529710326213)
        ·
          refine ⟨1831499331266161820686165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9767996433419529710326213 1831499331266161820686165)
          ·
            refine ⟨10731441394137666918083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1831499331266161820686165 10731441394137666918083)
            ·
              rfl

theorem cell21_1269639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 9].length) (baseStart_1269639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1269639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1269639 prefixEnd_1269639 := by exact prefixLift 1269639
  have htrace : WordTrace (prefixWord ++ tailWord_1269639) baseStart_1269639 baseEnd_1269639 := by
    simpa [prefixWord, tailWord_1269639, baseEnd_1269639] using wordTrace_append hprefix tailTrace_1269639
  have hstable : (prefixWord ++ tailWord_1269639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269639).length < 2 ^ (prefixWord ++ tailWord_1269639).sum := by decide
  have hdescent : baseEnd_1269639 < baseStart_1269639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269724 : List Nat := [2, 2, 6, 1, 2, 1, 2, 5]
def baseStart_1269724 : Nat := 118140960795 + 1269724 * 2 ^ 59
def prefixEnd_1269724 : Nat := 4983230072969 + 3 ^ 40 * 1269724 * 2
def baseEnd_1269724 : Nat := 96589438599925249290467

theorem tailTrace_1269724 : CollatzResearch.WordTrace tailWord_1269724 prefixEnd_1269724 96589438599925249290467 := by
  unfold tailWord_1269724
  simp only [CollatzResearch.WordTrace]
  refine ⟨23155319426007137219936113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30873759234676182959914817 23155319426007137219936113)
  ·
    refine ⟨17366489569505352914952085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23155319426007137219936113 17366489569505352914952085)
    ·
      refine ⟨814054198570563417888379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17366489569505352914952085 814054198570563417888379)
      ·
        refine ⟨1221081297855845126832569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 814054198570563417888379 1221081297855845126832569)
        ·
          refine ⟨915810973391883845124427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1221081297855845126832569 915810973391883845124427)
          ·
            refine ⟨1373716460087825767686641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915810973391883845124427 1373716460087825767686641)
            ·
              refine ⟨1030287345065869325764981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1373716460087825767686641 1030287345065869325764981)
              ·
                refine ⟨96589438599925249290467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1030287345065869325764981 96589438599925249290467)
                ·
                  rfl

theorem cell21_1269724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 5].length) (baseStart_1269724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1269724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1269724 prefixEnd_1269724 := by exact prefixLift 1269724
  have htrace : WordTrace (prefixWord ++ tailWord_1269724) baseStart_1269724 baseEnd_1269724 := by
    simpa [prefixWord, tailWord_1269724, baseEnd_1269724] using wordTrace_append hprefix tailTrace_1269724
  have hstable : (prefixWord ++ tailWord_1269724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269724).length < 2 ^ (prefixWord ++ tailWord_1269724).sum := by decide
  have hdescent : baseEnd_1269724 < baseStart_1269724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269898 : List Nat := [3, 1, 2, 3, 1, 2, 2, 2, 5]
def baseStart_1269898 : Nat := 118140960795 + 1269898 * 2 ^ 59
def prefixEnd_1269898 : Nat := 4983230072969 + 3 ^ 40 * 1269898 * 2
def baseEnd_1269898 : Nat := 289808024970390111971045

theorem tailTrace_1269898 : CollatzResearch.WordTrace tailWord_1269898 prefixEnd_1269898 289808024970390111971045 := by
  unfold tailWord_1269898
  simp only [CollatzResearch.WordTrace]
  refine ⟨11579246288345975539176587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30877990102255934771137565 11579246288345975539176587)
  ·
    refine ⟨17368869432518963308764881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11579246288345975539176587 17368869432518963308764881)
    ·
      refine ⟨13026652074389222481573661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17368869432518963308764881 13026652074389222481573661)
      ·
        refine ⟨4884994527895958430590123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13026652074389222481573661 4884994527895958430590123)
        ·
          refine ⟨7327491791843937645885185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4884994527895958430590123 7327491791843937645885185)
          ·
            refine ⟨5495618843882953234413889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7327491791843937645885185 5495618843882953234413889)
            ·
              refine ⟨4121714132912214925810417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5495618843882953234413889 4121714132912214925810417)
              ·
                refine ⟨3091285599684161194357813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4121714132912214925810417 3091285599684161194357813)
                ·
                  refine ⟨289808024970390111971045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3091285599684161194357813 289808024970390111971045)
                  ·
                    rfl

theorem cell21_1269898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_1269898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1269898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1269898 prefixEnd_1269898 := by exact prefixLift 1269898
  have htrace : WordTrace (prefixWord ++ tailWord_1269898) baseStart_1269898 baseEnd_1269898 := by
    simpa [prefixWord, tailWord_1269898, baseEnd_1269898] using wordTrace_append hprefix tailTrace_1269898
  have hstable : (prefixWord ++ tailWord_1269898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269898).length < 2 ^ (prefixWord ++ tailWord_1269898).sum := by decide
  have hdescent : baseEnd_1269898 < baseStart_1269898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269943 : List Nat := [1, 1, 3, 1, 4, 3, 2, 6]
def baseStart_1269943 : Nat := 118140960795 + 1269943 * 2 ^ 59
def prefixEnd_1269943 : Nat := 4983230072969 + 3 ^ 40 * 1269943 * 2
def baseEnd_1269943 : Nat := 96606098194493344573651

theorem tailTrace_1269943 : CollatzResearch.WordTrace tailWord_1269943 prefixEnd_1269943 96606098194493344573651 := by
  unfold tailWord_1269943
  simp only [CollatzResearch.WordTrace]
  refine ⟨46318626438220874842094483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30879084292147249894729655 46318626438220874842094483)
  ·
    refine ⟨69477939657331312263141725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46318626438220874842094483 69477939657331312263141725)
    ·
      refine ⟨26054227371499242098678147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69477939657331312263141725 26054227371499242098678147)
      ·
        refine ⟨39081341057248863148017221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26054227371499242098678147 39081341057248863148017221)
        ·
          refine ⟨7327751448234161840253229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39081341057248863148017221 7327751448234161840253229)
          ·
            refine ⟨2747906793087810690094961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7327751448234161840253229 2747906793087810690094961)
            ·
              refine ⟨2060930094815858017571221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2747906793087810690094961 2060930094815858017571221)
              ·
                refine ⟨96606098194493344573651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2060930094815858017571221 96606098194493344573651)
                ·
                  rfl

theorem cell21_1269943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 6].length) (baseStart_1269943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1269943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1269943 prefixEnd_1269943 := by exact prefixLift 1269943
  have htrace : WordTrace (prefixWord ++ tailWord_1269943) baseStart_1269943 baseEnd_1269943 := by
    simpa [prefixWord, tailWord_1269943, baseEnd_1269943] using wordTrace_append hprefix tailTrace_1269943
  have hstable : (prefixWord ++ tailWord_1269943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269943).length < 2 ^ (prefixWord ++ tailWord_1269943).sum := by decide
  have hdescent : baseEnd_1269943 < baseStart_1269943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269957 : List Nat := [1, 3, 1, 1, 1, 1, 4, 4, 5]
def baseStart_1269957 : Nat := 118140960795 + 1269957 * 2 ^ 59
def prefixEnd_1269957 : Nat := 4983230072969 + 3 ^ 40 * 1269957 * 2
def baseEnd_1269957 : Nat := 289821489574219120487591

theorem tailTrace_1269957 : CollatzResearch.WordTrace tailWord_1269957 prefixEnd_1269957 289821489574219120487591 := by
  unfold tailWord_1269957
  simp only [CollatzResearch.WordTrace]
  refine ⟨46319137060170155233104125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30879424706780103488736083 46319137060170155233104125)
  ·
    refine ⟨17369676397563808212414047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46319137060170155233104125 17369676397563808212414047)
    ·
      refine ⟨26054514596345712318621071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17369676397563808212414047 26054514596345712318621071)
      ·
        refine ⟨39081771894518568477931607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26054514596345712318621071 39081771894518568477931607)
        ·
          refine ⟨58622657841777852716897411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39081771894518568477931607 58622657841777852716897411)
          ·
            refine ⟨87933986762666779075346117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58622657841777852716897411 87933986762666779075346117)
            ·
              refine ⟨16487622518000021076627397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87933986762666779075346117 16487622518000021076627397)
              ·
                refine ⟨3091429222125003951867637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16487622518000021076627397 3091429222125003951867637)
                ·
                  refine ⟨289821489574219120487591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3091429222125003951867637 289821489574219120487591)
                  ·
                    rfl

theorem cell21_1269957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_1269957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1269957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1269957 prefixEnd_1269957 := by exact prefixLift 1269957
  have htrace : WordTrace (prefixWord ++ tailWord_1269957) baseStart_1269957 baseEnd_1269957 := by
    simpa [prefixWord, tailWord_1269957, baseEnd_1269957] using wordTrace_append hprefix tailTrace_1269957
  have hstable : (prefixWord ++ tailWord_1269957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269957).length < 2 ^ (prefixWord ++ tailWord_1269957).sum := by decide
  have hdescent : baseEnd_1269957 < baseStart_1269957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270019 : List Nat := [1, 1, 1, 3, 2, 3, 5, 5]
def baseStart_1270019 : Nat := 118140960795 + 1270019 * 2 ^ 59
def prefixEnd_1270019 : Nat := 4983230072969 + 3 ^ 40 * 1270019 * 2
def baseEnd_1270019 : Nat := 96611879606306930151377

theorem tailTrace_1270019 : CollatzResearch.WordTrace tailWord_1270019 prefixEnd_1270019 96611879606306930151377 := by
  unfold tailWord_1270019
  simp only [CollatzResearch.WordTrace]
  refine ⟨46321398385945539821861111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30880932257297026547907407 46321398385945539821861111)
  ·
    refine ⟨69482097578918309732791667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46321398385945539821861111 69482097578918309732791667)
    ·
      refine ⟨104223146368377464599187501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69482097578918309732791667 104223146368377464599187501)
      ·
        refine ⟨39083679888141549224695313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104223146368377464599187501 39083679888141549224695313)
        ·
          refine ⟨29312759916106161918521485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39083679888141549224695313 29312759916106161918521485)
          ·
            refine ⟨10992284968539810719445557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29312759916106161918521485 10992284968539810719445557)
            ·
              refine ⟨1030526715800607254948021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10992284968539810719445557 1030526715800607254948021)
              ·
                refine ⟨96611879606306930151377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1030526715800607254948021 96611879606306930151377)
                ·
                  rfl

theorem cell21_1270019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 5].length) (baseStart_1270019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1270019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1270019 prefixEnd_1270019 := by exact prefixLift 1270019
  have htrace : WordTrace (prefixWord ++ tailWord_1270019) baseStart_1270019 baseEnd_1270019 := by
    simpa [prefixWord, tailWord_1270019, baseEnd_1270019] using wordTrace_append hprefix tailTrace_1270019
  have hstable : (prefixWord ++ tailWord_1270019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270019).length < 2 ^ (prefixWord ++ tailWord_1270019).sum := by decide
  have hdescent : baseEnd_1270019 < baseStart_1270019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270050 : List Nat := [3, 3, 1, 1, 3, 1, 1, 3, 5]
def baseStart_1270050 : Nat := 118140960795 + 1270050 * 2 ^ 59
def prefixEnd_1270050 : Nat := 4983230072969 + 3 ^ 40 * 1270050 * 2
def baseEnd_1270050 : Nat := 289842713441271625437401

theorem tailTrace_1270050 : CollatzResearch.WordTrace tailWord_1270050 prefixEnd_1270050 289842713441271625437401 := by
  unfold tailWord_1270050
  simp only [CollatzResearch.WordTrace]
  refine ⟨11580632262208308029059901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30881686032555488077493069 11580632262208308029059901)
  ·
    refine ⟨4342737098328115510897463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11580632262208308029059901 4342737098328115510897463)
    ·
      refine ⟨6514105647492173266346195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4342737098328115510897463 6514105647492173266346195)
      ·
        refine ⟨9771158471238259899519293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6514105647492173266346195 9771158471238259899519293)
        ·
          refine ⟨3664184426714347462319735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9771158471238259899519293 3664184426714347462319735)
          ·
            refine ⟨5496276640071521193479603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3664184426714347462319735 5496276640071521193479603)
            ·
              refine ⟨8244414960107281790219405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5496276640071521193479603 8244414960107281790219405)
              ·
                refine ⟨3091655610040230671332277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8244414960107281790219405 3091655610040230671332277)
                ·
                  refine ⟨289842713441271625437401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3091655610040230671332277 289842713441271625437401)
                  ·
                    rfl

theorem cell21_1270050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_1270050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1270050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1270050 prefixEnd_1270050 := by exact prefixLift 1270050
  have htrace : WordTrace (prefixWord ++ tailWord_1270050) baseStart_1270050 baseEnd_1270050 := by
    simpa [prefixWord, tailWord_1270050, baseEnd_1270050] using wordTrace_append hprefix tailTrace_1270050
  have hstable : (prefixWord ++ tailWord_1270050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270050).length < 2 ^ (prefixWord ++ tailWord_1270050).sum := by decide
  have hdescent : baseEnd_1270050 < baseStart_1270050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270174 : List Nat := [4, 3, 1, 2, 1, 1, 2, 3, 4]
def baseStart_1270174 : Nat := 118140960795 + 1270174 * 2 ^ 59
def prefixEnd_1270174 : Nat := 4983230072969 + 3 ^ 40 * 1270174 * 2
def baseEnd_1270174 : Nat := 289871011930674965370481

theorem tailTrace_1270174 : CollatzResearch.WordTrace tailWord_1270174 prefixEnd_1270174 289871011930674965370481 := by
  unfold tailWord_1270174
  simp only [CollatzResearch.WordTrace]
  refine ⟨5790881462548000161719197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30884701133589334195835717 5790881462548000161719197)
  ·
    refine ⟨2171580548455500060644699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5790881462548000161719197 2171580548455500060644699)
    ·
      refine ⟨3257370822683250090967049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2171580548455500060644699 3257370822683250090967049)
      ·
        refine ⟨2443028117012437568225287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3257370822683250090967049 2443028117012437568225287)
        ·
          refine ⟨3664542175518656352337931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2443028117012437568225287 3664542175518656352337931)
          ·
            refine ⟨5496813263277984528506897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3664542175518656352337931 5496813263277984528506897)
            ·
              refine ⟨4122609947458488396380173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5496813263277984528506897 4122609947458488396380173)
              ·
                refine ⟨1545978730296933148642565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4122609947458488396380173 1545978730296933148642565)
                ·
                  refine ⟨289871011930674965370481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1545978730296933148642565 289871011930674965370481)
                  ·
                    rfl

theorem cell21_1270174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_1270174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1270174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1270174 prefixEnd_1270174 := by exact prefixLift 1270174
  have htrace : WordTrace (prefixWord ++ tailWord_1270174) baseStart_1270174 baseEnd_1270174 := by
    simpa [prefixWord, tailWord_1270174, baseEnd_1270174] using wordTrace_append hprefix tailTrace_1270174
  have hstable : (prefixWord ++ tailWord_1270174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270174).length < 2 ^ (prefixWord ++ tailWord_1270174).sum := by decide
  have hdescent : baseEnd_1270174 < baseStart_1270174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270216 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 6]
def baseStart_1270216 : Nat := 118140960795 + 1270216 * 2 ^ 59
def prefixEnd_1270216 : Nat := 4983230072969 + 3 ^ 40 * 1270216 * 2
def baseEnd_1270216 : Nat := 289880596902892225670395

theorem tailTrace_1270216 : CollatzResearch.WordTrace tailWord_1270216 prefixEnd_1270216 289880596902892225670395 := by
  unfold tailWord_1270216
  simp only [CollatzResearch.WordTrace]
  refine ⟨23164291783115921233391251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30885722377487894977855001 23164291783115921233391251)
  ·
    refine ⟨34746437674673881850086877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23164291783115921233391251 34746437674673881850086877)
    ·
      refine ⟨13029914128002705693782579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34746437674673881850086877 13029914128002705693782579)
      ·
        refine ⟨19544871192004058540673869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13029914128002705693782579 19544871192004058540673869)
        ·
          refine ⟨7329326697001521952752701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19544871192004058540673869 7329326697001521952752701)
          ·
            refine ⟨2748497511375570732282263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7329326697001521952752701 2748497511375570732282263)
            ·
              refine ⟨4122746267063356098423395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2748497511375570732282263 4122746267063356098423395)
              ·
                refine ⟨6184119400595034147635093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4122746267063356098423395 6184119400595034147635093)
                ·
                  refine ⟨289880596902892225670395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6184119400595034147635093 289880596902892225670395)
                  ·
                    rfl

theorem cell21_1270216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 6].length) (baseStart_1270216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1270216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1270216 prefixEnd_1270216 := by exact prefixLift 1270216
  have htrace : WordTrace (prefixWord ++ tailWord_1270216) baseStart_1270216 baseEnd_1270216 := by
    simpa [prefixWord, tailWord_1270216, baseEnd_1270216] using wordTrace_append hprefix tailTrace_1270216
  have hstable : (prefixWord ++ tailWord_1270216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270216).length < 2 ^ (prefixWord ++ tailWord_1270216).sum := by decide
  have hdescent : baseEnd_1270216 < baseStart_1270216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270233 : List Nat := [1, 2, 1, 2, 4, 1, 5, 1, 4]
def baseStart_1270233 : Nat := 118140960795 + 1270233 * 2 ^ 59
def prefixEnd_1270233 : Nat := 4983230072969 + 3 ^ 40 * 1270233 * 2
def baseEnd_1270233 : Nat := 289884476534503973887027

theorem tailTrace_1270233 : CollatzResearch.WordTrace tailWord_1270233 prefixEnd_1270233 289884476534503973887027 := by
  unfold tailWord_1270233
  simp only [CollatzResearch.WordTrace]
  refine ⟨46329203607170254370151353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30886135738113502913434235 46329203607170254370151353)
  ·
    refine ⟨34746902705377690777613515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46329203607170254370151353 34746902705377690777613515)
    ·
      refine ⟨52120354058066536166420273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34746902705377690777613515 52120354058066536166420273)
      ·
        refine ⟨39090265543549902124815205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52120354058066536166420273 39090265543549902124815205)
        ·
          refine ⟨7329424789415606648402851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39090265543549902124815205 7329424789415606648402851)
          ·
            refine ⟨10994137184123409972604277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7329424789415606648402851 10994137184123409972604277)
            ·
              refine ⟨1030700361011569684931651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10994137184123409972604277 1030700361011569684931651)
              ·
                refine ⟨1546050541517354527397477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1030700361011569684931651 1546050541517354527397477)
                ·
                  refine ⟨289884476534503973887027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1546050541517354527397477 289884476534503973887027)
                  ·
                    rfl

theorem cell21_1270233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 4].length) (baseStart_1270233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1270233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1270233 prefixEnd_1270233 := by exact prefixLift 1270233
  have htrace : WordTrace (prefixWord ++ tailWord_1270233) baseStart_1270233 baseEnd_1270233 := by
    simpa [prefixWord, tailWord_1270233, baseEnd_1270233] using wordTrace_append hprefix tailTrace_1270233
  have hstable : (prefixWord ++ tailWord_1270233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270233).length < 2 ^ (prefixWord ++ tailWord_1270233).sum := by decide
  have hdescent : baseEnd_1270233 < baseStart_1270233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270275 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 6]
def baseStart_1270275 : Nat := 118140960795 + 1270275 * 2 ^ 59
def prefixEnd_1270275 : Nat := 4983230072969 + 3 ^ 40 * 1270275 * 2
def baseEnd_1270275 : Nat := 289894061506721234186941

theorem tailTrace_1270275 : CollatzResearch.WordTrace tailWord_1270275 prefixEnd_1270275 289894061506721234186941 := by
  unfold tailWord_1270275
  simp only [CollatzResearch.WordTrace]
  refine ⟨46330735473018095543180279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30887156982012063695453519 46330735473018095543180279)
  ·
    refine ⟨69496103209527143314770419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46330735473018095543180279 69496103209527143314770419)
    ·
      refine ⟨104244154814290714972155629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69496103209527143314770419 104244154814290714972155629)
      ·
        refine ⟨39091558055359018114558361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104244154814290714972155629 39091558055359018114558361)
        ·
          refine ⟨29318668541519263585918771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39091558055359018114558361 29318668541519263585918771)
          ·
            refine ⟨43978002812278895378878157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29318668541519263585918771 43978002812278895378878157)
            ·
              refine ⟨16491751054604585767079309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43978002812278895378878157 16491751054604585767079309)
              ·
                refine ⟨6184406645476719662654741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16491751054604585767079309 6184406645476719662654741)
                ·
                  refine ⟨289894061506721234186941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6184406645476719662654741 289894061506721234186941)
                  ·
                    rfl

theorem cell21_1270275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 6].length) (baseStart_1270275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1270275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1270275 prefixEnd_1270275 := by exact prefixLift 1270275
  have htrace : WordTrace (prefixWord ++ tailWord_1270275) baseStart_1270275 baseEnd_1270275 := by
    simpa [prefixWord, tailWord_1270275, baseEnd_1270275] using wordTrace_append hprefix tailTrace_1270275
  have hstable : (prefixWord ++ tailWord_1270275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270275).length < 2 ^ (prefixWord ++ tailWord_1270275).sum := by decide
  have hdescent : baseEnd_1270275 < baseStart_1270275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270326 : List Nat := [5, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_1270326 : Nat := 118140960795 + 1270326 * 2 ^ 59
def prefixEnd_1270326 : Nat := 4983230072969 + 3 ^ 40 * 1270326 * 2
def baseEnd_1270326 : Nat := 289905700401556478836837

theorem tailTrace_1270326 : CollatzResearch.WordTrace tailWord_1270326 prefixEnd_1270326 289905700401556478836837 := by
  unfold tailWord_1270326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2895787224739583203330427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30888397063888887502191221 2895787224739583203330427)
  ·
    refine ⟨4343680837109374804995641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2895787224739583203330427 4343680837109374804995641)
    ·
      refine ⟨3257760627832031103746731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4343680837109374804995641 3257760627832031103746731)
      ·
        refine ⟨4886640941748046655620097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3257760627832031103746731 4886640941748046655620097)
        ·
          refine ⟨3664980706311034991715073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4886640941748046655620097 3664980706311034991715073)
          ·
            refine ⟨2748735529733276243786305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3664980706311034991715073 2748735529733276243786305)
            ·
              refine ⟨2061551647299957182839729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2748735529733276243786305 2061551647299957182839729)
              ·
                refine ⟨1546163735474967887129797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2061551647299957182839729 1546163735474967887129797)
                ·
                  refine ⟨289905700401556478836837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1546163735474967887129797 289905700401556478836837)
                  ·
                    rfl

theorem cell21_1270326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_1270326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1270326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1270326 prefixEnd_1270326 := by exact prefixLift 1270326
  have htrace : WordTrace (prefixWord ++ tailWord_1270326) baseStart_1270326 baseEnd_1270326 := by
    simpa [prefixWord, tailWord_1270326, baseEnd_1270326] using wordTrace_append hprefix tailTrace_1270326
  have hstable : (prefixWord ++ tailWord_1270326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270326).length < 2 ^ (prefixWord ++ tailWord_1270326).sum := by decide
  have hdescent : baseEnd_1270326 < baseStart_1270326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270447 : List Nat := [1, 1, 2, 1, 2, 6, 3, 2, 3]
def baseStart_1270447 : Nat := 118140960795 + 1270447 * 2 ^ 59
def prefixEnd_1270447 : Nat := 4983230072969 + 3 ^ 40 * 1270447 * 2
def baseEnd_1270447 : Nat := 289933314250087157319923

theorem tailTrace_1270447 : CollatzResearch.WordTrace tailWord_1270447 prefixEnd_1270447 289933314250087157319923 := by
  unfold tailWord_1270447
  simp only [CollatzResearch.WordTrace]
  refine ⟨46337008828394968918441595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30891339218929979278961063 46337008828394968918441595)
  ·
    refine ⟨69505513242592453377662393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46337008828394968918441595 69505513242592453377662393)
    ·
      refine ⟨52129134931944340033246795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69505513242592453377662393 52129134931944340033246795)
      ·
        refine ⟨78193702397916510049870193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52129134931944340033246795 78193702397916510049870193)
        ·
          refine ⟨58645276798437382537402645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78193702397916510049870193 58645276798437382537402645)
          ·
            refine ⟨2748997349926752306440749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58645276798437382537402645 2748997349926752306440749)
            ·
              refine ⟨1030874006222532114915281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2748997349926752306440749 1030874006222532114915281)
              ·
                refine ⟨773155504666899086186461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1030874006222532114915281 773155504666899086186461)
                ·
                  refine ⟨289933314250087157319923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 773155504666899086186461 289933314250087157319923)
                  ·
                    rfl

theorem cell21_1270447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 3].length) (baseStart_1270447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1270447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1270447 prefixEnd_1270447 := by exact prefixLift 1270447
  have htrace : WordTrace (prefixWord ++ tailWord_1270447) baseStart_1270447 baseEnd_1270447 := by
    simpa [prefixWord, tailWord_1270447, baseEnd_1270447] using wordTrace_append hprefix tailTrace_1270447
  have hstable : (prefixWord ++ tailWord_1270447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270447).length < 2 ^ (prefixWord ++ tailWord_1270447).sum := by decide
  have hdescent : baseEnd_1270447 < baseStart_1270447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270458 : List Nat := [3, 1, 1, 1, 2, 3, 4, 6]
def baseStart_1270458 : Nat := 118140960795 + 1270458 * 2 ^ 59
def prefixEnd_1270458 : Nat := 4983230072969 + 3 ^ 40 * 1270458 * 2
def baseEnd_1270458 : Nat := 96645274866651194212189

theorem tailTrace_1270458 : CollatzResearch.WordTrace tailWord_1270458 prefixEnd_1270458 96645274866651194212189 := by
  unfold tailWord_1270458
  simp only [CollatzResearch.WordTrace]
  refine ⟨11584352507838779449273007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30891606687570078531394685 11584352507838779449273007)
  ·
    refine ⟨17376528761758169173909511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11584352507838779449273007 17376528761758169173909511)
    ·
      refine ⟨26064793142637253760864267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17376528761758169173909511 26064793142637253760864267)
      ·
        refine ⟨39097189713955880641296401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26064793142637253760864267 39097189713955880641296401)
        ·
          refine ⟨29322892285466910480972301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39097189713955880641296401 29322892285466910480972301)
          ·
            refine ⟨10996084607050091430364613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29322892285466910480972301 10996084607050091430364613)
            ·
              refine ⟨2061765863821892143193365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10996084607050091430364613 2061765863821892143193365)
              ·
                refine ⟨96645274866651194212189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2061765863821892143193365 96645274866651194212189)
                ·
                  rfl

theorem cell21_1270458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_1270458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1270458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1270458 prefixEnd_1270458 := by exact prefixLift 1270458
  have htrace : WordTrace (prefixWord ++ tailWord_1270458) baseStart_1270458 baseEnd_1270458 := by
    simpa [prefixWord, tailWord_1270458, baseEnd_1270458] using wordTrace_append hprefix tailTrace_1270458
  have hstable : (prefixWord ++ tailWord_1270458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270458).length < 2 ^ (prefixWord ++ tailWord_1270458).sum := by decide
  have hdescent : baseEnd_1270458 < baseStart_1270458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270461 : List Nat := [1, 4, 1, 2, 1, 3, 4, 1, 4]
def baseStart_1270461 : Nat := 118140960795 + 1270461 * 2 ^ 59
def prefixEnd_1270461 : Nat := 4983230072969 + 3 ^ 40 * 1270461 * 2
def baseEnd_1270461 : Nat := 289936509240826244086561

theorem tailTrace_1270461 : CollatzResearch.WordTrace tailWord_1270461 prefixEnd_1270461 289936509240826244086561 := by
  unfold tailWord_1270461
  simp only [CollatzResearch.WordTrace]
  refine ⟨46337519450344249309451237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30891679633562832872967491 46337519450344249309451237)
  ·
    refine ⟨8688284896939546745522107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46337519450344249309451237 8688284896939546745522107)
    ·
      refine ⟨13032427345409320118283161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8688284896939546745522107 13032427345409320118283161)
      ·
        refine ⟨9774320509056990088712371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13032427345409320118283161 9774320509056990088712371)
        ·
          refine ⟨14661480763585485133068557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9774320509056990088712371 14661480763585485133068557)
          ·
            refine ⟨5498055286344556924900709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14661480763585485133068557 5498055286344556924900709)
            ·
              refine ⟨1030885366189604423418883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5498055286344556924900709 1030885366189604423418883)
              ·
                refine ⟨1546328049284406635128325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1030885366189604423418883 1546328049284406635128325)
                ·
                  refine ⟨289936509240826244086561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1546328049284406635128325 289936509240826244086561)
                  ·
                    rfl

theorem cell21_1270461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_1270461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1270461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1270461 prefixEnd_1270461 := by exact prefixLift 1270461
  have htrace : WordTrace (prefixWord ++ tailWord_1270461) baseStart_1270461 baseEnd_1270461 := by
    simpa [prefixWord, tailWord_1270461, baseEnd_1270461] using wordTrace_append hprefix tailTrace_1270461
  have hstable : (prefixWord ++ tailWord_1270461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270461).length < 2 ^ (prefixWord ++ tailWord_1270461).sum := by decide
  have hdescent : baseEnd_1270461 < baseStart_1270461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270565 : List Nat := [1, 3, 1, 2, 3, 1, 4, 1, 5]
def baseStart_1270565 : Nat := 118140960795 + 1270565 * 2 ^ 59
def prefixEnd_1270565 : Nat := 4983230072969 + 3 ^ 40 * 1270565 * 2
def baseEnd_1270565 : Nat := 289960243457745174353015

theorem tailTrace_1270565 : CollatzResearch.WordTrace tailWord_1270565 prefixEnd_1270565 289960243457745174353015 := by
  unfold tailWord_1270565
  simp only [CollatzResearch.WordTrace]
  refine ⟨46341312641967475071237149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30894208427978316714158099 46341312641967475071237149)
  ·
    refine ⟨17377992240737803151713931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46341312641967475071237149 17377992240737803151713931)
    ·
      refine ⟨26066988361106704727570897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17377992240737803151713931 26066988361106704727570897)
      ·
        refine ⟨19550241270830028545678173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26066988361106704727570897 19550241270830028545678173)
        ·
          refine ⟨7331340476561260704629315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19550241270830028545678173 7331340476561260704629315)
          ·
            refine ⟨10997010714841891056943973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7331340476561260704629315 10997010714841891056943973)
            ·
              refine ⟨2061939509032854573176995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10997010714841891056943973 2061939509032854573176995)
              ·
                refine ⟨3092909263549281859765493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2061939509032854573176995 3092909263549281859765493)
                ·
                  refine ⟨289960243457745174353015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3092909263549281859765493 289960243457745174353015)
                  ·
                    rfl

theorem cell21_1270565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_1270565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1270565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1270565 prefixEnd_1270565 := by exact prefixLift 1270565
  have htrace : WordTrace (prefixWord ++ tailWord_1270565) baseStart_1270565 baseEnd_1270565 := by
    simpa [prefixWord, tailWord_1270565, baseEnd_1270565] using wordTrace_append hprefix tailTrace_1270565
  have hstable : (prefixWord ++ tailWord_1270565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270565).length < 2 ^ (prefixWord ++ tailWord_1270565).sum := by decide
  have hdescent : baseEnd_1270565 < baseStart_1270565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270700 : List Nat := [2, 2, 1, 1, 1, 1, 2, 6, 5]
def baseStart_1270700 : Nat := 118140960795 + 1270700 * 2 ^ 59
def prefixEnd_1270700 : Nat := 4983230072969 + 3 ^ 40 * 1270700 * 2
def baseEnd_1270700 : Nat := 289991052297014939602739

theorem tailTrace_1270700 : CollatzResearch.WordTrace tailWord_1270700 prefixEnd_1270700 289991052297014939602739 := by
  unfold tailWord_1270700
  simp only [CollatzResearch.WordTrace]
  refine ⟨23173118248239196563700777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30897490997652262084934369 23173118248239196563700777)
  ·
    refine ⟨17379838686179397422775583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23173118248239196563700777 17379838686179397422775583)
    ·
      refine ⟨26069758029269096134163375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17379838686179397422775583 26069758029269096134163375)
      ·
        refine ⟨39104637043903644201245063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26069758029269096134163375 39104637043903644201245063)
        ·
          refine ⟨58656955565855466301867595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39104637043903644201245063 58656955565855466301867595)
          ·
            refine ⟨87985433348783199452801393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58656955565855466301867595 87985433348783199452801393)
            ·
              refine ⟨65989075011587399589601045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87985433348783199452801393 65989075011587399589601045)
              ·
                refine ⟨3093237891168159355762549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65989075011587399589601045 3093237891168159355762549)
                ·
                  refine ⟨289991052297014939602739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3093237891168159355762549 289991052297014939602739)
                  ·
                    rfl

theorem cell21_1270700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_1270700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1270700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1270700 prefixEnd_1270700 := by exact prefixLift 1270700
  have htrace : WordTrace (prefixWord ++ tailWord_1270700) baseStart_1270700 baseEnd_1270700 := by
    simpa [prefixWord, tailWord_1270700, baseEnd_1270700] using wordTrace_append hprefix tailTrace_1270700
  have hstable : (prefixWord ++ tailWord_1270700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270700).length < 2 ^ (prefixWord ++ tailWord_1270700).sum := by decide
  have hdescent : baseEnd_1270700 < baseStart_1270700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270731 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 6]
def baseStart_1270731 : Nat := 118140960795 + 1270731 * 2 ^ 59
def prefixEnd_1270731 : Nat := 4983230072969 + 3 ^ 40 * 1270731 * 2
def baseEnd_1270731 : Nat := 289998126919365774586009

theorem tailTrace_1270731 : CollatzResearch.WordTrace tailWord_1270731 prefixEnd_1270731 289998126919365774586009 := by
  unfold tailWord_1270731
  simp only [CollatzResearch.WordTrace]
  refine ⟨46347367159366085421780047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30898244772910723614520031 46347367159366085421780047)
  ·
    refine ⟨69521050739049128132670071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46347367159366085421780047 69521050739049128132670071)
    ·
      refine ⟨104281576108573692199005107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69521050739049128132670071 104281576108573692199005107)
      ·
        refine ⟨156422364162860538298507661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104281576108573692199005107 156422364162860538298507661)
        ·
          refine ⟨58658386561072701861940373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156422364162860538298507661 58658386561072701861940373)
          ·
            refine ⟨2749611870050282899778455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58658386561072701861940373 2749611870050282899778455)
            ·
              refine ⟨4124417805075424349667683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2749611870050282899778455 4124417805075424349667683)
              ·
                refine ⟨6186626707613136524501525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4124417805075424349667683 6186626707613136524501525)
                ·
                  refine ⟨289998126919365774586009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6186626707613136524501525 289998126919365774586009)
                  ·
                    rfl

theorem cell21_1270731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 6].length) (baseStart_1270731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1270731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1270731 prefixEnd_1270731 := by exact prefixLift 1270731
  have htrace : WordTrace (prefixWord ++ tailWord_1270731) baseStart_1270731 baseEnd_1270731 := by
    simpa [prefixWord, tailWord_1270731, baseEnd_1270731] using wordTrace_append hprefix tailTrace_1270731
  have hstable : (prefixWord ++ tailWord_1270731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270731).length < 2 ^ (prefixWord ++ tailWord_1270731).sum := by decide
  have hdescent : baseEnd_1270731 < baseStart_1270731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270734 : List Nat := [4, 1, 1, 1, 2, 3, 2, 4, 3]
def baseStart_1270734 : Nat := 118140960795 + 1270734 * 2 ^ 59
def prefixEnd_1270734 : Nat := 4983230072969 + 3 ^ 40 * 1270734 * 2
def baseEnd_1270734 : Nat := 289998811560238436036003

theorem tailTrace_1270734 : CollatzResearch.WordTrace tailWord_1270734 prefixEnd_1270734 289998811560238436036003 := by
  unfold tailWord_1270734
  simp only [CollatzResearch.WordTrace]
  refine ⟨5793434572294402116767407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30898317718903477956092837 5793434572294402116767407)
  ·
    refine ⟨8690151858441603175151111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5793434572294402116767407 8690151858441603175151111)
    ·
      refine ⟨13035227787662404762726667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8690151858441603175151111 13035227787662404762726667)
      ·
        refine ⟨19552841681493607144090001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13035227787662404762726667 19552841681493607144090001)
        ·
          refine ⟨14664631261120205358067501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19552841681493607144090001 14664631261120205358067501)
          ·
            refine ⟨5499236722920077009275313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14664631261120205358067501 5499236722920077009275313)
            ·
              refine ⟨4124427542190057756956485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5499236722920077009275313 4124427542190057756956485)
              ·
                refine ⟨773330164160635829429341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4124427542190057756956485 773330164160635829429341)
                ·
                  refine ⟨289998811560238436036003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 773330164160635829429341 289998811560238436036003)
                  ·
                    rfl

theorem cell21_1270734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_1270734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1270734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1270734 prefixEnd_1270734 := by exact prefixLift 1270734
  have htrace : WordTrace (prefixWord ++ tailWord_1270734) baseStart_1270734 baseEnd_1270734 := by
    simpa [prefixWord, tailWord_1270734, baseEnd_1270734] using wordTrace_append hprefix tailTrace_1270734
  have hstable : (prefixWord ++ tailWord_1270734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270734).length < 2 ^ (prefixWord ++ tailWord_1270734).sum := by decide
  have hdescent : baseEnd_1270734 < baseStart_1270734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270762 : List Nat := [3, 1, 3, 1, 2, 3, 1, 7]
def baseStart_1270762 : Nat := 118140960795 + 1270762 * 2 ^ 59
def prefixEnd_1270762 : Nat := 4983230072969 + 3 ^ 40 * 1270762 * 2
def baseEnd_1270762 : Nat := 96668400513905536523093

theorem tailTrace_1270762 : CollatzResearch.WordTrace tailWord_1270762 prefixEnd_1270762 96668400513905536523093 := by
  unfold tailWord_1270762
  simp only [CollatzResearch.WordTrace]
  refine ⟨11587124455563444429039635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30898998548169185144105693 11587124455563444429039635)
  ·
    refine ⟨17380686683345166643559453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11587124455563444429039635 17380686683345166643559453)
    ·
      refine ⟨6517757506254437491334795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17380686683345166643559453 6517757506254437491334795)
      ·
        refine ⟨9776636259381656237002193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6517757506254437491334795 9776636259381656237002193)
        ·
          refine ⟨7332477194536242177751645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9776636259381656237002193 7332477194536242177751645)
          ·
            refine ⟨2749678947951090816656867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7332477194536242177751645 2749678947951090816656867)
            ·
              refine ⟨4124518421926636224985301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2749678947951090816656867 4124518421926636224985301)
              ·
                refine ⟨96668400513905536523093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4124518421926636224985301 96668400513905536523093)
                ·
                  rfl

theorem cell21_1270762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_1270762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1270762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1270762 prefixEnd_1270762 := by exact prefixLift 1270762
  have htrace : WordTrace (prefixWord ++ tailWord_1270762) baseStart_1270762 baseEnd_1270762 := by
    simpa [prefixWord, tailWord_1270762, baseEnd_1270762] using wordTrace_append hprefix tailTrace_1270762
  have hstable : (prefixWord ++ tailWord_1270762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270762).length < 2 ^ (prefixWord ++ tailWord_1270762).sum := by decide
  have hdescent : baseEnd_1270762 < baseStart_1270762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270793 : List Nat := [1, 2, 1, 1, 3, 1, 1, 8, 3]
def baseStart_1270793 : Nat := 118140960795 + 1270793 * 2 ^ 59
def prefixEnd_1270793 : Nat := 4983230072969 + 3 ^ 40 * 1270793 * 2
def baseEnd_1270793 : Nat := 290012276164067444552549

theorem tailTrace_1270793 : CollatzResearch.WordTrace tailWord_1270793 prefixEnd_1270793 290012276164067444552549 := by
  unfold tailWord_1270793
  simp only [CollatzResearch.WordTrace]
  refine ⟨46349628485141470010537033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30899752323427646673691355 46349628485141470010537033)
  ·
    refine ⟨34762221363856102507902775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46349628485141470010537033 34762221363856102507902775)
    ·
      refine ⟨52143332045784153761854163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34762221363856102507902775 52143332045784153761854163)
      ·
        refine ⟨78214998068676230642781245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52143332045784153761854163 78214998068676230642781245)
        ·
          refine ⟨29330624275753586491042967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78214998068676230642781245 29330624275753586491042967)
          ·
            refine ⟨43995936413630379736564451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29330624275753586491042967 43995936413630379736564451)
            ·
              refine ⟨65993904620445569604846677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43995936413630379736564451 65993904620445569604846677)
              ·
                refine ⟨773366069770846518806797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 65993904620445569604846677 773366069770846518806797)
                ·
                  refine ⟨290012276164067444552549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 773366069770846518806797 290012276164067444552549)
                  ·
                    rfl

theorem cell21_1270793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 3].length) (baseStart_1270793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1270793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1270793 prefixEnd_1270793 := by exact prefixLift 1270793
  have htrace : WordTrace (prefixWord ++ tailWord_1270793) baseStart_1270793 baseEnd_1270793 := by
    simpa [prefixWord, tailWord_1270793, baseEnd_1270793] using wordTrace_append hprefix tailTrace_1270793
  have hstable : (prefixWord ++ tailWord_1270793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270793).length < 2 ^ (prefixWord ++ tailWord_1270793).sum := by decide
  have hdescent : baseEnd_1270793 < baseStart_1270793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270821 : List Nat := [1, 3, 1, 2, 2, 2, 1, 9]
def baseStart_1270821 : Nat := 118140960795 + 1270821 * 2 ^ 59
def prefixEnd_1270821 : Nat := 4983230072969 + 3 ^ 40 * 1270821 * 2
def baseEnd_1270821 : Nat := 96672888715181872695275

theorem tailTrace_1270821 : CollatzResearch.WordTrace tailWord_1270821 prefixEnd_1270821 96672888715181872695275 := by
  unfold tailWord_1270821
  simp only [CollatzResearch.WordTrace]
  refine ⟨46350649729040030792556317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30900433152693353861704211 46350649729040030792556317)
  ·
    refine ⟨17381493648390011547208619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46350649729040030792556317 17381493648390011547208619)
    ·
      refine ⟨26072240472585017320812929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17381493648390011547208619 26072240472585017320812929)
      ·
        refine ⟨19554180354438762990609697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26072240472585017320812929 19554180354438762990609697)
        ·
          refine ⟨14665635265829072242957273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19554180354438762990609697 14665635265829072242957273)
          ·
            refine ⟨10999226449371804182217955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14665635265829072242957273 10999226449371804182217955)
            ·
              refine ⟨16498839674057706273326933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10999226449371804182217955 16498839674057706273326933)
              ·
                refine ⟨96672888715181872695275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16498839674057706273326933 96672888715181872695275)
                ·
                  rfl

theorem cell21_1270821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 9].length) (baseStart_1270821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1270821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1270821 prefixEnd_1270821 := by exact prefixLift 1270821
  have htrace : WordTrace (prefixWord ++ tailWord_1270821) baseStart_1270821 baseEnd_1270821 := by
    simpa [prefixWord, tailWord_1270821, baseEnd_1270821] using wordTrace_append hprefix tailTrace_1270821
  have hstable : (prefixWord ++ tailWord_1270821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270821).length < 2 ^ (prefixWord ++ tailWord_1270821).sum := by decide
  have hdescent : baseEnd_1270821 < baseStart_1270821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270838 : List Nat := [5, 1, 2, 1, 1, 11]
def baseStart_1270838 : Nat := 118140960795 + 1270838 * 2 ^ 59
def prefixEnd_1270838 : Nat := 4983230072969 + 3 ^ 40 * 1270838 * 2
def baseEnd_1270838 : Nat := 10741575769524346900091

theorem tailTrace_1270838 : CollatzResearch.WordTrace tailWord_1270838 prefixEnd_1270838 10741575769524346900091 := by
  unfold tailWord_1270838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2896954360623652668495323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30900846513318961797283445 2896954360623652668495323)
  ·
    refine ⟨4345431540935479002742985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2896954360623652668495323 4345431540935479002742985)
    ·
      refine ⟨3259073655701609252057239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4345431540935479002742985 3259073655701609252057239)
      ·
        refine ⟨4888610483552413878085859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3259073655701609252057239 4888610483552413878085859)
        ·
          refine ⟨7332915725328620817128789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4888610483552413878085859 7332915725328620817128789)
          ·
            refine ⟨10741575769524346900091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7332915725328620817128789 10741575769524346900091)
            ·
              rfl

theorem cell21_1270838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 11].length) (baseStart_1270838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1270838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1270838 prefixEnd_1270838 := by exact prefixLift 1270838
  have htrace : WordTrace (prefixWord ++ tailWord_1270838) baseStart_1270838 baseEnd_1270838 := by
    simpa [prefixWord, tailWord_1270838, baseEnd_1270838] using wordTrace_append hprefix tailTrace_1270838
  have hstable : (prefixWord ++ tailWord_1270838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270838).length < 2 ^ (prefixWord ++ tailWord_1270838).sum := by decide
  have hdescent : baseEnd_1270838 < baseStart_1270838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270917 : List Nat := [1, 3, 1, 1, 6, 1, 3, 1, 4]
def baseStart_1270917 : Nat := 118140960795 + 1270917 * 2 ^ 59
def prefixEnd_1270917 : Nat := 4983230072969 + 3 ^ 40 * 1270917 * 2
def baseEnd_1270917 : Nat := 290040574653470784485629

theorem tailTrace_1270917 : CollatzResearch.WordTrace tailWord_1270917 prefixEnd_1270917 290040574653470784485629 := by
  unfold tailWord_1270917
  simp only [CollatzResearch.WordTrace]
  refine ⟨46354151136692239188051005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30902767424461492792034003 46354151136692239188051005)
  ·
    refine ⟨17382806676259589695519127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46354151136692239188051005 17382806676259589695519127)
    ·
      refine ⟨26074210014389384543278691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17382806676259589695519127 26074210014389384543278691)
      ·
        refine ⟨39111315021584076814918037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26074210014389384543278691 39111315021584076814918037)
        ·
          refine ⟨1833342891636753600699283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39111315021584076814918037 1833342891636753600699283)
          ·
            refine ⟨2750014337455130401048925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1833342891636753600699283 2750014337455130401048925)
            ·
              refine ⟨1031255376545673900393347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2750014337455130401048925 1031255376545673900393347)
              ·
                refine ⟨1546883064818510850590021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1031255376545673900393347 1546883064818510850590021)
                ·
                  refine ⟨290040574653470784485629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1546883064818510850590021 290040574653470784485629)
                  ·
                    rfl

theorem cell21_1270917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_1270917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1270917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1270917 prefixEnd_1270917 := by exact prefixLift 1270917
  have htrace : WordTrace (prefixWord ++ tailWord_1270917) baseStart_1270917 baseEnd_1270917 := by
    simpa [prefixWord, tailWord_1270917, baseEnd_1270917] using wordTrace_append hprefix tailTrace_1270917
  have hstable : (prefixWord ++ tailWord_1270917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270917).length < 2 ^ (prefixWord ++ tailWord_1270917).sum := by decide
  have hdescent : baseEnd_1270917 < baseStart_1270917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270973 : List Nat := [1, 4, 1, 2, 1, 1, 3, 8]
def baseStart_1270973 : Nat := 118140960795 + 1270973 * 2 ^ 59
def prefixEnd_1270973 : Nat := 4983230072969 + 3 ^ 40 * 1270973 * 2
def baseEnd_1270973 : Nat := 96684451538809043850727

theorem tailTrace_1270973 : CollatzResearch.WordTrace tailWord_1270973 prefixEnd_1270973 96684451538809043850727 := by
  unfold tailWord_1270973
  simp only [CollatzResearch.WordTrace]
  refine ⟨46356193624489360752089573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30904129082992907168059715 46356193624489360752089573)
  ·
    refine ⟨8691786304591755141016795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46356193624489360752089573 8691786304591755141016795)
    ·
      refine ⟨13037679456887632711525193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8691786304591755141016795 13037679456887632711525193)
      ·
        refine ⟨9778259592665724533643895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13037679456887632711525193 9778259592665724533643895)
        ·
          refine ⟨14667389388998586800465843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9778259592665724533643895 14667389388998586800465843)
          ·
            refine ⟨22001084083497880200698765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14667389388998586800465843 22001084083497880200698765)
            ·
              refine ⟨8250406531311705075262037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22001084083497880200698765 8250406531311705075262037)
              ·
                refine ⟨96684451538809043850727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8250406531311705075262037 96684451538809043850727)
                ·
                  rfl

theorem cell21_1270973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 8].length) (baseStart_1270973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1270973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1270973 prefixEnd_1270973 := by exact prefixLift 1270973
  have htrace : WordTrace (prefixWord ++ tailWord_1270973) baseStart_1270973 baseEnd_1270973 := by
    simpa [prefixWord, tailWord_1270973, baseEnd_1270973] using wordTrace_append hprefix tailTrace_1270973
  have hstable : (prefixWord ++ tailWord_1270973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270973).length < 2 ^ (prefixWord ++ tailWord_1270973).sum := by decide
  have hdescent : baseEnd_1270973 < baseStart_1270973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270976 : List Nat := [2, 1, 1, 2, 6, 1, 1, 3, 4]
def baseStart_1270976 : Nat := 118140960795 + 1270976 * 2 ^ 59
def prefixEnd_1270976 : Nat := 4983230072969 + 3 ^ 40 * 1270976 * 2
def baseEnd_1270976 : Nat := 290054039257299793002175

theorem tailTrace_1270976 : CollatzResearch.WordTrace tailWord_1270976 prefixEnd_1270976 290054039257299793002175 := by
  unfold tailWord_1270976
  simp only [CollatzResearch.WordTrace]
  refine ⟨23178151521739246132224391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30904202028985661509632521 23178151521739246132224391)
  ·
    refine ⟨34767227282608869198336587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23178151521739246132224391 34767227282608869198336587)
    ·
      refine ⟨52150840923913303797504881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34767227282608869198336587 52150840923913303797504881)
      ·
        refine ⟨39113130692934977848128661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52150840923913303797504881 39113130692934977848128661)
        ·
          refine ⟨1833428001231327086631031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39113130692934977848128661 1833428001231327086631031)
          ·
            refine ⟨2750142001846990629946547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1833428001231327086631031 2750142001846990629946547)
            ·
              refine ⟨4125213002770485944919821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2750142001846990629946547 4125213002770485944919821)
              ·
                refine ⟨1546954876038932229344933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4125213002770485944919821 1546954876038932229344933)
                ·
                  refine ⟨290054039257299793002175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1546954876038932229344933 290054039257299793002175)
                  ·
                    rfl

theorem cell21_1270976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 4].length) (baseStart_1270976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1270976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1270976 prefixEnd_1270976 := by exact prefixLift 1270976
  have htrace : WordTrace (prefixWord ++ tailWord_1270976) baseStart_1270976 baseEnd_1270976 := by
    simpa [prefixWord, tailWord_1270976, baseEnd_1270976] using wordTrace_append hprefix tailTrace_1270976
  have hstable : (prefixWord ++ tailWord_1270976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270976).length < 2 ^ (prefixWord ++ tailWord_1270976).sum := by decide
  have hdescent : baseEnd_1270976 < baseStart_1270976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271069 : List Nat := [1, 4, 2, 3, 1, 3, 1, 2, 4]
def baseStart_1271069 : Nat := 118140960795 + 1271069 * 2 ^ 59
def prefixEnd_1271069 : Nat := 4983230072969 + 3 ^ 40 * 1271069 * 2
def baseEnd_1271069 : Nat := 290075263124352297951985

theorem tailTrace_1271069 : CollatzResearch.WordTrace tailWord_1271069 prefixEnd_1271069 290075263124352297951985 := by
  unfold tailWord_1271069
  simp only [CollatzResearch.WordTrace]
  refine ⟨46359695032141569147584261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30906463354761046098389507 46359695032141569147584261)
  ·
    refine ⟨8692442818526544215172049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46359695032141569147584261 8692442818526544215172049)
    ·
      refine ⟨6519332113894908161379037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8692442818526544215172049 6519332113894908161379037)
      ·
        refine ⟨2444749542710590560517139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6519332113894908161379037 2444749542710590560517139)
        ·
          refine ⟨3667124314065885840775709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2444749542710590560517139 3667124314065885840775709)
          ·
            refine ⟨1375171617774707190290891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3667124314065885840775709 1375171617774707190290891)
            ·
              refine ⟨2062757426662060785436337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1375171617774707190290891 2062757426662060785436337)
              ·
                refine ⟨1547068069996545589077253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2062757426662060785436337 1547068069996545589077253)
                ·
                  refine ⟨290075263124352297951985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1547068069996545589077253 290075263124352297951985)
                  ·
                    rfl

theorem cell21_1271069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_1271069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1271069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1271069 prefixEnd_1271069 := by exact prefixLift 1271069
  have htrace : WordTrace (prefixWord ++ tailWord_1271069) baseStart_1271069 baseEnd_1271069 := by
    simpa [prefixWord, tailWord_1271069, baseEnd_1271069] using wordTrace_append hprefix tailTrace_1271069
  have hstable : (prefixWord ++ tailWord_1271069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271069).length < 2 ^ (prefixWord ++ tailWord_1271069).sum := by decide
  have hdescent : baseEnd_1271069 < baseStart_1271069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271125 : List Nat := [1, 3, 2, 2, 3, 1, 9]
def baseStart_1271125 : Nat := 118140960795 + 1271125 * 2 ^ 59
def prefixEnd_1271125 : Nat := 4983230072969 + 3 ^ 40 * 1271125 * 2
def baseEnd_1271125 : Nat := 32232004787478738335393

theorem tailTrace_1271125 : CollatzResearch.WordTrace tailWord_1271125 prefixEnd_1271125 32232004787478738335393 := by
  unfold tailWord_1271125
  simp only [CollatzResearch.WordTrace]
  refine ⟨46361737519938690711622829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30907825013292460474415219 46361737519938690711622829)
  ·
    refine ⟨17385651569977009016858561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46361737519938690711622829 17385651569977009016858561)
    ·
      refine ⟨13039238677482756762643921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17385651569977009016858561 13039238677482756762643921)
      ·
        refine ⟨9779429008112067571982941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13039238677482756762643921 9779429008112067571982941)
        ·
          refine ⟨3667285878042025339493603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9779429008112067571982941 3667285878042025339493603)
          ·
            refine ⟨5500928817063038009240405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3667285878042025339493603 5500928817063038009240405)
            ·
              refine ⟨32232004787478738335393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5500928817063038009240405 32232004787478738335393)
              ·
                rfl

theorem cell21_1271125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 9].length) (baseStart_1271125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1271125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1271125 prefixEnd_1271125 := by exact prefixLift 1271125
  have htrace : WordTrace (prefixWord ++ tailWord_1271125) baseStart_1271125 baseEnd_1271125 := by
    simpa [prefixWord, tailWord_1271125, baseEnd_1271125] using wordTrace_append hprefix tailTrace_1271125
  have hstable : (prefixWord ++ tailWord_1271125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271125).length < 2 ^ (prefixWord ++ tailWord_1271125).sum := by decide
  have hdescent : baseEnd_1271125 < baseStart_1271125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271356 : List Nat := [2, 2, 2, 2, 4, 1, 2, 2, 4]
def baseStart_1271356 : Nat := 118140960795 + 1271356 * 2 ^ 59
def prefixEnd_1271356 : Nat := 4983230072969 + 3 ^ 40 * 1271356 * 2
def baseEnd_1271356 : Nat := 290140760434503576668065

theorem tailTrace_1271356 : CollatzResearch.WordTrace tailWord_1271356 prefixEnd_1271356 290140760434503576668065 := by
  unfold tailWord_1271356
  simp only [CollatzResearch.WordTrace]
  refine ⟨23185081391050908581640961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30913441854734544775521281 23185081391050908581640961)
  ·
    refine ⟨17388811043288181436230721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23185081391050908581640961 17388811043288181436230721)
    ·
      refine ⟨13041608282466136077173041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17388811043288181436230721 13041608282466136077173041)
      ·
        refine ⟨9781206211849602057879781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13041608282466136077173041 9781206211849602057879781)
        ·
          refine ⟨1833976164721800385852459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9781206211849602057879781 1833976164721800385852459)
          ·
            refine ⟨2750964247082700578778689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1833976164721800385852459 2750964247082700578778689)
            ·
              refine ⟨2063223185312025434084017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2750964247082700578778689 2063223185312025434084017)
              ·
                refine ⟨1547417388984019075563013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2063223185312025434084017 1547417388984019075563013)
                ·
                  refine ⟨290140760434503576668065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1547417388984019075563013 290140760434503576668065)
                  ·
                    rfl

theorem cell21_1271356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_1271356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1271356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1271356 prefixEnd_1271356 := by exact prefixLift 1271356
  have htrace : WordTrace (prefixWord ++ tailWord_1271356) baseStart_1271356 baseEnd_1271356 := by
    simpa [prefixWord, tailWord_1271356, baseEnd_1271356] using wordTrace_append hprefix tailTrace_1271356
  have hstable : (prefixWord ++ tailWord_1271356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271356).length < 2 ^ (prefixWord ++ tailWord_1271356).sum := by decide
  have hdescent : baseEnd_1271356 < baseStart_1271356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271474 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 6]
def baseStart_1271474 : Nat := 118140960795 + 1271474 * 2 ^ 59
def prefixEnd_1271474 : Nat := 4983230072969 + 3 ^ 40 * 1271474 * 2
def baseEnd_1271474 : Nat := 290167689642161593701157

theorem tailTrace_1271474 : CollatzResearch.WordTrace tailWord_1271474 prefixEnd_1271474 290167689642161593701157 := by
  unfold tailWord_1271474
  simp only [CollatzResearch.WordTrace]
  refine ⟨11593616648918580829019369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30916311063782882210718317 11593616648918580829019369)
  ·
    refine ⟨8695212486688935621764527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11593616648918580829019369 8695212486688935621764527)
    ·
      refine ⟨13042818730033403432646791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8695212486688935621764527 13042818730033403432646791)
      ·
        refine ⟨19564228095050105148970187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13042818730033403432646791 19564228095050105148970187)
        ·
          refine ⟨29346342142575157723455281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19564228095050105148970187 29346342142575157723455281)
          ·
            refine ⟨22009756606931368292591461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29346342142575157723455281 22009756606931368292591461)
            ·
              refine ⟨4126829363799631554860899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22009756606931368292591461 4126829363799631554860899)
              ·
                refine ⟨6190244045699447332291349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4126829363799631554860899 6190244045699447332291349)
                ·
                  refine ⟨290167689642161593701157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6190244045699447332291349 290167689642161593701157)
                  ·
                    rfl

theorem cell21_1271474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_1271474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1271474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1271474 prefixEnd_1271474 := by exact prefixLift 1271474
  have htrace : WordTrace (prefixWord ++ tailWord_1271474) baseStart_1271474 baseEnd_1271474 := by
    simpa [prefixWord, tailWord_1271474, baseEnd_1271474] using wordTrace_append hprefix tailTrace_1271474
  have hstable : (prefixWord ++ tailWord_1271474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271474).length < 2 ^ (prefixWord ++ tailWord_1271474).sum := by decide
  have hdescent : baseEnd_1271474 < baseStart_1271474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271564 : List Nat := [2, 2, 1, 2, 2, 1, 2, 9]
def baseStart_1271564 : Nat := 118140960795 + 1271564 * 2 ^ 59
def prefixEnd_1271564 : Nat := 4983230072969 + 3 ^ 40 * 1271564 * 2
def baseEnd_1271564 : Nat := 96729409622780479066991

theorem tailTrace_1271564 : CollatzResearch.WordTrace tailWord_1271564 prefixEnd_1271564 96729409622780479066991 := by
  unfold tailWord_1271564
  simp only [CollatzResearch.WordTrace]
  refine ⟨23188874582674134343426873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30918499443565512457902497 23188874582674134343426873)
  ·
    refine ⟨17391655937005600757570155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23188874582674134343426873 17391655937005600757570155)
    ·
      refine ⟨26087483905508401136355233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17391655937005600757570155 26087483905508401136355233)
      ·
        refine ⟨19565612929131300852266425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26087483905508401136355233 19565612929131300852266425)
        ·
          refine ⟨14674209696848475639199819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19565612929131300852266425 14674209696848475639199819)
          ·
            refine ⟨22011314545272713458799729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14674209696848475639199819 22011314545272713458799729)
            ·
              refine ⟨16508485908954535094099797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22011314545272713458799729 16508485908954535094099797)
              ·
                refine ⟨96729409622780479066991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16508485908954535094099797 96729409622780479066991)
                ·
                  rfl

theorem cell21_1271564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 9].length) (baseStart_1271564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1271564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1271564 prefixEnd_1271564 := by exact prefixLift 1271564
  have htrace : WordTrace (prefixWord ++ tailWord_1271564) baseStart_1271564 baseEnd_1271564 := by
    simpa [prefixWord, tailWord_1271564, baseEnd_1271564] using wordTrace_append hprefix tailTrace_1271564
  have hstable : (prefixWord ++ tailWord_1271564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271564).length < 2 ^ (prefixWord ++ tailWord_1271564).sum := by decide
  have hdescent : baseEnd_1271564 < baseStart_1271564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271570 : List Nat := [3, 2, 4, 1, 1, 1, 1, 5, 3]
def baseStart_1271570 : Nat := 118140960795 + 1271570 * 2 ^ 59
def prefixEnd_1271570 : Nat := 4983230072969 + 3 ^ 40 * 1271570 * 2
def baseEnd_1271570 : Nat := 290189598150086760100961

theorem tailTrace_1271570 : CollatzResearch.WordTrace tailWord_1271570 prefixEnd_1271570 290189598150086760100961 := by
  unfold tailWord_1271570
  simp only [CollatzResearch.WordTrace]
  refine ⟨11594492000831632927893041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30918645335551021141048109 11594492000831632927893041)
  ·
    refine ⟨8695869000623724695919781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11594492000831632927893041 8695869000623724695919781)
    ·
      refine ⟨1630475437616948380484959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8695869000623724695919781 1630475437616948380484959)
      ·
        refine ⟨2445713156425422570727439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1630475437616948380484959 2445713156425422570727439)
        ·
          refine ⟨3668569734638133856091159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2445713156425422570727439 3668569734638133856091159)
          ·
            refine ⟨5502854601957200784136739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3668569734638133856091159 5502854601957200784136739)
            ·
              refine ⟨8254281902935801176205109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5502854601957200784136739 8254281902935801176205109)
              ·
                refine ⟨773838928400231360269229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8254281902935801176205109 773838928400231360269229)
                ·
                  refine ⟨290189598150086760100961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 773838928400231360269229 290189598150086760100961)
                  ·
                    rfl

theorem cell21_1271570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_1271570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1271570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1271570 prefixEnd_1271570 := by exact prefixLift 1271570
  have htrace : WordTrace (prefixWord ++ tailWord_1271570) baseStart_1271570 baseEnd_1271570 := by
    simpa [prefixWord, tailWord_1271570, baseEnd_1271570] using wordTrace_append hprefix tailTrace_1271570
  have hstable : (prefixWord ++ tailWord_1271570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271570).length < 2 ^ (prefixWord ++ tailWord_1271570).sum := by decide
  have hdescent : baseEnd_1271570 < baseStart_1271570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271615 : List Nat := [1, 1, 2, 2, 7, 1, 2, 5]
def baseStart_1271615 : Nat := 118140960795 + 1271615 * 2 ^ 59
def prefixEnd_1271615 : Nat := 4983230072969 + 3 ^ 40 * 1271615 * 2
def baseEnd_1271615 : Nat := 96733289254392227283623

theorem tailTrace_1271615 : CollatzResearch.WordTrace tailWord_1271615 prefixEnd_1271615 96733289254392227283623 := by
  unfold tailWord_1271615
  simp only [CollatzResearch.WordTrace]
  refine ⟨46379609288163504396960299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30919739525442336264640199 46379609288163504396960299)
  ·
    refine ⟨69569413932245256595440449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46379609288163504396960299 69569413932245256595440449)
    ·
      refine ⟨52177060449183942446580337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69569413932245256595440449 52177060449183942446580337)
      ·
        refine ⟨39132795336887956834935253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52177060449183942446580337 39132795336887956834935253)
        ·
          refine ⟨917174890708311488318795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 39132795336887956834935253 917174890708311488318795)
          ·
            refine ⟨1375762336062467232478193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917174890708311488318795 1375762336062467232478193)
            ·
              refine ⟨1031821752046850424358645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1375762336062467232478193 1031821752046850424358645)
              ·
                refine ⟨96733289254392227283623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1031821752046850424358645 96733289254392227283623)
                ·
                  rfl

theorem cell21_1271615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 5].length) (baseStart_1271615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1271615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1271615 prefixEnd_1271615 := by exact prefixLift 1271615
  have htrace : WordTrace (prefixWord ++ tailWord_1271615) baseStart_1271615 baseEnd_1271615 := by
    simpa [prefixWord, tailWord_1271615, baseEnd_1271615] using wordTrace_append hprefix tailTrace_1271615
  have hstable : (prefixWord ++ tailWord_1271615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271615).length < 2 ^ (prefixWord ++ tailWord_1271615).sum := by decide
  have hdescent : baseEnd_1271615 < baseStart_1271615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271660 : List Nat := [2, 2, 1, 1, 4, 4, 2, 1, 4]
def baseStart_1271660 : Nat := 118140960795 + 1271660 * 2 ^ 59
def prefixEnd_1271660 : Nat := 4983230072969 + 3 ^ 40 * 1271660 * 2
def baseEnd_1271660 : Nat := 290210137376266603600777

theorem tailTrace_1271660 : CollatzResearch.WordTrace tailWord_1271660 prefixEnd_1271660 290210137376266603600777 := by
  unfold tailWord_1271660
  simp only [CollatzResearch.WordTrace]
  refine ⟨23190625286500238541174217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30920833715333651388232289 23190625286500238541174217)
  ·
    refine ⟨17392968964875178905880663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23190625286500238541174217 17392968964875178905880663)
    ·
      refine ⟨26089453447312768358820995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17392968964875178905880663 26089453447312768358820995)
      ·
        refine ⟨39134180170969152538231493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26089453447312768358820995 39134180170969152538231493)
        ·
          refine ⟨7337658782056716100918405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39134180170969152538231493 7337658782056716100918405)
          ·
            refine ⟨1375811021635634268922201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7337658782056716100918405 1375811021635634268922201)
            ·
              refine ⟨1031858266226725701691651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1375811021635634268922201 1031858266226725701691651)
              ·
                refine ⟨1547787399340088552537477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1031858266226725701691651 1547787399340088552537477)
                ·
                  refine ⟨290210137376266603600777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1547787399340088552537477 290210137376266603600777)
                  ·
                    rfl

theorem cell21_1271660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_1271660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1271660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1271660 prefixEnd_1271660 := by exact prefixLift 1271660
  have htrace : WordTrace (prefixWord ++ tailWord_1271660) baseStart_1271660 baseEnd_1271660 := by
    simpa [prefixWord, tailWord_1271660, baseEnd_1271660] using wordTrace_append hprefix tailTrace_1271660
  have hstable : (prefixWord ++ tailWord_1271660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271660).length < 2 ^ (prefixWord ++ tailWord_1271660).sum := by decide
  have hdescent : baseEnd_1271660 < baseStart_1271660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271705 : List Nat := [1, 2, 1, 2, 1, 3, 6, 2, 3]
def baseStart_1271705 : Nat := 118140960795 + 1271705 * 2 ^ 59
def prefixEnd_1271705 : Nat := 4983230072969 + 3 ^ 40 * 1271705 * 2
def baseEnd_1271705 : Nat := 290220406989356525350685

theorem tailTrace_1271705 : CollatzResearch.WordTrace tailWord_1271705 prefixEnd_1271705 290220406989356525350685 := by
  unfold tailWord_1271705
  simp only [CollatzResearch.WordTrace]
  refine ⟨46382891857837449767736569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30921927905224966511824379 46382891857837449767736569)
  ·
    refine ⟨34787168893378087325802427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46382891857837449767736569 34787168893378087325802427)
    ·
      refine ⟨52180753340067130988703641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34787168893378087325802427 52180753340067130988703641)
      ·
        refine ⟨39135565005050348241527731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52180753340067130988703641 39135565005050348241527731)
        ·
          refine ⟨58703347507575522362291597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39135565005050348241527731 58703347507575522362291597)
          ·
            refine ⟨22013755315340820885859349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58703347507575522362291597 22013755315340820885859349)
            ·
              refine ⟨1031894780406600979024657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22013755315340820885859349 1031894780406600979024657)
              ·
                refine ⟨773921085304950734268493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1031894780406600979024657 773921085304950734268493)
                ·
                  refine ⟨290220406989356525350685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 773921085304950734268493 290220406989356525350685)
                  ·
                    rfl

theorem cell21_1271705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 3].length) (baseStart_1271705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1271705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1271705 prefixEnd_1271705 := by exact prefixLift 1271705
  have htrace : WordTrace (prefixWord ++ tailWord_1271705) baseStart_1271705 baseEnd_1271705 := by
    simpa [prefixWord, tailWord_1271705, baseEnd_1271705] using wordTrace_append hprefix tailTrace_1271705
  have hstable : (prefixWord ++ tailWord_1271705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271705).length < 2 ^ (prefixWord ++ tailWord_1271705).sum := by decide
  have hdescent : baseEnd_1271705 < baseStart_1271705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271719 : List Nat := [1, 1, 6, 1, 2, 1, 2, 3, 4]
def baseStart_1271719 : Nat := 118140960795 + 1271719 * 2 ^ 59
def prefixEnd_1271719 : Nat := 4983230072969 + 3 ^ 40 * 1271719 * 2
def baseEnd_1271719 : Nat := 290223601980095612117323

theorem tailTrace_1271719 : CollatzResearch.WordTrace tailWord_1271719 prefixEnd_1271719 290223601980095612117323 := by
  unfold tailWord_1271719
  simp only [CollatzResearch.WordTrace]
  refine ⟨46383402479786730158746211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30922268319857820105830807 46383402479786730158746211)
  ·
    refine ⟨69575103719680095238119317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46383402479786730158746211 69575103719680095238119317)
    ·
      refine ⟨3261332986860004464286843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69575103719680095238119317 3261332986860004464286843)
      ·
        refine ⟨4891999480290006696430265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3261332986860004464286843 4891999480290006696430265)
        ·
          refine ⟨3668999610217505022322699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4891999480290006696430265 3668999610217505022322699)
          ·
            refine ⟨5503499415326257533484049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3668999610217505022322699 5503499415326257533484049)
            ·
              refine ⟨4127624561494693150113037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5503499415326257533484049 4127624561494693150113037)
              ·
                refine ⟨1547859210560509931292389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4127624561494693150113037 1547859210560509931292389)
                ·
                  refine ⟨290223601980095612117323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1547859210560509931292389 290223601980095612117323)
                  ·
                    rfl

theorem cell21_1271719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 4].length) (baseStart_1271719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1271719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1271719 prefixEnd_1271719 := by exact prefixLift 1271719
  have htrace : WordTrace (prefixWord ++ tailWord_1271719) baseStart_1271719 baseEnd_1271719 := by
    simpa [prefixWord, tailWord_1271719, baseEnd_1271719] using wordTrace_append hprefix tailTrace_1271719
  have hstable : (prefixWord ++ tailWord_1271719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271719).length < 2 ^ (prefixWord ++ tailWord_1271719).sum := by decide
  have hdescent : baseEnd_1271719 < baseStart_1271719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271764 : List Nat := [2, 4, 1, 2, 1, 1, 4, 1, 5]
def baseStart_1271764 : Nat := 118140960795 + 1271764 * 2 ^ 59
def prefixEnd_1271764 : Nat := 4983230072969 + 3 ^ 40 * 1271764 * 2
def baseEnd_1271764 : Nat := 290233871593185533867231

theorem tailTrace_1271764 : CollatzResearch.WordTrace tailWord_1271764 prefixEnd_1271764 290233871593185533867231 := by
  unfold tailWord_1271764
  simp only [CollatzResearch.WordTrace]
  refine ⟨23192521882311851422067173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30923362509749135229422897 23192521882311851422067173)
  ·
    refine ⟨4348597852933472141637595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23192521882311851422067173 4348597852933472141637595)
    ·
      refine ⟨6522896779400208212456393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4348597852933472141637595 6522896779400208212456393)
      ·
        refine ⟨4892172584550156159342295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6522896779400208212456393 4892172584550156159342295)
        ·
          refine ⟨7338258876825234239013443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4892172584550156159342295 7338258876825234239013443)
          ·
            refine ⟨11007388315237851358520165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7338258876825234239013443 11007388315237851358520165)
            ·
              refine ⟨2063885309107097129722531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11007388315237851358520165 2063885309107097129722531)
              ·
                refine ⟨3095827963660645694583797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2063885309107097129722531 3095827963660645694583797)
                ·
                  refine ⟨290233871593185533867231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3095827963660645694583797 290233871593185533867231)
                  ·
                    rfl

theorem cell21_1271764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_1271764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1271764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1271764 prefixEnd_1271764 := by exact prefixLift 1271764
  have htrace : WordTrace (prefixWord ++ tailWord_1271764) baseStart_1271764 baseEnd_1271764 := by
    simpa [prefixWord, tailWord_1271764, baseEnd_1271764] using wordTrace_append hprefix tailTrace_1271764
  have hstable : (prefixWord ++ tailWord_1271764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271764).length < 2 ^ (prefixWord ++ tailWord_1271764).sum := by decide
  have hdescent : baseEnd_1271764 < baseStart_1271764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271829 : List Nat := [1, 3, 2, 1, 6, 1, 2, 1, 4]
def baseStart_1271829 : Nat := 118140960795 + 1271829 * 2 ^ 59
def prefixEnd_1271829 : Nat := 4983230072969 + 3 ^ 40 * 1271829 * 2
def baseEnd_1271829 : Nat := 290248705478759865283765

theorem tailTrace_1271829 : CollatzResearch.WordTrace tailWord_1271829 prefixEnd_1271829 290248705478759865283765 := by
  unfold tailWord_1271829
  simp only [CollatzResearch.WordTrace]
  refine ⟨46387414509388218945250541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30924943006258812630167027 46387414509388218945250541)
  ·
    refine ⟨17395280441020582104468953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46387414509388218945250541 17395280441020582104468953)
    ·
      refine ⟨13046460330765436578351715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17395280441020582104468953 13046460330765436578351715)
      ·
        refine ⟨19569690496148154867527573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13046460330765436578351715 19569690496148154867527573)
        ·
          refine ⟨917329242006944759415355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19569690496148154867527573 917329242006944759415355)
          ·
            refine ⟨1375993863010417139123033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917329242006944759415355 1375993863010417139123033)
            ·
              refine ⟨1031995397257812854342275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1375993863010417139123033 1031995397257812854342275)
              ·
                refine ⟨1547993095886719281513413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1031995397257812854342275 1547993095886719281513413)
                ·
                  refine ⟨290248705478759865283765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1547993095886719281513413 290248705478759865283765)
                  ·
                    rfl

theorem cell21_1271829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 4].length) (baseStart_1271829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1271829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1271829 prefixEnd_1271829 := by exact prefixLift 1271829
  have htrace : WordTrace (prefixWord ++ tailWord_1271829) baseStart_1271829 baseEnd_1271829 := by
    simpa [prefixWord, tailWord_1271829, baseEnd_1271829] using wordTrace_append hprefix tailTrace_1271829
  have hstable : (prefixWord ++ tailWord_1271829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271829).length < 2 ^ (prefixWord ++ tailWord_1271829).sum := by decide
  have hdescent : baseEnd_1271829 < baseStart_1271829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271913 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 6]
def baseStart_1271913 : Nat := 118140960795 + 1271913 * 2 ^ 59
def prefixEnd_1271913 : Nat := 4983230072969 + 3 ^ 40 * 1271913 * 2
def baseEnd_1271913 : Nat := 290267875423194385883593

theorem tailTrace_1271913 : CollatzResearch.WordTrace tailWord_1271913 prefixEnd_1271913 290267875423194385883593 := by
  unfold tailWord_1271913
  simp only [CollatzResearch.WordTrace]
  refine ⟨46390478241083901291308393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30926985494055934194205595 46390478241083901291308393)
  ·
    refine ⟨34792858680812925968481295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46390478241083901291308393 34792858680812925968481295)
    ·
      refine ⟨52189288021219388952721943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34792858680812925968481295 52189288021219388952721943)
      ·
        refine ⟨78283932031829083429082915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52189288021219388952721943 78283932031829083429082915)
        ·
          refine ⟨117425898047743625143624373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78283932031829083429082915 117425898047743625143624373)
          ·
            refine ⟨11008677941975964857214785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117425898047743625143624373 11008677941975964857214785)
            ·
              refine ⟨8256508456481973642911089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11008677941975964857214785 8256508456481973642911089)
              ·
                refine ⟨6192381342361480232183317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8256508456481973642911089 6192381342361480232183317)
                ·
                  refine ⟨290267875423194385883593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6192381342361480232183317 290267875423194385883593)
                  ·
                    rfl

theorem cell21_1271913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_1271913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1271913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1271913 prefixEnd_1271913 := by exact prefixLift 1271913
  have htrace : WordTrace (prefixWord ++ tailWord_1271913) baseStart_1271913 baseEnd_1271913 := by
    simpa [prefixWord, tailWord_1271913, baseEnd_1271913] using wordTrace_append hprefix tailTrace_1271913
  have hstable : (prefixWord ++ tailWord_1271913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271913).length < 2 ^ (prefixWord ++ tailWord_1271913).sum := by decide
  have hdescent : baseEnd_1271913 < baseStart_1271913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271916 : List Nat := [2, 2, 1, 1, 3, 3, 1, 5, 3]
def baseStart_1271916 : Nat := 118140960795 + 1271916 * 2 ^ 59
def prefixEnd_1271916 : Nat := 4983230072969 + 3 ^ 40 * 1271916 * 2
def baseEnd_1271916 : Nat := 290268560064067047333587

theorem tailTrace_1271916 : CollatzResearch.WordTrace tailWord_1271916 prefixEnd_1271916 290268560064067047333587 := by
  unfold tailWord_1271916
  simp only [CollatzResearch.WordTrace]
  refine ⟨23195293830036516401833801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30927058440048688535778401 23195293830036516401833801)
  ·
    refine ⟨17396470372527387301375351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23195293830036516401833801 17396470372527387301375351)
    ·
      refine ⟨26094705558791080952063027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17396470372527387301375351 26094705558791080952063027)
      ·
        refine ⟨39142058338186621428094541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26094705558791080952063027 39142058338186621428094541)
        ·
          refine ⟨14678271876819983035535453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39142058338186621428094541 14678271876819983035535453)
          ·
            refine ⟨5504351953807493638325795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14678271876819983035535453 5504351953807493638325795)
            ·
              refine ⟨8256527930711240457488693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5504351953807493638325795 8256527930711240457488693)
              ·
                refine ⟨774049493504178792889565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8256527930711240457488693 774049493504178792889565)
                ·
                  refine ⟨290268560064067047333587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 774049493504178792889565 290268560064067047333587)
                  ·
                    rfl

theorem cell21_1271916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 3].length) (baseStart_1271916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1271916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1271916 prefixEnd_1271916 := by exact prefixLift 1271916
  have htrace : WordTrace (prefixWord ++ tailWord_1271916) baseStart_1271916 baseEnd_1271916 := by
    simpa [prefixWord, tailWord_1271916, baseEnd_1271916] using wordTrace_append hprefix tailTrace_1271916
  have hstable : (prefixWord ++ tailWord_1271916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271916).length < 2 ^ (prefixWord ++ tailWord_1271916).sum := by decide
  have hdescent : baseEnd_1271916 < baseStart_1271916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271978 : List Nat := [3, 1, 5, 1, 2, 2, 7]
def baseStart_1271978 : Nat := 118140960795 + 1271978 * 2 ^ 59
def prefixEnd_1271978 : Nat := 4983230072969 + 3 ^ 40 * 1271978 * 2
def baseEnd_1271978 : Nat := 32253634367640968588903

theorem tailTrace_1271978 : CollatzResearch.WordTrace tailWord_1271978 prefixEnd_1271978 32253634367640968588903 := by
  unfold tailWord_1271978
  simp only [CollatzResearch.WordTrace]
  refine ⟨11598212246462104348106147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30928565990565611594949725 11598212246462104348106147)
  ·
    refine ⟨17397318369693156522159221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11598212246462104348106147 17397318369693156522159221)
    ·
      refine ⟨1630998597158733423952427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17397318369693156522159221 1630998597158733423952427)
      ·
        refine ⟨2446497895738100135928641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1630998597158733423952427 2446497895738100135928641)
        ·
          refine ⟨1834873421803575101946481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2446497895738100135928641 1834873421803575101946481)
          ·
            refine ⟨1376155066352681326459861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1834873421803575101946481 1376155066352681326459861)
            ·
              refine ⟨32253634367640968588903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1376155066352681326459861 32253634367640968588903)
              ·
                rfl

theorem cell21_1271978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 7].length) (baseStart_1271978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1271978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1271978 prefixEnd_1271978 := by exact prefixLift 1271978
  have htrace : WordTrace (prefixWord ++ tailWord_1271978) baseStart_1271978 baseEnd_1271978 := by
    simpa [prefixWord, tailWord_1271978, baseEnd_1271978] using wordTrace_append hprefix tailTrace_1271978
  have hstable : (prefixWord ++ tailWord_1271978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271978).length < 2 ^ (prefixWord ++ tailWord_1271978).sum := by decide
  have hdescent : baseEnd_1271978 < baseStart_1271978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272068 : List Nat := [2, 3, 2, 2, 3, 1, 1, 2, 5]
def baseStart_1272068 : Nat := 118140960795 + 1272068 * 2 ^ 59
def prefixEnd_1272068 : Nat := 4983230072969 + 3 ^ 40 * 1272068 * 2
def baseEnd_1272068 : Nat := 290303248534948560799943

theorem tailTrace_1272068 : CollatzResearch.WordTrace tailWord_1272068 prefixEnd_1272068 290303248534948560799943 := by
  unfold tailWord_1272068
  simp only [CollatzResearch.WordTrace]
  refine ⟨23198065777761181381600429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30930754370348241842133905 23198065777761181381600429)
  ·
    refine ⟨8699274666660443018100161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23198065777761181381600429 8699274666660443018100161)
    ·
      refine ⟨6524455999995332263575121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8699274666660443018100161 6524455999995332263575121)
      ·
        refine ⟨4893341999996499197681341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6524455999995332263575121 4893341999996499197681341)
        ·
          refine ⟨1835003249998687199130503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4893341999996499197681341 1835003249998687199130503)
          ·
            refine ⟨2752504874998030798695755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1835003249998687199130503 2752504874998030798695755)
            ·
              refine ⟨4128757312497046198043633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2752504874998030798695755 4128757312497046198043633)
              ·
                refine ⟨3096567984372784648532725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4128757312497046198043633 3096567984372784648532725)
                ·
                  refine ⟨290303248534948560799943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3096567984372784648532725 290303248534948560799943)
                  ·
                    rfl

theorem cell21_1272068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_1272068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1272068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1272068 prefixEnd_1272068 := by exact prefixLift 1272068
  have htrace : WordTrace (prefixWord ++ tailWord_1272068) baseStart_1272068 baseEnd_1272068 := by
    simpa [prefixWord, tailWord_1272068, baseEnd_1272068] using wordTrace_append hprefix tailTrace_1272068
  have hstable : (prefixWord ++ tailWord_1272068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272068).length < 2 ^ (prefixWord ++ tailWord_1272068).sum := by decide
  have hdescent : baseEnd_1272068 < baseStart_1272068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272079 : List Nat := [1, 1, 2, 1, 1, 1, 3, 11]
def baseStart_1272079 : Nat := 118140960795 + 1272079 * 2 ^ 59
def prefixEnd_1272079 : Nat := 4983230072969 + 3 ^ 40 * 1272079 * 2
def baseEnd_1272079 : Nat := 96768586294938328705529

theorem tailTrace_1272079 : CollatzResearch.WordTrace tailWord_1272079 prefixEnd_1272079 96768586294938328705529 := by
  unfold tailWord_1272079
  simp only [CollatzResearch.WordTrace]
  refine ⟨46396532758482511641851291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30931021838988341094567527 46396532758482511641851291)
  ·
    refine ⟨69594799137723767462776937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46396532758482511641851291 69594799137723767462776937)
    ·
      refine ⟨52196099353292825597082703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69594799137723767462776937 52196099353292825597082703)
      ·
        refine ⟨78294149029939238395624055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52196099353292825597082703 78294149029939238395624055)
        ·
          refine ⟨117441223544908857593436083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78294149029939238395624055 117441223544908857593436083)
          ·
            refine ⟨176161835317363286390154125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117441223544908857593436083 176161835317363286390154125)
            ·
              refine ⟨66060688244011232396307797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176161835317363286390154125 66060688244011232396307797)
              ·
                refine ⟨96768586294938328705529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 66060688244011232396307797 96768586294938328705529)
                ·
                  rfl

theorem cell21_1272079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 11].length) (baseStart_1272079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1272079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1272079 prefixEnd_1272079 := by exact prefixLift 1272079
  have htrace : WordTrace (prefixWord ++ tailWord_1272079) baseStart_1272079 baseEnd_1272079 := by
    simpa [prefixWord, tailWord_1272079, baseEnd_1272079] using wordTrace_append hprefix tailTrace_1272079
  have hstable : (prefixWord ++ tailWord_1272079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272079).length < 2 ^ (prefixWord ++ tailWord_1272079).sum := by decide
  have hdescent : baseEnd_1272079 < baseStart_1272079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272096 : List Nat := [2, 1, 1, 5, 2, 2, 8]
def baseStart_1272096 : Nat := 118140960795 + 1272096 * 2 ^ 59
def prefixEnd_1272096 : Nat := 4983230072969 + 3 ^ 40 * 1272096 * 2
def baseEnd_1272096 : Nat := 32256626501825192703691

theorem tailTrace_1272096 : CollatzResearch.WordTrace tailWord_1272096 prefixEnd_1272096 32256626501825192703691 := by
  unfold tailWord_1272096
  simp only [CollatzResearch.WordTrace]
  refine ⟨23198576399710461772610071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30931435199613949030146761 23198576399710461772610071)
  ·
    refine ⟨34797864599565692658915107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23198576399710461772610071 34797864599565692658915107)
    ·
      refine ⟨52196796899348538988372661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34797864599565692658915107 52196796899348538988372661)
      ·
        refine ⟨4893449709313925530159937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52196796899348538988372661 4893449709313925530159937)
        ·
          refine ⟨3670087281985444147619953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4893449709313925530159937 3670087281985444147619953)
          ·
            refine ⟨2752565461489083110714965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3670087281985444147619953 2752565461489083110714965)
            ·
              refine ⟨32256626501825192703691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2752565461489083110714965 32256626501825192703691)
              ·
                rfl

theorem cell21_1272096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 8].length) (baseStart_1272096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1272096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1272096 prefixEnd_1272096 := by exact prefixLift 1272096
  have htrace : WordTrace (prefixWord ++ tailWord_1272096) baseStart_1272096 baseEnd_1272096 := by
    simpa [prefixWord, tailWord_1272096, baseEnd_1272096] using wordTrace_append hprefix tailTrace_1272096
  have hstable : (prefixWord ++ tailWord_1272096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272096).length < 2 ^ (prefixWord ++ tailWord_1272096).sum := by decide
  have hdescent : baseEnd_1272096 < baseStart_1272096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272116 : List Nat := [2, 5, 1, 1, 1, 3, 3, 1, 4]
def baseStart_1272116 : Nat := 118140960795 + 1272116 * 2 ^ 59
def prefixEnd_1272116 : Nat := 4983230072969 + 3 ^ 40 * 1272116 * 2
def baseEnd_1272116 : Nat := 290314202788911143999845

theorem tailTrace_1272116 : CollatzResearch.WordTrace tailWord_1272116 prefixEnd_1272116 290314202788911143999845 := by
  unfold tailWord_1272116
  simp only [CollatzResearch.WordTrace]
  refine ⟨23198941129674233480474101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30931921506232311307298801 23198941129674233480474101)
  ·
    refine ⟨2174900730906959388794447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23198941129674233480474101 2174900730906959388794447)
    ·
      refine ⟨3262351096360439083191671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2174900730906959388794447 3262351096360439083191671)
      ·
        refine ⟨4893526644540658624787507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3262351096360439083191671 4893526644540658624787507)
        ·
          refine ⟨7340289966810987937181261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4893526644540658624787507 7340289966810987937181261)
          ·
            refine ⟨2752608737554120476442973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7340289966810987937181261 2752608737554120476442973)
            ·
              refine ⟨1032228276582795178666115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2752608737554120476442973 1032228276582795178666115)
              ·
                refine ⟨1548342414874192767999173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1032228276582795178666115 1548342414874192767999173)
                ·
                  refine ⟨290314202788911143999845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1548342414874192767999173 290314202788911143999845)
                  ·
                    rfl

theorem cell21_1272116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_1272116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1272116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1272116 prefixEnd_1272116 := by exact prefixLift 1272116
  have htrace : WordTrace (prefixWord ++ tailWord_1272116) baseStart_1272116 baseEnd_1272116 := by
    simpa [prefixWord, tailWord_1272116, baseEnd_1272116] using wordTrace_append hprefix tailTrace_1272116
  have hstable : (prefixWord ++ tailWord_1272116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272116).length < 2 ^ (prefixWord ++ tailWord_1272116).sum := by decide
  have hdescent : baseEnd_1272116 < baseStart_1272116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272144 : List Nat := [2, 1, 1, 1, 1, 6, 3, 3, 3]
def baseStart_1272144 : Nat := 118140960795 + 1272144 * 2 ^ 59
def prefixEnd_1272144 : Nat := 4983230072969 + 3 ^ 40 * 1272144 * 2
def baseEnd_1272144 : Nat := 290320592770389317533121

theorem tailTrace_1272144 : CollatzResearch.WordTrace tailWord_1272144 prefixEnd_1272144 290320592770389317533121 := by
  unfold tailWord_1272144
  simp only [CollatzResearch.WordTrace]
  refine ⟨23199451751623513871483743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30932602335498018495311657 23199451751623513871483743)
  ·
    refine ⟨34799177627435270807225615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23199451751623513871483743 34799177627435270807225615)
    ·
      refine ⟨52198766441152906210838423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34799177627435270807225615 52198766441152906210838423)
      ·
        refine ⟨78298149661729359316257635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52198766441152906210838423 78298149661729359316257635)
        ·
          refine ⟨117447224492594038974386453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78298149661729359316257635 117447224492594038974386453)
          ·
            refine ⟨5505338648090345576924365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 117447224492594038974386453 5505338648090345576924365)
            ·
              refine ⟨2064501993033879591346637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5505338648090345576924365 2064501993033879591346637)
              ·
                refine ⟨774188247387704846754989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2064501993033879591346637 774188247387704846754989)
                ·
                  refine ⟨290320592770389317533121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 774188247387704846754989 290320592770389317533121)
                  ·
                    rfl

theorem cell21_1272144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 3].length) (baseStart_1272144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1272144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1272144 prefixEnd_1272144 := by exact prefixLift 1272144
  have htrace : WordTrace (prefixWord ++ tailWord_1272144) baseStart_1272144 baseEnd_1272144 := by
    simpa [prefixWord, tailWord_1272144, baseEnd_1272144] using wordTrace_append hprefix tailTrace_1272144
  have hstable : (prefixWord ++ tailWord_1272144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272144).length < 2 ^ (prefixWord ++ tailWord_1272144).sum := by decide
  have hdescent : baseEnd_1272144 < baseStart_1272144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272268 : List Nat := [2, 2, 1, 4, 4, 1, 1, 2, 4]
def baseStart_1272268 : Nat := 118140960795 + 1272268 * 2 ^ 59
def prefixEnd_1272268 : Nat := 4983230072969 + 3 ^ 40 * 1272268 * 2
def baseEnd_1272268 : Nat := 290348891259792657466201

theorem tailTrace_1272268 : CollatzResearch.WordTrace tailWord_1272268 prefixEnd_1272268 290348891259792657466201 := by
  unfold tailWord_1272268
  simp only [CollatzResearch.WordTrace]
  refine ⟨23201713077398898460240729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30935617436531864613654305 23201713077398898460240729)
  ·
    refine ⟨17401284808049173845180547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23201713077398898460240729 17401284808049173845180547)
    ·
      refine ⟨26101927212073760767770821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17401284808049173845180547 26101927212073760767770821)
      ·
        refine ⟨4894111352263830143957029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26101927212073760767770821 4894111352263830143957029)
        ·
          refine ⟨917645878549468151991943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4894111352263830143957029 917645878549468151991943)
          ·
            refine ⟨1376468817824202227987915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917645878549468151991943 1376468817824202227987915)
            ·
              refine ⟨2064703226736303341981873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1376468817824202227987915 2064703226736303341981873)
              ·
                refine ⟨1548527420052227506486405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2064703226736303341981873 1548527420052227506486405)
                ·
                  refine ⟨290348891259792657466201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1548527420052227506486405 290348891259792657466201)
                  ·
                    rfl

theorem cell21_1272268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 4].length) (baseStart_1272268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1272268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1272268 prefixEnd_1272268 := by exact prefixLift 1272268
  have htrace : WordTrace (prefixWord ++ tailWord_1272268) baseStart_1272268 baseEnd_1272268 := by
    simpa [prefixWord, tailWord_1272268, baseEnd_1272268] using wordTrace_append hprefix tailTrace_1272268
  have hstable : (prefixWord ++ tailWord_1272268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272268).length < 2 ^ (prefixWord ++ tailWord_1272268).sum := by decide
  have hdescent : baseEnd_1272268 < baseStart_1272268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272307 : List Nat := [1, 1, 1, 2, 2, 2, 5, 7]
def baseStart_1272307 : Nat := 118140960795 + 1272307 * 2 ^ 59
def prefixEnd_1272307 : Nat := 4983230072969 + 3 ^ 40 * 1272307 * 2
def baseEnd_1272307 : Nat := 96785930530379085438707

theorem tailTrace_1272307 : CollatzResearch.WordTrace tailWord_1272307 prefixEnd_1272307 96785930530379085438707 := by
  unfold tailWord_1272307
  simp only [CollatzResearch.WordTrace]
  refine ⟨46404848601656506581151175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30936565734437671054100783 46404848601656506581151175)
  ·
    refine ⟨69607272902484759871726763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46404848601656506581151175 69607272902484759871726763)
    ·
      refine ⟨104410909353727139807590145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69607272902484759871726763 104410909353727139807590145)
      ·
        refine ⟨78308182015295354855692609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104410909353727139807590145 78308182015295354855692609)
        ·
          refine ⟨58731136511471516141769457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78308182015295354855692609 58731136511471516141769457)
          ·
            refine ⟨44048352383603637106327093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58731136511471516141769457 44048352383603637106327093)
            ·
              refine ⟨4129533035962840978718165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44048352383603637106327093 4129533035962840978718165)
              ·
                refine ⟨96785930530379085438707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4129533035962840978718165 96785930530379085438707)
                ·
                  rfl

theorem cell21_1272307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 7].length) (baseStart_1272307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1272307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1272307 prefixEnd_1272307 := by exact prefixLift 1272307
  have htrace : WordTrace (prefixWord ++ tailWord_1272307) baseStart_1272307 baseEnd_1272307 := by
    simpa [prefixWord, tailWord_1272307, baseEnd_1272307] using wordTrace_append hprefix tailTrace_1272307
  have hstable : (prefixWord ++ tailWord_1272307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272307).length < 2 ^ (prefixWord ++ tailWord_1272307).sum := by decide
  have hdescent : baseEnd_1272307 < baseStart_1272307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272324 : List Nat := [2, 3, 2, 3, 1, 1, 9]
def baseStart_1272324 : Nat := 118140960795 + 1272324 * 2 ^ 59
def prefixEnd_1272324 : Nat := 4983230072969 + 3 ^ 40 * 1272324 * 2
def baseEnd_1272324 : Nat := 32262407913638778281417

theorem tailTrace_1272324 : CollatzResearch.WordTrace tailWord_1272324 prefixEnd_1272324 32262407913638778281417 := by
  unfold tailWord_1272324
  simp only [CollatzResearch.WordTrace]
  refine ⟨23202734321297459242260013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30936979095063278989680017 23202734321297459242260013)
  ·
    refine ⟨8701025370486547215847505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23202734321297459242260013 8701025370486547215847505)
    ·
      refine ⟨6525769027864910411885629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8701025370486547215847505 6525769027864910411885629)
      ·
        refine ⟨2447163385449341404457111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6525769027864910411885629 2447163385449341404457111)
        ·
          refine ⟨3670745078174012106685667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2447163385449341404457111 3670745078174012106685667)
          ·
            refine ⟨5506117617261018160028501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3670745078174012106685667 5506117617261018160028501)
            ·
              refine ⟨32262407913638778281417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5506117617261018160028501 32262407913638778281417)
              ·
                rfl

theorem cell21_1272324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 9].length) (baseStart_1272324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1272324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1272324 prefixEnd_1272324 := by exact prefixLift 1272324
  have htrace : WordTrace (prefixWord ++ tailWord_1272324) baseStart_1272324 baseEnd_1272324 := by
    simpa [prefixWord, tailWord_1272324, baseEnd_1272324] using wordTrace_append hprefix tailTrace_1272324
  have hstable : (prefixWord ++ tailWord_1272324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272324).length < 2 ^ (prefixWord ++ tailWord_1272324).sum := by decide
  have hdescent : baseEnd_1272324 < baseStart_1272324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272389 : List Nat := [1, 3, 1, 1, 1, 7, 2, 2, 3]
def baseStart_1272389 : Nat := 118140960795 + 1272389 * 2 ^ 59
def prefixEnd_1272389 : Nat := 4983230072969 + 3 ^ 40 * 1272389 * 2
def baseEnd_1272389 : Nat := 290376505108323335949287

theorem tailTrace_1272389 : CollatzResearch.WordTrace tailWord_1272389 prefixEnd_1272389 290376505108323335949287 := by
  unfold tailWord_1272389
  simp only [CollatzResearch.WordTrace]
  refine ⟨46407839387359434585636221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30938559591572956390424147 46407839387359434585636221)
  ·
    refine ⟨17402939770259787969613583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46407839387359434585636221 17402939770259787969613583)
    ·
      refine ⟨26104409655389681954420375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17402939770259787969613583 26104409655389681954420375)
      ·
        refine ⟨39156614483084522931630563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26104409655389681954420375 39156614483084522931630563)
        ·
          refine ⟨58734921724626784397445845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39156614483084522931630563 58734921724626784397445845)
          ·
            refine ⟨1376599727920940259315137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 58734921724626784397445845 1376599727920940259315137)
            ·
              refine ⟨1032449795940705194486353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1376599727920940259315137 1032449795940705194486353)
              ·
                refine ⟨774337346955528895864765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1032449795940705194486353 774337346955528895864765)
                ·
                  refine ⟨290376505108323335949287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 774337346955528895864765 290376505108323335949287)
                  ·
                    rfl

theorem cell21_1272389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 3].length) (baseStart_1272389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1272389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1272389 prefixEnd_1272389 := by exact prefixLift 1272389
  have htrace : WordTrace (prefixWord ++ tailWord_1272389) baseStart_1272389 baseEnd_1272389 := by
    simpa [prefixWord, tailWord_1272389, baseEnd_1272389] using wordTrace_append hprefix tailTrace_1272389
  have hstable : (prefixWord ++ tailWord_1272389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272389).length < 2 ^ (prefixWord ++ tailWord_1272389).sum := by decide
  have hdescent : baseEnd_1272389 < baseStart_1272389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272431 : List Nat := [1, 1, 2, 1, 3, 2, 3, 5, 3]
def baseStart_1272431 : Nat := 118140960795 + 1272431 * 2 ^ 59
def prefixEnd_1272431 : Nat := 4983230072969 + 3 ^ 40 * 1272431 * 2
def baseEnd_1272431 : Nat := 290386090080540596249201

theorem tailTrace_1272431 : CollatzResearch.WordTrace tailWord_1272431 prefixEnd_1272431 290386090080540596249201 := by
  unfold tailWord_1272431
  simp only [CollatzResearch.WordTrace]
  refine ⟨46409371253207275758665147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30939580835471517172443431 46409371253207275758665147)
  ·
    refine ⟨69614056879810913637997721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46409371253207275758665147 69614056879810913637997721)
    ·
      refine ⟨52210542659858185228498291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69614056879810913637997721 52210542659858185228498291)
      ·
        refine ⟨78315813989787277842747437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52210542659858185228498291 78315813989787277842747437)
        ·
          refine ⟨29368430246170229191030289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78315813989787277842747437 29368430246170229191030289)
          ·
            refine ⟨22026322684627671893272717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29368430246170229191030289 22026322684627671893272717)
            ·
              refine ⟨8259871006735376959977269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22026322684627671893272717 8259871006735376959977269)
              ·
                refine ⟨774362906881441589997869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8259871006735376959977269 774362906881441589997869)
                ·
                  refine ⟨290386090080540596249201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 774362906881441589997869 290386090080540596249201)
                  ·
                    rfl

theorem cell21_1272431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 3].length) (baseStart_1272431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1272431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1272431 prefixEnd_1272431 := by exact prefixLift 1272431
  have htrace : WordTrace (prefixWord ++ tailWord_1272431) baseStart_1272431 baseEnd_1272431 := by
    simpa [prefixWord, tailWord_1272431, baseEnd_1272431] using wordTrace_append hprefix tailTrace_1272431
  have hstable : (prefixWord ++ tailWord_1272431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272431).length < 2 ^ (prefixWord ++ tailWord_1272431).sum := by decide
  have hdescent : baseEnd_1272431 < baseStart_1272431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272476 : List Nat := [2, 2, 3, 2, 2, 2, 1, 7]
def baseStart_1272476 : Nat := 118140960795 + 1272476 * 2 ^ 59
def prefixEnd_1272476 : Nat := 4983230072969 + 3 ^ 40 * 1272476 * 2
def baseEnd_1272476 : Nat := 96798786564543505999703

theorem tailTrace_1272476 : CollatzResearch.WordTrace tailWord_1272476 prefixEnd_1272476 96798786564543505999703 := by
  unfold tailWord_1272476
  simp only [CollatzResearch.WordTrace]
  refine ⟨23205506269022124222026641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30940675025362832296035521 23205506269022124222026641)
  ·
    refine ⟨17404129701766593166519981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23205506269022124222026641 17404129701766593166519981)
    ·
      refine ⟨6526548638162472437444993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17404129701766593166519981 6526548638162472437444993)
      ·
        refine ⟨4894911478621854328083745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6526548638162472437444993 4894911478621854328083745)
        ·
          refine ⟨3671183608966390746062809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4894911478621854328083745 3671183608966390746062809)
          ·
            refine ⟨2753387706724793059547107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3671183608966390746062809 2753387706724793059547107)
            ·
              refine ⟨4130081560087189589320661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753387706724793059547107 4130081560087189589320661)
              ·
                refine ⟨96798786564543505999703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4130081560087189589320661 96798786564543505999703)
                ·
                  rfl

theorem cell21_1272476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 7].length) (baseStart_1272476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1272476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1272476 prefixEnd_1272476 := by exact prefixLift 1272476
  have htrace : WordTrace (prefixWord ++ tailWord_1272476) baseStart_1272476 baseEnd_1272476 := by
    simpa [prefixWord, tailWord_1272476, baseEnd_1272476] using wordTrace_append hprefix tailTrace_1272476
  have hstable : (prefixWord ++ tailWord_1272476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272476).length < 2 ^ (prefixWord ++ tailWord_1272476).sum := by decide
  have hdescent : baseEnd_1272476 < baseStart_1272476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272513 : List Nat := [1, 2, 6, 2, 1, 2, 2, 1, 4]
def baseStart_1272513 : Nat := 118140960795 + 1272513 * 2 ^ 59
def prefixEnd_1272513 : Nat := 4983230072969 + 3 ^ 40 * 1272513 * 2
def baseEnd_1272513 : Nat := 290404803597726675882367

theorem tailTrace_1272513 : CollatzResearch.WordTrace tailWord_1272513 prefixEnd_1272513 290404803597726675882367 := by
  unfold tailWord_1272513
  simp only [CollatzResearch.WordTrace]
  refine ⟨46412362038910203763150193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30941574692606802508766795 46412362038910203763150193)
  ·
    refine ⟨34809271529182652822362645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46412362038910203763150193 34809271529182652822362645)
    ·
      refine ⟨1631684602930436851048249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34809271529182652822362645 1631684602930436851048249)
      ·
        refine ⟨1223763452197827638286187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1631684602930436851048249 1223763452197827638286187)
        ·
          refine ⟨1835645178296741457429281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1223763452197827638286187 1835645178296741457429281)
          ·
            refine ⟨1376733883722556093071961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1835645178296741457429281 1376733883722556093071961)
            ·
              refine ⟨1032550412791917069803971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1376733883722556093071961 1032550412791917069803971)
              ·
                refine ⟨1548825619187875604705957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1032550412791917069803971 1548825619187875604705957)
                ·
                  refine ⟨290404803597726675882367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1548825619187875604705957 290404803597726675882367)
                  ·
                    rfl

theorem cell21_1272513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 4].length) (baseStart_1272513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1272513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1272513 prefixEnd_1272513 := by exact prefixLift 1272513
  have htrace : WordTrace (prefixWord ++ tailWord_1272513) baseStart_1272513 baseEnd_1272513 := by
    simpa [prefixWord, tailWord_1272513, baseEnd_1272513] using wordTrace_append hprefix tailTrace_1272513
  have hstable : (prefixWord ++ tailWord_1272513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272513).length < 2 ^ (prefixWord ++ tailWord_1272513).sum := by decide
  have hdescent : baseEnd_1272513 < baseStart_1272513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272535 : List Nat := [1, 1, 3, 2, 1, 4, 2, 7]
def baseStart_1272535 : Nat := 118140960795 + 1272535 * 2 ^ 59
def prefixEnd_1272535 : Nat := 4983230072969 + 3 ^ 40 * 1272535 * 2
def baseEnd_1272535 : Nat := 96803274765819842171885

theorem tailTrace_1272535 : CollatzResearch.WordTrace tailWord_1272535 prefixEnd_1272535 96803274765819842171885 := by
  unfold tailWord_1272535
  simp only [CollatzResearch.WordTrace]
  refine ⟨46413164444830501520451059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30942109629887001013634039 46413164444830501520451059)
  ·
    refine ⟨69619746667245752280676589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46413164444830501520451059 69619746667245752280676589)
    ·
      refine ⟨26107405000217157105253721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69619746667245752280676589 26107405000217157105253721)
      ·
        refine ⟨19580553750162867828940291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26107405000217157105253721 19580553750162867828940291)
        ·
          refine ⟨29370830625244301743410437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19580553750162867828940291 29370830625244301743410437)
          ·
            refine ⟨5507030742233306576889457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29370830625244301743410437 5507030742233306576889457)
            ·
              refine ⟨4130273056674979932667093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5507030742233306576889457 4130273056674979932667093)
              ·
                refine ⟨96803274765819842171885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4130273056674979932667093 96803274765819842171885)
                ·
                  rfl

theorem cell21_1272535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 7].length) (baseStart_1272535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1272535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1272535 prefixEnd_1272535 := by exact prefixLift 1272535
  have htrace : WordTrace (prefixWord ++ tailWord_1272535) baseStart_1272535 baseEnd_1272535 := by
    simpa [prefixWord, tailWord_1272535, baseEnd_1272535] using wordTrace_append hprefix tailTrace_1272535
  have hstable : (prefixWord ++ tailWord_1272535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272535).length < 2 ^ (prefixWord ++ tailWord_1272535).sum := by decide
  have hdescent : baseEnd_1272535 < baseStart_1272535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272552 : List Nat := [2, 1, 4, 1, 5, 8]
def baseStart_1272552 : Nat := 118140960795 + 1272552 * 2 ^ 59
def prefixEnd_1272552 : Nat := 4983230072969 + 3 ^ 40 * 1272552 * 2
def baseEnd_1272552 : Nat := 10756063108484121286381

theorem tailTrace_1272552 : CollatzResearch.WordTrace tailWord_1272552 prefixEnd_1272552 10756063108484121286381 := by
  unfold tailWord_1272552
  simp only [CollatzResearch.WordTrace]
  refine ⟨23206892242884456711909955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30942522990512608949213273 23206892242884456711909955)
  ·
    refine ⟨34810338364326685067864933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23206892242884456711909955 34810338364326685067864933)
    ·
      refine ⟨6526938443311253450224675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34810338364326685067864933 6526938443311253450224675)
      ·
        refine ⟨9790407664966880175337013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6526938443311253450224675 9790407664966880175337013)
        ·
          refine ⟨917850718590645016437845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9790407664966880175337013 917850718590645016437845)
          ·
            refine ⟨10756063108484121286381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 917850718590645016437845 10756063108484121286381)
            ·
              rfl

theorem cell21_1272552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 8].length) (baseStart_1272552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1272552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1272552 prefixEnd_1272552 := by exact prefixLift 1272552
  have htrace : WordTrace (prefixWord ++ tailWord_1272552) baseStart_1272552 baseEnd_1272552 := by
    simpa [prefixWord, tailWord_1272552, baseEnd_1272552] using wordTrace_append hprefix tailTrace_1272552
  have hstable : (prefixWord ++ tailWord_1272552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272552).length < 2 ^ (prefixWord ++ tailWord_1272552).sum := by decide
  have hdescent : baseEnd_1272552 < baseStart_1272552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272583 : List Nat := [1, 1, 4, 4, 1, 2, 1, 2, 5]
def baseStart_1272583 : Nat := 118140960795 + 1272583 * 2 ^ 59
def prefixEnd_1272583 : Nat := 4983230072969 + 3 ^ 40 * 1272583 * 2
def baseEnd_1272583 : Nat := 290420778551422109715557

theorem tailTrace_1272583 : CollatzResearch.WordTrace tailWord_1272583 prefixEnd_1272583 290420778551422109715557 := by
  unfold tailWord_1272583
  simp only [CollatzResearch.WordTrace]
  refine ⟨46414915148656605718198403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30943276765771070478798935 46414915148656605718198403)
  ·
    refine ⟨69622372722984908577297605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46414915148656605718198403 69622372722984908577297605)
    ·
      refine ⟨13054194885559670358243301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69622372722984908577297605 13054194885559670358243301)
      ·
        refine ⟨2447661541042438192170619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13054194885559670358243301 2447661541042438192170619)
        ·
          refine ⟨3671492311563657288255929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2447661541042438192170619 3671492311563657288255929)
          ·
            refine ⟨2753619233672742966191947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3671492311563657288255929 2753619233672742966191947)
            ·
              refine ⟨4130428850509114449287921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753619233672742966191947 4130428850509114449287921)
              ·
                refine ⟨3097821637881835836965941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4130428850509114449287921 3097821637881835836965941)
                ·
                  refine ⟨290420778551422109715557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3097821637881835836965941 290420778551422109715557)
                  ·
                    rfl

theorem cell21_1272583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 5].length) (baseStart_1272583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1272583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1272583 prefixEnd_1272583 := by exact prefixLift 1272583
  have htrace : WordTrace (prefixWord ++ tailWord_1272583) baseStart_1272583 baseEnd_1272583 := by
    simpa [prefixWord, tailWord_1272583, baseEnd_1272583] using wordTrace_append hprefix tailTrace_1272583
  have hstable : (prefixWord ++ tailWord_1272583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272583).length < 2 ^ (prefixWord ++ tailWord_1272583).sum := by decide
  have hdescent : baseEnd_1272583 < baseStart_1272583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272656 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 6]
def baseStart_1272656 : Nat := 118140960795 + 1272656 * 2 ^ 59
def prefixEnd_1272656 : Nat := 4983230072969 + 3 ^ 40 * 1272656 * 2
def baseEnd_1272656 : Nat := 290437438145990204998741

theorem tailTrace_1272656 : CollatzResearch.WordTrace tailWord_1272656 prefixEnd_1272656 290437438145990204998741 := by
  unfold tailWord_1272656
  simp only [CollatzResearch.WordTrace]
  refine ⟨23208788838696069592802911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30945051784928092790403881 23208788838696069592802911)
  ·
    refine ⟨34813183258044104389204367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23208788838696069592802911 34813183258044104389204367)
    ·
      refine ⟨52219774887066156583806551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34813183258044104389204367 52219774887066156583806551)
      ·
        refine ⟨78329662330599234875709827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52219774887066156583806551 78329662330599234875709827)
        ·
          refine ⟨117494493495898852313564741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78329662330599234875709827 117494493495898852313564741)
          ·
            refine ⟨22030217530481034808793389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117494493495898852313564741 22030217530481034808793389)
            ·
              refine ⟨8261331573930388053297521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22030217530481034808793389 8261331573930388053297521)
              ·
                refine ⟨6195998680447791039973141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8261331573930388053297521 6195998680447791039973141)
                ·
                  refine ⟨290437438145990204998741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6195998680447791039973141 290437438145990204998741)
                  ·
                    rfl

theorem cell21_1272656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_1272656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1272656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1272656 prefixEnd_1272656 := by exact prefixLift 1272656
  have htrace : WordTrace (prefixWord ++ tailWord_1272656) baseStart_1272656 baseEnd_1272656 := by
    simpa [prefixWord, tailWord_1272656, baseEnd_1272656] using wordTrace_append hprefix tailTrace_1272656
  have hstable : (prefixWord ++ tailWord_1272656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272656).length < 2 ^ (prefixWord ++ tailWord_1272656).sum := by decide
  have hdescent : baseEnd_1272656 < baseStart_1272656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272690 : List Nat := [3, 2, 1, 2, 1, 1, 6, 1, 4]
def baseStart_1272690 : Nat := 118140960795 + 1272690 * 2 ^ 59
def prefixEnd_1272690 : Nat := 4983230072969 + 3 ^ 40 * 1272690 * 2
def baseEnd_1272690 : Nat := 290445197409213701432005

theorem tailTrace_1272690 : CollatzResearch.WordTrace tailWord_1272690 prefixEnd_1272690 290445197409213701432005 := by
  unfold tailWord_1272690
  simp only [CollatzResearch.WordTrace]
  refine ⟨11604704439817240748085881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30945878506179308661562349 11604704439817240748085881)
  ·
    refine ⟨8703528329862930561064411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11604704439817240748085881 8703528329862930561064411)
    ·
      refine ⟨13055292494794395841596617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8703528329862930561064411 13055292494794395841596617)
      ·
        refine ⟨9791469371095796881197463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13055292494794395841596617 9791469371095796881197463)
        ·
          refine ⟨14687204056643695321796195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9791469371095796881197463 14687204056643695321796195)
          ·
            refine ⟨22030806084965542982694293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14687204056643695321796195 22030806084965542982694293)
            ·
              refine ⟨1032694035232759827313795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22030806084965542982694293 1032694035232759827313795)
              ·
                refine ⟨1549041052849139740970693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1032694035232759827313795 1549041052849139740970693)
                ·
                  refine ⟨290445197409213701432005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1549041052849139740970693 290445197409213701432005)
                  ·
                    rfl

theorem cell21_1272690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_1272690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1272690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1272690 prefixEnd_1272690 := by exact prefixLift 1272690
  have htrace : WordTrace (prefixWord ++ tailWord_1272690) baseStart_1272690 baseEnd_1272690 := by
    simpa [prefixWord, tailWord_1272690, baseEnd_1272690] using wordTrace_append hprefix tailTrace_1272690
  have hstable : (prefixWord ++ tailWord_1272690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272690).length < 2 ^ (prefixWord ++ tailWord_1272690).sum := by decide
  have hdescent : baseEnd_1272690 < baseStart_1272690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272794 : List Nat := [3, 1, 1, 2, 4, 1, 1, 3, 5]
def baseStart_1272794 : Nat := 118140960795 + 1272794 * 2 ^ 59
def prefixEnd_1272794 : Nat := 4983230072969 + 3 ^ 40 * 1272794 * 2
def baseEnd_1272794 : Nat := 290468931626132631698459

theorem tailTrace_1272794 : CollatzResearch.WordTrace tailWord_1272794 prefixEnd_1272794 290468931626132631698459 := by
  unfold tailWord_1272794
  simp only [CollatzResearch.WordTrace]
  refine ⟨11605652737723047188532359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30948407300594792502752957 11605652737723047188532359)
  ·
    refine ⟨17408479106584570782798539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11605652737723047188532359 17408479106584570782798539)
    ·
      refine ⟨26112718659876856174197809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17408479106584570782798539 26112718659876856174197809)
      ·
        refine ⟨19584538994907642130648357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26112718659876856174197809 19584538994907642130648357)
        ·
          refine ⟨3672101061545182899496567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19584538994907642130648357 3672101061545182899496567)
          ·
            refine ⟨5508151592317774349244851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3672101061545182899496567 5508151592317774349244851)
            ·
              refine ⟨8262227388476661523867277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5508151592317774349244851 8262227388476661523867277)
              ·
                refine ⟨3098335270678748071450229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8262227388476661523867277 3098335270678748071450229)
                ·
                  refine ⟨290468931626132631698459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3098335270678748071450229 290468931626132631698459)
                  ·
                    rfl

theorem cell21_1272794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_1272794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1272794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1272794 prefixEnd_1272794 := by exact prefixLift 1272794
  have htrace : WordTrace (prefixWord ++ tailWord_1272794) baseStart_1272794 baseEnd_1272794 := by
    simpa [prefixWord, tailWord_1272794, baseEnd_1272794] using wordTrace_append hprefix tailTrace_1272794
  have hstable : (prefixWord ++ tailWord_1272794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272794).length < 2 ^ (prefixWord ++ tailWord_1272794).sum := by decide
  have hdescent : baseEnd_1272794 < baseStart_1272794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272814 : List Nat := [4, 1, 2, 1, 5, 1, 2, 5]
def baseStart_1272814 : Nat := 118140960795 + 1272814 * 2 ^ 59
def prefixEnd_1272814 : Nat := 4983230072969 + 3 ^ 40 * 1272814 * 2
def baseEnd_1272814 : Nat := 96824498632872347121695

theorem tailTrace_1272814 : CollatzResearch.WordTrace tailWord_1272814 prefixEnd_1272814 96824498632872347121695 := by
  unfold tailWord_1272814
  simp only [CollatzResearch.WordTrace]
  refine ⟨5802917551352466521232187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30948893607213154779904997 5802917551352466521232187)
  ·
    refine ⟨8704376327028699781848281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5802917551352466521232187 8704376327028699781848281)
    ·
      refine ⟨6528282245271524836386211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8704376327028699781848281 6528282245271524836386211)
      ·
        refine ⟨9792423367907287254579317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6528282245271524836386211 9792423367907287254579317)
        ·
          refine ⟨918039690741308180116811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9792423367907287254579317 918039690741308180116811)
          ·
            refine ⟨1377059536111962270175217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 918039690741308180116811 1377059536111962270175217)
            ·
              refine ⟨1032794652083971702631413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1377059536111962270175217 1032794652083971702631413)
              ·
                refine ⟨96824498632872347121695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1032794652083971702631413 96824498632872347121695)
                ·
                  rfl

theorem cell21_1272814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_1272814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1272814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1272814 prefixEnd_1272814 := by exact prefixLift 1272814
  have htrace : WordTrace (prefixWord ++ tailWord_1272814) baseStart_1272814 baseEnd_1272814 := by
    simpa [prefixWord, tailWord_1272814, baseEnd_1272814] using wordTrace_append hprefix tailTrace_1272814
  have hstable : (prefixWord ++ tailWord_1272814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272814).length < 2 ^ (prefixWord ++ tailWord_1272814).sum := by decide
  have hdescent : baseEnd_1272814 < baseStart_1272814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272820 : List Nat := [2, 6, 2, 1, 1, 2, 1, 3, 3]
def baseStart_1272820 : Nat := 118140960795 + 1272820 * 2 ^ 59
def prefixEnd_1272820 : Nat := 4983230072969 + 3 ^ 40 * 1272820 * 2
def baseEnd_1272820 : Nat := 290474865180362364265073

theorem tailTrace_1272820 : CollatzResearch.WordTrace tailWord_1272820 prefixEnd_1272820 290474865180362364265073 := by
  unfold tailWord_1272820
  simp only [CollatzResearch.WordTrace]
  refine ⟨23211779624398997597287957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30949039499198663463050609 23211779624398997597287957)
  ·
    refine ⟨1088052169893703012372873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23211779624398997597287957 1088052169893703012372873)
    ·
      refine ⟨816039127420277259279655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1088052169893703012372873 816039127420277259279655)
      ·
        refine ⟨1224058691130415888919483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 816039127420277259279655 1224058691130415888919483)
        ·
          refine ⟨1836088036695623833379225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1224058691130415888919483 1836088036695623833379225)
          ·
            refine ⟨1377066027521717875034419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1836088036695623833379225 1377066027521717875034419)
            ·
              refine ⟨2065599041282576812551629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1377066027521717875034419 2065599041282576812551629)
              ·
                refine ⟨774599640480966304706861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2065599041282576812551629 774599640480966304706861)
                ·
                  refine ⟨290474865180362364265073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 774599640480966304706861 290474865180362364265073)
                  ·
                    rfl

theorem cell21_1272820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_1272820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1272820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1272820 prefixEnd_1272820 := by exact prefixLift 1272820
  have htrace : WordTrace (prefixWord ++ tailWord_1272820) baseStart_1272820 baseEnd_1272820 := by
    simpa [prefixWord, tailWord_1272820, baseEnd_1272820] using wordTrace_append hprefix tailTrace_1272820
  have hstable : (prefixWord ++ tailWord_1272820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272820).length < 2 ^ (prefixWord ++ tailWord_1272820).sum := by decide
  have hdescent : baseEnd_1272820 < baseStart_1272820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272828 : List Nat := [2, 2, 2, 1, 2, 5, 1, 3, 3]
def baseStart_1272828 : Nat := 118140960795 + 1272828 * 2 ^ 59
def prefixEnd_1272828 : Nat := 4983230072969 + 3 ^ 40 * 1272828 * 2
def baseEnd_1272828 : Nat := 290476690889356128131723

theorem tailTrace_1272828 : CollatzResearch.WordTrace tailWord_1272828 prefixEnd_1272828 290476690889356128131723 := by
  unfold tailWord_1272828
  simp only [CollatzResearch.WordTrace]
  refine ⟨23211925516384506280433569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30949234021846008373911425 23211925516384506280433569)
  ·
    refine ⟨17408944137288379710325177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23211925516384506280433569 17408944137288379710325177)
    ·
      refine ⟨13056708102966284782743883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17408944137288379710325177 13056708102966284782743883)
      ·
        refine ⟨19585062154449427174115825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13056708102966284782743883 19585062154449427174115825)
        ·
          refine ⟨14688796615837070380586869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19585062154449427174115825 14688796615837070380586869)
          ·
            refine ⟨1377074682734725348180019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14688796615837070380586869 1377074682734725348180019)
            ·
              refine ⟨2065612024102088022270029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1377074682734725348180019 2065612024102088022270029)
              ·
                refine ⟨774604509038283008351261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2065612024102088022270029 774604509038283008351261)
                ·
                  refine ⟨290476690889356128131723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 774604509038283008351261 290476690889356128131723)
                  ·
                    rfl

theorem cell21_1272828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 3].length) (baseStart_1272828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1272828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1272828 prefixEnd_1272828 := by exact prefixLift 1272828
  have htrace : WordTrace (prefixWord ++ tailWord_1272828) baseStart_1272828 baseEnd_1272828 := by
    simpa [prefixWord, tailWord_1272828, baseEnd_1272828] using wordTrace_append hprefix tailTrace_1272828
  have hstable : (prefixWord ++ tailWord_1272828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272828).length < 2 ^ (prefixWord ++ tailWord_1272828).sum := by decide
  have hdescent : baseEnd_1272828 < baseStart_1272828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272929 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 7]
def baseStart_1272929 : Nat := 118140960795 + 1272929 * 2 ^ 59
def prefixEnd_1272929 : Nat := 4983230072969 + 3 ^ 40 * 1272929 * 2
def baseEnd_1272929 : Nat := 290499740465402396948183

theorem tailTrace_1272929 : CollatzResearch.WordTrace tailWord_1272929 prefixEnd_1272929 290499740465402396948183 := by
  unfold tailWord_1272929
  simp only [CollatzResearch.WordTrace]
  refine ⟨46427534805403106810293841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30951689870268737873529227 46427534805403106810293841)
  ·
    refine ⟨34820651104052330107720381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46427534805403106810293841 34820651104052330107720381)
    ·
      refine ⟨13057744164019623790395143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34820651104052330107720381 13057744164019623790395143)
      ·
        refine ⟨19586616246029435685592715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13057744164019623790395143 19586616246029435685592715)
        ·
          refine ⟨29379924369044153528389073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19586616246029435685592715 29379924369044153528389073)
          ·
            refine ⟨22034943276783115146291805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29379924369044153528389073 22034943276783115146291805)
            ·
              refine ⟨8263103728793668179859427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22034943276783115146291805 8263103728793668179859427)
              ·
                refine ⟨12394655593190502269789141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8263103728793668179859427 12394655593190502269789141)
                ·
                  refine ⟨290499740465402396948183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12394655593190502269789141 290499740465402396948183)
                  ·
                    rfl

theorem cell21_1272929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_1272929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1272929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1272929 prefixEnd_1272929 := by exact prefixLift 1272929
  have htrace : WordTrace (prefixWord ++ tailWord_1272929) baseStart_1272929 baseEnd_1272929 := by
    simpa [prefixWord, tailWord_1272929, baseEnd_1272929] using wordTrace_append hprefix tailTrace_1272929
  have hstable : (prefixWord ++ tailWord_1272929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272929).length < 2 ^ (prefixWord ++ tailWord_1272929).sum := by decide
  have hdescent : baseEnd_1272929 < baseStart_1272929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273014 : List Nat := [5, 1, 3, 2, 2, 1, 1, 1, 5]
def baseStart_1273014 : Nat := 118140960795 + 1273014 * 2 ^ 59
def prefixEnd_1273014 : Nat := 4983230072969 + 3 ^ 40 * 1273014 * 2
def baseEnd_1273014 : Nat := 290519138623461138031343

theorem tailTrace_1273014 : CollatzResearch.WordTrace tailWord_1273014 prefixEnd_1273014 290519138623461138031343 := by
  unfold tailWord_1273014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2901914688130947895446131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30953756673396777551425397 2901914688130947895446131)
  ·
    refine ⟨4352872032196421843169197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2901914688130947895446131 4352872032196421843169197)
    ·
      refine ⟨1632327012073658191188449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4352872032196421843169197 1632327012073658191188449)
      ·
        refine ⟨1224245259055243643391337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1632327012073658191188449 1224245259055243643391337)
        ·
          refine ⟨918183944291432732543503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1224245259055243643391337 918183944291432732543503)
          ·
            refine ⟨1377275916437149098815255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 918183944291432732543503 1377275916437149098815255)
            ·
              refine ⟨2065913874655723648222883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1377275916437149098815255 2065913874655723648222883)
              ·
                refine ⟨3098870811983585472334325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2065913874655723648222883 3098870811983585472334325)
                ·
                  refine ⟨290519138623461138031343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3098870811983585472334325 290519138623461138031343)
                  ·
                    rfl

theorem cell21_1273014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_1273014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1273014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1273014 prefixEnd_1273014 := by exact prefixLift 1273014
  have htrace : WordTrace (prefixWord ++ tailWord_1273014) baseStart_1273014 baseEnd_1273014 := by
    simpa [prefixWord, tailWord_1273014, baseEnd_1273014] using wordTrace_append hprefix tailTrace_1273014
  have hstable : (prefixWord ++ tailWord_1273014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273014).length < 2 ^ (prefixWord ++ tailWord_1273014).sum := by decide
  have hdescent : baseEnd_1273014 < baseStart_1273014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273028 : List Nat := [2, 3, 3, 1, 4, 1, 2, 1, 4]
def baseStart_1273028 : Nat := 118140960795 + 1273028 * 2 ^ 59
def prefixEnd_1273028 : Nat := 4983230072969 + 3 ^ 40 * 1273028 * 2
def baseEnd_1273028 : Nat := 290522333614200224797981

theorem tailTrace_1273028 : CollatzResearch.WordTrace tailWord_1273028 prefixEnd_1273028 290522333614200224797981 := by
  unfold tailWord_1273028
  simp only [CollatzResearch.WordTrace]
  refine ⟨23215572816022223359073869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30954097088029631145431825 23215572816022223359073869)
  ·
    refine ⟨8705839806008333759652701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23215572816022223359073869 8705839806008333759652701)
    ·
      refine ⟨3264689927253125159869763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8705839806008333759652701 3264689927253125159869763)
      ·
        refine ⟨4897034890879687739804645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3264689927253125159869763 4897034890879687739804645)
        ·
          refine ⟨918194042039941451213371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4897034890879687739804645 918194042039941451213371)
          ·
            refine ⟨1377291063059912176820057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 918194042039941451213371 1377291063059912176820057)
            ·
              refine ⟨1032968297294934132615043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1377291063059912176820057 1032968297294934132615043)
              ·
                refine ⟨1549452445942401198922565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1032968297294934132615043 1549452445942401198922565)
                ·
                  refine ⟨290522333614200224797981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1549452445942401198922565 290522333614200224797981)
                  ·
                    rfl

theorem cell21_1273028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_1273028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1273028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1273028 prefixEnd_1273028 := by exact prefixLift 1273028
  have htrace : WordTrace (prefixWord ++ tailWord_1273028) baseStart_1273028 baseEnd_1273028 := by
    simpa [prefixWord, tailWord_1273028, baseEnd_1273028] using wordTrace_append hprefix tailTrace_1273028
  have hstable : (prefixWord ++ tailWord_1273028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273028).length < 2 ^ (prefixWord ++ tailWord_1273028).sum := by decide
  have hdescent : baseEnd_1273028 < baseStart_1273028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273081 : List Nat := [1, 2, 1, 3, 1, 1, 4, 3, 5]
def baseStart_1273081 : Nat := 118140960795 + 1273081 * 2 ^ 59
def prefixEnd_1273081 : Nat := 4983230072969 + 3 ^ 40 * 1273081 * 2
def baseEnd_1273081 : Nat := 290534428936283910414539

theorem tailTrace_1273081 : CollatzResearch.WordTrace tailWord_1273081 prefixEnd_1273081 290534428936283910414539 := by
  unfold tailWord_1273081
  simp only [CollatzResearch.WordTrace]
  refine ⟨46433078700852436769827097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30955385800568291179884731 46433078700852436769827097)
  ·
    refine ⟨34824809025639327577370323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46433078700852436769827097 34824809025639327577370323)
    ·
      refine ⟨52237213538458991366055485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34824809025639327577370323 52237213538458991366055485)
      ·
        refine ⟨19588955076922121762270807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52237213538458991366055485 19588955076922121762270807)
        ·
          refine ⟨29383432615383182643406211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19588955076922121762270807 29383432615383182643406211)
          ·
            refine ⟨44075148923074773965109317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29383432615383182643406211 44075148923074773965109317)
            ·
              refine ⟨8264090423076520118457997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44075148923074773965109317 8264090423076520118457997)
              ·
                refine ⟨3099033908653695044421749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8264090423076520118457997 3099033908653695044421749)
                ·
                  refine ⟨290534428936283910414539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3099033908653695044421749 290534428936283910414539)
                  ·
                    rfl

theorem cell21_1273081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_1273081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1273081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1273081 prefixEnd_1273081 := by exact prefixLift 1273081
  have htrace : WordTrace (prefixWord ++ tailWord_1273081) baseStart_1273081 baseEnd_1273081 := by
    simpa [prefixWord, tailWord_1273081, baseEnd_1273081] using wordTrace_append hprefix tailTrace_1273081
  have hstable : (prefixWord ++ tailWord_1273081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273081).length < 2 ^ (prefixWord ++ tailWord_1273081).sum := by decide
  have hdescent : baseEnd_1273081 < baseStart_1273081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273084 : List Nat := [2, 2, 2, 1, 5, 2, 1, 6]
def baseStart_1273084 : Nat := 118140960795 + 1273084 * 2 ^ 59
def prefixEnd_1273084 : Nat := 4983230072969 + 3 ^ 40 * 1273084 * 2
def baseEnd_1273084 : Nat := 96845037859052190621511

theorem tailTrace_1273084 : CollatzResearch.WordTrace tailWord_1273084 prefixEnd_1273084 96845037859052190621511 := by
  unfold tailWord_1273084
  simp only [CollatzResearch.WordTrace]
  refine ⟨23216594059920784141093153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30955458746561045521457537 23216594059920784141093153)
  ·
    refine ⟨17412445544940588105819865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23216594059920784141093153 17412445544940588105819865)
    ·
      refine ⟨13059334158705441079364899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17412445544940588105819865 13059334158705441079364899)
      ·
        refine ⟨19589001238058161619047349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13059334158705441079364899 19589001238058161619047349)
        ·
          refine ⟨1836468866067952651785689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19589001238058161619047349 1836468866067952651785689)
          ·
            refine ⟨1377351649550964488839267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1836468866067952651785689 1377351649550964488839267)
            ·
              refine ⟨2066027474326446733258901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1377351649550964488839267 2066027474326446733258901)
              ·
                refine ⟨96845037859052190621511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2066027474326446733258901 96845037859052190621511)
                ·
                  rfl

theorem cell21_1273084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 6].length) (baseStart_1273084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1273084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1273084 prefixEnd_1273084 := by exact prefixLift 1273084
  have htrace : WordTrace (prefixWord ++ tailWord_1273084) baseStart_1273084 baseEnd_1273084 := by
    simpa [prefixWord, tailWord_1273084, baseEnd_1273084] using wordTrace_append hprefix tailTrace_1273084
  have hstable : (prefixWord ++ tailWord_1273084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273084).length < 2 ^ (prefixWord ++ tailWord_1273084).sum := by decide
  have hdescent : baseEnd_1273084 < baseStart_1273084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273171 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 8]
def baseStart_1273171 : Nat := 118140960795 + 1273171 * 2 ^ 59
def prefixEnd_1273171 : Nat := 4983230072969 + 3 ^ 40 * 1273171 * 2
def baseEnd_1273171 : Nat := 290554968162463753914355

theorem tailTrace_1273171 : CollatzResearch.WordTrace tailWord_1273171 prefixEnd_1273171 290554968162463753914355 := by
  unfold tailWord_1273171
  simp only [CollatzResearch.WordTrace]
  refine ⟨46436361270526382140603367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30957574180350921427068911 46436361270526382140603367)
  ·
    refine ⟨69654541905789573210905051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46436361270526382140603367 69654541905789573210905051)
    ·
      refine ⟨104481812858684359816357577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69654541905789573210905051 104481812858684359816357577)
      ·
        refine ⟨78361359644013269862268183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104481812858684359816357577 78361359644013269862268183)
        ·
          refine ⟨117542039466019904793402275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78361359644013269862268183 117542039466019904793402275)
          ·
            refine ⟨176313059199029857190103413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117542039466019904793402275 176313059199029857190103413)
            ·
              refine ⟨16529349299909049111572195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 176313059199029857190103413 16529349299909049111572195)
              ·
                refine ⟨24794023949863573667358293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16529349299909049111572195 24794023949863573667358293)
                ·
                  refine ⟨290554968162463753914355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24794023949863573667358293 290554968162463753914355)
                  ·
                    rfl

theorem cell21_1273171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 8].length) (baseStart_1273171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1273171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1273171 prefixEnd_1273171 := by exact prefixLift 1273171
  have htrace : WordTrace (prefixWord ++ tailWord_1273171) baseStart_1273171 baseEnd_1273171 := by
    simpa [prefixWord, tailWord_1273171, baseEnd_1273171] using wordTrace_append hprefix tailTrace_1273171
  have hstable : (prefixWord ++ tailWord_1273171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273171).length < 2 ^ (prefixWord ++ tailWord_1273171).sum := by decide
  have hdescent : baseEnd_1273171 < baseStart_1273171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273188 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 6]
def baseStart_1273188 : Nat := 118140960795 + 1273188 * 2 ^ 59
def prefixEnd_1273188 : Nat := 4983230072969 + 3 ^ 40 * 1273188 * 2
def baseEnd_1273188 : Nat := 290558847794075502130987

theorem tailTrace_1273188 : CollatzResearch.WordTrace tailWord_1273188 prefixEnd_1273188 290558847794075502130987 := by
  unfold tailWord_1273188
  simp only [CollatzResearch.WordTrace]
  refine ⟨23218490655732397021986109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30957987540976529362648145 23218490655732397021986109)
  ·
    refine ⟨8706933995899648883244791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23218490655732397021986109 8706933995899648883244791)
    ·
      refine ⟨13060400993849473324867187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8706933995899648883244791 13060400993849473324867187)
      ·
        refine ⟨19590601490774209987300781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13060400993849473324867187 19590601490774209987300781)
        ·
          refine ⟨7346475559040328745237793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19590601490774209987300781 7346475559040328745237793)
          ·
            refine ⟨5509856669280246558928345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7346475559040328745237793 5509856669280246558928345)
            ·
              refine ⟨4132392501960184919196259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5509856669280246558928345 4132392501960184919196259)
              ·
                refine ⟨6198588752940277378794389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4132392501960184919196259 6198588752940277378794389)
                ·
                  refine ⟨290558847794075502130987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6198588752940277378794389 290558847794075502130987)
                  ·
                    rfl

theorem cell21_1273188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_1273188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1273188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1273188 prefixEnd_1273188 := by exact prefixLift 1273188
  have htrace : WordTrace (prefixWord ++ tailWord_1273188) baseStart_1273188 baseEnd_1273188 := by
    simpa [prefixWord, tailWord_1273188, baseEnd_1273188] using wordTrace_append hprefix tailTrace_1273188
  have hstable : (prefixWord ++ tailWord_1273188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273188).length < 2 ^ (prefixWord ++ tailWord_1273188).sum := by decide
  have hdescent : baseEnd_1273188 < baseStart_1273188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273191 : List Nat := [1, 1, 5, 1, 4, 2, 1, 1, 5]
def baseStart_1273191 : Nat := 118140960795 + 1273191 * 2 ^ 59
def prefixEnd_1273191 : Nat := 4983230072969 + 3 ^ 40 * 1273191 * 2
def baseEnd_1273191 : Nat := 290559532434948163580981

theorem tailTrace_1273191 : CollatzResearch.WordTrace tailWord_1273191 prefixEnd_1273191 290559532434948163580981 := by
  unfold tailWord_1273191
  simp only [CollatzResearch.WordTrace]
  refine ⟨46437090730453925556331427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30958060486969283704220951 46437090730453925556331427)
  ·
    refine ⟨69655636095680888334497141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46437090730453925556331427 69655636095680888334497141)
    ·
      refine ⟨6530215883970083281359107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69655636095680888334497141 6530215883970083281359107)
      ·
        refine ⟨9795323825955124922038661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6530215883970083281359107 9795323825955124922038661)
        ·
          refine ⟨1836623217366585922882249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9795323825955124922038661 1836623217366585922882249)
          ·
            refine ⟨1377467413024939442161687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1836623217366585922882249 1377467413024939442161687)
            ·
              refine ⟨2066201119537409163242531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1377467413024939442161687 2066201119537409163242531)
              ·
                refine ⟨3099301679306113744863797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2066201119537409163242531 3099301679306113744863797)
                ·
                  refine ⟨290559532434948163580981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3099301679306113744863797 290559532434948163580981)
                  ·
                    rfl

theorem cell21_1273191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 5].length) (baseStart_1273191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1273191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1273191 prefixEnd_1273191 := by exact prefixLift 1273191
  have htrace : WordTrace (prefixWord ++ tailWord_1273191) baseStart_1273191 baseEnd_1273191 := by
    simpa [prefixWord, tailWord_1273191, baseEnd_1273191] using wordTrace_append hprefix tailTrace_1273191
  have hstable : (prefixWord ++ tailWord_1273191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273191).length < 2 ^ (prefixWord ++ tailWord_1273191).sum := by decide
  have hdescent : baseEnd_1273191 < baseStart_1273191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273284 : List Nat := [2, 3, 3, 2, 1, 2, 2, 3, 3]
def baseStart_1273284 : Nat := 118140960795 + 1273284 * 2 ^ 59
def prefixEnd_1273284 : Nat := 4983230072969 + 3 ^ 40 * 1273284 * 2
def baseEnd_1273284 : Nat := 290580756302000668530791

theorem tailTrace_1273284 : CollatzResearch.WordTrace tailWord_1273284 prefixEnd_1273284 290580756302000668530791 := by
  unfold tailWord_1273284
  simp only [CollatzResearch.WordTrace]
  refine ⟨23220241359558501219733453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30960321812744668292977937 23220241359558501219733453)
  ·
    refine ⟨8707590509834437957400045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23220241359558501219733453 8707590509834437957400045)
    ·
      refine ⟨3265346441187914234025017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8707590509834437957400045 3265346441187914234025017)
      ·
        refine ⟨2449009830890935675518763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3265346441187914234025017 2449009830890935675518763)
        ·
          refine ⟨3673514746336403513278145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2449009830890935675518763 3673514746336403513278145)
          ·
            refine ⟨2755136059752302634958609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3673514746336403513278145 2755136059752302634958609)
            ·
              refine ⟨2066352044814226976218957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2755136059752302634958609 2066352044814226976218957)
              ·
                refine ⟨774882016805335116082109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2066352044814226976218957 774882016805335116082109)
                ·
                  refine ⟨290580756302000668530791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 774882016805335116082109 290580756302000668530791)
                  ·
                    rfl

theorem cell21_1273284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_1273284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1273284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1273284 prefixEnd_1273284 := by exact prefixLift 1273284
  have htrace : WordTrace (prefixWord ++ tailWord_1273284) baseStart_1273284 baseEnd_1273284 := by
    simpa [prefixWord, tailWord_1273284, baseEnd_1273284] using wordTrace_append hprefix tailTrace_1273284
  have hstable : (prefixWord ++ tailWord_1273284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273284).length < 2 ^ (prefixWord ++ tailWord_1273284).sum := by decide
  have hdescent : baseEnd_1273284 < baseStart_1273284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273354 : List Nat := [3, 1, 2, 2, 2, 2, 9]
def baseStart_1273354 : Nat := 118140960795 + 1273354 * 2 ^ 59
def prefixEnd_1273354 : Nat := 4983230072969 + 3 ^ 40 * 1273354 * 2
def baseEnd_1273354 : Nat := 32288525695077344707109

theorem tailTrace_1273354 : CollatzResearch.WordTrace tailWord_1273354 prefixEnd_1273354 32288525695077344707109 := by
  unfold tailWord_1273354
  simp only [CollatzResearch.WordTrace]
  refine ⟨11610758957215851098628779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30962023885908936263010077 11610758957215851098628779)
  ·
    refine ⟨17416138435823776647943169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11610758957215851098628779 17416138435823776647943169)
    ·
      refine ⟨13062103826867832485957377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17416138435823776647943169 13062103826867832485957377)
      ·
        refine ⟨9796577870150874364468033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13062103826867832485957377 9796577870150874364468033)
        ·
          refine ⟨7347433402613155773351025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9796577870150874364468033 7347433402613155773351025)
          ·
            refine ⟨5510575051959866830013269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7347433402613155773351025 5510575051959866830013269)
            ·
              refine ⟨32288525695077344707109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5510575051959866830013269 32288525695077344707109)
              ·
                rfl

theorem cell21_1273354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 9].length) (baseStart_1273354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1273354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1273354 prefixEnd_1273354 := by exact prefixLift 1273354
  have htrace : WordTrace (prefixWord ++ tailWord_1273354) baseStart_1273354 baseEnd_1273354 := by
    simpa [prefixWord, tailWord_1273354, baseEnd_1273354] using wordTrace_append hprefix tailTrace_1273354
  have hstable : (prefixWord ++ tailWord_1273354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273354).length < 2 ^ (prefixWord ++ tailWord_1273354).sum := by decide
  have hdescent : baseEnd_1273354 < baseStart_1273354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273402 : List Nat := [3, 1, 1, 1, 3, 2, 2, 5, 3]
def baseStart_1273402 : Nat := 118140960795 + 1273402 * 2 ^ 59
def prefixEnd_1273402 : Nat := 4983230072969 + 3 ^ 40 * 1273402 * 2
def baseEnd_1273402 : Nat := 290607685509658685563883

theorem tailTrace_1273402 : CollatzResearch.WordTrace tailWord_1273402 prefixEnd_1273402 290607685509658685563883 := by
  unfold tailWord_1273402
  simp only [CollatzResearch.WordTrace]
  refine ⟨11611196633172377148065615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30963191021793005728174973 11611196633172377148065615)
  ·
    refine ⟨17416794949758565722098423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11611196633172377148065615 17416794949758565722098423)
    ·
      refine ⟨26125192424637848583147635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17416794949758565722098423 26125192424637848583147635)
      ·
        refine ⟨39187788636956772874721453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26125192424637848583147635 39187788636956772874721453)
        ·
          refine ⟨14695420738858789828020545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39187788636956772874721453 14695420738858789828020545)
          ·
            refine ⟨11021565554144092371015409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14695420738858789828020545 11021565554144092371015409)
            ·
              refine ⟨8266174165608069278261557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11021565554144092371015409 8266174165608069278261557)
              ·
                refine ⟨774953828025756494837021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8266174165608069278261557 774953828025756494837021)
                ·
                  refine ⟨290607685509658685563883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 774953828025756494837021 290607685509658685563883)
                  ·
                    rfl

theorem cell21_1273402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 3].length) (baseStart_1273402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1273402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1273402 prefixEnd_1273402 := by exact prefixLift 1273402
  have htrace : WordTrace (prefixWord ++ tailWord_1273402) baseStart_1273402 baseEnd_1273402 := by
    simpa [prefixWord, tailWord_1273402, baseEnd_1273402] using wordTrace_append hprefix tailTrace_1273402
  have hstable : (prefixWord ++ tailWord_1273402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273402).length < 2 ^ (prefixWord ++ tailWord_1273402).sum := by decide
  have hdescent : baseEnd_1273402 < baseStart_1273402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273520 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 7]
def baseStart_1273520 : Nat := 118140960795 + 1273520 * 2 ^ 59
def prefixEnd_1273520 : Nat := 4983230072969 + 3 ^ 40 * 1273520 * 2
def baseEnd_1273520 : Nat := 290634614717316702596975

theorem tailTrace_1273520 : CollatzResearch.WordTrace tailWord_1273520 prefixEnd_1273520 290634614717316702596975 := by
  unfold tailWord_1273520
  simp only [CollatzResearch.WordTrace]
  refine ⟨23224545173131007372529007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30966060230841343163372009 23224545173131007372529007)
  ·
    refine ⟨34836817759696511058793511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23224545173131007372529007 34836817759696511058793511)
    ·
      refine ⟨52255226639544766588190267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34836817759696511058793511 52255226639544766588190267)
      ·
        refine ⟨78382839959317149882285401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52255226639544766588190267 78382839959317149882285401)
        ·
          refine ⟨58787129969487862411714051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78382839959317149882285401 58787129969487862411714051)
          ·
            refine ⟨88180694954231793617571077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58787129969487862411714051 88180694954231793617571077)
            ·
              refine ⟨16533880303918461303294577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88180694954231793617571077 16533880303918461303294577)
              ·
                refine ⟨12400410227938845977470933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16533880303918461303294577 12400410227938845977470933)
                ·
                  refine ⟨290634614717316702596975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12400410227938845977470933 290634614717316702596975)
                  ·
                    rfl

theorem cell21_1273520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_1273520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1273520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1273520 prefixEnd_1273520 := by exact prefixLift 1273520
  have htrace : WordTrace (prefixWord ++ tailWord_1273520) baseStart_1273520 baseEnd_1273520 := by
    simpa [prefixWord, tailWord_1273520, baseEnd_1273520] using wordTrace_append hprefix tailTrace_1273520
  have hstable : (prefixWord ++ tailWord_1273520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273520).length < 2 ^ (prefixWord ++ tailWord_1273520).sum := by decide
  have hdescent : baseEnd_1273520 < baseStart_1273520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273644 : List Nat := [2, 2, 1, 1, 1, 5, 3, 2, 4]
def baseStart_1273644 : Nat := 118140960795 + 1273644 * 2 ^ 59
def prefixEnd_1273644 : Nat := 4983230072969 + 3 ^ 40 * 1273644 * 2
def baseEnd_1273644 : Nat := 290662913206720042530055

theorem tailTrace_1273644 : CollatzResearch.WordTrace tailWord_1273644 prefixEnd_1273644 290662913206720042530055 := by
  unfold tailWord_1273644
  simp only [CollatzResearch.WordTrace]
  refine ⟨23226806498906391961285993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30969075331875189281714657 23226806498906391961285993)
  ·
    refine ⟨17420104874179793970964495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23226806498906391961285993 17420104874179793970964495)
    ·
      refine ⟨26130157311269690956446743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17420104874179793970964495 26130157311269690956446743)
      ·
        refine ⟨39195235966904536434670115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26130157311269690956446743 39195235966904536434670115)
        ·
          refine ⟨58792853950356804652005173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39195235966904536434670115 58792853950356804652005173)
          ·
            refine ⟨5511830057845950436125485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58792853950356804652005173 5511830057845950436125485)
            ·
              refine ⟨2066936271692231413547057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5511830057845950436125485 2066936271692231413547057)
              ·
                refine ⟨1550202203769173560160293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2066936271692231413547057 1550202203769173560160293)
                ·
                  refine ⟨290662913206720042530055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1550202203769173560160293 290662913206720042530055)
                  ·
                    rfl

theorem cell21_1273644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_1273644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1273644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1273644 prefixEnd_1273644 := by exact prefixLift 1273644
  have htrace : WordTrace (prefixWord ++ tailWord_1273644) baseStart_1273644 baseEnd_1273644 := by
    simpa [prefixWord, tailWord_1273644, baseEnd_1273644] using wordTrace_append hprefix tailTrace_1273644
  have hstable : (prefixWord ++ tailWord_1273644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273644).length < 2 ^ (prefixWord ++ tailWord_1273644).sum := by decide
  have hdescent : baseEnd_1273644 < baseStart_1273644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273692 : List Nat := [2, 2, 4, 2, 3, 1, 7]
def baseStart_1273692 : Nat := 118140960795 + 1273692 * 2 ^ 59
def prefixEnd_1273692 : Nat := 4983230072969 + 3 ^ 40 * 1273692 * 2
def baseEnd_1273692 : Nat := 32297096384520291747773

theorem tailTrace_1273692 : CollatzResearch.WordTrace tailWord_1273692 prefixEnd_1273692 32297096384520291747773 := by
  unfold tailWord_1273692
  simp only [CollatzResearch.WordTrace]
  refine ⟨23227681850819444060159665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30970242467759258746879553 23227681850819444060159665)
  ·
    refine ⟨17420761388114583045119749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23227681850819444060159665 17420761388114583045119749)
    ·
      refine ⟨3266392760271484320959953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17420761388114583045119749 3266392760271484320959953)
      ·
        refine ⟨2449794570203613240719965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3266392760271484320959953 2449794570203613240719965)
        ·
          refine ⟨918672963826354965269987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2449794570203613240719965 918672963826354965269987)
          ·
            refine ⟨1378009445739532447904981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 918672963826354965269987 1378009445739532447904981)
            ·
              refine ⟨32297096384520291747773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1378009445739532447904981 32297096384520291747773)
              ·
                rfl

theorem cell21_1273692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 7].length) (baseStart_1273692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1273692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1273692 prefixEnd_1273692 := by exact prefixLift 1273692
  have htrace : WordTrace (prefixWord ++ tailWord_1273692) baseStart_1273692 baseEnd_1273692 := by
    simpa [prefixWord, tailWord_1273692, baseEnd_1273692] using wordTrace_append hprefix tailTrace_1273692
  have hstable : (prefixWord ++ tailWord_1273692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273692).length < 2 ^ (prefixWord ++ tailWord_1273692).sum := by decide
  have hdescent : baseEnd_1273692 < baseStart_1273692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273703 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 6]
def baseStart_1273703 : Nat := 118140960795 + 1273703 * 2 ^ 59
def prefixEnd_1273703 : Nat := 4983230072969 + 3 ^ 40 * 1273703 * 2
def baseEnd_1273703 : Nat := 290676377810549051046601

theorem tailTrace_1273703 : CollatzResearch.WordTrace tailWord_1273703 prefixEnd_1273703 290676377810549051046601 := by
  unfold tailWord_1273703
  simp only [CollatzResearch.WordTrace]
  refine ⟨46455764904599036998969763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30970509936399357999313175 46455764904599036998969763)
  ·
    refine ⟨69683647356898555498454645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46455764904599036998969763 69683647356898555498454645)
    ·
      refine ⟨6532841939709239577980123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69683647356898555498454645 6532841939709239577980123)
      ·
        refine ⟨9799262909563859366970185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6532841939709239577980123 9799262909563859366970185)
        ·
          refine ⟨7349447182172894525227639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9799262909563859366970185 7349447182172894525227639)
          ·
            refine ⟨11024170773259341787841459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7349447182172894525227639 11024170773259341787841459)
            ·
              refine ⟨16536256159889012681762189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11024170773259341787841459 16536256159889012681762189)
              ·
                refine ⟨6201096059958379755660821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16536256159889012681762189 6201096059958379755660821)
                ·
                  refine ⟨290676377810549051046601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6201096059958379755660821 290676377810549051046601)
                  ·
                    rfl

theorem cell21_1273703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 6].length) (baseStart_1273703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1273703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1273703 prefixEnd_1273703 := by exact prefixLift 1273703
  have htrace : WordTrace (prefixWord ++ tailWord_1273703) baseStart_1273703 baseEnd_1273703 := by
    simpa [prefixWord, tailWord_1273703, baseEnd_1273703] using wordTrace_append hprefix tailTrace_1273703
  have hstable : (prefixWord ++ tailWord_1273703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273703).length < 2 ^ (prefixWord ++ tailWord_1273703).sum := by decide
  have hdescent : baseEnd_1273703 < baseStart_1273703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273779 : List Nat := [1, 1, 1, 2, 3, 1, 3, 5, 4]
def baseStart_1273779 : Nat := 118140960795 + 1273779 * 2 ^ 59
def prefixEnd_1273779 : Nat := 4983230072969 + 3 ^ 40 * 1273779 * 2
def baseEnd_1273779 : Nat := 290693722045989807779779

theorem tailTrace_1273779 : CollatzResearch.WordTrace tailWord_1273779 prefixEnd_1273779 290693722045989807779779 := by
  unfold tailWord_1273779
  simp only [CollatzResearch.WordTrace]
  refine ⟨46458536852323701978736391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30972357901549134652490927 46458536852323701978736391)
  ·
    refine ⟨69687805278485552968104587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46458536852323701978736391 69687805278485552968104587)
    ·
      refine ⟨104531707917728329452156881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69687805278485552968104587 104531707917728329452156881)
      ·
        refine ⟨78398780938296247089117661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104531707917728329452156881 78398780938296247089117661)
        ·
          refine ⟨29399542851861092658419123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78398780938296247089117661 29399542851861092658419123)
          ·
            refine ⟨44099314277791638987628685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29399542851861092658419123 44099314277791638987628685)
            ·
              refine ⟨16537242854171864620360757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44099314277791638987628685 16537242854171864620360757)
              ·
                refine ⟨1550366517578612308158821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16537242854171864620360757 1550366517578612308158821)
                ·
                  refine ⟨290693722045989807779779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1550366517578612308158821 290693722045989807779779)
                  ·
                    rfl

theorem cell21_1273779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 4].length) (baseStart_1273779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1273779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1273779 prefixEnd_1273779 := by exact prefixLift 1273779
  have htrace : WordTrace (prefixWord ++ tailWord_1273779) baseStart_1273779 baseEnd_1273779 := by
    simpa [prefixWord, tailWord_1273779, baseEnd_1273779] using wordTrace_append hprefix tailTrace_1273779
  have hstable : (prefixWord ++ tailWord_1273779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273779).length < 2 ^ (prefixWord ++ tailWord_1273779).sum := by decide
  have hdescent : baseEnd_1273779 < baseStart_1273779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273813 : List Nat := [1, 3, 2, 3, 2, 3, 1, 2, 4]
def baseStart_1273813 : Nat := 118140960795 + 1273813 * 2 ^ 59
def prefixEnd_1273813 : Nat := 4983230072969 + 3 ^ 40 * 1273813 * 2
def baseEnd_1273813 : Nat := 290701481309213304213043

theorem tailTrace_1273813 : CollatzResearch.WordTrace tailWord_1273813 prefixEnd_1273813 290701481309213304213043 := by
  unfold tailWord_1273813
  simp only [CollatzResearch.WordTrace]
  refine ⟨46459776934200525785474093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30973184622800350523649395 46459776934200525785474093)
  ·
    refine ⟨17422416350325197169552785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46459776934200525785474093 17422416350325197169552785)
    ·
      refine ⟨13066812262743897877164589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17422416350325197169552785 13066812262743897877164589)
      ·
        refine ⟨4900054598528961703936721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13066812262743897877164589 4900054598528961703936721)
        ·
          refine ⟨3675040948896721277952541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4900054598528961703936721 3675040948896721277952541)
          ·
            refine ⟨1378140355836270479232203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3675040948896721277952541 1378140355836270479232203)
            ·
              refine ⟨2067210533754405718848305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1378140355836270479232203 2067210533754405718848305)
              ·
                refine ⟨1550407900315804289136229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2067210533754405718848305 1550407900315804289136229)
                ·
                  refine ⟨290701481309213304213043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1550407900315804289136229 290701481309213304213043)
                  ·
                    rfl

theorem cell21_1273813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_1273813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1273813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1273813 prefixEnd_1273813 := by exact prefixLift 1273813
  have htrace : WordTrace (prefixWord ++ tailWord_1273813) baseStart_1273813 baseEnd_1273813 := by
    simpa [prefixWord, tailWord_1273813, baseEnd_1273813] using wordTrace_append hprefix tailTrace_1273813
  have hstable : (prefixWord ++ tailWord_1273813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273813).length < 2 ^ (prefixWord ++ tailWord_1273813).sum := by decide
  have hdescent : baseEnd_1273813 < baseStart_1273813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
