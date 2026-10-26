import V185TrunkScan23Chunk0963

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5707413 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 11]
def baseStart_5707413 : Nat := 118140960795 + 5707413 * 2 ^ 59
def prefixEnd_5707413 : Nat := 4983230072969 + 3 ^ 40 * 5707413 * 2
def baseEnd_5707413 : Nat := 325627351413287050454399

theorem tailTrace_5707413 : CollatzResearch.WordTrace tailWord_5707413 prefixEnd_5707413 325627351413287050454399 := by
  unfold tailWord_5707413
  simp only [CollatzResearch.WordTrace]
  refine ⟨208166453672024924381814893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138777635781349949587876595 208166453672024924381814893)
  ·
    refine ⟨78062420127009346643180585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208166453672024924381814893 78062420127009346643180585)
    ·
      refine ⟨58546815095257009982385439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78062420127009346643180585 58546815095257009982385439)
      ·
        refine ⟨87820222642885514973578159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58546815095257009982385439 87820222642885514973578159)
        ·
          refine ⟨131730333964328272460367239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87820222642885514973578159 131730333964328272460367239)
          ·
            refine ⟨197595500946492408690550859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131730333964328272460367239 197595500946492408690550859)
            ·
              refine ⟨296393251419738613035826289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197595500946492408690550859 296393251419738613035826289)
              ·
                refine ⟨222294938564803959776869717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296393251419738613035826289 222294938564803959776869717)
                ·
                  refine ⟨325627351413287050454399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 222294938564803959776869717 325627351413287050454399)
                  ·
                    rfl

theorem cell23_5707413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 11].length) (baseStart_5707413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707413 prefixEnd_5707413 := by exact prefixLift 5707413
  have htrace : WordTrace (prefixWord ++ tailWord_5707413) baseStart_5707413 baseEnd_5707413 := by
    simpa [prefixWord, tailWord_5707413, baseEnd_5707413] using wordTrace_append hprefix tailTrace_5707413
  have hstable : (prefixWord ++ tailWord_5707413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707413).length < 2 ^ (prefixWord ++ tailWord_5707413).sum := by decide
  have hdescent : baseEnd_5707413 < baseStart_5707413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707424 : List Nat := [2, 1, 1, 4, 3, 2, 2, 1, 1, 4, 2]
def baseStart_5707424 : Nat := 118140960795 + 5707424 * 2 ^ 59
def prefixEnd_5707424 : Nat := 4983230072969 + 3 ^ 40 * 5707424 * 2
def baseEnd_5707424 : Nat := 2930651811006782911052041

theorem tailTrace_5707424 : CollatzResearch.WordTrace tailWord_5707424 prefixEnd_5707424 2930651811006782911052041 := by
  unfold tailWord_5707424
  simp only [CollatzResearch.WordTrace]
  refine ⟨104083427437492536630232663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138777903249990048840310217 104083427437492536630232663)
  ·
    refine ⟨156125141156238804945348995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104083427437492536630232663 156125141156238804945348995)
    ·
      refine ⟨234187711734358207418023493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156125141156238804945348995 234187711734358207418023493)
      ·
        refine ⟨43910195950192163890879405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234187711734358207418023493 43910195950192163890879405)
        ·
          refine ⟨16466323481322061459079777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43910195950192163890879405 16466323481322061459079777)
          ·
            refine ⟨12349742610991546094309833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16466323481322061459079777 12349742610991546094309833)
            ·
              refine ⟨9262306958243659570732375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12349742610991546094309833 9262306958243659570732375)
              ·
                refine ⟨13893460437365489356098563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9262306958243659570732375 13893460437365489356098563)
                ·
                  refine ⟨20840190656048234034147845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13893460437365489356098563 20840190656048234034147845)
                  ·
                    refine ⟨3907535748009043881402721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20840190656048234034147845 3907535748009043881402721)
                    ·
                      refine ⟨2930651811006782911052041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3907535748009043881402721 2930651811006782911052041)
                      ·
                        rfl

theorem cell23_5707424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_5707424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707424 prefixEnd_5707424 := by exact prefixLift 5707424
  have htrace : WordTrace (prefixWord ++ tailWord_5707424) baseStart_5707424 baseEnd_5707424 := by
    simpa [prefixWord, tailWord_5707424, baseEnd_5707424] using wordTrace_append hprefix tailTrace_5707424
  have hstable : (prefixWord ++ tailWord_5707424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707424).length < 2 ^ (prefixWord ++ tailWord_5707424).sum := by decide
  have hdescent : baseEnd_5707424 < baseStart_5707424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707433 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 2, 4, 6]
def baseStart_5707433 : Nat := 118140960795 + 5707433 * 2 ^ 59
def prefixEnd_5707433 : Nat := 4983230072969 + 3 ^ 40 * 5707433 * 2
def baseEnd_5707433 : Nat := 2930656432332673375839499

theorem tailTrace_5707433 : CollatzResearch.WordTrace tailWord_5707433 prefixEnd_5707433 2930656432332673375839499 := by
  unfold tailWord_5707433
  simp only [CollatzResearch.WordTrace]
  refine ⟨208167183131952467797542953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138778122087968311865028635 208167183131952467797542953)
  ·
    refine ⟨156125387348964350848157215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208167183131952467797542953 156125387348964350848157215)
    ·
      refine ⟨234188081023446526272235823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156125387348964350848157215 234188081023446526272235823)
      ·
        refine ⟨351282121535169789408353735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234188081023446526272235823 351282121535169789408353735)
        ·
          refine ⟨526923182302754684112530603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351282121535169789408353735 526923182302754684112530603)
          ·
            refine ⟨790384773454132026168795905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526923182302754684112530603 790384773454132026168795905)
            ·
              refine ⟨592788580090599019626596929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 790384773454132026168795905 592788580090599019626596929)
              ·
                refine ⟨444591435067949264719947697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 592788580090599019626596929 444591435067949264719947697)
                ·
                  refine ⟨333443576300961948539960773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 444591435067949264719947697 333443576300961948539960773)
                  ·
                    refine ⟨62520670556430365351242645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 333443576300961948539960773 62520670556430365351242645)
                    ·
                      refine ⟨2930656432332673375839499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62520670556430365351242645 2930656432332673375839499)
                      ·
                        rfl

theorem cell23_5707433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_5707433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707433 prefixEnd_5707433 := by exact prefixLift 5707433
  have htrace : WordTrace (prefixWord ++ tailWord_5707433) baseStart_5707433 baseEnd_5707433 := by
    simpa [prefixWord, tailWord_5707433, baseEnd_5707433] using wordTrace_append hprefix tailTrace_5707433
  have hstable : (prefixWord ++ tailWord_5707433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707433).length < 2 ^ (prefixWord ++ tailWord_5707433).sum := by decide
  have hdescent : baseEnd_5707433 < baseStart_5707433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707445 : List Nat := [1, 3, 3, 3, 3, 1, 2, 1, 1, 3, 2]
def baseStart_5707445 : Nat := 118140960795 + 5707445 * 2 ^ 59
def prefixEnd_5707445 : Nat := 4983230072969 + 3 ^ 40 * 5707445 * 2
def baseEnd_5707445 : Nat := 2930662594100527328889445

theorem tailTrace_5707445 : CollatzResearch.WordTrace tailWord_5707445 prefixEnd_5707445 2930662594100527328889445 := by
  unfold tailWord_5707445
  simp only [CollatzResearch.WordTrace]
  refine ⟨208167620807908993846979789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138778413871939329231319859 208167620807908993846979789)
  ·
    refine ⟨78062857802965872692617421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208167620807908993846979789 78062857802965872692617421)
    ·
      refine ⟨29273571676112202259731533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78062857802965872692617421 29273571676112202259731533)
      ·
        refine ⟨10977589378542075847399325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29273571676112202259731533 10977589378542075847399325)
        ·
          refine ⟨4116596016953278442774747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10977589378542075847399325 4116596016953278442774747)
          ·
            refine ⟨6174894025429917664162121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4116596016953278442774747 6174894025429917664162121)
            ·
              refine ⟨4631170519072438248121591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6174894025429917664162121 4631170519072438248121591)
              ·
                refine ⟨6946755778608657372182387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4631170519072438248121591 6946755778608657372182387)
                ·
                  refine ⟨10420133667912986058273581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6946755778608657372182387 10420133667912986058273581)
                  ·
                    refine ⟨3907550125467369771852593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10420133667912986058273581 3907550125467369771852593)
                    ·
                      refine ⟨2930662594100527328889445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3907550125467369771852593 2930662594100527328889445)
                      ·
                        rfl

theorem cell23_5707445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_5707445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707445 prefixEnd_5707445 := by exact prefixLift 5707445
  have htrace : WordTrace (prefixWord ++ tailWord_5707445) baseStart_5707445 baseEnd_5707445 := by
    simpa [prefixWord, tailWord_5707445, baseEnd_5707445] using wordTrace_append hprefix tailTrace_5707445
  have hstable : (prefixWord ++ tailWord_5707445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707445).length < 2 ^ (prefixWord ++ tailWord_5707445).sum := by decide
  have hdescent : baseEnd_5707445 < baseStart_5707445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707447 : List Nat := [1, 1, 3, 1, 5, 1, 1, 5, 5]
def baseStart_5707447 : Nat := 118140960795 + 5707447 * 2 ^ 59
def prefixEnd_5707447 : Nat := 4983230072969 + 3 ^ 40 * 5707447 * 2
def baseEnd_5707447 : Nat := 325629291229092924562715

theorem tailTrace_5707447 : CollatzResearch.WordTrace tailWord_5707447 prefixEnd_5707447 325629291229092924562715 := by
  unfold tailWord_5707447
  simp only [CollatzResearch.WordTrace]
  refine ⟨208167693753901748188552595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138778462502601165459035063 208167693753901748188552595)
  ·
    refine ⟨312251540630852622282828893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208167693753901748188552595 312251540630852622282828893)
    ·
      refine ⟨117094327736569733356060835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312251540630852622282828893 117094327736569733356060835)
      ·
        refine ⟨175641491604854600034091253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117094327736569733356060835 175641491604854600034091253)
        ·
          refine ⟨16466389837955118753196055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 175641491604854600034091253 16466389837955118753196055)
          ·
            refine ⟨24699584756932678129794083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16466389837955118753196055 24699584756932678129794083)
            ·
              refine ⟨37049377135399017194691125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24699584756932678129794083 37049377135399017194691125)
              ·
                refine ⟨3473379106443657862002293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37049377135399017194691125 3473379106443657862002293)
                ·
                  refine ⟨325629291229092924562715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3473379106443657862002293 325629291229092924562715)
                  ·
                    rfl

theorem cell23_5707447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 5].length) (baseStart_5707447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707447 prefixEnd_5707447 := by exact prefixLift 5707447
  have htrace : WordTrace (prefixWord ++ tailWord_5707447) baseStart_5707447 baseEnd_5707447 := by
    simpa [prefixWord, tailWord_5707447, baseEnd_5707447] using wordTrace_append hprefix tailTrace_5707447
  have hstable : (prefixWord ++ tailWord_5707447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707447).length < 2 ^ (prefixWord ++ tailWord_5707447).sum := by decide
  have hdescent : baseEnd_5707447 < baseStart_5707447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707470 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7]
def baseStart_5707470 : Nat := 118140960795 + 5707470 * 2 ^ 59
def prefixEnd_5707470 : Nat := 4983230072969 + 3 ^ 40 * 5707470 * 2
def baseEnd_5707470 : Nat := 2930675431116889731076829

theorem tailTrace_5707470 : CollatzResearch.WordTrace tailWord_5707470 prefixEnd_5707470 2930675431116889731076829 := by
  unfold tailWord_5707470
  simp only [CollatzResearch.WordTrace]
  refine ⟨26021066579102302889579983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138779021755212282077759909 26021066579102302889579983)
  ·
    refine ⟨39031599868653454334369975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26021066579102302889579983 39031599868653454334369975)
    ·
      refine ⟨58547399802980181501554963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39031599868653454334369975 58547399802980181501554963)
      ·
        refine ⟨87821099704470272252332445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58547399802980181501554963 87821099704470272252332445)
        ·
          refine ⟨32932912389176352094624667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87821099704470272252332445 32932912389176352094624667)
          ·
            refine ⟨49399368583764528141937001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32932912389176352094624667 49399368583764528141937001)
            ·
              refine ⟨37049526437823396106452751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49399368583764528141937001 37049526437823396106452751)
              ·
                refine ⟨55574289656735094159679127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37049526437823396106452751 55574289656735094159679127)
                ·
                  refine ⟨83361434485102641239518691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55574289656735094159679127 83361434485102641239518691)
                  ·
                    refine ⟨125042151727653961859278037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83361434485102641239518691 125042151727653961859278037)
                    ·
                      refine ⟨2930675431116889731076829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125042151727653961859278037 2930675431116889731076829)
                      ·
                        rfl

theorem cell23_5707470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_5707470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707470 prefixEnd_5707470 := by exact prefixLift 5707470
  have htrace : WordTrace (prefixWord ++ tailWord_5707470) baseStart_5707470 baseEnd_5707470 := by
    simpa [prefixWord, tailWord_5707470, baseEnd_5707470] using wordTrace_append hprefix tailTrace_5707470
  have hstable : (prefixWord ++ tailWord_5707470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707470).length < 2 ^ (prefixWord ++ tailWord_5707470).sum := by decide
  have hdescent : baseEnd_5707470 < baseStart_5707470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707480 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 3, 3, 4]
def baseStart_5707480 : Nat := 118140960795 + 5707480 * 2 ^ 59
def prefixEnd_5707480 : Nat := 4983230072969 + 3 ^ 40 * 5707480 * 2
def baseEnd_5707480 : Nat := 2930680565923434691951783

theorem tailTrace_5707480 : CollatzResearch.WordTrace tailWord_5707480 prefixEnd_5707480 2930680565923434691951783 := by
  unfold tailWord_5707480
  simp only [CollatzResearch.WordTrace]
  refine ⟨104084448681391097412251947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138779264908521463216335929 104084448681391097412251947)
  ·
    refine ⟨156126673022086646118377921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104084448681391097412251947 156126673022086646118377921)
    ·
      refine ⟨117095004766564984588783441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156126673022086646118377921 117095004766564984588783441)
      ·
        refine ⟨87821253574923738441587581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117095004766564984588783441 87821253574923738441587581)
        ·
          refine ⟨32932970090596401915595343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87821253574923738441587581 32932970090596401915595343)
          ·
            refine ⟨49399455135894602873393015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32932970090596401915595343 49399455135894602873393015)
            ·
              refine ⟨74099182703841904310089523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49399455135894602873393015 74099182703841904310089523)
              ·
                refine ⟨111148774055762856465134285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74099182703841904310089523 111148774055762856465134285)
                ·
                  refine ⟨41680790270911071174425357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111148774055762856465134285 41680790270911071174425357)
                  ·
                    refine ⟨15630296351591651690409509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41680790270911071174425357 15630296351591651690409509)
                    ·
                      refine ⟨2930680565923434691951783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15630296351591651690409509 2930680565923434691951783)
                      ·
                        rfl

theorem cell23_5707480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_5707480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707480 prefixEnd_5707480 := by exact prefixLift 5707480
  have htrace : WordTrace (prefixWord ++ tailWord_5707480) baseStart_5707480 baseEnd_5707480 := by
    simpa [prefixWord, tailWord_5707480, baseEnd_5707480] using wordTrace_append hprefix tailTrace_5707480
  have hstable : (prefixWord ++ tailWord_5707480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707480).length < 2 ^ (prefixWord ++ tailWord_5707480).sum := by decide
  have hdescent : baseEnd_5707480 < baseStart_5707480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707524 : List Nat := [2, 3, 2, 2, 1, 2, 3, 1, 3, 4]
def baseStart_5707524 : Nat := 118140960795 + 5707524 * 2 ^ 59
def prefixEnd_5707524 : Nat := 4983230072969 + 3 ^ 40 * 5707524 * 2
def baseEnd_5707524 : Nat := 976901053024077506600527

theorem tailTrace_5707524 : CollatzResearch.WordTrace tailWord_5707524 prefixEnd_5707524 976901053024077506600527 := by
  unfold tailWord_5707524
  simp only [CollatzResearch.WordTrace]
  refine ⟨104085251087311395169552813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138780334783081860226070417 104085251087311395169552813)
  ·
    refine ⟨39031969157741773188582305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104085251087311395169552813 39031969157741773188582305)
    ·
      refine ⟨29273976868306329891436729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39031969157741773188582305 29273976868306329891436729)
      ·
        refine ⟨21955482651229747418577547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29273976868306329891436729 21955482651229747418577547)
        ·
          refine ⟨32933223976844621127866321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21955482651229747418577547 32933223976844621127866321)
          ·
            refine ⟨24699917982633465845899741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32933223976844621127866321 24699917982633465845899741)
            ·
              refine ⟨9262469243487549692212403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24699917982633465845899741 9262469243487549692212403)
              ·
                refine ⟨13893703865231324538318605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9262469243487549692212403 13893703865231324538318605)
                ·
                  refine ⟨5210138949461746701869477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13893703865231324538318605 5210138949461746701869477)
                  ·
                    refine ⟨976901053024077506600527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5210138949461746701869477 976901053024077506600527)
                    ·
                      rfl

theorem cell23_5707524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_5707524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707524 prefixEnd_5707524 := by exact prefixLift 5707524
  have htrace : WordTrace (prefixWord ++ tailWord_5707524) baseStart_5707524 baseEnd_5707524 := by
    simpa [prefixWord, tailWord_5707524, baseEnd_5707524] using wordTrace_append hprefix tailTrace_5707524
  have hstable : (prefixWord ++ tailWord_5707524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707524).length < 2 ^ (prefixWord ++ tailWord_5707524).sum := by decide
  have hdescent : baseEnd_5707524 < baseStart_5707524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707587 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 4]
def baseStart_5707587 : Nat := 118140960795 + 5707587 * 2 ^ 59
def prefixEnd_5707587 : Nat := 4983230072969 + 3 ^ 40 * 5707587 * 2
def baseEnd_5707587 : Nat := 2930735508353465773313791

theorem tailTrace_5707587 : CollatzResearch.WordTrace tailWord_5707587 prefixEnd_5707587 2930735508353465773313791 := by
  unfold tailWord_5707587
  simp only [CollatzResearch.WordTrace]
  refine ⟨208172799973394552098649015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138781866648929701399099343 208172799973394552098649015)
  ·
    refine ⟨312259199960091828147973523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208172799973394552098649015 312259199960091828147973523)
    ·
      refine ⟨468388799940137742221960285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312259199960091828147973523 468388799940137742221960285)
      ·
        refine ⟨175645799977551653333235107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 468388799940137742221960285 175645799977551653333235107)
        ·
          refine ⟨263468699966327479999852661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175645799977551653333235107 263468699966327479999852661)
          ·
            refine ⟨24700190621843201249986187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 263468699966327479999852661 24700190621843201249986187)
            ·
              refine ⟨37050285932764801874979281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24700190621843201249986187 37050285932764801874979281)
              ·
                refine ⟨27787714449573601406234461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37050285932764801874979281 27787714449573601406234461)
                ·
                  refine ⟨10420392918590100527337923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27787714449573601406234461 10420392918590100527337923)
                  ·
                    refine ⟨15630589377885150791006885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10420392918590100527337923 15630589377885150791006885)
                    ·
                      refine ⟨2930735508353465773313791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15630589377885150791006885 2930735508353465773313791)
                      ·
                        rfl

theorem cell23_5707587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_5707587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707587 prefixEnd_5707587 := by exact prefixLift 5707587
  have htrace : WordTrace (prefixWord ++ tailWord_5707587) baseStart_5707587 baseEnd_5707587 := by
    simpa [prefixWord, tailWord_5707587, baseEnd_5707587] using wordTrace_append hprefix tailTrace_5707587
  have hstable : (prefixWord ++ tailWord_5707587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707587).length < 2 ^ (prefixWord ++ tailWord_5707587).sum := by decide
  have hdescent : baseEnd_5707587 < baseStart_5707587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707604 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_5707604 : Nat := 118140960795 + 5707604 * 2 ^ 59
def prefixEnd_5707604 : Nat := 4983230072969 + 3 ^ 40 * 5707604 * 2
def baseEnd_5707604 : Nat := 2930744237524592206801213

theorem tailTrace_5707604 : CollatzResearch.WordTrace tailWord_5707604 prefixEnd_5707604 2930744237524592206801213 := by
  unfold tailWord_5707604
  simp only [CollatzResearch.WordTrace]
  refine ⟨104086710007166482001008933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138782280009555309334678577 104086710007166482001008933)
  ·
    refine ⟨19516258126343715375189175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104086710007166482001008933 19516258126343715375189175)
    ·
      refine ⟨29274387189515573062783763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19516258126343715375189175 29274387189515573062783763)
      ·
        refine ⟨43911580784273359594175645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29274387189515573062783763 43911580784273359594175645)
        ·
          refine ⟨16466842794102509847815867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43911580784273359594175645 16466842794102509847815867)
          ·
            refine ⟨24700264191153764771723801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16466842794102509847815867 24700264191153764771723801)
            ·
              refine ⟨18525198143365323578792851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24700264191153764771723801 18525198143365323578792851)
              ·
                refine ⟨27787797215047985368189277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18525198143365323578792851 27787797215047985368189277)
                ·
                  refine ⟨10420423955642994513070979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27787797215047985368189277 10420423955642994513070979)
                  ·
                    refine ⟨15630635933464491769606469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10420423955642994513070979 15630635933464491769606469)
                    ·
                      refine ⟨2930744237524592206801213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15630635933464491769606469 2930744237524592206801213)
                      ·
                        rfl

theorem cell23_5707604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_5707604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707604 prefixEnd_5707604 := by exact prefixLift 5707604
  have htrace : WordTrace (prefixWord ++ tailWord_5707604) baseStart_5707604 baseEnd_5707604 := by
    simpa [prefixWord, tailWord_5707604, baseEnd_5707604] using wordTrace_append hprefix tailTrace_5707604
  have hstable : (prefixWord ++ tailWord_5707604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707604).length < 2 ^ (prefixWord ++ tailWord_5707604).sum := by decide
  have hdescent : baseEnd_5707604 < baseStart_5707604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707617 : List Nat := [1, 2, 3, 1, 1, 1, 3, 4, 1, 2, 4]
def baseStart_5707617 : Nat := 118140960795 + 5707617 * 2 ^ 59
def prefixEnd_5707617 : Nat := 4983230072969 + 3 ^ 40 * 5707617 * 2
def baseEnd_5707617 : Nat := 2930750912773100655938653

theorem tailTrace_5707617 : CollatzResearch.WordTrace tailWord_5707617 prefixEnd_5707617 2930750912773100655938653 := by
  unfold tailWord_5707617
  simp only [CollatzResearch.WordTrace]
  refine ⟨208173894163285867222241105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138782596108857244814827403 208173894163285867222241105)
  ·
    refine ⟨156130420622464400416680829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208173894163285867222241105 156130420622464400416680829)
    ·
      refine ⟨58548907733424150156255311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156130420622464400416680829 58548907733424150156255311)
      ·
        refine ⟨87823361600136225234382967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58548907733424150156255311 87823361600136225234382967)
        ·
          refine ⟨131735042400204337851574451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87823361600136225234382967 131735042400204337851574451)
          ·
            refine ⟨197602563600306506777361677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131735042400204337851574451 197602563600306506777361677)
            ·
              refine ⟨74100961350114940041510629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197602563600306506777361677 74100961350114940041510629)
              ·
                refine ⟨13893930253146551257783243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74100961350114940041510629 13893930253146551257783243)
                ·
                  refine ⟨20840895379719826886674865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13893930253146551257783243 20840895379719826886674865)
                  ·
                    refine ⟨15630671534789870165006149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20840895379719826886674865 15630671534789870165006149)
                    ·
                      refine ⟨2930750912773100655938653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15630671534789870165006149 2930750912773100655938653)
                      ·
                        rfl

theorem cell23_5707617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_5707617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707617 prefixEnd_5707617 := by exact prefixLift 5707617
  have htrace : WordTrace (prefixWord ++ tailWord_5707617) baseStart_5707617 baseEnd_5707617 := by
    simpa [prefixWord, tailWord_5707617, baseEnd_5707617] using wordTrace_append hprefix tailTrace_5707617
  have hstable : (prefixWord ++ tailWord_5707617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707617).length < 2 ^ (prefixWord ++ tailWord_5707617).sum := by decide
  have hdescent : baseEnd_5707617 < baseStart_5707617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707618 : List Nat := [3, 3, 2, 1, 2, 3, 2, 1, 1, 5]
def baseStart_5707618 : Nat := 118140960795 + 5707618 * 2 ^ 59
def prefixEnd_5707618 : Nat := 4983230072969 + 3 ^ 40 * 5707618 * 2
def baseEnd_5707618 : Nat := 976917142084585050675383

theorem tailTrace_5707618 : CollatzResearch.WordTrace tailWord_5707618 prefixEnd_5707618 976917142084585050675383 := by
  unfold tailWord_5707618
  simp only [CollatzResearch.WordTrace]
  refine ⟨52043482659070561098256877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138782620424188162928685005 52043482659070561098256877)
  ·
    refine ⟨19516305997151460411846329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52043482659070561098256877 19516305997151460411846329)
    ·
      refine ⟨14637229497863595308884747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19516305997151460411846329 14637229497863595308884747)
      ·
        refine ⟨21955844246795392963327121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14637229497863595308884747 21955844246795392963327121)
        ·
          refine ⟨16466883185096544722495341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21955844246795392963327121 16466883185096544722495341)
          ·
            refine ⟨6175081194411204270935753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16466883185096544722495341 6175081194411204270935753)
            ·
              refine ⟨4631310895808403203201815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6175081194411204270935753 4631310895808403203201815)
              ·
                refine ⟨6946966343712604804802723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4631310895808403203201815 6946966343712604804802723)
                ·
                  refine ⟨10420449515568907207204085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6946966343712604804802723 10420449515568907207204085)
                  ·
                    refine ⟨976917142084585050675383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10420449515568907207204085 976917142084585050675383)
                    ·
                      rfl

theorem cell23_5707618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_5707618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707618 prefixEnd_5707618 := by exact prefixLift 5707618
  have htrace : WordTrace (prefixWord ++ tailWord_5707618) baseStart_5707618 baseEnd_5707618 := by
    simpa [prefixWord, tailWord_5707618, baseEnd_5707618] using wordTrace_append hprefix tailTrace_5707618
  have hstable : (prefixWord ++ tailWord_5707618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707618).length < 2 ^ (prefixWord ++ tailWord_5707618).sum := by decide
  have hdescent : baseEnd_5707618 < baseStart_5707618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707658 : List Nat := [3, 1, 2, 4, 2, 1, 2, 2, 1, 2, 3]
def baseStart_5707658 : Nat := 118140960795 + 5707658 * 2 ^ 59
def prefixEnd_5707658 : Nat := 4983230072969 + 3 ^ 40 * 5707658 * 2
def baseEnd_5707658 : Nat := 2930771965479934995525965

theorem tailTrace_5707658 : CollatzResearch.WordTrace tailWord_5707658 prefixEnd_5707658 2930771965479934995525965 := by
  unfold tailWord_5707658
  simp only [CollatzResearch.WordTrace]
  refine ⟨52043847389034332806120907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138783593037424887482989085 52043847389034332806120907)
  ·
    refine ⟨78065771083551499209181361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52043847389034332806120907 78065771083551499209181361)
    ·
      refine ⟨58549328312663624406886021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78065771083551499209181361 58549328312663624406886021)
      ·
        refine ⟨10977999058624429576291129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58549328312663624406886021 10977999058624429576291129)
        ·
          refine ⟨8233499293968322182218347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10977999058624429576291129 8233499293968322182218347)
          ·
            refine ⟨12350248940952483273327521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8233499293968322182218347 12350248940952483273327521)
            ·
              refine ⟨9262686705714362454995641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12350248940952483273327521 9262686705714362454995641)
              ·
                refine ⟨6947015029285771841246731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9262686705714362454995641 6947015029285771841246731)
                ·
                  refine ⟨10420522543928657761870097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6947015029285771841246731 10420522543928657761870097)
                  ·
                    refine ⟨7815391907946493321402573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10420522543928657761870097 7815391907946493321402573)
                    ·
                      refine ⟨2930771965479934995525965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7815391907946493321402573 2930771965479934995525965)
                      ·
                        rfl

theorem cell23_5707658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_5707658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707658 prefixEnd_5707658 := by exact prefixLift 5707658
  have htrace : WordTrace (prefixWord ++ tailWord_5707658) baseStart_5707658 baseEnd_5707658 := by
    simpa [prefixWord, tailWord_5707658, baseEnd_5707658] using wordTrace_append hprefix tailTrace_5707658
  have hstable : (prefixWord ++ tailWord_5707658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707658).length < 2 ^ (prefixWord ++ tailWord_5707658).sum := by decide
  have hdescent : baseEnd_5707658 < baseStart_5707658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707678 : List Nat := [4, 3, 1, 3, 2, 1, 9]
def baseStart_5707678 : Nat := 118140960795 + 5707678 * 2 ^ 59
def prefixEnd_5707678 : Nat := 4983230072969 + 3 ^ 40 * 5707678 * 2
def baseEnd_5707678 : Nat := 36182496729543517497233

theorem tailTrace_5707678 : CollatzResearch.WordTrace tailWord_5707678 prefixEnd_5707678 36182496729543517497233 := by
  unfold tailWord_5707678
  simp only [CollatzResearch.WordTrace]
  refine ⟨26022014877008109330026461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138784079344043249760141125 26022014877008109330026461)
  ·
    refine ⟨9758255578878040998759923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26022014877008109330026461 9758255578878040998759923)
    ·
      refine ⟨14637383368317061498139885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9758255578878040998759923 14637383368317061498139885)
      ·
        refine ⟨5489018763118898061802457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14637383368317061498139885 5489018763118898061802457)
        ·
          refine ⟨4116764072339173546351843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5489018763118898061802457 4116764072339173546351843)
          ·
            refine ⟨6175146108508760319527765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4116764072339173546351843 6175146108508760319527765)
            ·
              refine ⟨36182496729543517497233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6175146108508760319527765 36182496729543517497233)
              ·
                rfl

theorem cell23_5707678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 9].length) (baseStart_5707678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707678 prefixEnd_5707678 := by exact prefixLift 5707678
  have htrace : WordTrace (prefixWord ++ tailWord_5707678) baseStart_5707678 baseEnd_5707678 := by
    simpa [prefixWord, tailWord_5707678, baseEnd_5707678] using wordTrace_append hprefix tailTrace_5707678
  have hstable : (prefixWord ++ tailWord_5707678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707678).length < 2 ^ (prefixWord ++ tailWord_5707678).sum := by decide
  have hdescent : baseEnd_5707678 < baseStart_5707678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707761 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 2, 3, 3]
def baseStart_5707761 : Nat := 118140960795 + 5707761 * 2 ^ 59
def prefixEnd_5707761 : Nat := 4983230072969 + 3 ^ 40 * 5707761 * 2
def baseEnd_5707761 : Nat := 2930824853987348092537991

theorem tailTrace_5707761 : CollatzResearch.WordTrace tailWord_5707761 prefixEnd_5707761 2930824853987348092537991 := by
  unfold tailWord_5707761
  simp only [CollatzResearch.WordTrace]
  refine ⟨208179146274764179815483137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138786097516509453210322091 208179146274764179815483137)
  ·
    refine ⟨156134359706073134861612353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208179146274764179815483137 156134359706073134861612353)
    ·
      refine ⟨117100769779554851146209265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156134359706073134861612353 117100769779554851146209265)
      ·
        refine ⟨87825577334666138359656949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117100769779554851146209265 87825577334666138359656949)
        ·
          refine ⟨8233647875124950471217839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87825577334666138359656949 8233647875124950471217839)
          ·
            refine ⟨12350471812687425706826759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8233647875124950471217839 12350471812687425706826759)
            ·
              refine ⟨18525707719031138560240139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12350471812687425706826759 18525707719031138560240139)
              ·
                refine ⟨27788561578546707840360209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18525707719031138560240139 27788561578546707840360209)
                ·
                  refine ⟨20841421183910030880270157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27788561578546707840360209 20841421183910030880270157)
                  ·
                    refine ⟨7815532943966261580101309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20841421183910030880270157 7815532943966261580101309)
                    ·
                      refine ⟨2930824853987348092537991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7815532943966261580101309 2930824853987348092537991)
                      ·
                        rfl

theorem cell23_5707761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_5707761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707761 prefixEnd_5707761 := by exact prefixLift 5707761
  have htrace : WordTrace (prefixWord ++ tailWord_5707761) baseStart_5707761 baseEnd_5707761 := by
    simpa [prefixWord, tailWord_5707761, baseEnd_5707761] using wordTrace_append hprefix tailTrace_5707761
  have hstable : (prefixWord ++ tailWord_5707761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707761).length < 2 ^ (prefixWord ++ tailWord_5707761).sum := by decide
  have hdescent : baseEnd_5707761 < baseStart_5707761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707781 : List Nat := [1, 3, 1, 1, 2, 6, 1, 1, 2, 5]
def baseStart_5707781 : Nat := 118140960795 + 5707781 * 2 ^ 59
def prefixEnd_5707781 : Nat := 4983230072969 + 3 ^ 40 * 5707781 * 2
def baseEnd_5707781 : Nat := 976945041200146004762633

theorem tailTrace_5707781 : CollatzResearch.WordTrace tailWord_5707781 prefixEnd_5707781 976945041200146004762633 := by
  unfold tailWord_5707781
  simp only [CollatzResearch.WordTrace]
  refine ⟨208179875734691723231211197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138786583823127815487474131 208179875734691723231211197)
  ·
    refine ⟨78067453400509396211704199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208179875734691723231211197 78067453400509396211704199)
    ·
      refine ⟨117101180100764094317556299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78067453400509396211704199 117101180100764094317556299)
      ·
        refine ⟨175651770151146141476334449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117101180100764094317556299 175651770151146141476334449)
        ·
          refine ⟨131738827613359606107250837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175651770151146141476334449 131738827613359606107250837)
          ·
            refine ⟨6175257544376231536277383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 131738827613359606107250837 6175257544376231536277383)
            ·
              refine ⟨9262886316564347304416075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6175257544376231536277383 9262886316564347304416075)
              ·
                refine ⟨13894329474846520956624113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9262886316564347304416075 13894329474846520956624113)
                ·
                  refine ⟨10420747106134890717468085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13894329474846520956624113 10420747106134890717468085)
                  ·
                    refine ⟨976945041200146004762633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10420747106134890717468085 976945041200146004762633)
                    ·
                      rfl

theorem cell23_5707781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 5].length) (baseStart_5707781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707781 prefixEnd_5707781 := by exact prefixLift 5707781
  have htrace : WordTrace (prefixWord ++ tailWord_5707781) baseStart_5707781 baseEnd_5707781 := by
    simpa [prefixWord, tailWord_5707781, baseEnd_5707781] using wordTrace_append hprefix tailTrace_5707781
  have hstable : (prefixWord ++ tailWord_5707781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707781).length < 2 ^ (prefixWord ++ tailWord_5707781).sum := by decide
  have hdescent : baseEnd_5707781 < baseStart_5707781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707784 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 1, 3, 4]
def baseStart_5707784 : Nat := 118140960795 + 5707784 * 2 ^ 59
def prefixEnd_5707784 : Nat := 4983230072969 + 3 ^ 40 * 5707784 * 2
def baseEnd_5707784 : Nat := 2930836664042401502550385

theorem tailTrace_5707784 : CollatzResearch.WordTrace tailWord_5707784 prefixEnd_5707784 2930836664042401502550385 := by
  unfold tailWord_5707784
  simp only [CollatzResearch.WordTrace]
  refine ⟨104089992576840427371785203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138786656769120569829046937 104089992576840427371785203)
  ·
    refine ⟨156134988865260641057677805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104089992576840427371785203 156134988865260641057677805)
    ·
      refine ⟨58550620824472740396629177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156134988865260641057677805 58550620824472740396629177)
      ·
        refine ⟨43912965618354555297471883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58550620824472740396629177 43912965618354555297471883)
        ·
          refine ⟨65869448427531832946207825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43912965618354555297471883 65869448427531832946207825)
          ·
            refine ⟨49402086320648874709655869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65869448427531832946207825 49402086320648874709655869)
            ·
              refine ⟨18525782370243328016120951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49402086320648874709655869 18525782370243328016120951)
              ·
                refine ⟨27788673555364992024181427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18525782370243328016120951 27788673555364992024181427)
                ·
                  refine ⟨41683010333047488036272141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27788673555364992024181427 41683010333047488036272141)
                  ·
                    refine ⟨15631128874892808013602053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41683010333047488036272141 15631128874892808013602053)
                    ·
                      refine ⟨2930836664042401502550385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15631128874892808013602053 2930836664042401502550385)
                      ·
                        rfl

theorem cell23_5707784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_5707784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707784 prefixEnd_5707784 := by exact prefixLift 5707784
  have htrace : WordTrace (prefixWord ++ tailWord_5707784) baseStart_5707784 baseEnd_5707784 := by
    simpa [prefixWord, tailWord_5707784, baseEnd_5707784] using wordTrace_append hprefix tailTrace_5707784
  have hstable : (prefixWord ++ tailWord_5707784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707784).length < 2 ^ (prefixWord ++ tailWord_5707784).sum := by decide
  have hdescent : baseEnd_5707784 < baseStart_5707784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707796 : List Nat := [2, 4, 3, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_5707796 : Nat := 118140960795 + 5707796 * 2 ^ 59
def prefixEnd_5707796 : Nat := 4983230072969 + 3 ^ 40 * 5707796 * 2
def baseEnd_5707796 : Nat := 2930842825810255455600331

theorem tailTrace_5707796 : CollatzResearch.WordTrace tailWord_5707796 prefixEnd_5707796 2930842825810255455600331 := by
  unfold tailWord_5707796
  simp only [CollatzResearch.WordTrace]
  refine ⟨104090211414818690396503621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138786948553091587195338161 104090211414818690396503621)
  ·
    refine ⟨19516914640278504449344429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104090211414818690396503621 19516914640278504449344429)
    ·
      refine ⟨7318842990104439168504161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19516914640278504449344429 7318842990104439168504161)
      ·
        refine ⟨5489132242578329376378121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7318842990104439168504161 5489132242578329376378121)
        ·
          refine ⟨4116849181933747032283591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5489132242578329376378121 4116849181933747032283591)
          ·
            refine ⟨6175273772900620548425387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4116849181933747032283591 6175273772900620548425387)
            ·
              refine ⟨9262910659350930822638081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6175273772900620548425387 9262910659350930822638081)
              ·
                refine ⟨6947182994513198116978561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9262910659350930822638081 6947182994513198116978561)
                ·
                  refine ⟨5210387245884898587733921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6947182994513198116978561 5210387245884898587733921)
                  ·
                    refine ⟨3907790434413673940800441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5210387245884898587733921 3907790434413673940800441)
                    ·
                      refine ⟨2930842825810255455600331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3907790434413673940800441 2930842825810255455600331)
                      ·
                        rfl

theorem cell23_5707796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_5707796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707796 prefixEnd_5707796 := by exact prefixLift 5707796
  have htrace : WordTrace (prefixWord ++ tailWord_5707796) baseStart_5707796 baseEnd_5707796 := by
    simpa [prefixWord, tailWord_5707796, baseEnd_5707796] using wordTrace_append hprefix tailTrace_5707796
  have hstable : (prefixWord ++ tailWord_5707796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707796).length < 2 ^ (prefixWord ++ tailWord_5707796).sum := by decide
  have hdescent : baseEnd_5707796 < baseStart_5707796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707811 : List Nat := [1, 1, 1, 4, 3, 1, 4, 1, 3, 4]
def baseStart_5707811 : Nat := 118140960795 + 5707811 * 2 ^ 59
def prefixEnd_5707811 : Nat := 4983230072969 + 3 ^ 40 * 5707811 * 2
def baseEnd_5707811 : Nat := 976950176006690965637587

theorem tailTrace_5707811 : CollatzResearch.WordTrace tailWord_5707811 prefixEnd_5707811 976950176006690965637587 := by
  unfold tailWord_5707811
  simp only [CollatzResearch.WordTrace]
  refine ⟨208180969924583038354803287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138787313283055358903202191 208180969924583038354803287)
  ·
    refine ⟨312271454886874557532204931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208180969924583038354803287 312271454886874557532204931)
    ·
      refine ⟨468407182330311836298307397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312271454886874557532204931 468407182330311836298307397)
      ·
        refine ⟨87826346686933469305932637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 468407182330311836298307397 87826346686933469305932637)
        ·
          refine ⟨32934880007600050989724739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87826346686933469305932637 32934880007600050989724739)
          ·
            refine ⟨49402320011400076484587109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32934880007600050989724739 49402320011400076484587109)
            ·
              refine ⟨9262935002137514340860083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49402320011400076484587109 9262935002137514340860083)
              ·
                refine ⟨13894402503206271511290125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9262935002137514340860083 13894402503206271511290125)
                ·
                  refine ⟨5210400938702351816733797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13894402503206271511290125 5210400938702351816733797)
                  ·
                    refine ⟨976950176006690965637587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5210400938702351816733797 976950176006690965637587)
                    ·
                      rfl

theorem cell23_5707811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 4].length) (baseStart_5707811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707811 prefixEnd_5707811 := by exact prefixLift 5707811
  have htrace : WordTrace (prefixWord ++ tailWord_5707811) baseStart_5707811 baseEnd_5707811 := by
    simpa [prefixWord, tailWord_5707811, baseEnd_5707811] using wordTrace_append hprefix tailTrace_5707811
  have hstable : (prefixWord ++ tailWord_5707811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707811).length < 2 ^ (prefixWord ++ tailWord_5707811).sum := by decide
  have hdescent : baseEnd_5707811 < baseStart_5707811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707817 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 9]
def baseStart_5707817 : Nat := 118140960795 + 5707817 * 2 ^ 59
def prefixEnd_5707817 : Nat := 4983230072969 + 3 ^ 40 * 5707817 * 2
def baseEnd_5707817 : Nat := 2930853608903999873437733

theorem tailTrace_5707817 : CollatzResearch.WordTrace tailWord_5707817 prefixEnd_5707817 2930853608903999873437733 := by
  unfold tailWord_5707817
  simp only [CollatzResearch.WordTrace]
  refine ⟨208181188762561301379521705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138787459175040867586347803 208181188762561301379521705)
  ·
    refine ⟨156135891571920976034641279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208181188762561301379521705 156135891571920976034641279)
    ·
      refine ⟨234203837357881464051961919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156135891571920976034641279 234203837357881464051961919)
      ·
        refine ⟨351305756036822196077942879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234203837357881464051961919 351305756036822196077942879)
        ·
          refine ⟨526958634055233294116914319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351305756036822196077942879 526958634055233294116914319)
          ·
            refine ⟨790437951082849941175371479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526958634055233294116914319 790437951082849941175371479)
            ·
              refine ⟨1185656926624274911763057219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 790437951082849941175371479 1185656926624274911763057219)
              ·
                refine ⟨1778485389936412367644585829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1185656926624274911763057219 1778485389936412367644585829)
                ·
                  refine ⟨333466010613077318933359843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1778485389936412367644585829 333466010613077318933359843)
                  ·
                    refine ⟨500199015919615978400039765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 333466010613077318933359843 500199015919615978400039765)
                    ·
                      refine ⟨2930853608903999873437733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 500199015919615978400039765 2930853608903999873437733)
                      ·
                        rfl

theorem cell23_5707817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_5707817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707817 prefixEnd_5707817 := by exact prefixLift 5707817
  have htrace : WordTrace (prefixWord ++ tailWord_5707817) baseStart_5707817 baseEnd_5707817 := by
    simpa [prefixWord, tailWord_5707817, baseEnd_5707817] using wordTrace_append hprefix tailTrace_5707817
  have hstable : (prefixWord ++ tailWord_5707817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707817).length < 2 ^ (prefixWord ++ tailWord_5707817).sum := by decide
  have hdescent : baseEnd_5707817 < baseStart_5707817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707818 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 2, 4, 2]
def baseStart_5707818 : Nat := 118140960795 + 5707818 * 2 ^ 59
def prefixEnd_5707818 : Nat := 4983230072969 + 3 ^ 40 * 5707818 * 2
def baseEnd_5707818 : Nat := 2930854122384654369525229

theorem tailTrace_5707818 : CollatzResearch.WordTrace tailWord_5707818 prefixEnd_5707818 2930854122384654369525229 := by
  unfold tailWord_5707818
  simp only [CollatzResearch.WordTrace]
  refine ⟨52045306308889419637577027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138787483490371785700205405 52045306308889419637577027)
  ·
    refine ⟨78067959463334129456365541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52045306308889419637577027 78067959463334129456365541)
    ·
      refine ⟨14637742399375149273068539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78067959463334129456365541 14637742399375149273068539)
      ·
        refine ⟨21956613599062723909602809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14637742399375149273068539 21956613599062723909602809)
        ·
          refine ⟨16467460199297042932202107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21956613599062723909602809 16467460199297042932202107)
          ·
            refine ⟨24701190298945564398303161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16467460199297042932202107 24701190298945564398303161)
            ·
              refine ⟨18525892724209173298727371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24701190298945564398303161 18525892724209173298727371)
              ·
                refine ⟨27788839086313759948091057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18525892724209173298727371 27788839086313759948091057)
                ·
                  refine ⟨20841629314735319961068293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27788839086313759948091057 20841629314735319961068293)
                  ·
                    refine ⟨3907805496512872492700305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20841629314735319961068293 3907805496512872492700305)
                    ·
                      refine ⟨2930854122384654369525229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3907805496512872492700305 2930854122384654369525229)
                      ·
                        rfl

theorem cell23_5707818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_5707818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707818 prefixEnd_5707818 := by exact prefixLift 5707818
  have htrace : WordTrace (prefixWord ++ tailWord_5707818) baseStart_5707818 baseEnd_5707818 := by
    simpa [prefixWord, tailWord_5707818, baseEnd_5707818] using wordTrace_append hprefix tailTrace_5707818
  have hstable : (prefixWord ++ tailWord_5707818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707818).length < 2 ^ (prefixWord ++ tailWord_5707818).sum := by decide
  have hdescent : baseEnd_5707818 < baseStart_5707818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707834 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3]
def baseStart_5707834 : Nat := 118140960795 + 5707834 * 2 ^ 59
def prefixEnd_5707834 : Nat := 4983230072969 + 3 ^ 40 * 5707834 * 2
def baseEnd_5707834 : Nat := 2930862338075126306925155

theorem tailTrace_5707834 : CollatzResearch.WordTrace tailWord_5707834 prefixEnd_5707834 2930862338075126306925155 := by
  unfold tailWord_5707834
  simp only [CollatzResearch.WordTrace]
  refine ⟨52045452200874928320722639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138787872535666475521927037 52045452200874928320722639)
  ·
    refine ⟨78068178301312392481083959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52045452200874928320722639 78068178301312392481083959)
    ·
      refine ⟨117102267451968588721625939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78068178301312392481083959 117102267451968588721625939)
      ·
        refine ⟨175653401177952883082438909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117102267451968588721625939 175653401177952883082438909)
        ·
          refine ⟨65870025441732331155914591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175653401177952883082438909 65870025441732331155914591)
          ·
            refine ⟨98805038162598496733871887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65870025441732331155914591 98805038162598496733871887)
            ·
              refine ⟨148207557243897745100807831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98805038162598496733871887 148207557243897745100807831)
              ·
                refine ⟨222311335865846617651211747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148207557243897745100807831 222311335865846617651211747)
                ·
                  refine ⟨333467003798769926476817621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222311335865846617651211747 333467003798769926476817621)
                  ·
                    refine ⟨7815632901533670151800413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 333467003798769926476817621 7815632901533670151800413)
                    ·
                      refine ⟨2930862338075126306925155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7815632901533670151800413 2930862338075126306925155)
                      ·
                        rfl

theorem cell23_5707834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3].length) (baseStart_5707834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707834 prefixEnd_5707834 := by exact prefixLift 5707834
  have htrace : WordTrace (prefixWord ++ tailWord_5707834) baseStart_5707834 baseEnd_5707834 := by
    simpa [prefixWord, tailWord_5707834, baseEnd_5707834] using wordTrace_append hprefix tailTrace_5707834
  have hstable : (prefixWord ++ tailWord_5707834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707834).length < 2 ^ (prefixWord ++ tailWord_5707834).sum := by decide
  have hdescent : baseEnd_5707834 < baseStart_5707834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707862 : List Nat := [5, 2, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_5707862 : Nat := 118140960795 + 5707862 * 2 ^ 59
def prefixEnd_5707862 : Nat := 4983230072969 + 3 ^ 40 * 5707862 * 2
def baseEnd_5707862 : Nat := 976958905177817399125009

theorem tailTrace_5707862 : CollatzResearch.WordTrace tailWord_5707862 prefixEnd_5707862 976958905177817399125009 := by
  unfold tailWord_5707862
  simp only [CollatzResearch.WordTrace]
  refine ⟨13011426877962392129056865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138788553364932182709939893 13011426877962392129056865)
  ·
    refine ⟨9758570158471794096792649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13011426877962392129056865 9758570158471794096792649)
    ·
      refine ⟨7318927618853845572594487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9758570158471794096792649 7318927618853845572594487)
      ·
        refine ⟨10978391428280768358891731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7318927618853845572594487 10978391428280768358891731)
        ·
          refine ⟨16467587142421152538337597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10978391428280768358891731 16467587142421152538337597)
          ·
            refine ⟨6175345178407932201876599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16467587142421152538337597 6175345178407932201876599)
            ·
              refine ⟨9263017767611898302814899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6175345178407932201876599 9263017767611898302814899)
              ·
                refine ⟨13894526651417847454222349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9263017767611898302814899 13894526651417847454222349)
                ·
                  refine ⟨5210447494281692795333381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13894526651417847454222349 5210447494281692795333381)
                  ·
                    refine ⟨976958905177817399125009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5210447494281692795333381 976958905177817399125009)
                    ·
                      rfl

theorem cell23_5707862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_5707862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707862 prefixEnd_5707862 := by exact prefixLift 5707862
  have htrace : WordTrace (prefixWord ++ tailWord_5707862) baseStart_5707862 baseEnd_5707862 := by
    simpa [prefixWord, tailWord_5707862, baseEnd_5707862] using wordTrace_append hprefix tailTrace_5707862
  have hstable : (prefixWord ++ tailWord_5707862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707862).length < 2 ^ (prefixWord ++ tailWord_5707862).sum := by decide
  have hdescent : baseEnd_5707862 < baseStart_5707862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707888 : List Nat := [2, 1, 1, 1, 5, 4, 1, 2, 1, 5]
def baseStart_5707888 : Nat := 118140960795 + 5707888 * 2 ^ 59
def prefixEnd_5707888 : Nat := 4983230072969 + 3 ^ 40 * 5707888 * 2
def baseEnd_5707888 : Nat := 976963355343489698549969

theorem tailTrace_5707888 : CollatzResearch.WordTrace tailWord_5707888 prefixEnd_5707888 976963355343489698549969 := by
  unfold tailWord_5707888
  simp only [CollatzResearch.WordTrace]
  refine ⟨104091889172652040252678159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138789185563536053670237545 104091889172652040252678159)
  ·
    refine ⟨156137833758978060379017239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104091889172652040252678159 156137833758978060379017239)
    ·
      refine ⟨234206750638467090568525859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156137833758978060379017239 234206750638467090568525859)
      ·
        refine ⟨351310125957700635852788789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234206750638467090568525859 351310125957700635852788789)
        ·
          refine ⟨32935324308534434611198949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 351310125957700635852788789 32935324308534434611198949)
          ·
            refine ⟨6175373307850206489599803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32935324308534434611198949 6175373307850206489599803)
            ·
              refine ⟨9263059961775309734399705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6175373307850206489599803 9263059961775309734399705)
              ·
                refine ⟨6947294971331482300799779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9263059961775309734399705 6947294971331482300799779)
                ·
                  refine ⟨10420942456997223451199669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6947294971331482300799779 10420942456997223451199669)
                  ·
                    refine ⟨976963355343489698549969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10420942456997223451199669 976963355343489698549969)
                    ·
                      rfl

theorem cell23_5707888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 1, 5].length) (baseStart_5707888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707888 prefixEnd_5707888 := by exact prefixLift 5707888
  have htrace : WordTrace (prefixWord ++ tailWord_5707888) baseStart_5707888 baseEnd_5707888 := by
    simpa [prefixWord, tailWord_5707888, baseEnd_5707888] using wordTrace_append hprefix tailTrace_5707888
  have hstable : (prefixWord ++ tailWord_5707888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707888).length < 2 ^ (prefixWord ++ tailWord_5707888).sum := by decide
  have hdescent : baseEnd_5707888 < baseStart_5707888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707901 : List Nat := [1, 4, 1, 1, 3, 3, 1, 2, 1, 6]
def baseStart_5707901 : Nat := 118140960795 + 5707901 * 2 ^ 59
def prefixEnd_5707901 : Nat := 4983230072969 + 3 ^ 40 * 5707901 * 2
def baseEnd_5707901 : Nat := 976965580426325848262449

theorem tailTrace_5707901 : CollatzResearch.WordTrace tailWord_5707901 prefixEnd_5707901 976965580426325848262449 := by
  unfold tailWord_5707901
  simp only [CollatzResearch.WordTrace]
  refine ⟨208184252494256983725579557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138789501662837989150386371 208184252494256983725579557)
  ·
    refine ⟨39034547342673184448546167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208184252494256983725579557 39034547342673184448546167)
    ·
      refine ⟨58551821014009776672819251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39034547342673184448546167 58551821014009776672819251)
      ·
        refine ⟨87827731521014665009228877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58551821014009776672819251 87827731521014665009228877)
        ·
          refine ⟨32935399320380499378460829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87827731521014665009228877 32935399320380499378460829)
          ·
            refine ⟨12350774745142687266922811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32935399320380499378460829 12350774745142687266922811)
            ·
              refine ⟨18526162117714030900384217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12350774745142687266922811 18526162117714030900384217)
              ·
                refine ⟨13894621588285523175288163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18526162117714030900384217 13894621588285523175288163)
                ·
                  refine ⟨20841932382428284762932245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13894621588285523175288163 20841932382428284762932245)
                  ·
                    refine ⟨976965580426325848262449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20841932382428284762932245 976965580426325848262449)
                    ·
                      rfl

theorem cell23_5707901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_5707901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707901 prefixEnd_5707901 := by exact prefixLift 5707901
  have htrace : WordTrace (prefixWord ++ tailWord_5707901) baseStart_5707901 baseEnd_5707901 := by
    simpa [prefixWord, tailWord_5707901, baseEnd_5707901] using wordTrace_append hprefix tailTrace_5707901
  have hstable : (prefixWord ++ tailWord_5707901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707901).length < 2 ^ (prefixWord ++ tailWord_5707901).sum := by decide
  have hdescent : baseEnd_5707901 < baseStart_5707901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707905 : List Nat := [1, 2, 4, 2, 3, 1, 3, 1, 1, 5]
def baseStart_5707905 : Nat := 118140960795 + 5707905 * 2 ^ 59
def prefixEnd_5707905 : Nat := 4983230072969 + 3 ^ 40 * 5707905 * 2
def baseEnd_5707905 : Nat := 976966265067198509712443

theorem tailTrace_5707905 : CollatzResearch.WordTrace tailWord_5707905 prefixEnd_5707905 976966265067198509712443 := by
  unfold tailWord_5707905
  simp only [CollatzResearch.WordTrace]
  refine ⟨208184398386242492408725169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138789598924161661605816779 208184398386242492408725169)
  ·
    refine ⟨156138298789681869306543877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208184398386242492408725169 156138298789681869306543877)
    ·
      refine ⟨29275931023065350494976977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156138298789681869306543877 29275931023065350494976977)
      ·
        refine ⟨21956948267299012871232733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29275931023065350494976977 21956948267299012871232733)
        ·
          refine ⟨8233855600237129826712275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21956948267299012871232733 8233855600237129826712275)
          ·
            refine ⟨12350783400355694740068413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8233855600237129826712275 12350783400355694740068413)
            ·
              refine ⟨4631543775133385527525655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12350783400355694740068413 4631543775133385527525655)
              ·
                refine ⟨6947315662700078291288483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4631543775133385527525655 6947315662700078291288483)
                ·
                  refine ⟨10420973494050117436932725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6947315662700078291288483 10420973494050117436932725)
                  ·
                    refine ⟨976966265067198509712443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10420973494050117436932725 976966265067198509712443)
                    ·
                      rfl

theorem cell23_5707905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_5707905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707905 prefixEnd_5707905 := by exact prefixLift 5707905
  have htrace : WordTrace (prefixWord ++ tailWord_5707905) baseStart_5707905 baseEnd_5707905 := by
    simpa [prefixWord, tailWord_5707905, baseEnd_5707905] using wordTrace_append hprefix tailTrace_5707905
  have hstable : (prefixWord ++ tailWord_5707905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707905).length < 2 ^ (prefixWord ++ tailWord_5707905).sum := by decide
  have hdescent : baseEnd_5707905 < baseStart_5707905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707911 : List Nat := [1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 5]
def baseStart_5707911 : Nat := 118140960795 + 5707911 * 2 ^ 59
def prefixEnd_5707911 : Nat := 4983230072969 + 3 ^ 40 * 5707911 * 2
def baseEnd_5707911 : Nat := 2930901876085522505662301

theorem tailTrace_5707911 : CollatzResearch.WordTrace tailWord_5707911 prefixEnd_5707911 2930901876085522505662301 := by
  unfold tailWord_5707911
  simp only [CollatzResearch.WordTrace]
  refine ⟨208184617224220755433443587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138789744816147170288962391 208184617224220755433443587)
  ·
    refine ⟨312276925836331133150165381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208184617224220755433443587 312276925836331133150165381)
    ·
      refine ⟨58551923594312087465656009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 312276925836331133150165381 58551923594312087465656009)
      ·
        refine ⟨43913942695734065599242007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58551923594312087465656009 43913942695734065599242007)
        ·
          refine ⟨65870914043601098398863011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43913942695734065599242007 65870914043601098398863011)
          ·
            refine ⟨98806371065401647598294517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65870914043601098398863011 98806371065401647598294517)
            ·
              refine ⟨9263097287381404462340111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98806371065401647598294517 9263097287381404462340111)
              ·
                refine ⟨13894645931072106693510167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9263097287381404462340111 13894645931072106693510167)
                ·
                  refine ⟨20841968896608160040265251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13894645931072106693510167 20841968896608160040265251)
                  ·
                    refine ⟨31262953344912240060397877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20841968896608160040265251 31262953344912240060397877)
                    ·
                      refine ⟨2930901876085522505662301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31262953344912240060397877 2930901876085522505662301)
                      ·
                        rfl

theorem cell23_5707911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_5707911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707911 prefixEnd_5707911 := by exact prefixLift 5707911
  have htrace : WordTrace (prefixWord ++ tailWord_5707911) baseStart_5707911 baseEnd_5707911 := by
    simpa [prefixWord, tailWord_5707911, baseEnd_5707911] using wordTrace_append hprefix tailTrace_5707911
  have hstable : (prefixWord ++ tailWord_5707911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707911).length < 2 ^ (prefixWord ++ tailWord_5707911).sum := by decide
  have hdescent : baseEnd_5707911 < baseStart_5707911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707914 : List Nat := [3, 1, 2, 3, 1, 13]
def baseStart_5707914 : Nat := 118140960795 + 5707914 * 2 ^ 59
def prefixEnd_5707914 : Nat := 4983230072969 + 3 ^ 40 * 5707914 * 2
def baseEnd_5707914 : Nat := 12061330932211876518209

theorem tailTrace_5707914 : CollatzResearch.WordTrace tailWord_5707914 prefixEnd_5707914 12061330932211876518209 := by
  unfold tailWord_5707914
  simp only [CollatzResearch.WordTrace]
  refine ⟨52046181660802471736450699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138789817762139924630535197 52046181660802471736450699)
  ·
    refine ⟨78069272491203707604676049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52046181660802471736450699 78069272491203707604676049)
    ·
      refine ⟨58551954368402780703507037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78069272491203707604676049 58551954368402780703507037)
      ·
        refine ⟨21956982888151042763815139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58551954368402780703507037 21956982888151042763815139)
        ·
          refine ⟨32935474332226564145722709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21956982888151042763815139 32935474332226564145722709)
          ·
            refine ⟨12061330932211876518209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 32935474332226564145722709 12061330932211876518209)
            ·
              rfl

theorem cell23_5707914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 13].length) (baseStart_5707914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707914 prefixEnd_5707914 := by exact prefixLift 5707914
  have htrace : WordTrace (prefixWord ++ tailWord_5707914) baseStart_5707914 baseEnd_5707914 := by
    simpa [prefixWord, tailWord_5707914, baseEnd_5707914] using wordTrace_append hprefix tailTrace_5707914
  have hstable : (prefixWord ++ tailWord_5707914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707914).length < 2 ^ (prefixWord ++ tailWord_5707914).sum := by decide
  have hdescent : baseEnd_5707914 < baseStart_5707914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707938 : List Nat := [3, 3, 1, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_5707938 : Nat := 118140960795 + 5707938 * 2 ^ 59
def prefixEnd_5707938 : Nat := 4983230072969 + 3 ^ 40 * 5707938 * 2
def baseEnd_5707938 : Nat := 2930915740063193900024677

theorem tailTrace_5707938 : CollatzResearch.WordTrace tailWord_5707938 prefixEnd_5707938 2930915740063193900024677 := by
  unfold tailWord_5707938
  simp only [CollatzResearch.WordTrace]
  refine ⟨52046400498780734761169117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138790401330081959363117645 52046400498780734761169117)
  ·
    refine ⟨19517400187042775535438419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52046400498780734761169117 19517400187042775535438419)
    ·
      refine ⟨29276100280564163303157629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19517400187042775535438419 29276100280564163303157629)
      ·
        refine ⟨10978537605211561238684111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29276100280564163303157629 10978537605211561238684111)
        ·
          refine ⟨16467806407817341858026167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10978537605211561238684111 16467806407817341858026167)
          ·
            refine ⟨24701709611726012787039251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16467806407817341858026167 24701709611726012787039251)
            ·
              refine ⟨37052564417589019180558877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24701709611726012787039251 37052564417589019180558877)
              ·
                refine ⟨13894711656595882192709579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37052564417589019180558877 13894711656595882192709579)
                ·
                  refine ⟨20842067484893823289064369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13894711656595882192709579 20842067484893823289064369)
                  ·
                    refine ⟨15631550613670367466798277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20842067484893823289064369 15631550613670367466798277)
                    ·
                      refine ⟨2930915740063193900024677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15631550613670367466798277 2930915740063193900024677)
                      ·
                        rfl

theorem cell23_5707938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_5707938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707938 prefixEnd_5707938 := by exact prefixLift 5707938
  have htrace : WordTrace (prefixWord ++ tailWord_5707938) baseStart_5707938 baseEnd_5707938 := by
    simpa [prefixWord, tailWord_5707938, baseEnd_5707938] using wordTrace_append hprefix tailTrace_5707938
  have hstable : (prefixWord ++ tailWord_5707938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707938).length < 2 ^ (prefixWord ++ tailWord_5707938).sum := by decide
  have hdescent : baseEnd_5707938 < baseStart_5707938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707956 : List Nat := [2, 5, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_5707956 : Nat := 118140960795 + 5707956 * 2 ^ 59
def prefixEnd_5707956 : Nat := 4983230072969 + 3 ^ 40 * 5707956 * 2
def baseEnd_5707956 : Nat := 976974994238324943199865

theorem tailTrace_5707956 : CollatzResearch.WordTrace tailWord_5707956 prefixEnd_5707956 976974994238324943199865 := by
  unfold tailWord_5707956
  simp only [CollatzResearch.WordTrace]
  refine ⟨104093129254528864059415861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138790839006038485412554481 104093129254528864059415861)
  ·
    refine ⟨9758730867612081005570237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104093129254528864059415861 9758730867612081005570237)
    ·
      refine ⟨3659524075354530377088839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9758730867612081005570237 3659524075354530377088839)
      ·
        refine ⟨5489286113031795565633259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3659524075354530377088839 5489286113031795565633259)
        ·
          refine ⟨8233929169547693348449889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5489286113031795565633259 8233929169547693348449889)
          ·
            refine ⟨6175446877160770011337417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8233929169547693348449889 6175446877160770011337417)
            ·
              refine ⟨4631585157870577508503063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6175446877160770011337417 4631585157870577508503063)
              ·
                refine ⟨6947377736805866262754595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4631585157870577508503063 6947377736805866262754595)
                ·
                  refine ⟨10421066605208799394131893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6947377736805866262754595 10421066605208799394131893)
                  ·
                    refine ⟨976974994238324943199865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10421066605208799394131893 976974994238324943199865)
                    ·
                      rfl

theorem cell23_5707956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_5707956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707956 prefixEnd_5707956 := by exact prefixLift 5707956
  have htrace : WordTrace (prefixWord ++ tailWord_5707956) baseStart_5707956 baseEnd_5707956 := by
    simpa [prefixWord, tailWord_5707956, baseEnd_5707956] using wordTrace_append hprefix tailTrace_5707956
  have hstable : (prefixWord ++ tailWord_5707956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707956).length < 2 ^ (prefixWord ++ tailWord_5707956).sum := by decide
  have hdescent : baseEnd_5707956 < baseStart_5707956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707969 : List Nat := [1, 2, 6, 1, 3, 1, 1, 2, 2, 4]
def baseStart_5707969 : Nat := 118140960795 + 5707969 * 2 ^ 59
def prefixEnd_5707969 : Nat := 4983230072969 + 3 ^ 40 * 5707969 * 2
def baseEnd_5707969 : Nat := 976977219321161092912345

theorem tailTrace_5707969 : CollatzResearch.WordTrace tailWord_5707969 prefixEnd_5707969 976977219321161092912345 := by
  unfold tailWord_5707969
  simp only [CollatzResearch.WordTrace]
  refine ⟨208186732658010631339054961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138791155105340420892703307 208186732658010631339054961)
  ·
    refine ⟨156140049493507973504291221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208186732658010631339054961 156140049493507973504291221)
    ·
      refine ⟨7319064820008186258013651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 156140049493507973504291221 7319064820008186258013651)
      ·
        refine ⟨10978597230012279387020477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7319064820008186258013651 10978597230012279387020477)
        ·
          refine ⟨4116973961254604770132679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10978597230012279387020477 4116973961254604770132679)
          ·
            refine ⟨6175460941881907155199019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4116973961254604770132679 6175460941881907155199019)
            ·
              refine ⟨9263191412822860732798529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6175460941881907155199019 9263191412822860732798529)
              ·
                refine ⟨6947393559617145549598897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9263191412822860732798529 6947393559617145549598897)
                ·
                  refine ⟨5210545169712859162199173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6947393559617145549598897 5210545169712859162199173)
                  ·
                    refine ⟨976977219321161092912345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5210545169712859162199173 976977219321161092912345)
                    ·
                      rfl

theorem cell23_5707969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_5707969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707969 prefixEnd_5707969 := by exact prefixLift 5707969
  have htrace : WordTrace (prefixWord ++ tailWord_5707969) baseStart_5707969 baseEnd_5707969 := by
    simpa [prefixWord, tailWord_5707969, baseEnd_5707969] using wordTrace_append hprefix tailTrace_5707969
  have hstable : (prefixWord ++ tailWord_5707969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707969).length < 2 ^ (prefixWord ++ tailWord_5707969).sum := by decide
  have hdescent : baseEnd_5707969 < baseStart_5707969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707992 : List Nat := [2, 1, 2, 2, 4, 2, 3, 1, 2, 1, 3]
def baseStart_5707992 : Nat := 118140960795 + 5707992 * 2 ^ 59
def prefixEnd_5707992 : Nat := 4983230072969 + 3 ^ 40 * 5707992 * 2
def baseEnd_5707992 : Nat := 2930943468018536688749429

theorem tailTrace_5707992 : CollatzResearch.WordTrace tailWord_5707992 prefixEnd_5707992 2930943468018536688749429 := by
  unfold tailWord_5707992
  simp only [CollatzResearch.WordTrace]
  refine ⟨104093785768463653133571115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138791714357951537511428153 104093785768463653133571115)
  ·
    refine ⟨156140678652695479700356673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104093785768463653133571115 156140678652695479700356673)
    ·
      refine ⟨117105508989521609775267505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156140678652695479700356673 117105508989521609775267505)
      ·
        refine ⟨87829131742141207331450629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117105508989521609775267505 87829131742141207331450629)
        ·
          refine ⟨16467962201651476374646993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87829131742141207331450629 16467962201651476374646993)
          ·
            refine ⟨12350971651238607280985245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16467962201651476374646993 12350971651238607280985245)
            ·
              refine ⟨4631614369214477730369467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12350971651238607280985245 4631614369214477730369467)
              ·
                refine ⟨6947421553821716595554201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4631614369214477730369467 6947421553821716595554201)
                ·
                  refine ⟨5210566165366287446665651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6947421553821716595554201 5210566165366287446665651)
                  ·
                    refine ⟨7815849248049431169998477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5210566165366287446665651 7815849248049431169998477)
                    ·
                      refine ⟨2930943468018536688749429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7815849248049431169998477 2930943468018536688749429)
                      ·
                        rfl

theorem cell23_5707992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 2, 1, 3].length) (baseStart_5707992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707992 prefixEnd_5707992 := by exact prefixLift 5707992
  have htrace : WordTrace (prefixWord ++ tailWord_5707992) baseStart_5707992 baseEnd_5707992 := by
    simpa [prefixWord, tailWord_5707992, baseEnd_5707992] using wordTrace_append hprefix tailTrace_5707992
  have hstable : (prefixWord ++ tailWord_5707992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707992).length < 2 ^ (prefixWord ++ tailWord_5707992).sum := by decide
  have hdescent : baseEnd_5707992 < baseStart_5707992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708001 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 2, 1, 5]
def baseStart_5708001 : Nat := 118140960795 + 5708001 * 2 ^ 59
def prefixEnd_5708001 : Nat := 4983230072969 + 3 ^ 40 * 5708001 * 2
def baseEnd_5708001 : Nat := 2930948089344427153536887

theorem tailTrace_5708001 : CollatzResearch.WordTrace tailWord_5708001 prefixEnd_5708001 2930948089344427153536887 := by
  unfold tailWord_5708001
  simp only [CollatzResearch.WordTrace]
  refine ⟨208187899793894700804219857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138791933195929800536146571 208187899793894700804219857)
  ·
    refine ⟨156140924845421025603164893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208187899793894700804219857 156140924845421025603164893)
    ·
      refine ⟨58552846817032884601186835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156140924845421025603164893 58552846817032884601186835)
      ·
        refine ⟨87829270225549326901780253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58552846817032884601186835 87829270225549326901780253)
        ·
          refine ⟨32935976334580997588167595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87829270225549326901780253 32935976334580997588167595)
          ·
            refine ⟨49403964501871496382251393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32935976334580997588167595 49403964501871496382251393)
            ·
              refine ⟨37052973376403622286688545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49403964501871496382251393 37052973376403622286688545)
              ·
                refine ⟨27789730032302716715016409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37052973376403622286688545 27789730032302716715016409)
                ·
                  refine ⟨20842297524227037536262307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27789730032302716715016409 20842297524227037536262307)
                  ·
                    refine ⟨31263446286340556304393461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20842297524227037536262307 31263446286340556304393461)
                    ·
                      refine ⟨2930948089344427153536887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31263446286340556304393461 2930948089344427153536887)
                      ·
                        rfl

theorem cell23_5708001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_5708001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708001 prefixEnd_5708001 := by exact prefixLift 5708001
  have htrace : WordTrace (prefixWord ++ tailWord_5708001) baseStart_5708001 baseEnd_5708001 := by
    simpa [prefixWord, tailWord_5708001, baseEnd_5708001] using wordTrace_append hprefix tailTrace_5708001
  have hstable : (prefixWord ++ tailWord_5708001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708001).length < 2 ^ (prefixWord ++ tailWord_5708001).sum := by decide
  have hdescent : baseEnd_5708001 < baseStart_5708001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708015 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 4, 2, 2]
def baseStart_5708015 : Nat := 118140960795 + 5708015 * 2 ^ 59
def prefixEnd_5708015 : Nat := 4983230072969 + 3 ^ 40 * 5708015 * 2
def baseEnd_5708015 : Nat := 2930955278073590098761823

theorem tailTrace_5708015 : CollatzResearch.WordTrace tailWord_5708015 prefixEnd_5708015 2930955278073590098761823 := by
  unfold tailWord_5708015
  simp only [CollatzResearch.WordTrace]
  refine ⟨208188410415843981195229499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138792273610562654130152999 208188410415843981195229499)
  ·
    refine ⟨312282615623765971792844249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208188410415843981195229499 312282615623765971792844249)
    ·
      refine ⟨234211961717824478844633187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312282615623765971792844249 234211961717824478844633187)
      ·
        refine ⟨351317942576736718266949781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234211961717824478844633187 351317942576736718266949781)
        ·
          refine ⟨16468028558284533668763271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 351317942576736718266949781 16468028558284533668763271)
          ·
            refine ⟨24702042837426800503144907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16468028558284533668763271 24702042837426800503144907)
            ·
              refine ⟨37053064256140200754717361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24702042837426800503144907 37053064256140200754717361)
              ·
                refine ⟨27789798192105150566038021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37053064256140200754717361 27789798192105150566038021)
                ·
                  refine ⟨5210587161019715731132129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27789798192105150566038021 5210587161019715731132129)
                  ·
                    refine ⟨3907940370764786798349097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5210587161019715731132129 3907940370764786798349097)
                    ·
                      refine ⟨2930955278073590098761823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3907940370764786798349097 2930955278073590098761823)
                      ·
                        rfl

theorem cell23_5708015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 2, 2].length) (baseStart_5708015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708015 prefixEnd_5708015 := by exact prefixLift 5708015
  have htrace : WordTrace (prefixWord ++ tailWord_5708015) baseStart_5708015 baseEnd_5708015 := by
    simpa [prefixWord, tailWord_5708015, baseEnd_5708015] using wordTrace_append hprefix tailTrace_5708015
  have hstable : (prefixWord ++ tailWord_5708015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708015).length < 2 ^ (prefixWord ++ tailWord_5708015).sum := by decide
  have hdescent : baseEnd_5708015 < baseStart_5708015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708018 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 2, 1, 5]
def baseStart_5708018 : Nat := 118140960795 + 5708018 * 2 ^ 59
def prefixEnd_5708018 : Nat := 4983230072969 + 3 ^ 40 * 5708018 * 2
def baseEnd_5708018 : Nat := 2930956818515553587024309

theorem tailTrace_5708018 : CollatzResearch.WordTrace tailWord_5708018 prefixEnd_5708018 2930956818515553587024309 := by
  unfold tailWord_5708018
  simp only [CollatzResearch.WordTrace]
  refine ⟨52047129958708278176897177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138792346556555408471725805 52047129958708278176897177)
  ·
    refine ⟨39035347469031208632672883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52047129958708278176897177 39035347469031208632672883)
    ·
      refine ⟨58553021203546812949009325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39035347469031208632672883 58553021203546812949009325)
      ·
        refine ⟨21957382951330054855878497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58553021203546812949009325 21957382951330054855878497)
        ·
          refine ⟨16468037213497541141908873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21957382951330054855878497 16468037213497541141908873)
          ·
            refine ⟨12351027910123155856431655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16468037213497541141908873 12351027910123155856431655)
            ·
              refine ⟨18526541865184733784647483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12351027910123155856431655 18526541865184733784647483)
              ·
                refine ⟨27789812797777100676971225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18526541865184733784647483 27789812797777100676971225)
                ·
                  refine ⟨20842359598332825507728419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27789812797777100676971225 20842359598332825507728419)
                  ·
                    refine ⟨31263539397499238261592629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20842359598332825507728419 31263539397499238261592629)
                    ·
                      refine ⟨2930956818515553587024309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31263539397499238261592629 2930956818515553587024309)
                      ·
                        rfl

theorem cell23_5708018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_5708018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708018 prefixEnd_5708018 := by exact prefixLift 5708018
  have htrace : WordTrace (prefixWord ++ tailWord_5708018) baseStart_5708018 baseEnd_5708018 := by
    simpa [prefixWord, tailWord_5708018, baseEnd_5708018] using wordTrace_append hprefix tailTrace_5708018
  have hstable : (prefixWord ++ tailWord_5708018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708018).length < 2 ^ (prefixWord ++ tailWord_5708018).sum := by decide
  have hdescent : baseEnd_5708018 < baseStart_5708018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708049 : List Nat := [1, 2, 2, 1, 1, 7, 2, 1, 2, 2, 2]
def baseStart_5708049 : Nat := 118140960795 + 5708049 * 2 ^ 59
def prefixEnd_5708049 : Nat := 4983230072969 + 3 ^ 40 * 5708049 * 2
def baseEnd_5708049 : Nat := 2930972736415842965736667

theorem tailTrace_5708049 : CollatzResearch.WordTrace tailWord_5708049 prefixEnd_5708049 2930972736415842965736667 := by
  unfold tailWord_5708049
  simp only [CollatzResearch.WordTrace]
  refine ⟨208189650497720805001967201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138793100331813870001311467 208189650497720805001967201)
  ·
    refine ⟨156142237873290603751475401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208189650497720805001967201 156142237873290603751475401)
    ·
      refine ⟨117106678404967952813606551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156142237873290603751475401 117106678404967952813606551)
      ·
        refine ⟨175660017607451929220409827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117106678404967952813606551 175660017607451929220409827)
        ·
          refine ⟨263490026411177893830614741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175660017607451929220409827 263490026411177893830614741)
          ·
            refine ⟨6175547494011981886655033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 263490026411177893830614741 6175547494011981886655033)
            ·
              refine ⟨4631660620508986414991275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6175547494011981886655033 4631660620508986414991275)
              ·
                refine ⟨6947490930763479622486913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4631660620508986414991275 6947490930763479622486913)
                ·
                  refine ⟨5210618198072609716865185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6947490930763479622486913 5210618198072609716865185)
                  ·
                    refine ⟨3907963648554457287648889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5210618198072609716865185 3907963648554457287648889)
                    ·
                      refine ⟨2930972736415842965736667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3907963648554457287648889 2930972736415842965736667)
                      ·
                        rfl

theorem cell23_5708049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 2, 2, 2].length) (baseStart_5708049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708049 prefixEnd_5708049 := by exact prefixLift 5708049
  have htrace : WordTrace (prefixWord ++ tailWord_5708049) baseStart_5708049 baseEnd_5708049 := by
    simpa [prefixWord, tailWord_5708049, baseEnd_5708049] using wordTrace_append hprefix tailTrace_5708049
  have hstable : (prefixWord ++ tailWord_5708049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708049).length < 2 ^ (prefixWord ++ tailWord_5708049).sum := by decide
  have hdescent : baseEnd_5708049 < baseStart_5708049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708068 : List Nat := [2, 3, 1, 3, 1, 2, 1, 3, 2, 5]
def baseStart_5708068 : Nat := 118140960795 + 5708068 * 2 ^ 59
def prefixEnd_5708068 : Nat := 4983230072969 + 3 ^ 40 * 5708068 * 2
def baseEnd_5708068 : Nat := 976994164182759463799693

theorem tailTrace_5708068 : CollatzResearch.WordTrace tailWord_5708068 prefixEnd_5708068 976994164182759463799693 := by
  unfold tailWord_5708068
  simp only [CollatzResearch.WordTrace]
  refine ⟨104095171742325985623454429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138793562323101314164605905 104095171742325985623454429)
  ·
    refine ⟨39035689403372244608795411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104095171742325985623454429 39035689403372244608795411)
    ·
      refine ⟨58553534105058366913193117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39035689403372244608795411 58553534105058366913193117)
      ·
        refine ⟨21957575289396887592447419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58553534105058366913193117 21957575289396887592447419)
        ·
          refine ⟨32936362934095331388671129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21957575289396887592447419 32936362934095331388671129)
          ·
            refine ⟨24702272200571498541503347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32936362934095331388671129 24702272200571498541503347)
            ·
              refine ⟨37053408300857247812255021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24702272200571498541503347 37053408300857247812255021)
              ·
                refine ⟨13895028112821467929595633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37053408300857247812255021 13895028112821467929595633)
                ·
                  refine ⟨10421271084616100947196725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13895028112821467929595633 10421271084616100947196725)
                  ·
                    refine ⟨976994164182759463799693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10421271084616100947196725 976994164182759463799693)
                    ·
                      rfl

theorem cell23_5708068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_5708068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708068 prefixEnd_5708068 := by exact prefixLift 5708068
  have htrace : WordTrace (prefixWord ++ tailWord_5708068) baseStart_5708068 baseEnd_5708068 := by
    simpa [prefixWord, tailWord_5708068, baseEnd_5708068] using wordTrace_append hprefix tailTrace_5708068
  have hstable : (prefixWord ++ tailWord_5708068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708068).length < 2 ^ (prefixWord ++ tailWord_5708068).sum := by decide
  have hdescent : baseEnd_5708068 < baseStart_5708068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708088 : List Nat := [2, 1, 2, 1, 3, 1, 4, 2, 2, 1, 4]
def baseStart_5708088 : Nat := 118140960795 + 5708088 * 2 ^ 59
def prefixEnd_5708088 : Nat := 4983230072969 + 3 ^ 40 * 5708088 * 2
def baseEnd_5708088 : Nat := 2930992762161368313148987

theorem tailTrace_5708088 : CollatzResearch.WordTrace tailWord_5708088 prefixEnd_5708088 2930992762161368313148987 := by
  unfold tailWord_5708088
  simp only [CollatzResearch.WordTrace]
  refine ⟨104095536472289757331318459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138794048629719676441757945 104095536472289757331318459)
  ·
    refine ⟨156143304708434635996977689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104095536472289757331318459 156143304708434635996977689)
    ·
      refine ⟨117107478531325976997733267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156143304708434635996977689 117107478531325976997733267)
      ·
        refine ⟨175661217796988965496599901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117107478531325976997733267 175661217796988965496599901)
        ·
          refine ⟨65872956673870862061224963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175661217796988965496599901 65872956673870862061224963)
          ·
            refine ⟨98809435010806293091837445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65872956673870862061224963 98809435010806293091837445)
            ·
              refine ⟨18526769064526179954719521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98809435010806293091837445 18526769064526179954719521)
              ·
                refine ⟨13895076798394634966039641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18526769064526179954719521 13895076798394634966039641)
                ·
                  refine ⟨10421307598795976224529731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13895076798394634966039641 10421307598795976224529731)
                  ·
                    refine ⟨15631961398193964336794597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10421307598795976224529731 15631961398193964336794597)
                    ·
                      refine ⟨2930992762161368313148987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15631961398193964336794597 2930992762161368313148987)
                      ·
                        rfl

theorem cell23_5708088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_5708088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708088 prefixEnd_5708088 := by exact prefixLift 5708088
  have htrace : WordTrace (prefixWord ++ tailWord_5708088) baseStart_5708088 baseEnd_5708088 := by
    simpa [prefixWord, tailWord_5708088, baseEnd_5708088] using wordTrace_append hprefix tailTrace_5708088
  have hstable : (prefixWord ++ tailWord_5708088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708088).length < 2 ^ (prefixWord ++ tailWord_5708088).sum := by decide
  have hdescent : baseEnd_5708088 < baseStart_5708088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708101 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 4, 4, 4]
def baseStart_5708101 : Nat := 118140960795 + 5708101 * 2 ^ 59
def prefixEnd_5708101 : Nat := 4983230072969 + 3 ^ 40 * 5708101 * 2
def baseEnd_5708101 : Nat := 2930999437409876762286427

theorem tailTrace_5708101 : CollatzResearch.WordTrace tailWord_5708101 prefixEnd_5708101 2930999437409876762286427 := by
  unfold tailWord_5708101
  simp only [CollatzResearch.WordTrace]
  refine ⟨208191547093532417882860157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138794364729021611921906771 208191547093532417882860157)
  ·
    refine ⟨78071830160074656706072559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208191547093532417882860157 78071830160074656706072559)
    ·
      refine ⟨117107745240111985059108839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78071830160074656706072559 117107745240111985059108839)
      ·
        refine ⟨175661617860167977588663259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117107745240111985059108839 175661617860167977588663259)
        ·
          refine ⟨263492426790251966382994889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175661617860167977588663259 263492426790251966382994889)
          ·
            refine ⟨197619320092688974787246167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263492426790251966382994889 197619320092688974787246167)
            ·
              refine ⟨296428980139033462180869251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197619320092688974787246167 296428980139033462180869251)
              ·
                refine ⟨444643470208550193271303877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296428980139033462180869251 444643470208550193271303877)
                ·
                  refine ⟨83370650664103161238369477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 444643470208550193271303877 83370650664103161238369477)
                  ·
                    refine ⟨15631996999519342732194277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83370650664103161238369477 15631996999519342732194277)
                    ·
                      refine ⟨2930999437409876762286427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15631996999519342732194277 2930999437409876762286427)
                      ·
                        rfl

theorem cell23_5708101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_5708101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708101 prefixEnd_5708101 := by exact prefixLift 5708101
  have htrace : WordTrace (prefixWord ++ tailWord_5708101) baseStart_5708101 baseEnd_5708101 := by
    simpa [prefixWord, tailWord_5708101, baseEnd_5708101] using wordTrace_append hprefix tailTrace_5708101
  have hstable : (prefixWord ++ tailWord_5708101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708101).length < 2 ^ (prefixWord ++ tailWord_5708101).sum := by decide
  have hdescent : baseEnd_5708101 < baseStart_5708101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708108 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 1, 4, 3]
def baseStart_5708108 : Nat := 118140960795 + 5708108 * 2 ^ 59
def prefixEnd_5708108 : Nat := 4983230072969 + 3 ^ 40 * 5708108 * 2
def baseEnd_5708108 : Nat := 2931003031774458234898895

theorem tailTrace_5708108 : CollatzResearch.WordTrace tailWord_5708108 prefixEnd_5708108 2931003031774458234898895 := by
  unfold tailWord_5708108
  simp only [CollatzResearch.WordTrace]
  refine ⟨104095901202253529039182489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138794534936338038718909985 104095901202253529039182489)
  ·
    refine ⟨78071925901690146779386867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104095901202253529039182489 78071925901690146779386867)
    ·
      refine ⟨117107888852535220169080301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78071925901690146779386867 117107888852535220169080301)
      ·
        refine ⟨43915458319700707563405113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117107888852535220169080301 43915458319700707563405113)
        ·
          refine ⟨32936593739775530672553835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43915458319700707563405113 32936593739775530672553835)
          ·
            refine ⟨49404890609663296008830753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32936593739775530672553835 49404890609663296008830753)
            ·
              refine ⟨37053667957247472006623065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49404890609663296008830753 37053667957247472006623065)
              ·
                refine ⟨27790250967935604004967299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37053667957247472006623065 27790250967935604004967299)
                ·
                  refine ⟨41685376451903406007450949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27790250967935604004967299 41685376451903406007450949)
                  ·
                    refine ⟨7816008084731888626397053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41685376451903406007450949 7816008084731888626397053)
                    ·
                      refine ⟨2931003031774458234898895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7816008084731888626397053 2931003031774458234898895)
                      ·
                        rfl

theorem cell23_5708108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_5708108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708108 prefixEnd_5708108 := by exact prefixLift 5708108
  have htrace : WordTrace (prefixWord ++ tailWord_5708108) baseStart_5708108 baseEnd_5708108 := by
    simpa [prefixWord, tailWord_5708108, baseEnd_5708108] using wordTrace_append hprefix tailTrace_5708108
  have hstable : (prefixWord ++ tailWord_5708108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708108).length < 2 ^ (prefixWord ++ tailWord_5708108).sum := by decide
  have hdescent : baseEnd_5708108 < baseStart_5708108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708132 : List Nat := [2, 3, 1, 1, 3, 1, 4, 3, 1, 4]
def baseStart_5708132 : Nat := 118140960795 + 5708132 * 2 ^ 59
def prefixEnd_5708132 : Nat := 4983230072969 + 3 ^ 40 * 5708132 * 2
def baseEnd_5708132 : Nat := 977005118436722046999595

theorem tailTrace_5708132 : CollatzResearch.WordTrace tailWord_5708132 prefixEnd_5708132 977005118436722046999595 := by
  unfold tailWord_5708132
  simp only [CollatzResearch.WordTrace]
  refine ⟨104096338878210055088619325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138795118504280073451492433 104096338878210055088619325)
  ·
    refine ⟨39036127079328770658232247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104096338878210055088619325 39036127079328770658232247)
    ·
      refine ⟨58554190618993155987348371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39036127079328770658232247 58554190618993155987348371)
      ·
        refine ⟨87831285928489733981022557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58554190618993155987348371 87831285928489733981022557)
        ·
          refine ⟨32936732223183650242883459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87831285928489733981022557 32936732223183650242883459)
          ·
            refine ⟨49405098334775475364325189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32936732223183650242883459 49405098334775475364325189)
            ·
              refine ⟨9263455937770401630810973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49405098334775475364325189 9263455937770401630810973)
              ·
                refine ⟨3473795976663900611554115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9263455937770401630810973 3473795976663900611554115)
                ·
                  refine ⟨5210693964995850917331173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3473795976663900611554115 5210693964995850917331173)
                  ·
                    refine ⟨977005118436722046999595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5210693964995850917331173 977005118436722046999595)
                    ·
                      rfl

theorem cell23_5708132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_5708132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708132 prefixEnd_5708132 := by exact prefixLift 5708132
  have htrace : WordTrace (prefixWord ++ tailWord_5708132) baseStart_5708132 baseEnd_5708132 := by
    simpa [prefixWord, tailWord_5708132, baseEnd_5708132] using wordTrace_append hprefix tailTrace_5708132
  have hstable : (prefixWord ++ tailWord_5708132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708132).length < 2 ^ (prefixWord ++ tailWord_5708132).sum := by decide
  have hdescent : baseEnd_5708132 < baseStart_5708132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708151 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 7]
def baseStart_5708151 : Nat := 118140960795 + 5708151 * 2 ^ 59
def prefixEnd_5708151 : Nat := 4983230072969 + 3 ^ 40 * 5708151 * 2
def baseEnd_5708151 : Nat := 2931025111442601566661197

theorem tailTrace_5708151 : CollatzResearch.WordTrace tailWord_5708151 prefixEnd_5708151 2931025111442601566661197 := by
  unfold tailWord_5708151
  simp only [CollatzResearch.WordTrace]
  refine ⟨208193370743351276422180307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138795580495567517614786871 208193370743351276422180307)
  ·
    refine ⟨312290056115026914633270461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208193370743351276422180307 312290056115026914633270461)
    ·
      refine ⟨117108771043135092987476423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312290056115026914633270461 117108771043135092987476423)
      ·
        refine ⟨175663156564702639481214635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117108771043135092987476423 175663156564702639481214635)
        ·
          refine ⟨263494734847053959221821953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175663156564702639481214635 263494734847053959221821953)
          ·
            refine ⟨197621051135290469416366465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263494734847053959221821953 197621051135290469416366465)
            ·
              refine ⟨148215788351467852062274849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197621051135290469416366465 148215788351467852062274849)
              ·
                refine ⟨111161841263600889046706137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148215788351467852062274849 111161841263600889046706137)
                ·
                  refine ⟨83371380947700666785029603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111161841263600889046706137 83371380947700666785029603)
                  ·
                    refine ⟨125057071421551000177544405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83371380947700666785029603 125057071421551000177544405)
                    ·
                      refine ⟨2931025111442601566661197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125057071421551000177544405 2931025111442601566661197)
                      ·
                        rfl

theorem cell23_5708151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_5708151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708151 prefixEnd_5708151 := by exact prefixLift 5708151
  have htrace : WordTrace (prefixWord ++ tailWord_5708151) baseStart_5708151 baseEnd_5708151 := by
    simpa [prefixWord, tailWord_5708151, baseEnd_5708151] using wordTrace_append hprefix tailTrace_5708151
  have hstable : (prefixWord ++ tailWord_5708151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708151).length < 2 ^ (prefixWord ++ tailWord_5708151).sum := by decide
  have hdescent : baseEnd_5708151 < baseStart_5708151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708155 : List Nat := [1, 1, 1, 1, 1, 7, 1, 3, 3, 1, 3]
def baseStart_5708155 : Nat := 118140960795 + 5708155 * 2 ^ 59
def prefixEnd_5708155 : Nat := 4983230072969 + 3 ^ 40 * 5708155 * 2
def baseEnd_5708155 : Nat := 2931027165365219551011179

theorem tailTrace_5708155 : CollatzResearch.WordTrace tailWord_5708155 prefixEnd_5708155 2931027165365219551011179 := by
  unfold tailWord_5708155
  simp only [CollatzResearch.WordTrace]
  refine ⟨208193516635336785105325919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138795677756891190070217279 208193516635336785105325919)
  ·
    refine ⟨312290274953005177657988879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208193516635336785105325919 312290274953005177657988879)
    ·
      refine ⟨468435412429507766486983319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312290274953005177657988879 468435412429507766486983319)
      ·
        refine ⟨702653118644261649730474979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468435412429507766486983319 702653118644261649730474979)
        ·
          refine ⟨1053979677966392474595712469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 702653118644261649730474979 1053979677966392474595712469)
          ·
            refine ⟨24702648702337323623337011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1053979677966392474595712469 24702648702337323623337011)
            ·
              refine ⟨37053973053505985435005517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24702648702337323623337011 37053973053505985435005517)
              ·
                refine ⟨13895239895064744538127069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37053973053505985435005517 13895239895064744538127069)
                ·
                  refine ⟨5210714960649279201797651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13895239895064744538127069 5210714960649279201797651)
                  ·
                    refine ⟨7816072440973918802696477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5210714960649279201797651 7816072440973918802696477)
                    ·
                      refine ⟨2931027165365219551011179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7816072440973918802696477 2931027165365219551011179)
                      ·
                        rfl

theorem cell23_5708155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 1, 3].length) (baseStart_5708155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708155 prefixEnd_5708155 := by exact prefixLift 5708155
  have htrace : WordTrace (prefixWord ++ tailWord_5708155) baseStart_5708155 baseEnd_5708155 := by
    simpa [prefixWord, tailWord_5708155, baseEnd_5708155] using wordTrace_append hprefix tailTrace_5708155
  have hstable : (prefixWord ++ tailWord_5708155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708155).length < 2 ^ (prefixWord ++ tailWord_5708155).sum := by decide
  have hdescent : baseEnd_5708155 < baseStart_5708155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708195 : List Nat := [1, 1, 1, 4, 1, 4, 2, 3, 1, 1, 4]
def baseStart_5708195 : Nat := 118140960795 + 5708195 * 2 ^ 59
def prefixEnd_5708195 : Nat := 4983230072969 + 3 ^ 40 * 5708195 * 2
def baseEnd_5708195 : Nat := 2931047704591399394510995

theorem tailTrace_5708195 : CollatzResearch.WordTrace tailWord_5708195 prefixEnd_5708195 2931047704591399394510995 := by
  unfold tailWord_5708195
  simp only [CollatzResearch.WordTrace]
  refine ⟨208194975555191871936782039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138796650370127914624521359 208194975555191871936782039)
  ·
    refine ⟨312292463332787807905173059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208194975555191871936782039 312292463332787807905173059)
    ·
      refine ⟨468438694999181711857759589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312292463332787807905173059 468438694999181711857759589)
      ·
        refine ⟨87832255312346570973329923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 468438694999181711857759589 87832255312346570973329923)
        ·
          refine ⟨131748382968519856459994885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87832255312346570973329923 131748382968519856459994885)
          ·
            refine ⟨24702821806597473086249041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131748382968519856459994885 24702821806597473086249041)
            ·
              refine ⟨18527116354948104814686781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24702821806597473086249041 18527116354948104814686781)
              ·
                refine ⟨6947668633105539305507543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18527116354948104814686781 6947668633105539305507543)
                ·
                  refine ⟨10421502949658308958261315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6947668633105539305507543 10421502949658308958261315)
                  ·
                    refine ⟨15632254424487463437391973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10421502949658308958261315 15632254424487463437391973)
                    ·
                      refine ⟨2931047704591399394510995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15632254424487463437391973 2931047704591399394510995)
                      ·
                        rfl

theorem cell23_5708195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_5708195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708195 prefixEnd_5708195 := by exact prefixLift 5708195
  have htrace : WordTrace (prefixWord ++ tailWord_5708195) baseStart_5708195 baseEnd_5708195 := by
    simpa [prefixWord, tailWord_5708195, baseEnd_5708195] using wordTrace_append hprefix tailTrace_5708195
  have hstable : (prefixWord ++ tailWord_5708195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708195).length < 2 ^ (prefixWord ++ tailWord_5708195).sum := by decide
  have hdescent : baseEnd_5708195 < baseStart_5708195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708232 : List Nat := [2, 1, 3, 1, 3, 2, 3, 2, 1, 2, 3]
def baseStart_5708232 : Nat := 118140960795 + 5708232 * 2 ^ 59
def prefixEnd_5708232 : Nat := 4983230072969 + 3 ^ 40 * 5708232 * 2
def baseEnd_5708232 : Nat := 2931066703375615749748325

theorem tailTrace_5708232 : CollatzResearch.WordTrace tailWord_5708232 prefixEnd_5708232 2931066703375615749748325 := by
  unfold tailWord_5708232
  simp only [CollatzResearch.WordTrace]
  refine ⟨104098162528028913627939475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138797550037371884837252633 104098162528028913627939475)
  ·
    refine ⟨156147243792043370441909213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104098162528028913627939475 156147243792043370441909213)
    ·
      refine ⟨58555216422016263915715955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156147243792043370441909213 58555216422016263915715955)
      ·
        refine ⟨87832824633024395873573933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58555216422016263915715955 87832824633024395873573933)
        ·
          refine ⟨32937309237384148452590225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87832824633024395873573933 32937309237384148452590225)
          ·
            refine ⟨24702981928038111339442669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32937309237384148452590225 24702981928038111339442669)
            ·
              refine ⟨9263618223014291752291001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24702981928038111339442669 9263618223014291752291001)
              ·
                refine ⟨6947713667260718814218251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9263618223014291752291001 6947713667260718814218251)
                ·
                  refine ⟨10421570500891078221327377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6947713667260718814218251 10421570500891078221327377)
                  ·
                    refine ⟨7816177875668308665995533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10421570500891078221327377 7816177875668308665995533)
                    ·
                      refine ⟨2931066703375615749748325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7816177875668308665995533 2931066703375615749748325)
                      ·
                        rfl

theorem cell23_5708232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_5708232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708232 prefixEnd_5708232 := by exact prefixLift 5708232
  have htrace : WordTrace (prefixWord ++ tailWord_5708232) baseStart_5708232 baseEnd_5708232 := by
    simpa [prefixWord, tailWord_5708232, baseEnd_5708232] using wordTrace_append hprefix tailTrace_5708232
  have hstable : (prefixWord ++ tailWord_5708232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708232).length < 2 ^ (prefixWord ++ tailWord_5708232).sum := by decide
  have hdescent : baseEnd_5708232 < baseStart_5708232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708245 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 3, 3, 3]
def baseStart_5708245 : Nat := 118140960795 + 5708245 * 2 ^ 59
def prefixEnd_5708245 : Nat := 4983230072969 + 3 ^ 40 * 5708245 * 2
def baseEnd_5708245 : Nat := 2931073378624124198885765

theorem tailTrace_5708245 : CollatzResearch.WordTrace tailWord_5708245 prefixEnd_5708245 2931073378624124198885765 := by
  unfold tailWord_5708245
  simp only [CollatzResearch.WordTrace]
  refine ⟨208196799205010730476102189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138797866136673820317401459 208196799205010730476102189)
  ·
    refine ⟨78073799701879023928538321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208196799205010730476102189 78073799701879023928538321)
    ·
      refine ⟨58555349776409267946403741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78073799701879023928538321 58555349776409267946403741)
      ·
        refine ⟨21958256166153475479901403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58555349776409267946403741 21958256166153475479901403)
        ·
          refine ⟨32937384249230213219852105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21958256166153475479901403 32937384249230213219852105)
          ·
            refine ⟨24703038186922659914889079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32937384249230213219852105 24703038186922659914889079)
            ·
              refine ⟨37054557280383989872333619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24703038186922659914889079 37054557280383989872333619)
              ·
                refine ⟨55581835920575984808500429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37054557280383989872333619 55581835920575984808500429)
                ·
                  refine ⟨20843188470215994303187661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55581835920575984808500429 20843188470215994303187661)
                  ·
                    refine ⟨7816195676330997863695373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20843188470215994303187661 7816195676330997863695373)
                    ·
                      refine ⟨2931073378624124198885765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7816195676330997863695373 2931073378624124198885765)
                      ·
                        rfl

theorem cell23_5708245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_5708245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708245 prefixEnd_5708245 := by exact prefixLift 5708245
  have htrace : WordTrace (prefixWord ++ tailWord_5708245) baseStart_5708245 baseEnd_5708245 := by
    simpa [prefixWord, tailWord_5708245, baseEnd_5708245] using wordTrace_append hprefix tailTrace_5708245
  have hstable : (prefixWord ++ tailWord_5708245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708245).length < 2 ^ (prefixWord ++ tailWord_5708245).sum := by decide
  have hdescent : baseEnd_5708245 < baseStart_5708245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708268 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 4]
def baseStart_5708268 : Nat := 118140960795 + 5708268 * 2 ^ 59
def prefixEnd_5708268 : Nat := 4983230072969 + 3 ^ 40 * 5708268 * 2
def baseEnd_5708268 : Nat := 2931085188679177608898159

theorem tailTrace_5708268 : CollatzResearch.WordTrace tailWord_5708268 prefixEnd_5708268 2931085188679177608898159 := by
  unfold tailWord_5708268
  simp only [CollatzResearch.WordTrace]
  refine ⟨104098819041963702702094729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138798425389284936936126305 104098819041963702702094729)
  ·
    refine ⟨78074114281472777026571047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104098819041963702702094729 78074114281472777026571047)
    ·
      refine ⟨117111171422209165539856571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78074114281472777026571047 117111171422209165539856571)
      ·
        refine ⟨175666757133313748309784857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117111171422209165539856571 175666757133313748309784857)
        ·
          refine ⟨131750067849985311232338643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175666757133313748309784857 131750067849985311232338643)
          ·
            refine ⟨197625101774977966848507965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131750067849985311232338643 197625101774977966848507965)
            ·
              refine ⟨74109413165616737568190487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197625101774977966848507965 74109413165616737568190487)
              ·
                refine ⟨111164119748425106352285731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74109413165616737568190487 111164119748425106352285731)
                ·
                  refine ⟨166746179622637659528428597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111164119748425106352285731 166746179622637659528428597)
                  ·
                    refine ⟨15632454339622280580790181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 166746179622637659528428597 15632454339622280580790181)
                    ·
                      refine ⟨2931085188679177608898159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15632454339622280580790181 2931085188679177608898159)
                      ·
                        rfl

theorem cell23_5708268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_5708268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708268 prefixEnd_5708268 := by exact prefixLift 5708268
  have htrace : WordTrace (prefixWord ++ tailWord_5708268) baseStart_5708268 baseEnd_5708268 := by
    simpa [prefixWord, tailWord_5708268, baseEnd_5708268] using wordTrace_append hprefix tailTrace_5708268
  have hstable : (prefixWord ++ tailWord_5708268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708268).length < 2 ^ (prefixWord ++ tailWord_5708268).sum := by decide
  have hdescent : baseEnd_5708268 < baseStart_5708268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708342 : List Nat := [5, 1, 2, 1, 2, 1, 2, 2, 7]
def baseStart_5708342 : Nat := 118140960795 + 5708342 * 2 ^ 59
def prefixEnd_5708342 : Nat := 4983230072969 + 3 ^ 40 * 5708342 * 2
def baseEnd_5708342 : Nat := 325680354027512257708091

theorem tailTrace_5708342 : CollatzResearch.WordTrace tailWord_5708342 prefixEnd_5708342 325680354027512257708091 := by
  unfold tailWord_5708342
  simp only [CollatzResearch.WordTrace]
  refine ⟨13012521067853707252648955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138800224723772877361588853 13012521067853707252648955)
  ·
    refine ⟨19518781601780560878973433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13012521067853707252648955 19518781601780560878973433)
    ·
      refine ⟨14639086201335420659230075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19518781601780560878973433 14639086201335420659230075)
      ·
        refine ⟨21958629302003130988845113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14639086201335420659230075 21958629302003130988845113)
        ·
          refine ⟨16468971976502348241633835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21958629302003130988845113 16468971976502348241633835)
          ·
            refine ⟨24703457964753522362450753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16468971976502348241633835 24703457964753522362450753)
            ·
              refine ⟨18527593473565141771838065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24703457964753522362450753 18527593473565141771838065)
              ·
                refine ⟨13895695105173856328878549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18527593473565141771838065 13895695105173856328878549)
                ·
                  refine ⟨325680354027512257708091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13895695105173856328878549 325680354027512257708091)
                  ·
                    rfl

theorem cell23_5708342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_5708342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708342 prefixEnd_5708342 := by exact prefixLift 5708342
  have htrace : WordTrace (prefixWord ++ tailWord_5708342) baseStart_5708342 baseEnd_5708342 := by
    simpa [prefixWord, tailWord_5708342, baseEnd_5708342] using wordTrace_append hprefix tailTrace_5708342
  have hstable : (prefixWord ++ tailWord_5708342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708342).length < 2 ^ (prefixWord ++ tailWord_5708342).sum := by decide
  have hdescent : baseEnd_5708342 < baseStart_5708342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708356 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_5708356 : Nat := 118140960795 + 5708356 * 2 ^ 59
def prefixEnd_5708356 : Nat := 4983230072969 + 3 ^ 40 * 5708356 * 2
def baseEnd_5708356 : Nat := 2931130374976773264597755

theorem tailTrace_5708356 : CollatzResearch.WordTrace tailWord_5708356 prefixEnd_5708356 2931130374976773264597755 := by
  unfold tailWord_5708356
  simp only [CollatzResearch.WordTrace]
  refine ⟨104100423853804298216696461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138800565138405730955595281 104100423853804298216696461)
  ·
    refine ⟨39037658945176611831261173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104100423853804298216696461 39037658945176611831261173)
    ·
      refine ⟨3659780526110307359180735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39037658945176611831261173 3659780526110307359180735)
      ·
        refine ⟨5489670789165461038771103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3659780526110307359180735 5489670789165461038771103)
        ·
          refine ⟨8234506183748191558156655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5489670789165461038771103 8234506183748191558156655)
          ·
            refine ⟨12351759275622287337234983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8234506183748191558156655 12351759275622287337234983)
            ·
              refine ⟨18527638913433431005852475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12351759275622287337234983 18527638913433431005852475)
              ·
                refine ⟨27791458370150146508778713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18527638913433431005852475 27791458370150146508778713)
                ·
                  refine ⟨20843593777612609881584035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27791458370150146508778713 20843593777612609881584035)
                  ·
                    refine ⟨31265390666418914822376053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20843593777612609881584035 31265390666418914822376053)
                    ·
                      refine ⟨2931130374976773264597755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31265390666418914822376053 2931130374976773264597755)
                      ·
                        rfl

theorem cell23_5708356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_5708356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708356 prefixEnd_5708356 := by exact prefixLift 5708356
  have htrace : WordTrace (prefixWord ++ tailWord_5708356) baseStart_5708356 baseEnd_5708356 := by
    simpa [prefixWord, tailWord_5708356, baseEnd_5708356] using wordTrace_append hprefix tailTrace_5708356
  have hstable : (prefixWord ++ tailWord_5708356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708356).length < 2 ^ (prefixWord ++ tailWord_5708356).sum := by decide
  have hdescent : baseEnd_5708356 < baseStart_5708356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708359 : List Nat := [1, 1, 4, 1, 4, 3, 1, 3, 5]
def baseStart_5708359 : Nat := 118140960795 + 5708359 * 2 ^ 59
def prefixEnd_5708359 : Nat := 4983230072969 + 3 ^ 40 * 5708359 * 2
def baseEnd_5708359 : Nat := 325681323935415194762249

theorem tailTrace_5708359 : CollatzResearch.WordTrace tailWord_5708359 prefixEnd_5708359 325681323935415194762249 := by
  unfold tailWord_5708359
  simp only [CollatzResearch.WordTrace]
  refine ⟨208200957126597727945752131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138800638084398485297168087 208200957126597727945752131)
  ·
    refine ⟨312301435689896591918628197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208200957126597727945752131 312301435689896591918628197)
    ·
      refine ⟨58556519191855610984742787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 312301435689896591918628197 58556519191855610984742787)
      ·
        refine ⟨87834778787783416477114181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58556519191855610984742787 87834778787783416477114181)
        ·
          refine ⟨16469021022709390589458909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87834778787783416477114181 16469021022709390589458909)
          ·
            refine ⟨6175882883516021471047091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16469021022709390589458909 6175882883516021471047091)
            ·
              refine ⟨9263824325274032206570637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6175882883516021471047091 9263824325274032206570637)
              ·
                refine ⟨3473934121977762077463989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9263824325274032206570637 3473934121977762077463989)
                ·
                  refine ⟨325681323935415194762249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3473934121977762077463989 325681323935415194762249)
                  ·
                    rfl

theorem cell23_5708359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 5].length) (baseStart_5708359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708359 prefixEnd_5708359 := by exact prefixLift 5708359
  have htrace : WordTrace (prefixWord ++ tailWord_5708359) baseStart_5708359 baseEnd_5708359 := by
    simpa [prefixWord, tailWord_5708359, baseEnd_5708359] using wordTrace_append hprefix tailTrace_5708359
  have hstable : (prefixWord ++ tailWord_5708359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708359).length < 2 ^ (prefixWord ++ tailWord_5708359).sum := by decide
  have hdescent : baseEnd_5708359 < baseStart_5708359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708372 : List Nat := [2, 4, 1, 1, 1, 4, 1, 2, 2, 5]
def baseStart_5708372 : Nat := 118140960795 + 5708372 * 2 ^ 59
def prefixEnd_5708372 : Nat := 4983230072969 + 3 ^ 40 * 5708372 * 2
def baseEnd_5708372 : Nat := 977046196889081733999227

theorem tailTrace_5708372 : CollatzResearch.WordTrace tailWord_5708372 prefixEnd_5708372 977046196889081733999227 := by
  unfold tailWord_5708372
  simp only [CollatzResearch.WordTrace]
  refine ⟨104100715637775315582987685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138800954183700420777316913 104100715637775315582987685)
  ·
    refine ⟨19518884182082871671810191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104100715637775315582987685 19518884182082871671810191)
    ·
      refine ⟨29278326273124307507715287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19518884182082871671810191 29278326273124307507715287)
      ·
        refine ⟨43917489409686461261572931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29278326273124307507715287 43917489409686461261572931)
        ·
          refine ⟨65876234114529691892359397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43917489409686461261572931 65876234114529691892359397)
          ·
            refine ⟨12351793896474317229817387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65876234114529691892359397 12351793896474317229817387)
            ·
              refine ⟨18527690844711475844726081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12351793896474317229817387 18527690844711475844726081)
              ·
                refine ⟨13895768133533606883544561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18527690844711475844726081 13895768133533606883544561)
                ·
                  refine ⟨10421826100150205162658421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13895768133533606883544561 10421826100150205162658421)
                  ·
                    refine ⟨977046196889081733999227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10421826100150205162658421 977046196889081733999227)
                    ·
                      rfl

theorem cell23_5708372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_5708372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708372 prefixEnd_5708372 := by exact prefixLift 5708372
  have htrace : WordTrace (prefixWord ++ tailWord_5708372) baseStart_5708372 baseEnd_5708372 := by
    simpa [prefixWord, tailWord_5708372, baseEnd_5708372] using wordTrace_append hprefix tailTrace_5708372
  have hstable : (prefixWord ++ tailWord_5708372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708372).length < 2 ^ (prefixWord ++ tailWord_5708372).sum := by decide
  have hdescent : baseEnd_5708372 < baseStart_5708372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708395 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 3]
def baseStart_5708395 : Nat := 118140960795 + 5708395 * 2 ^ 59
def prefixEnd_5708395 : Nat := 4983230072969 + 3 ^ 40 * 5708395 * 2
def baseEnd_5708395 : Nat := 2931150400722298612010075

theorem tailTrace_5708395 : CollatzResearch.WordTrace tailWord_5708395 prefixEnd_5708395 2931150400722298612010075 := by
  unfold tailWord_5708395
  simp only [CollatzResearch.WordTrace]
  refine ⟨208202270154467306094062639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138801513436311537396041759 208202270154467306094062639)
  ·
    refine ⟨312303405231700959141093959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208202270154467306094062639 312303405231700959141093959)
    ·
      refine ⟨468455107847551438711640939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312303405231700959141093959 468455107847551438711640939)
      ·
        refine ⟨702682661771327158067461409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468455107847551438711640939 702682661771327158067461409)
        ·
          refine ⟨527011996328495368550596057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 702682661771327158067461409 527011996328495368550596057)
          ·
            refine ⟨395258997246371526412947043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 527011996328495368550596057 395258997246371526412947043)
            ·
              refine ⟨592888495869557289619420565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395258997246371526412947043 592888495869557289619420565)
              ·
                refine ⟨27791648243885497950910339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 592888495869557289619420565 27791648243885497950910339)
                ·
                  refine ⟨41687472365828246926365509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27791648243885497950910339 41687472365828246926365509)
                  ·
                    refine ⟨7816401068592796298693533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41687472365828246926365509 7816401068592796298693533)
                    ·
                      refine ⟨2931150400722298612010075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7816401068592796298693533 2931150400722298612010075)
                      ·
                        rfl

theorem cell23_5708395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 3].length) (baseStart_5708395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708395 prefixEnd_5708395 := by exact prefixLift 5708395
  have htrace : WordTrace (prefixWord ++ tailWord_5708395) baseStart_5708395 baseEnd_5708395 := by
    simpa [prefixWord, tailWord_5708395, baseEnd_5708395] using wordTrace_append hprefix tailTrace_5708395
  have hstable : (prefixWord ++ tailWord_5708395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708395).length < 2 ^ (prefixWord ++ tailWord_5708395).sum := by decide
  have hdescent : baseEnd_5708395 < baseStart_5708395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708412 : List Nat := [2, 2, 2, 1, 1, 2, 3, 3, 2, 2, 3]
def baseStart_5708412 : Nat := 118140960795 + 5708412 * 2 ^ 59
def prefixEnd_5708412 : Nat := 4983230072969 + 3 ^ 40 * 5708412 * 2
def baseEnd_5708412 : Nat := 2931159129893425045497497

theorem tailTrace_5708412 : CollatzResearch.WordTrace tailWord_5708412 prefixEnd_5708412 2931159129893425045497497 := by
  unfold tailWord_5708412
  simp only [CollatzResearch.WordTrace]
  refine ⟨104101445097702858998715745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138801926796937145331620993 104101445097702858998715745)
  ·
    refine ⟨78076083823277144249036809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104101445097702858998715745 78076083823277144249036809)
    ·
      refine ⟨58557062867457858186777607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78076083823277144249036809 58557062867457858186777607)
      ·
        refine ⟨87835594301186787280166411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58557062867457858186777607 87835594301186787280166411)
        ·
          refine ⟨131753391451780180920249617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87835594301186787280166411 131753391451780180920249617)
          ·
            refine ⟨98815043588835135690187213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131753391451780180920249617 98815043588835135690187213)
            ·
              refine ⟨37055641345813175883820205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98815043588835135690187213 37055641345813175883820205)
              ·
                refine ⟨13895865504679940956432577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37055641345813175883820205 13895865504679940956432577)
                ·
                  refine ⟨10421899128509955717324433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13895865504679940956432577 10421899128509955717324433)
                  ·
                    refine ⟨7816424346382466787993325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10421899128509955717324433 7816424346382466787993325)
                    ·
                      refine ⟨2931159129893425045497497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7816424346382466787993325 2931159129893425045497497)
                      ·
                        rfl

theorem cell23_5708412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_5708412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708412 prefixEnd_5708412 := by exact prefixLift 5708412
  have htrace : WordTrace (prefixWord ++ tailWord_5708412) baseStart_5708412 baseEnd_5708412 := by
    simpa [prefixWord, tailWord_5708412, baseEnd_5708412] using wordTrace_append hprefix tailTrace_5708412
  have hstable : (prefixWord ++ tailWord_5708412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708412).length < 2 ^ (prefixWord ++ tailWord_5708412).sum := by decide
  have hdescent : baseEnd_5708412 < baseStart_5708412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708470 : List Nat := [5, 1, 3, 1, 2, 1, 2, 3, 1, 4]
def baseStart_5708470 : Nat := 118140960795 + 5708470 * 2 ^ 59
def prefixEnd_5708470 : Nat := 4983230072969 + 3 ^ 40 * 5708470 * 2
def baseEnd_5708470 : Nat := 977062970590461939524077

theorem tailTrace_5708470 : CollatzResearch.WordTrace tailWord_5708470 prefixEnd_5708470 977062970590461939524077 := by
  unfold tailWord_5708470
  simp only [CollatzResearch.WordTrace]
  refine ⟨13012812851824724618940179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138803337086130395935361909 13012812851824724618940179)
  ·
    refine ⟨19519219277737086928410269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13012812851824724618940179 19519219277737086928410269)
    ·
      refine ⟨7319707229151407598153851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19519219277737086928410269 7319707229151407598153851)
      ·
        refine ⟨10979560843727111397230777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7319707229151407598153851 10979560843727111397230777)
        ·
          refine ⟨8234670632795333547923083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10979560843727111397230777 8234670632795333547923083)
          ·
            refine ⟨12352005949193000321884625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8234670632795333547923083 12352005949193000321884625)
            ·
              refine ⟨9264004461894750241413469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12352005949193000321884625 9264004461894750241413469)
              ·
                refine ⟨3474001673210531340530051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9264004461894750241413469 3474001673210531340530051)
                ·
                  refine ⟨5211002509815797010795077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3474001673210531340530051 5211002509815797010795077)
                  ·
                    refine ⟨977062970590461939524077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5211002509815797010795077 977062970590461939524077)
                    ·
                      rfl

theorem cell23_5708470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_5708470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708470 prefixEnd_5708470 := by exact prefixLift 5708470
  have htrace : WordTrace (prefixWord ++ tailWord_5708470) baseStart_5708470 baseEnd_5708470 := by
    simpa [prefixWord, tailWord_5708470, baseEnd_5708470] using wordTrace_append hprefix tailTrace_5708470
  have hstable : (prefixWord ++ tailWord_5708470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708470).length < 2 ^ (prefixWord ++ tailWord_5708470).sum := by decide
  have hdescent : baseEnd_5708470 < baseStart_5708470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708479 : List Nat := [1, 1, 2, 2, 2, 4, 4, 1, 1, 5]
def baseStart_5708479 : Nat := 118140960795 + 5708479 * 2 ^ 59
def prefixEnd_5708479 : Nat := 4983230072969 + 3 ^ 40 * 5708479 * 2
def baseEnd_5708479 : Nat := 977064511032425427786563

theorem tailTrace_5708479 : CollatzResearch.WordTrace tailWord_5708479 prefixEnd_5708479 977064511032425427786563 := by
  unfold tailWord_5708479
  simp only [CollatzResearch.WordTrace]
  refine ⟨208205333886162988440120491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138803555924108658960080327 208205333886162988440120491)
  ·
    refine ⟨312308000829244482660180737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208205333886162988440120491 312308000829244482660180737)
    ·
      refine ⟨234231000621933361995135553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312308000829244482660180737 234231000621933361995135553)
      ·
        refine ⟨175673250466450021496351665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234231000621933361995135553 175673250466450021496351665)
        ·
          refine ⟨131754937849837516122263749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175673250466450021496351665 131754937849837516122263749)
          ·
            refine ⟨24704050846844534272924453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131754937849837516122263749 24704050846844534272924453)
            ·
              refine ⟨4632009533783350176173335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24704050846844534272924453 4632009533783350176173335)
              ·
                refine ⟨6948014300675025264260003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4632009533783350176173335 6948014300675025264260003)
                ·
                  refine ⟨10422021451012537896390005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6948014300675025264260003 10422021451012537896390005)
                  ·
                    refine ⟨977064511032425427786563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10422021451012537896390005 977064511032425427786563)
                    ·
                      rfl

theorem cell23_5708479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 1, 5].length) (baseStart_5708479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708479 prefixEnd_5708479 := by exact prefixLift 5708479
  have htrace : WordTrace (prefixWord ++ tailWord_5708479) baseStart_5708479 baseEnd_5708479 := by
    simpa [prefixWord, tailWord_5708479, baseEnd_5708479] using wordTrace_append hprefix tailTrace_5708479
  have hstable : (prefixWord ++ tailWord_5708479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708479).length < 2 ^ (prefixWord ++ tailWord_5708479).sum := by decide
  have hdescent : baseEnd_5708479 < baseStart_5708479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708495 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 4]
def baseStart_5708495 : Nat := 118140960795 + 5708495 * 2 ^ 59
def prefixEnd_5708495 : Nat := 4983230072969 + 3 ^ 40 * 5708495 * 2
def baseEnd_5708495 : Nat := 2931201748787748220759615

theorem tailTrace_5708495 : CollatzResearch.WordTrace tailWord_5708495 prefixEnd_5708495 2931201748787748220759615 := by
  unfold tailWord_5708495
  simp only [CollatzResearch.WordTrace]
  refine ⟨208205917454105023172702939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138803944969403348781801959 208205917454105023172702939)
  ·
    refine ⟨312308876181157534759054409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208205917454105023172702939 312308876181157534759054409)
    ·
      refine ⟨234231657135868151069290807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312308876181157534759054409 234231657135868151069290807)
      ·
        refine ⟨351347485703802226603936211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234231657135868151069290807 351347485703802226603936211)
        ·
          refine ⟨527021228555703339905904317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351347485703802226603936211 527021228555703339905904317)
          ·
            refine ⟨197632960708388752464714119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 527021228555703339905904317 197632960708388752464714119)
            ·
              refine ⟨296449441062583128697071179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197632960708388752464714119 296449441062583128697071179)
              ·
                refine ⟨444674161593874693045606769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296449441062583128697071179 444674161593874693045606769)
                ·
                  refine ⟨333505621195406019784205077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 444674161593874693045606769 333505621195406019784205077)
                  ·
                    refine ⟨15633075993534657177384613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 333505621195406019784205077 15633075993534657177384613)
                    ·
                      refine ⟨2931201748787748220759615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15633075993534657177384613 2931201748787748220759615)
                      ·
                        rfl

theorem cell23_5708495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 4].length) (baseStart_5708495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708495 prefixEnd_5708495 := by exact prefixLift 5708495
  have htrace : WordTrace (prefixWord ++ tailWord_5708495) baseStart_5708495 baseEnd_5708495 := by
    simpa [prefixWord, tailWord_5708495, baseEnd_5708495] using wordTrace_append hprefix tailTrace_5708495
  have hstable : (prefixWord ++ tailWord_5708495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708495).length < 2 ^ (prefixWord ++ tailWord_5708495).sum := by decide
  have hdescent : baseEnd_5708495 < baseStart_5708495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708505 : List Nat := [1, 2, 1, 2, 3, 2, 2, 10]
def baseStart_5708505 : Nat := 118140960795 + 5708505 * 2 ^ 59
def prefixEnd_5708505 : Nat := 4983230072969 + 3 ^ 40 * 5708505 * 2
def baseEnd_5708505 : Nat := 108563217910899747467947

theorem tailTrace_5708505 : CollatzResearch.WordTrace tailWord_5708505 prefixEnd_5708505 108563217910899747467947 := by
  unfold tailWord_5708505
  simp only [CollatzResearch.WordTrace]
  refine ⟨208206282184068794880566969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138804188122712529920377979 208206282184068794880566969)
  ·
    refine ⟨156154711638051596160425227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208206282184068794880566969 156154711638051596160425227)
    ·
      refine ⟨234232067457077394240637841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156154711638051596160425227 234232067457077394240637841)
      ·
        refine ⟨175674050592808045680478381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234232067457077394240637841 175674050592808045680478381)
        ·
          refine ⟨65877768972303017130179393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175674050592808045680478381 65877768972303017130179393)
          ·
            refine ⟨49408326729227262847634545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65877768972303017130179393 49408326729227262847634545)
            ·
              refine ⟨37056245046920447135725909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49408326729227262847634545 37056245046920447135725909)
              ·
                refine ⟨108563217910899747467947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37056245046920447135725909 108563217910899747467947)
                ·
                  rfl

theorem cell23_5708505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 10].length) (baseStart_5708505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708505 prefixEnd_5708505 := by exact prefixLift 5708505
  have htrace : WordTrace (prefixWord ++ tailWord_5708505) baseStart_5708505 baseEnd_5708505 := by
    simpa [prefixWord, tailWord_5708505, baseEnd_5708505] using wordTrace_append hprefix tailTrace_5708505
  have hstable : (prefixWord ++ tailWord_5708505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708505).length < 2 ^ (prefixWord ++ tailWord_5708505).sum := by decide
  have hdescent : baseEnd_5708505 < baseStart_5708505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708516 : List Nat := [2, 3, 1, 1, 1, 4, 2, 2, 3, 2, 2]
def baseStart_5708516 : Nat := 118140960795 + 5708516 * 2 ^ 59
def prefixEnd_5708516 : Nat := 4983230072969 + 3 ^ 40 * 5708516 * 2
def baseEnd_5708516 : Nat := 2931212531881492638597019

theorem tailTrace_5708516 : CollatzResearch.WordTrace tailWord_5708516 prefixEnd_5708516 2931212531881492638597019 := by
  unfold tailWord_5708516
  simp only [CollatzResearch.WordTrace]
  refine ⟨104103341693514471879608701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138804455591352629172811601 104103341693514471879608701)
  ·
    refine ⟨39038753135067926954853263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104103341693514471879608701 39038753135067926954853263)
    ·
      refine ⟨58558129702601890432279895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39038753135067926954853263 58558129702601890432279895)
      ·
        refine ⟨87837194553902835648419843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58558129702601890432279895 87837194553902835648419843)
        ·
          refine ⟨131755791830854253472629765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87837194553902835648419843 131755791830854253472629765)
          ·
            refine ⟨24704210968285172526118081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131755791830854253472629765 24704210968285172526118081)
            ·
              refine ⟨18528158226213879394588561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24704210968285172526118081 18528158226213879394588561)
              ·
                refine ⟨13896118669660409545941421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18528158226213879394588561 13896118669660409545941421)
                ·
                  refine ⟨5211044501122653579728033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13896118669660409545941421 5211044501122653579728033)
                  ·
                    refine ⟨3908283375841990184796025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5211044501122653579728033 3908283375841990184796025)
                    ·
                      refine ⟨2931212531881492638597019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3908283375841990184796025 2931212531881492638597019)
                      ·
                        rfl

theorem cell23_5708516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 3, 2, 2].length) (baseStart_5708516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708516 prefixEnd_5708516 := by exact prefixLift 5708516
  have htrace : WordTrace (prefixWord ++ tailWord_5708516) baseStart_5708516 baseEnd_5708516 := by
    simpa [prefixWord, tailWord_5708516, baseEnd_5708516] using wordTrace_append hprefix tailTrace_5708516
  have hstable : (prefixWord ++ tailWord_5708516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708516).length < 2 ^ (prefixWord ++ tailWord_5708516).sum := by decide
  have hdescent : baseEnd_5708516 < baseStart_5708516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708535 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 1, 9]
def baseStart_5708535 : Nat := 118140960795 + 5708535 * 2 ^ 59
def prefixEnd_5708535 : Nat := 4983230072969 + 3 ^ 40 * 5708535 * 2
def baseEnd_5708535 : Nat := 977074096004642688086477

theorem tailTrace_5708535 : CollatzResearch.WordTrace tailWord_5708535 prefixEnd_5708535 977074096004642688086477 := by
  unfold tailWord_5708535
  simp only [CollatzResearch.WordTrace]
  refine ⟨208207376373960110004159059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138804917582640073336106039 208207376373960110004159059)
  ·
    refine ⟨312311064560940165006238589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208207376373960110004159059 312311064560940165006238589)
    ·
      refine ⟨117116649210352561877339471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312311064560940165006238589 117116649210352561877339471)
      ·
        refine ⟨175674973815528842816009207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117116649210352561877339471 175674973815528842816009207)
        ·
          refine ⟨263512460723293264224013811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175674973815528842816009207 263512460723293264224013811)
          ·
            refine ⟨395268691084939896336020717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263512460723293264224013811 395268691084939896336020717)
            ·
              refine ⟨148225759156852461126007769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 395268691084939896336020717 148225759156852461126007769)
              ·
                refine ⟨111169319367639345844505827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148225759156852461126007769 111169319367639345844505827)
                ·
                  refine ⟨166753979051459018766758741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111169319367639345844505827 166753979051459018766758741)
                  ·
                    refine ⟨977074096004642688086477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 166753979051459018766758741 977074096004642688086477)
                    ·
                      rfl

theorem cell23_5708535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_5708535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708535 prefixEnd_5708535 := by exact prefixLift 5708535
  have htrace : WordTrace (prefixWord ++ tailWord_5708535) baseStart_5708535 baseEnd_5708535 := by
    simpa [prefixWord, tailWord_5708535, baseEnd_5708535] using wordTrace_append hprefix tailTrace_5708535
  have hstable : (prefixWord ++ tailWord_5708535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708535).length < 2 ^ (prefixWord ++ tailWord_5708535).sum := by decide
  have hdescent : baseEnd_5708535 < baseStart_5708535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708559 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 3, 3, 2]
def baseStart_5708559 : Nat := 118140960795 + 5708559 * 2 ^ 59
def prefixEnd_5708559 : Nat := 4983230072969 + 3 ^ 40 * 5708559 * 2
def baseEnd_5708559 : Nat := 2931234611549635970359321

theorem tailTrace_5708559 : CollatzResearch.WordTrace tailWord_5708559 prefixEnd_5708559 2931234611549635970359321 := by
  unfold tailWord_5708559
  simp only [CollatzResearch.WordTrace]
  refine ⟨208208251725873162103032731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138805501150582108068688487 208208251725873162103032731)
  ·
    refine ⟨312312377588809743154549097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208208251725873162103032731 312312377588809743154549097)
    ·
      refine ⟨234234283191607307365911823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312312377588809743154549097 234234283191607307365911823)
      ·
        refine ⟨351351424787410961048867735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234234283191607307365911823 351351424787410961048867735)
        ·
          refine ⟨527027137181116441573301603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351351424787410961048867735 527027137181116441573301603)
          ·
            refine ⟨790540705771674662359952405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527027137181116441573301603 790540705771674662359952405)
            ·
              refine ⟨37056595583047249798122769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 790540705771674662359952405 37056595583047249798122769)
              ·
                refine ⟨27792446687285437348592077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37056595583047249798122769 27792446687285437348592077)
                ·
                  refine ⟨10422167507732039005722029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27792446687285437348592077 10422167507732039005722029)
                  ·
                    refine ⟨3908312815399514627145761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10422167507732039005722029 3908312815399514627145761)
                    ·
                      refine ⟨2931234611549635970359321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3908312815399514627145761 2931234611549635970359321)
                      ·
                        rfl

theorem cell23_5708559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 3, 2].length) (baseStart_5708559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708559 prefixEnd_5708559 := by exact prefixLift 5708559
  have htrace : WordTrace (prefixWord ++ tailWord_5708559) baseStart_5708559 baseEnd_5708559 := by
    simpa [prefixWord, tailWord_5708559, baseEnd_5708559] using wordTrace_append hprefix tailTrace_5708559
  have hstable : (prefixWord ++ tailWord_5708559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708559).length < 2 ^ (prefixWord ++ tailWord_5708559).sum := by decide
  have hdescent : baseEnd_5708559 < baseStart_5708559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708576 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 3, 3, 2]
def baseStart_5708576 : Nat := 118140960795 + 5708576 * 2 ^ 59
def prefixEnd_5708576 : Nat := 4983230072969 + 3 ^ 40 * 5708576 * 2
def baseEnd_5708576 : Nat := 2931243340720762403846743

theorem tailTrace_5708576 : CollatzResearch.WordTrace tailWord_5708576 prefixEnd_5708576 2931243340720762403846743 := by
  unfold tailWord_5708576
  simp only [CollatzResearch.WordTrace]
  refine ⟨104104435883405787003200791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138805914511207716004267721 104104435883405787003200791)
  ·
    refine ⟨156156653825108680504801187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104104435883405787003200791 156156653825108680504801187)
    ·
      refine ⟨234234980737663020757201781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156156653825108680504801187 234234980737663020757201781)
      ·
        refine ⟨21959529444155908195987667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 234234980737663020757201781 21959529444155908195987667)
        ·
          refine ⟨32939294166233862293981501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21959529444155908195987667 32939294166233862293981501)
          ·
            refine ⟨12352235312337698360243063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32939294166233862293981501 12352235312337698360243063)
            ·
              refine ⟨18528352968506547540364595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12352235312337698360243063 18528352968506547540364595)
              ·
                refine ⟨27792529452759821310546893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18528352968506547540364595 27792529452759821310546893)
                ·
                  refine ⟨10422198544784932991455085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27792529452759821310546893 10422198544784932991455085)
                  ·
                    refine ⟨3908324454294349871795657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10422198544784932991455085 3908324454294349871795657)
                    ·
                      refine ⟨2931243340720762403846743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3908324454294349871795657 2931243340720762403846743)
                      ·
                        rfl

theorem cell23_5708576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_5708576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708576 prefixEnd_5708576 := by exact prefixLift 5708576
  have htrace : WordTrace (prefixWord ++ tailWord_5708576) baseStart_5708576 baseEnd_5708576 := by
    simpa [prefixWord, tailWord_5708576, baseEnd_5708576] using wordTrace_append hprefix tailTrace_5708576
  have hstable : (prefixWord ++ tailWord_5708576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708576).length < 2 ^ (prefixWord ++ tailWord_5708576).sum := by decide
  have hdescent : baseEnd_5708576 < baseStart_5708576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708592 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 3]
def baseStart_5708592 : Nat := 118140960795 + 5708592 * 2 ^ 59
def prefixEnd_5708592 : Nat := 4983230072969 + 3 ^ 40 * 5708592 * 2
def baseEnd_5708592 : Nat := 2931251556411234341246669

theorem tailTrace_5708592 : CollatzResearch.WordTrace tailWord_5708592 prefixEnd_5708592 2931251556411234341246669 := by
  unfold tailWord_5708592
  simp only [CollatzResearch.WordTrace]
  refine ⟨104104727667376804369492015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138806303556502405825989353 104104727667376804369492015)
  ·
    refine ⟨156157091501065206554238023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104104727667376804369492015 156157091501065206554238023)
    ·
      refine ⟨234235637251597809831357035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156157091501065206554238023 234235637251597809831357035)
      ·
        refine ⟨351353455877396714747035553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234235637251597809831357035 351353455877396714747035553)
        ·
          refine ⟨263515091908047536060276665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351353455877396714747035553 263515091908047536060276665)
          ·
            refine ⟨197636318931035652045207499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263515091908047536060276665 197636318931035652045207499)
            ·
              refine ⟨296454478396553478067811249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197636318931035652045207499 296454478396553478067811249)
              ·
                refine ⟨222340858797415108550858437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296454478396553478067811249 222340858797415108550858437)
                ·
                  refine ⟨41688911024515332853285957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 222340858797415108550858437 41688911024515332853285957)
                  ·
                    refine ⟨7816670817096624909991117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41688911024515332853285957 7816670817096624909991117)
                    ·
                      refine ⟨2931251556411234341246669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7816670817096624909991117 2931251556411234341246669)
                      ·
                        rfl

theorem cell23_5708592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 3].length) (baseStart_5708592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708592 prefixEnd_5708592 := by exact prefixLift 5708592
  have htrace : WordTrace (prefixWord ++ tailWord_5708592) baseStart_5708592 baseEnd_5708592 := by
    simpa [prefixWord, tailWord_5708592, baseEnd_5708592] using wordTrace_append hprefix tailTrace_5708592
  have hstable : (prefixWord ++ tailWord_5708592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708592).length < 2 ^ (prefixWord ++ tailWord_5708592).sum := by decide
  have hdescent : baseEnd_5708592 < baseStart_5708592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708593 : List Nat := [1, 2, 2, 3, 2, 1, 5, 1, 1, 3, 2]
def baseStart_5708593 : Nat := 118140960795 + 5708593 * 2 ^ 59
def prefixEnd_5708593 : Nat := 4983230072969 + 3 ^ 40 * 5708593 * 2
def baseEnd_5708593 : Nat := 2931252069891888837334165

theorem tailTrace_5708593 : CollatzResearch.WordTrace tailWord_5708593 prefixEnd_5708593 2931252069891888837334165 := by
  unfold tailWord_5708593
  simp only [CollatzResearch.WordTrace]
  refine ⟨208209491807749985909770433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138806327871833323939846955 208209491807749985909770433)
  ·
    refine ⟨156157118855812489432327825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208209491807749985909770433 156157118855812489432327825)
    ·
      refine ⟨117117839141859367074245869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156157118855812489432327825 117117839141859367074245869)
      ·
        refine ⟨43919189678197262652842201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117117839141859367074245869 43919189678197262652842201)
        ·
          refine ⟨32939392258647946989631651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43919189678197262652842201 32939392258647946989631651)
          ·
            refine ⟨49409088387971920484447477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32939392258647946989631651 49409088387971920484447477)
            ·
              refine ⟨4632102036372367545416951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49409088387971920484447477 4632102036372367545416951)
              ·
                refine ⟨6948153054558551318125427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4632102036372367545416951 6948153054558551318125427)
                ·
                  refine ⟨10422229581837826977188141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6948153054558551318125427 10422229581837826977188141)
                  ·
                    refine ⟨3908336093189185116445553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10422229581837826977188141 3908336093189185116445553)
                    ·
                      refine ⟨2931252069891888837334165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3908336093189185116445553 2931252069891888837334165)
                      ·
                        rfl

theorem cell23_5708593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_5708593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708593 prefixEnd_5708593 := by exact prefixLift 5708593
  have htrace : WordTrace (prefixWord ++ tailWord_5708593) baseStart_5708593 baseEnd_5708593 := by
    simpa [prefixWord, tailWord_5708593, baseEnd_5708593] using wordTrace_append hprefix tailTrace_5708593
  have hstable : (prefixWord ++ tailWord_5708593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708593).length < 2 ^ (prefixWord ++ tailWord_5708593).sum := by decide
  have hdescent : baseEnd_5708593 < baseStart_5708593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708674 : List Nat := [3, 4, 2, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_5708674 : Nat := 118140960795 + 5708674 * 2 ^ 59
def prefixEnd_5708674 : Nat := 4983230072969 + 3 ^ 40 * 5708674 * 2
def baseEnd_5708674 : Nat := 2931293661824903020421293

theorem tailTrace_5708674 : CollatzResearch.WordTrace tailWord_5708674 prefixEnd_5708674 2931293661824903020421293 := by
  unfold tailWord_5708674
  simp only [CollatzResearch.WordTrace]
  refine ⟨52053111530114134185867269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138808297413637691162312717 52053111530114134185867269)
  ·
    refine ⟨9759958411896400159850113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52053111530114134185867269 9759958411896400159850113)
    ·
      refine ⟨7319968808922300119887585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9759958411896400159850113 7319968808922300119887585)
      ·
        refine ⟨5489976606691725089915689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7319968808922300119887585 5489976606691725089915689)
        ·
          refine ⟨4117482455018793817436767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5489976606691725089915689 4117482455018793817436767)
          ·
            refine ⟨6176223682528190726155151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4117482455018793817436767 6176223682528190726155151)
            ·
              refine ⟨9264335523792286089232727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6176223682528190726155151 9264335523792286089232727)
              ·
                refine ⟨13896503285688429133849091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9264335523792286089232727 13896503285688429133849091)
                ·
                  refine ⟨20844754928532643700773637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13896503285688429133849091 20844754928532643700773637)
                  ·
                    refine ⟨3908391549099870693895057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20844754928532643700773637 3908391549099870693895057)
                    ·
                      refine ⟨2931293661824903020421293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3908391549099870693895057 2931293661824903020421293)
                      ·
                        rfl

theorem cell23_5708674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_5708674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708674 prefixEnd_5708674 := by exact prefixLift 5708674
  have htrace : WordTrace (prefixWord ++ tailWord_5708674) baseStart_5708674 baseEnd_5708674 := by
    simpa [prefixWord, tailWord_5708674, baseEnd_5708674] using wordTrace_append hprefix tailTrace_5708674
  have hstable : (prefixWord ++ tailWord_5708674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708674).length < 2 ^ (prefixWord ++ tailWord_5708674).sum := by decide
  have hdescent : baseEnd_5708674 < baseStart_5708674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708679 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 4]
def baseStart_5708679 : Nat := 118140960795 + 5708679 * 2 ^ 59
def prefixEnd_5708679 : Nat := 4983230072969 + 3 ^ 40 * 5708679 * 2
def baseEnd_5708679 : Nat := 2931296229228175500858769

theorem tailTrace_5708679 : CollatzResearch.WordTrace tailWord_5708679 prefixEnd_5708679 2931296229228175500858769 := by
  unfold tailWord_5708679
  simp only [CollatzResearch.WordTrace]
  refine ⟨208212628485438422597401091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138808418990292281731600727 208212628485438422597401091)
  ·
    refine ⟨312318942728157633896101637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208212628485438422597401091 312318942728157633896101637)
    ·
      refine ⟨58559801761529556355519057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 312318942728157633896101637 58559801761529556355519057)
      ·
        refine ⟨43919851321147167266639293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58559801761529556355519057 43919851321147167266639293)
        ·
          refine ⟨16469944245430187724989735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43919851321147167266639293 16469944245430187724989735)
          ·
            refine ⟨24704916368145281587484603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16469944245430187724989735 24704916368145281587484603)
            ·
              refine ⟨37057374552217922381226905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24704916368145281587484603 37057374552217922381226905)
              ·
                refine ⟨27793030914163441785920179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37057374552217922381226905 27793030914163441785920179)
                ·
                  refine ⟨41689546371245162678880269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27793030914163441785920179 41689546371245162678880269)
                  ·
                    refine ⟨15633579889216936004580101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41689546371245162678880269 15633579889216936004580101)
                    ·
                      refine ⟨2931296229228175500858769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15633579889216936004580101 2931296229228175500858769)
                      ·
                        rfl

theorem cell23_5708679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_5708679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708679 prefixEnd_5708679 := by exact prefixLift 5708679
  have htrace : WordTrace (prefixWord ++ tailWord_5708679) baseStart_5708679 baseEnd_5708679 := by
    simpa [prefixWord, tailWord_5708679, baseEnd_5708679] using wordTrace_append hprefix tailTrace_5708679
  have hstable : (prefixWord ++ tailWord_5708679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708679).length < 2 ^ (prefixWord ++ tailWord_5708679).sum := by decide
  have hdescent : baseEnd_5708679 < baseStart_5708679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708736 : List Nat := [2, 1, 1, 2, 3, 3, 4, 1, 6]
def baseStart_5708736 : Nat := 118140960795 + 5708736 * 2 ^ 59
def prefixEnd_5708736 : Nat := 4983230072969 + 3 ^ 40 * 5708736 * 2
def baseEnd_5708736 : Nat := 325702833069497975316223

theorem tailTrace_5708736 : CollatzResearch.WordTrace tailWord_5708736 prefixEnd_5708736 325702833069497975316223 := by
  unfold tailWord_5708736
  simp only [CollatzResearch.WordTrace]
  refine ⟨104107353723115960666113031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138809804964154614221484041 104107353723115960666113031)
  ·
    refine ⟨156161030584673940999169547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104107353723115960666113031 156161030584673940999169547)
    ·
      refine ⟨234241545877010911498754321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156161030584673940999169547 234241545877010911498754321)
      ·
        refine ⟨175681159407758183624065741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234241545877010911498754321 175681159407758183624065741)
        ·
          refine ⟨65880434777909318859024653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175681159407758183624065741 65880434777909318859024653)
          ·
            refine ⟨24705163041715994572134245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65880434777909318859024653 24705163041715994572134245)
            ·
              refine ⟨4632218070321748982275171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24705163041715994572134245 4632218070321748982275171)
              ·
                refine ⟨6948327105482623473412757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4632218070321748982275171 6948327105482623473412757)
                ·
                  refine ⟨325702833069497975316223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6948327105482623473412757 325702833069497975316223)
                  ·
                    rfl

theorem cell23_5708736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 6].length) (baseStart_5708736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708736 prefixEnd_5708736 := by exact prefixLift 5708736
  have htrace : WordTrace (prefixWord ++ tailWord_5708736) baseStart_5708736 baseEnd_5708736 := by
    simpa [prefixWord, tailWord_5708736, baseEnd_5708736] using wordTrace_append hprefix tailTrace_5708736
  have hstable : (prefixWord ++ tailWord_5708736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708736).length < 2 ^ (prefixWord ++ tailWord_5708736).sum := by decide
  have hdescent : baseEnd_5708736 < baseStart_5708736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708746 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 5, 1, 3]
def baseStart_5708746 : Nat := 118140960795 + 5708746 * 2 ^ 59
def prefixEnd_5708746 : Nat := 4983230072969 + 3 ^ 40 * 5708746 * 2
def baseEnd_5708746 : Nat := 2931330632432026738720961

theorem tailTrace_5708746 : CollatzResearch.WordTrace tailWord_5708746 prefixEnd_5708746 2931330632432026738720961 := by
  unfold tailWord_5708746
  simp only [CollatzResearch.WordTrace]
  refine ⟨52053768044048923260022523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138810048117463795360060061 52053768044048923260022523)
  ·
    refine ⟨78080652066073384890033785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52053768044048923260022523 78080652066073384890033785)
    ·
      refine ⟨58560489049555038667525339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78080652066073384890033785 58560489049555038667525339)
      ·
        refine ⟨87840733574332558001288009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58560489049555038667525339 87840733574332558001288009)
        ·
          refine ⟨65880550180749418500966007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87840733574332558001288009 65880550180749418500966007)
          ·
            refine ⟨98820825271124127751449011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65880550180749418500966007 98820825271124127751449011)
            ·
              refine ⟨148231237906686191627173517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98820825271124127751449011 148231237906686191627173517)
              ·
                refine ⟨55586714215007321860190069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148231237906686191627173517 55586714215007321860190069)
                ·
                  refine ⟨5211254457656936424392819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55586714215007321860190069 5211254457656936424392819)
                  ·
                    refine ⟨7816881686485404636589229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5211254457656936424392819 7816881686485404636589229)
                    ·
                      refine ⟨2931330632432026738720961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7816881686485404636589229 2931330632432026738720961)
                      ·
                        rfl

theorem cell23_5708746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_5708746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708746 prefixEnd_5708746 := by exact prefixLift 5708746
  have htrace : WordTrace (prefixWord ++ tailWord_5708746) baseStart_5708746 baseEnd_5708746 := by
    simpa [prefixWord, tailWord_5708746, baseEnd_5708746] using wordTrace_append hprefix tailTrace_5708746
  have hstable : (prefixWord ++ tailWord_5708746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708746).length < 2 ^ (prefixWord ++ tailWord_5708746).sum := by decide
  have hdescent : baseEnd_5708746 < baseStart_5708746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708796 : List Nat := [2, 2, 2, 1, 2, 4, 2, 1, 1, 6]
def baseStart_5708796 : Nat := 118140960795 + 5708796 * 2 ^ 59
def prefixEnd_5708796 : Nat := 4983230072969 + 3 ^ 40 * 5708796 * 2
def baseEnd_5708796 : Nat := 977118768821583847698577

theorem tailTrace_5708796 : CollatzResearch.WordTrace tailWord_5708796 prefixEnd_5708796 977118768821583847698577 := by
  unfold tailWord_5708796
  simp only [CollatzResearch.WordTrace]
  refine ⟨104108447913007275789705121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138811263884009701052940161 104108447913007275789705121)
  ·
    refine ⟨78081335934755456842278841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104108447913007275789705121 78081335934755456842278841)
    ·
      refine ⟨58561001951066592631709131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78081335934755456842278841 58561001951066592631709131)
      ·
        refine ⟨87841502926599888947563697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58561001951066592631709131 87841502926599888947563697)
        ·
          refine ⟨65881127194949916710672773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87841502926599888947563697 65881127194949916710672773)
          ·
            refine ⟨12352711349053109383251145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65881127194949916710672773 12352711349053109383251145)
            ·
              refine ⟨9264533511789832037438359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12352711349053109383251145 9264533511789832037438359)
              ·
                refine ⟨13896800267684748056157539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9264533511789832037438359 13896800267684748056157539)
                ·
                  refine ⟨20845200401527122084236309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13896800267684748056157539 20845200401527122084236309)
                  ·
                    refine ⟨977118768821583847698577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20845200401527122084236309 977118768821583847698577)
                    ·
                      rfl

theorem cell23_5708796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_5708796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708796 prefixEnd_5708796 := by exact prefixLift 5708796
  have htrace : WordTrace (prefixWord ++ tailWord_5708796) baseStart_5708796 baseEnd_5708796 := by
    simpa [prefixWord, tailWord_5708796, baseEnd_5708796] using wordTrace_append hprefix tailTrace_5708796
  have hstable : (prefixWord ++ tailWord_5708796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708796).length < 2 ^ (prefixWord ++ tailWord_5708796).sum := by decide
  have hdescent : baseEnd_5708796 < baseStart_5708796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708869 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 1, 8]
def baseStart_5708869 : Nat := 118140960795 + 5708869 * 2 ^ 59
def prefixEnd_5708869 : Nat := 4983230072969 + 3 ^ 40 * 5708869 * 2
def baseEnd_5708869 : Nat := 977131263517509919160965

theorem tailTrace_5708869 : CollatzResearch.WordTrace tailWord_5708869 prefixEnd_5708869 977131263517509919160965 := by
  unfold tailWord_5708869
  simp only [CollatzResearch.WordTrace]
  refine ⟨208219558354750085046817661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138813038903166723364545107 208219558354750085046817661)
  ·
    refine ⟨78082334383031281892556623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208219558354750085046817661 78082334383031281892556623)
    ·
      refine ⟨117123501574546922838834935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78082334383031281892556623 117123501574546922838834935)
      ·
        refine ⟨175685252361820384258252403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117123501574546922838834935 175685252361820384258252403)
        ·
          refine ⟨263527878542730576387378605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175685252361820384258252403 263527878542730576387378605)
          ·
            refine ⟨98822954453523966145266977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263527878542730576387378605 98822954453523966145266977)
            ·
              refine ⟨74117215840142974608950233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98822954453523966145266977 74117215840142974608950233)
              ·
                refine ⟨55587911880107230956712675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74117215840142974608950233 55587911880107230956712675)
                ·
                  refine ⟨83381867820160846435069013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55587911880107230956712675 83381867820160846435069013)
                  ·
                    refine ⟨977131263517509919160965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83381867820160846435069013 977131263517509919160965)
                    ·
                      rfl

theorem cell23_5708869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_5708869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708869 prefixEnd_5708869 := by exact prefixLift 5708869
  have htrace : WordTrace (prefixWord ++ tailWord_5708869) baseStart_5708869 baseEnd_5708869 := by
    simpa [prefixWord, tailWord_5708869, baseEnd_5708869] using wordTrace_append hprefix tailTrace_5708869
  have hstable : (prefixWord ++ tailWord_5708869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708869).length < 2 ^ (prefixWord ++ tailWord_5708869).sum := by decide
  have hdescent : baseEnd_5708869 < baseStart_5708869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708889 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 2, 3, 6]
def baseStart_5708889 : Nat := 118140960795 + 5708889 * 2 ^ 59
def prefixEnd_5708889 : Nat := 4983230072969 + 3 ^ 40 * 5708889 * 2
def baseEnd_5708889 : Nat := 2931404060165619679232803

theorem tailTrace_5708889 : CollatzResearch.WordTrace tailWord_5708889 prefixEnd_5708889 2931404060165619679232803 := by
  unfold tailWord_5708889
  simp only [CollatzResearch.WordTrace]
  refine ⟨208220287814677628462545721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138813525209785085641697147 208220287814677628462545721)
  ·
    refine ⟨156165215861008221346909291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208220287814677628462545721 156165215861008221346909291)
    ·
      refine ⟨234247823791512332020363937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156165215861008221346909291 234247823791512332020363937)
      ·
        refine ⟨175685867843634249015272953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234247823791512332020363937 175685867843634249015272953)
        ·
          refine ⟨131764400882725686761454715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175685867843634249015272953 131764400882725686761454715)
          ·
            refine ⟨197646601324088530142182073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131764400882725686761454715 197646601324088530142182073)
            ·
              refine ⟨148234950993066397606636555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197646601324088530142182073 148234950993066397606636555)
              ·
                refine ⟨222352426489599596409954833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148234950993066397606636555 222352426489599596409954833)
                ·
                  refine ⟨166764319867199697307466125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 222352426489599596409954833 166764319867199697307466125)
                  ·
                    refine ⟨62536619950199886490299797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 166764319867199697307466125 62536619950199886490299797)
                    ·
                      refine ⟨2931404060165619679232803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62536619950199886490299797 2931404060165619679232803)
                      ·
                        rfl

theorem cell23_5708889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_5708889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708889 prefixEnd_5708889 := by exact prefixLift 5708889
  have htrace : WordTrace (prefixWord ++ tailWord_5708889) baseStart_5708889 baseEnd_5708889 := by
    simpa [prefixWord, tailWord_5708889, baseEnd_5708889] using wordTrace_append hprefix tailTrace_5708889
  have hstable : (prefixWord ++ tailWord_5708889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708889).length < 2 ^ (prefixWord ++ tailWord_5708889).sum := by decide
  have hdescent : baseEnd_5708889 < baseStart_5708889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708896 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 3]
def baseStart_5708896 : Nat := 118140960795 + 5708896 * 2 ^ 59
def prefixEnd_5708896 : Nat := 4983230072969 + 3 ^ 40 * 5708896 * 2
def baseEnd_5708896 : Nat := 2931407654530201151845271

theorem tailTrace_5708896 : CollatzResearch.WordTrace tailWord_5708896 prefixEnd_5708896 2931407654530201151845271 := by
  unfold tailWord_5708896
  simp only [CollatzResearch.WordTrace]
  refine ⟨104110271562826134329025271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138813695417101512438700361 104110271562826134329025271)
  ·
    refine ⟨156165407344239201493537907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104110271562826134329025271 156165407344239201493537907)
    ·
      refine ⟨234248111016358802240306861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156165407344239201493537907 234248111016358802240306861)
      ·
        refine ⟨87843041631134550840115073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234248111016358802240306861 87843041631134550840115073)
        ·
          refine ⟨65882281223350913130086305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87843041631134550840115073 65882281223350913130086305)
          ·
            refine ⟨49411710917513184847564729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65882281223350913130086305 49411710917513184847564729)
            ·
              refine ⟨37058783188134888635673547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49411710917513184847564729 37058783188134888635673547)
              ·
                refine ⟨55588174782202332953510321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37058783188134888635673547 55588174782202332953510321)
                ·
                  refine ⟨41691131086651749715132741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55588174782202332953510321 41691131086651749715132741)
                  ·
                    refine ⟨7817087078747203071587389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41691131086651749715132741 7817087078747203071587389)
                    ·
                      refine ⟨2931407654530201151845271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7817087078747203071587389 2931407654530201151845271)
                      ·
                        rfl

theorem cell23_5708896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_5708896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708896 prefixEnd_5708896 := by exact prefixLift 5708896
  have htrace : WordTrace (prefixWord ++ tailWord_5708896) baseStart_5708896 baseEnd_5708896 := by
    simpa [prefixWord, tailWord_5708896, baseEnd_5708896] using wordTrace_append hprefix tailTrace_5708896
  have hstable : (prefixWord ++ tailWord_5708896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708896).length < 2 ^ (prefixWord ++ tailWord_5708896).sum := by decide
  have hdescent : baseEnd_5708896 < baseStart_5708896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5708983 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 1, 6, 2]
def baseStart_5708983 : Nat := 118140960795 + 5708983 * 2 ^ 59
def prefixEnd_5708983 : Nat := 4983230072969 + 3 ^ 40 * 5708983 * 2
def baseEnd_5708983 : Nat := 2931452327347142311457371

theorem tailTrace_5708983 : CollatzResearch.WordTrace tailWord_5708983 prefixEnd_5708983 2931452327347142311457371 := by
  unfold tailWord_5708983
  simp only [CollatzResearch.WordTrace]
  refine ⟨208223716276337082516467603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138815810850891388344311735 208223716276337082516467603)
  ·
    refine ⟨312335574414505623774701405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208223716276337082516467603 312335574414505623774701405)
    ·
      refine ⟨117125840405439608915513027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312335574414505623774701405 117125840405439608915513027)
      ·
        refine ⟨175688760608159413373269541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117125840405439608915513027 175688760608159413373269541)
        ·
          refine ⟨32941642614029890007488039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175688760608159413373269541 32941642614029890007488039)
          ·
            refine ⟨49412463921044835011232059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32941642614029890007488039 49412463921044835011232059)
            ·
              refine ⟨74118695881567252516848089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49412463921044835011232059 74118695881567252516848089)
              ·
                refine ⟨55589021911175439387636067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74118695881567252516848089 55589021911175439387636067)
                ·
                  refine ⟨83383532866763159081454101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55589021911175439387636067 83383532866763159081454101)
                  ·
                    refine ⟨3908603103129523081943161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83383532866763159081454101 3908603103129523081943161)
                    ·
                      refine ⟨2931452327347142311457371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3908603103129523081943161 2931452327347142311457371)
                      ·
                        rfl

theorem cell23_5708983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 6, 2].length) (baseStart_5708983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5708983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5708983 prefixEnd_5708983 := by exact prefixLift 5708983
  have htrace : WordTrace (prefixWord ++ tailWord_5708983) baseStart_5708983 baseEnd_5708983 := by
    simpa [prefixWord, tailWord_5708983, baseEnd_5708983] using wordTrace_append hprefix tailTrace_5708983
  have hstable : (prefixWord ++ tailWord_5708983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5708983).length < 2 ^ (prefixWord ++ tailWord_5708983).sum := by decide
  have hdescent : baseEnd_5708983 < baseStart_5708983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5708983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709010 : List Nat := [3, 2, 2, 2, 1, 1, 4, 1, 3, 4]
def baseStart_5709010 : Nat := 118140960795 + 5709010 * 2 ^ 59
def prefixEnd_5709010 : Nat := 4983230072969 + 3 ^ 40 * 5709010 * 2
def baseEnd_5709010 : Nat := 977155397108271235273249

theorem tailTrace_5709010 : CollatzResearch.WordTrace tailWord_5709010 prefixEnd_5709010 977155397108271235273249 := by
  unfold tailWord_5709010
  simp only [CollatzResearch.WordTrace]
  refine ⟨52056175261809816531925121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138816467364826177418466989 52056175261809816531925121)
  ·
    refine ⟨39042131446357362398943841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52056175261809816531925121 39042131446357362398943841)
    ·
      refine ⟨29281598584768021799207881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39042131446357362398943841 29281598584768021799207881)
      ·
        refine ⟨21961198938576016349405911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29281598584768021799207881 21961198938576016349405911)
        ·
          refine ⟨32941798407864024524108867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21961198938576016349405911 32941798407864024524108867)
          ·
            refine ⟨49412697611796036786163301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32941798407864024524108867 49412697611796036786163301)
            ·
              refine ⟨9264880802211756897405619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49412697611796036786163301 9264880802211756897405619)
              ·
                refine ⟨13897321203317635346108429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9264880802211756897405619 13897321203317635346108429)
                ·
                  refine ⟨5211495451244113254790661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13897321203317635346108429 5211495451244113254790661)
                  ·
                    refine ⟨977155397108271235273249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5211495451244113254790661 977155397108271235273249)
                    ·
                      rfl

theorem cell23_5709010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_5709010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709010 prefixEnd_5709010 := by exact prefixLift 5709010
  have htrace : WordTrace (prefixWord ++ tailWord_5709010) baseStart_5709010 baseEnd_5709010 := by
    simpa [prefixWord, tailWord_5709010, baseEnd_5709010] using wordTrace_append hprefix tailTrace_5709010
  have hstable : (prefixWord ++ tailWord_5709010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709010).length < 2 ^ (prefixWord ++ tailWord_5709010).sum := by decide
  have hdescent : baseEnd_5709010 < baseStart_5709010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709067 : List Nat := [1, 1, 1, 1, 5, 5, 1, 1, 3, 1, 3]
def baseStart_5709067 : Nat := 118140960795 + 5709067 * 2 ^ 59
def prefixEnd_5709067 : Nat := 4983230072969 + 3 ^ 40 * 5709067 * 2
def baseEnd_5709067 : Nat := 2931495459722119982806985

theorem tailTrace_5709067 : CollatzResearch.WordTrace tailWord_5709067 prefixEnd_5709067 2931495459722119982806985 := by
  unfold tailWord_5709067
  simp only [CollatzResearch.WordTrace]
  refine ⟨208226780008032764862525455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138817853338688509908350303 208226780008032764862525455)
  ·
    refine ⟨312340170012049147293788183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208226780008032764862525455 312340170012049147293788183)
    ·
      refine ⟨468510255018073720940682275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312340170012049147293788183 468510255018073720940682275)
      ·
        refine ⟨702765382527110581411023413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468510255018073720940682275 702765382527110581411023413)
        ·
          refine ⟨65884254611916617007283445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 702765382527110581411023413 65884254611916617007283445)
          ·
            refine ⟨6176648869867182844432823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65884254611916617007283445 6176648869867182844432823)
            ·
              refine ⟨9264973304800774266649235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6176648869867182844432823 9264973304800774266649235)
              ·
                refine ⟨13897459957201161399973853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9264973304800774266649235 13897459957201161399973853)
                ·
                  refine ⟨5211547483950435524990195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13897459957201161399973853 5211547483950435524990195)
                  ·
                    refine ⟨7817321225925653287485293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5211547483950435524990195 7817321225925653287485293)
                    ·
                      refine ⟨2931495459722119982806985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7817321225925653287485293 2931495459722119982806985)
                      ·
                        rfl

theorem cell23_5709067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 1, 3].length) (baseStart_5709067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709067 prefixEnd_5709067 := by exact prefixLift 5709067
  have htrace : WordTrace (prefixWord ++ tailWord_5709067) baseStart_5709067 baseEnd_5709067 := by
    simpa [prefixWord, tailWord_5709067, baseEnd_5709067] using wordTrace_append hprefix tailTrace_5709067
  have hstable : (prefixWord ++ tailWord_5709067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709067).length < 2 ^ (prefixWord ++ tailWord_5709067).sum := by decide
  have hdescent : baseEnd_5709067 < baseStart_5709067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709073 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 4]
def baseStart_5709073 : Nat := 118140960795 + 5709073 * 2 ^ 59
def prefixEnd_5709073 : Nat := 4983230072969 + 3 ^ 40 * 5709073 * 2
def baseEnd_5709073 : Nat := 2931498540606046959331957

theorem tailTrace_5709073 : CollatzResearch.WordTrace tailWord_5709073 prefixEnd_5709073 2931498540606046959331957 := by
  unfold tailWord_5709073
  simp only [CollatzResearch.WordTrace]
  refine ⟨208226998846011027887243873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138817999230674018591495915 208226998846011027887243873)
  ·
    refine ⟨156170249134508270915432905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208226998846011027887243873 156170249134508270915432905)
    ·
      refine ⟨117127686850881203186574679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156170249134508270915432905 117127686850881203186574679)
      ·
        refine ⟨175691530276321804779862019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117127686850881203186574679 175691530276321804779862019)
        ·
          refine ⟨263537295414482707169793029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175691530276321804779862019 263537295414482707169793029)
          ·
            refine ⟨49413242890215507594336193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 263537295414482707169793029 49413242890215507594336193)
            ·
              refine ⟨37059932167661630695752145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49413242890215507594336193 37059932167661630695752145)
              ·
                refine ⟨27794949125746223021814109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37059932167661630695752145 27794949125746223021814109)
                ·
                  refine ⟨10423105922154833633180291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27794949125746223021814109 10423105922154833633180291)
                  ·
                    refine ⟨15634658883232250449770437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10423105922154833633180291 15634658883232250449770437)
                    ·
                      refine ⟨2931498540606046959331957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15634658883232250449770437 2931498540606046959331957)
                      ·
                        rfl

theorem cell23_5709073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_5709073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709073 prefixEnd_5709073 := by exact prefixLift 5709073
  have htrace : WordTrace (prefixWord ++ tailWord_5709073) baseStart_5709073 baseEnd_5709073 := by
    simpa [prefixWord, tailWord_5709073, baseEnd_5709073] using wordTrace_append hprefix tailTrace_5709073
  have hstable : (prefixWord ++ tailWord_5709073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709073).length < 2 ^ (prefixWord ++ tailWord_5709073).sum := by decide
  have hdescent : baseEnd_5709073 < baseStart_5709073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709087 : List Nat := [1, 1, 2, 4, 4, 2, 1, 2, 1, 5]
def baseStart_5709087 : Nat := 118140960795 + 5709087 * 2 ^ 59
def prefixEnd_5709087 : Nat := 4983230072969 + 3 ^ 40 * 5709087 * 2
def baseEnd_5709087 : Nat := 977168576445069968185631

theorem tailTrace_5709087 : CollatzResearch.WordTrace tailWord_5709087 prefixEnd_5709087 977168576445069968185631 := by
  unfold tailWord_5709087
  simp only [CollatzResearch.WordTrace]
  refine ⟨208227509467960308278253515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138818339645306872185502343 208227509467960308278253515)
  ·
    refine ⟨312341264201940462417380273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208227509467960308278253515 312341264201940462417380273)
    ·
      refine ⟨234255948151455346813035205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312341264201940462417380273 234255948151455346813035205)
      ·
        refine ⟨43922990278397877527444101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234255948151455346813035205 43922990278397877527444101)
        ·
          refine ⟨8235560677199602036395769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43922990278397877527444101 8235560677199602036395769)
          ·
            refine ⟨6176670507899701527296827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8235560677199602036395769 6176670507899701527296827)
            ·
              refine ⟨9265005761849552290945241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6176670507899701527296827 9265005761849552290945241)
              ·
                refine ⟨6948754321387164218208931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9265005761849552290945241 6948754321387164218208931)
                ·
                  refine ⟨10423131482080746327313397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6948754321387164218208931 10423131482080746327313397)
                  ·
                    refine ⟨977168576445069968185631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10423131482080746327313397 977168576445069968185631)
                    ·
                      rfl

theorem cell23_5709087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 5].length) (baseStart_5709087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709087 prefixEnd_5709087 := by exact prefixLift 5709087
  have htrace : WordTrace (prefixWord ++ tailWord_5709087) baseStart_5709087 baseEnd_5709087 := by
    simpa [prefixWord, tailWord_5709087, baseEnd_5709087] using wordTrace_append hprefix tailTrace_5709087
  have hstable : (prefixWord ++ tailWord_5709087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709087).length < 2 ^ (prefixWord ++ tailWord_5709087).sum := by decide
  have hdescent : baseEnd_5709087 < baseStart_5709087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709107 : List Nat := [1, 1, 1, 2, 5, 3, 3, 1, 1, 1, 4]
def baseStart_5709107 : Nat := 118140960795 + 5709107 * 2 ^ 59
def prefixEnd_5709107 : Nat := 4983230072969 + 3 ^ 40 * 5709107 * 2
def baseEnd_5709107 : Nat := 2931515998948299826306801

theorem tailTrace_5709107 : CollatzResearch.WordTrace tailWord_5709107 prefixEnd_5709107 2931515998948299826306801 := by
  unfold tailWord_5709107
  simp only [CollatzResearch.WordTrace]
  refine ⟨208228238927887851693981575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138818825951925234462654383 208228238927887851693981575)
  ·
    refine ⟨312342358391831777540972363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208228238927887851693981575 312342358391831777540972363)
    ·
      refine ⟨468513537587747666311458545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312342358391831777540972363 468513537587747666311458545)
      ·
        refine ⟨351385153190810749733593909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 468513537587747666311458545 351385153190810749733593909)
        ·
          refine ⟨32942358111638507787524429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 351385153190810749733593909 32942358111638507787524429)
          ·
            refine ⟨12353384291864440420321661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32942358111638507787524429 12353384291864440420321661)
            ·
              refine ⟨4632519109449165157620623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12353384291864440420321661 4632519109449165157620623)
              ·
                refine ⟨6948778664173747736430935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4632519109449165157620623 6948778664173747736430935)
                ·
                  refine ⟨10423167996260621604646403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6948778664173747736430935 10423167996260621604646403)
                  ·
                    refine ⟨15634751994390932406969605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10423167996260621604646403 15634751994390932406969605)
                    ·
                      refine ⟨2931515998948299826306801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15634751994390932406969605 2931515998948299826306801)
                      ·
                        rfl

theorem cell23_5709107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 1, 1, 4].length) (baseStart_5709107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709107 prefixEnd_5709107 := by exact prefixLift 5709107
  have htrace : WordTrace (prefixWord ++ tailWord_5709107) baseStart_5709107 baseEnd_5709107 := by
    simpa [prefixWord, tailWord_5709107, baseEnd_5709107] using wordTrace_append hprefix tailTrace_5709107
  have hstable : (prefixWord ++ tailWord_5709107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709107).length < 2 ^ (prefixWord ++ tailWord_5709107).sum := by decide
  have hdescent : baseEnd_5709107 < baseStart_5709107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709113 : List Nat := [1, 2, 1, 6, 2, 11]
def baseStart_5709113 : Nat := 118140960795 + 5709113 * 2 ^ 59
def prefixEnd_5709113 : Nat := 4983230072969 + 3 ^ 40 * 5709113 * 2
def baseEnd_5709113 : Nat := 12063864526058546513711

theorem tailTrace_5709113 : CollatzResearch.WordTrace tailWord_5709113 prefixEnd_5709113 12063864526058546513711 := by
  unfold tailWord_5709113
  simp only [CollatzResearch.WordTrace]
  refine ⟨208228457765866114718699993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138818971843910743145799995 208228457765866114718699993)
  ·
    refine ⟨156171343324399586039024995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208228457765866114718699993 156171343324399586039024995)
    ·
      refine ⟨234257014986599379058537493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156171343324399586039024995 234257014986599379058537493)
      ·
        refine ⟨10980797577496845893368945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 234257014986599379058537493 10980797577496845893368945)
        ·
          refine ⟨8235598183122634420026709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10980797577496845893368945 8235598183122634420026709)
          ·
            refine ⟨12063864526058546513711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8235598183122634420026709 12063864526058546513711)
            ·
              rfl

theorem cell23_5709113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 11].length) (baseStart_5709113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709113 prefixEnd_5709113 := by exact prefixLift 5709113
  have htrace : WordTrace (prefixWord ++ tailWord_5709113) baseStart_5709113 baseEnd_5709113 := by
    simpa [prefixWord, tailWord_5709113, baseEnd_5709113] using wordTrace_append hprefix tailTrace_5709113
  have hstable : (prefixWord ++ tailWord_5709113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709113).length < 2 ^ (prefixWord ++ tailWord_5709113).sum := by decide
  have hdescent : baseEnd_5709113 < baseStart_5709113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709123 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 3]
def baseStart_5709123 : Nat := 118140960795 + 5709123 * 2 ^ 59
def prefixEnd_5709123 : Nat := 4983230072969 + 3 ^ 40 * 5709123 * 2
def baseEnd_5709123 : Nat := 2931524214638771763706727

theorem tailTrace_5709123 : CollatzResearch.WordTrace tailWord_5709123 prefixEnd_5709123 2931524214638771763706727 := by
  unfold tailWord_5709123
  simp only [CollatzResearch.WordTrace]
  refine ⟨208228822495829886426564023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138819214997219924284376015 208228822495829886426564023)
  ·
    refine ⟨312343233743744829639846035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208228822495829886426564023 312343233743744829639846035)
    ·
      refine ⟨468514850615617244459769053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312343233743744829639846035 468514850615617244459769053)
      ·
        refine ⟨175693068980856466672413395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 468514850615617244459769053 175693068980856466672413395)
        ·
          refine ⟨263539603471284700008620093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175693068980856466672413395 263539603471284700008620093)
          ·
            refine ⟨98827351301731762503232535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263539603471284700008620093 98827351301731762503232535)
            ·
              refine ⟨148241026952597643754848803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98827351301731762503232535 148241026952597643754848803)
              ·
                refine ⟨222361540428896465632273205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148241026952597643754848803 222361540428896465632273205)
                ·
                  refine ⟨20846394415209043653025613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 222361540428896465632273205 20846394415209043653025613)
                  ·
                    refine ⟨7817397905703391369884605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20846394415209043653025613 7817397905703391369884605)
                    ·
                      refine ⟨2931524214638771763706727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7817397905703391369884605 2931524214638771763706727)
                      ·
                        rfl

theorem cell23_5709123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 3].length) (baseStart_5709123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709123 prefixEnd_5709123 := by exact prefixLift 5709123
  have htrace : WordTrace (prefixWord ++ tailWord_5709123) baseStart_5709123 baseEnd_5709123 := by
    simpa [prefixWord, tailWord_5709123, baseEnd_5709123] using wordTrace_append hprefix tailTrace_5709123
  have hstable : (prefixWord ++ tailWord_5709123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709123).length < 2 ^ (prefixWord ++ tailWord_5709123).sum := by decide
  have hdescent : baseEnd_5709123 < baseStart_5709123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709167 : List Nat := [1, 1, 2, 1, 3, 1, 5, 3, 1, 3, 2]
def baseStart_5709167 : Nat := 118140960795 + 5709167 * 2 ^ 59
def prefixEnd_5709167 : Nat := 4983230072969 + 3 ^ 40 * 5709167 * 2
def baseEnd_5709167 : Nat := 2931546807787569591556525

theorem tailTrace_5709167 : CollatzResearch.WordTrace tailWord_5709167 prefixEnd_5709167 2931546807787569591556525 := by
  unfold tailWord_5709167
  simp only [CollatzResearch.WordTrace]
  refine ⟨208230427307670481941165755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138820284871780321294110503 208230427307670481941165755)
  ·
    refine ⟨312345640961505722911748633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208230427307670481941165755 312345640961505722911748633)
    ·
      refine ⟨234259230721129292183811475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312345640961505722911748633 234259230721129292183811475)
      ·
        refine ⟨351388846081693938275717213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234259230721129292183811475 351388846081693938275717213)
        ·
          refine ⟨131770817280635226853393955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 351388846081693938275717213 131770817280635226853393955)
          ·
            refine ⟨197656225920952840280090933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131770817280635226853393955 197656225920952840280090933)
            ·
              refine ⟨18530271180089328776258525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 197656225920952840280090933 18530271180089328776258525)
              ·
                refine ⟨6948851692533498291096947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18530271180089328776258525 6948851692533498291096947)
                ·
                  refine ⟨10423277538800247436645421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6948851692533498291096947 10423277538800247436645421)
                  ·
                    refine ⟨3908729077050092788742033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10423277538800247436645421 3908729077050092788742033)
                    ·
                      refine ⟨2931546807787569591556525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3908729077050092788742033 2931546807787569591556525)
                      ·
                        rfl

theorem cell23_5709167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 3, 2].length) (baseStart_5709167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709167 prefixEnd_5709167 := by exact prefixLift 5709167
  have htrace : WordTrace (prefixWord ++ tailWord_5709167) baseStart_5709167 baseEnd_5709167 := by
    simpa [prefixWord, tailWord_5709167, baseEnd_5709167] using wordTrace_append hprefix tailTrace_5709167
  have hstable : (prefixWord ++ tailWord_5709167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709167).length < 2 ^ (prefixWord ++ tailWord_5709167).sum := by decide
  have hdescent : baseEnd_5709167 < baseStart_5709167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709237 : List Nat := [1, 3, 3, 2, 2, 3, 1, 1, 7]
def baseStart_5709237 : Nat := 118140960795 + 5709237 * 2 ^ 59
def prefixEnd_5709237 : Nat := 4983230072969 + 3 ^ 40 * 5709237 * 2
def baseEnd_5709237 : Nat := 325731416825931590853467

theorem tailTrace_5709237 : CollatzResearch.WordTrace tailWord_5709237 prefixEnd_5709237 325731416825931590853467 := by
  unfold tailWord_5709237
  simp only [CollatzResearch.WordTrace]
  refine ⟨208232980417416883896213965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138821986944944589264142643 208232980417416883896213965)
  ·
    refine ⟨78087367656531331461080237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208232980417416883896213965 78087367656531331461080237)
    ·
      refine ⟨29282762871199249297905089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78087367656531331461080237 29282762871199249297905089)
      ·
        refine ⟨21962072153399436973428817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29282762871199249297905089 21962072153399436973428817)
        ·
          refine ⟨16471554115049577730071613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21962072153399436973428817 16471554115049577730071613)
          ·
            refine ⟨6176832793143591648776855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16471554115049577730071613 6176832793143591648776855)
            ·
              refine ⟨9265249189715387473165283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6176832793143591648776855 9265249189715387473165283)
              ·
                refine ⟨13897873784573081209747925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9265249189715387473165283 13897873784573081209747925)
                ·
                  refine ⟨325731416825931590853467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13897873784573081209747925 325731416825931590853467)
                  ·
                    rfl

theorem cell23_5709237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 7].length) (baseStart_5709237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709237 prefixEnd_5709237 := by exact prefixLift 5709237
  have htrace : WordTrace (prefixWord ++ tailWord_5709237) baseStart_5709237 baseEnd_5709237 := by
    simpa [prefixWord, tailWord_5709237, baseEnd_5709237] using wordTrace_append hprefix tailTrace_5709237
  have hstable : (prefixWord ++ tailWord_5709237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709237).length < 2 ^ (prefixWord ++ tailWord_5709237).sum := by decide
  have hdescent : baseEnd_5709237 < baseStart_5709237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709263 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 2, 8]
def baseStart_5709263 : Nat := 118140960795 + 5709263 * 2 ^ 59
def prefixEnd_5709263 : Nat := 4983230072969 + 3 ^ 40 * 5709263 * 2
def baseEnd_5709263 : Nat := 977198700643467071985361

theorem tailTrace_5709263 : CollatzResearch.WordTrace tailWord_5709263 prefixEnd_5709263 977198700643467071985361 := by
  unfold tailWord_5709263
  simp only [CollatzResearch.WordTrace]
  refine ⟨208233928715322690336660443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138822619143548460224440295 208233928715322690336660443)
  ·
    refine ⟨312350893072984035504990665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208233928715322690336660443 312350893072984035504990665)
    ·
      refine ⟨234263169804738026628742999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312350893072984035504990665 234263169804738026628742999)
      ·
        refine ⟨351394754707107039943114499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234263169804738026628742999 351394754707107039943114499)
        ·
          refine ⟨527092132060660559914671749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351394754707107039943114499 527092132060660559914671749)
          ·
            refine ⟨98829774761373854984000953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 527092132060660559914671749 98829774761373854984000953)
            ·
              refine ⟨74122331071030391238000715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98829774761373854984000953 74122331071030391238000715)
              ·
                refine ⟨111183496606545586857001073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74122331071030391238000715 111183496606545586857001073)
                ·
                  refine ⟨83387622454909190142750805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111183496606545586857001073 83387622454909190142750805)
                  ·
                    refine ⟨977198700643467071985361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83387622454909190142750805 977198700643467071985361)
                    ·
                      rfl

theorem cell23_5709263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 8].length) (baseStart_5709263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709263 prefixEnd_5709263 := by exact prefixLift 5709263
  have htrace : WordTrace (prefixWord ++ tailWord_5709263) baseStart_5709263 baseEnd_5709263 := by
    simpa [prefixWord, tailWord_5709263, baseEnd_5709263] using wordTrace_append hprefix tailTrace_5709263
  have hstable : (prefixWord ++ tailWord_5709263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709263).length < 2 ^ (prefixWord ++ tailWord_5709263).sum := by decide
  have hdescent : baseEnd_5709263 < baseStart_5709263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709280 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 7, 4]
def baseStart_5709280 : Nat := 118140960795 + 5709280 * 2 ^ 59
def prefixEnd_5709280 : Nat := 4983230072969 + 3 ^ 40 * 5709280 * 2
def baseEnd_5709280 : Nat := 977201610367175883147835

theorem tailTrace_5709280 : CollatzResearch.WordTrace tailWord_5709280 prefixEnd_5709280 977201610367175883147835 := by
  unfold tailWord_5709280
  simp only [CollatzResearch.WordTrace]
  refine ⟨104117274378130551120014647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138823032504174068160019529 104117274378130551120014647)
  ·
    refine ⟨156175911567195826680021971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104117274378130551120014647 156175911567195826680021971)
    ·
      refine ⟨234263867350793740020032957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156175911567195826680021971 234263867350793740020032957)
      ·
        refine ⟨87848950256547652507512359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234263867350793740020032957 87848950256547652507512359)
        ·
          refine ⟨131773425384821478761268539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87848950256547652507512359 131773425384821478761268539)
          ·
            refine ⟨197660138077232218141902809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131773425384821478761268539 197660138077232218141902809)
            ·
              refine ⟨148245103557924163606427107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197660138077232218141902809 148245103557924163606427107)
              ·
                refine ⟨222367655336886245409640661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148245103557924163606427107 222367655336886245409640661)
                ·
                  refine ⟨5211741921958271376788453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 222367655336886245409640661 5211741921958271376788453)
                  ·
                    refine ⟨977201610367175883147835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5211741921958271376788453 977201610367175883147835)
                    ·
                      rfl

theorem cell23_5709280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 7, 4].length) (baseStart_5709280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709280 prefixEnd_5709280 := by exact prefixLift 5709280
  have htrace : WordTrace (prefixWord ++ tailWord_5709280) baseStart_5709280 baseEnd_5709280 := by
    simpa [prefixWord, tailWord_5709280, baseEnd_5709280] using wordTrace_append hprefix tailTrace_5709280
  have hstable : (prefixWord ++ tailWord_5709280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709280).length < 2 ^ (prefixWord ++ tailWord_5709280).sum := by decide
  have hdescent : baseEnd_5709280 < baseStart_5709280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709287 : List Nat := [1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_5709287 : Nat := 118140960795 + 5709287 * 2 ^ 59
def prefixEnd_5709287 : Nat := 4983230072969 + 3 ^ 40 * 5709287 * 2
def baseEnd_5709287 : Nat := 2931608425466109122055973

theorem tailTrace_5709287 : CollatzResearch.WordTrace tailWord_5709287 prefixEnd_5709287 2931608425466109122055973 := by
  unfold tailWord_5709287
  simp only [CollatzResearch.WordTrace]
  refine ⟨208234804067235742435534115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138823202711490494957022743 208234804067235742435534115)
  ·
    refine ⟨312352206100853613653301173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208234804067235742435534115 312352206100853613653301173)
    ·
      refine ⟨29283019321955026279996985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 312352206100853613653301173 29283019321955026279996985)
      ·
        refine ⟨21962264491466269709997739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29283019321955026279996985 21962264491466269709997739)
        ·
          refine ⟨32943396737199404564996609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21962264491466269709997739 32943396737199404564996609)
          ·
            refine ⟨24707547552899553423747457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32943396737199404564996609 24707547552899553423747457)
            ·
              refine ⟨18530660664674665067810593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24707547552899553423747457 18530660664674665067810593)
              ·
                refine ⟨13897995498505998800857945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18530660664674665067810593 13897995498505998800857945)
                ·
                  refine ⟨10423496623879499100643459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13897995498505998800857945 10423496623879499100643459)
                  ·
                    refine ⟨15635244935819248650965189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10423496623879499100643459 15635244935819248650965189)
                    ·
                      refine ⟨2931608425466109122055973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15635244935819248650965189 2931608425466109122055973)
                      ·
                        rfl

theorem cell23_5709287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_5709287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709287 prefixEnd_5709287 := by exact prefixLift 5709287
  have htrace : WordTrace (prefixWord ++ tailWord_5709287) baseStart_5709287 baseEnd_5709287 := by
    simpa [prefixWord, tailWord_5709287, baseEnd_5709287] using wordTrace_append hprefix tailTrace_5709287
  have hstable : (prefixWord ++ tailWord_5709287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709287).length < 2 ^ (prefixWord ++ tailWord_5709287).sum := by decide
  have hdescent : baseEnd_5709287 < baseStart_5709287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709314 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_5709314 : Nat := 118140960795 + 5709314 * 2 ^ 59
def prefixEnd_5709314 : Nat := 4983230072969 + 3 ^ 40 * 5709314 * 2
def baseEnd_5709314 : Nat := 977207429814593505472783

theorem tailTrace_5709314 : CollatzResearch.WordTrace tailWord_5709314 prefixEnd_5709314 977207429814593505472783 := by
  unfold tailWord_5709314
  simp only [CollatzResearch.WordTrace]
  refine ⟨52058947209534481511691749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138823859225425284031177997 52058947209534481511691749)
  ·
    refine ⟨9761052601787715283442203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52058947209534481511691749 9761052601787715283442203)
    ·
      refine ⟨14641578902681572925163305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9761052601787715283442203 14641578902681572925163305)
      ·
        refine ⟨10981184177011179693872479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14641578902681572925163305 10981184177011179693872479)
        ·
          refine ⟨16471776265516769540808719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10981184177011179693872479 16471776265516769540808719)
          ·
            refine ⟨24707664398275154311213079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16471776265516769540808719 24707664398275154311213079)
            ·
              refine ⟨37061496597412731466819619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24707664398275154311213079 37061496597412731466819619)
              ·
                refine ⟨55592244896119097200229429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37061496597412731466819619 55592244896119097200229429)
                ·
                  refine ⟨5211772959011165362521509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55592244896119097200229429 5211772959011165362521509)
                  ·
                    refine ⟨977207429814593505472783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5211772959011165362521509 977207429814593505472783)
                    ·
                      rfl

theorem cell23_5709314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_5709314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709314 prefixEnd_5709314 := by exact prefixLift 5709314
  have htrace : WordTrace (prefixWord ++ tailWord_5709314) baseStart_5709314 baseEnd_5709314 := by
    simpa [prefixWord, tailWord_5709314, baseEnd_5709314] using wordTrace_append hprefix tailTrace_5709314
  have hstable : (prefixWord ++ tailWord_5709314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709314).length < 2 ^ (prefixWord ++ tailWord_5709314).sum := by decide
  have hdescent : baseEnd_5709314 < baseStart_5709314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709344 : List Nat := [2, 1, 1, 6, 1, 3, 1, 2, 6]
def baseStart_5709344 : Nat := 118140960795 + 5709344 * 2 ^ 59
def prefixEnd_5709344 : Nat := 4983230072969 + 3 ^ 40 * 5709344 * 2
def baseEnd_5709344 : Nat := 325737521540379488782579

theorem tailTrace_5709344 : CollatzResearch.WordTrace tailWord_5709344 prefixEnd_5709344 325737521540379488782579 := by
  unfold tailWord_5709344
  simp only [CollatzResearch.WordTrace]
  refine ⟨104118441514014620585179543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138824588685352827446906057 104118441514014620585179543)
  ·
    refine ⟨156177662271021930877769315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104118441514014620585179543 156177662271021930877769315)
    ·
      refine ⟨234266493406532896316653973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156177662271021930877769315 234266493406532896316653973)
      ·
        refine ⟨10981241878431229514843155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 234266493406532896316653973 10981241878431229514843155)
        ·
          refine ⟨16471862817646844272264733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10981241878431229514843155 16471862817646844272264733)
          ·
            refine ⟨6176948556617566602099275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16471862817646844272264733 6176948556617566602099275)
            ·
              refine ⟨9265422834926349903148913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6176948556617566602099275 9265422834926349903148913)
              ·
                refine ⟨6949067126194762427361685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9265422834926349903148913 6949067126194762427361685)
                ·
                  refine ⟨325737521540379488782579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6949067126194762427361685 325737521540379488782579)
                  ·
                    rfl

theorem cell23_5709344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 6].length) (baseStart_5709344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709344 prefixEnd_5709344 := by exact prefixLift 5709344
  have htrace : WordTrace (prefixWord ++ tailWord_5709344) baseStart_5709344 baseEnd_5709344 := by
    simpa [prefixWord, tailWord_5709344, baseEnd_5709344] using wordTrace_append hprefix tailTrace_5709344
  have hstable : (prefixWord ++ tailWord_5709344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709344).length < 2 ^ (prefixWord ++ tailWord_5709344).sum := by decide
  have hdescent : baseEnd_5709344 < baseStart_5709344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709382 : List Nat := [6, 1, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_5709382 : Nat := 118140960795 + 5709382 * 2 ^ 59
def prefixEnd_5709382 : Nat := 4983230072969 + 3 ^ 40 * 5709382 * 2
def baseEnd_5709382 : Nat := 977219068709428750122679

theorem tailTrace_5709382 : CollatzResearch.WordTrace tailWord_5709382 prefixEnd_5709382 977219068709428750122679 := by
  unfold tailWord_5709382
  simp only [CollatzResearch.WordTrace]
  refine ⟨6507445906309111676882575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 138825512667927715773494933 6507445906309111676882575)
  ·
    refine ⟨9761168859463667515323863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6507445906309111676882575 9761168859463667515323863)
    ·
      refine ⟨14641753289195501272985795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9761168859463667515323863 14641753289195501272985795)
      ·
        refine ⟨21962629933793251909478693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14641753289195501272985795 21962629933793251909478693)
        ·
          refine ⟨4117993112586234733027255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21962629933793251909478693 4117993112586234733027255)
          ·
            refine ⟨6176989668879352099540883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4117993112586234733027255 6176989668879352099540883)
            ·
              refine ⟨9265484503319028149311325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6176989668879352099540883 9265484503319028149311325)
              ·
                refine ⟨3474556688744635555991747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9265484503319028149311325 3474556688744635555991747)
                ·
                  refine ⟨5211835033116953333987621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3474556688744635555991747 5211835033116953333987621)
                  ·
                    refine ⟨977219068709428750122679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5211835033116953333987621 977219068709428750122679)
                    ·
                      rfl

theorem cell23_5709382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_5709382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709382 prefixEnd_5709382 := by exact prefixLift 5709382
  have htrace : WordTrace (prefixWord ++ tailWord_5709382) baseStart_5709382 baseEnd_5709382 := by
    simpa [prefixWord, tailWord_5709382, baseEnd_5709382] using wordTrace_append hprefix tailTrace_5709382
  have hstable : (prefixWord ++ tailWord_5709382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709382).length < 2 ^ (prefixWord ++ tailWord_5709382).sum := by decide
  have hdescent : baseEnd_5709382 < baseStart_5709382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709388 : List Nat := [2, 2, 1, 3, 1, 5, 1, 3, 1, 1, 3]
def baseStart_5709388 : Nat := 118140960795 + 5709388 * 2 ^ 59
def prefixEnd_5709388 : Nat := 4983230072969 + 3 ^ 40 * 5709388 * 2
def baseEnd_5709388 : Nat := 2931660287012213226893009

theorem tailTrace_5709388 : CollatzResearch.WordTrace tailWord_5709388 prefixEnd_5709388 2931660287012213226893009 := by
  unfold tailWord_5709388
  simp only [CollatzResearch.WordTrace]
  refine ⟨104119243919934918342480409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138825658559913224456640545 104119243919934918342480409)
  ·
    refine ⟨78089432939951188756860307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104119243919934918342480409 78089432939951188756860307)
    ·
      refine ⟨117134149409926783135290461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78089432939951188756860307 117134149409926783135290461)
      ·
        refine ⟨43925306028722543675733923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117134149409926783135290461 43925306028722543675733923)
        ·
          refine ⟨65887959043083815513600885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43925306028722543675733923 65887959043083815513600885)
          ·
            refine ⟨6176996160289107704400083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65887959043083815513600885 6176996160289107704400083)
            ·
              refine ⟨9265494240433661556600125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6176996160289107704400083 9265494240433661556600125)
              ·
                refine ⟨3474560340162623083725047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9265494240433661556600125 3474560340162623083725047)
                ·
                  refine ⟨5211840510243934625587571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3474560340162623083725047 5211840510243934625587571)
                  ·
                    refine ⟨7817760765365901938381357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5211840510243934625587571 7817760765365901938381357)
                    ·
                      refine ⟨2931660287012213226893009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7817760765365901938381357 2931660287012213226893009)
                      ·
                        rfl

theorem cell23_5709388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_5709388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709388 prefixEnd_5709388 := by exact prefixLift 5709388
  have htrace : WordTrace (prefixWord ++ tailWord_5709388) baseStart_5709388 baseEnd_5709388 := by
    simpa [prefixWord, tailWord_5709388, baseEnd_5709388] using wordTrace_append hprefix tailTrace_5709388
  have hstable : (prefixWord ++ tailWord_5709388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709388).length < 2 ^ (prefixWord ++ tailWord_5709388).sum := by decide
  have hdescent : baseEnd_5709388 < baseStart_5709388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709394 : List Nat := [3, 2, 2, 1, 2, 2, 2, 3, 1, 1, 4]
def baseStart_5709394 : Nat := 118140960795 + 5709394 * 2 ^ 59
def prefixEnd_5709394 : Nat := 4983230072969 + 3 ^ 40 * 5709394 * 2
def baseEnd_5709394 : Nat := 2931663367896140203417981

theorem tailTrace_5709394 : CollatzResearch.WordTrace tailWord_5709394 prefixEnd_5709394 2931663367896140203417981 := by
  unfold tailWord_5709394
  simp only [CollatzResearch.WordTrace]
  refine ⟨52059676669462024927419809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138825804451898733139786157 52059676669462024927419809)
  ·
    refine ⟨39044757502096518695564857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52059676669462024927419809 39044757502096518695564857)
    ·
      refine ⟨29283568126572389021673643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39044757502096518695564857 29283568126572389021673643)
      ·
        refine ⟨43925352189858583532510465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29283568126572389021673643 43925352189858583532510465)
        ·
          refine ⟨32944014142393937649382849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43925352189858583532510465 32944014142393937649382849)
          ·
            refine ⟨24708010606795453237037137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32944014142393937649382849 24708010606795453237037137)
            ·
              refine ⟨18531007955096589927777853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24708010606795453237037137 18531007955096589927777853)
              ·
                refine ⟨6949127983161221222916695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18531007955096589927777853 6949127983161221222916695)
                ·
                  refine ⟨10423691974741831834375043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6949127983161221222916695 10423691974741831834375043)
                  ·
                    refine ⟨15635537962112747751562565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10423691974741831834375043 15635537962112747751562565)
                    ·
                      refine ⟨2931663367896140203417981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15635537962112747751562565 2931663367896140203417981)
                      ·
                        rfl

theorem cell23_5709394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_5709394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709394 prefixEnd_5709394 := by exact prefixLift 5709394
  have htrace : WordTrace (prefixWord ++ tailWord_5709394) baseStart_5709394 baseEnd_5709394 := by
    simpa [prefixWord, tailWord_5709394, baseEnd_5709394] using wordTrace_append hprefix tailTrace_5709394
  have hstable : (prefixWord ++ tailWord_5709394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709394).length < 2 ^ (prefixWord ++ tailWord_5709394).sum := by decide
  have hdescent : baseEnd_5709394 < baseStart_5709394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709397 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 5, 2, 3]
def baseStart_5709397 : Nat := 118140960795 + 5709397 * 2 ^ 59
def prefixEnd_5709397 : Nat := 4983230072969 + 3 ^ 40 * 5709397 * 2
def baseEnd_5709397 : Nat := 2931664908338103691680467

theorem tailTrace_5709397 : CollatzResearch.WordTrace tailWord_5709397 prefixEnd_5709397 2931664908338103691680467 := by
  unfold tailWord_5709397
  simp only [CollatzResearch.WordTrace]
  refine ⟨208238816096837231222038445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138825877397891487481358963 208238816096837231222038445)
  ·
    refine ⟨78089556036313961708264417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208238816096837231222038445 78089556036313961708264417)
    ·
      refine ⟨58567167027235471281198313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78089556036313961708264417 58567167027235471281198313)
      ·
        refine ⟨43925375270426603460898735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58567167027235471281198313 43925375270426603460898735)
        ·
          refine ⟨65888062905639905191348103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43925375270426603460898735 65888062905639905191348103)
          ·
            refine ⟨98832094358459857787022155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65888062905639905191348103 98832094358459857787022155)
            ·
              refine ⟨148248141537689786680533233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98832094358459857787022155 148248141537689786680533233)
              ·
                refine ⟨111186106153267340010399925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148248141537689786680533233 111186106153267340010399925)
                ·
                  refine ⟨10423697451868813125974993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111186106153267340010399925 10423697451868813125974993)
                  ·
                    refine ⟨7817773088901609844481245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10423697451868813125974993 7817773088901609844481245)
                    ·
                      refine ⟨2931664908338103691680467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7817773088901609844481245 2931664908338103691680467)
                      ·
                        rfl

theorem cell23_5709397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_5709397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709397 prefixEnd_5709397 := by exact prefixLift 5709397
  have htrace : WordTrace (prefixWord ++ tailWord_5709397) baseStart_5709397 baseEnd_5709397 := by
    simpa [prefixWord, tailWord_5709397, baseEnd_5709397] using wordTrace_append hprefix tailTrace_5709397
  have hstable : (prefixWord ++ tailWord_5709397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709397).length < 2 ^ (prefixWord ++ tailWord_5709397).sum := by decide
  have hdescent : baseEnd_5709397 < baseStart_5709397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709404 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 4, 4]
def baseStart_5709404 : Nat := 118140960795 + 5709404 * 2 ^ 59
def prefixEnd_5709404 : Nat := 4983230072969 + 3 ^ 40 * 5709404 * 2
def baseEnd_5709404 : Nat := 977222834234228388097645

theorem tailTrace_5709404 : CollatzResearch.WordTrace tailWord_5709404 prefixEnd_5709404 977222834234228388097645 := by
  unfold tailWord_5709404
  simp only [CollatzResearch.WordTrace]
  refine ⟨104119535703905935708771633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138826047605207914278362177 104119535703905935708771633)
  ·
    refine ⟨78089651777929451781578725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104119535703905935708771633 78089651777929451781578725)
    ·
      refine ⟨14641809708361772209046011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78089651777929451781578725 14641809708361772209046011)
      ·
        refine ⟨21962714562542658313569017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14641809708361772209046011 21962714562542658313569017)
        ·
          refine ⟨16472035921906993735176763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21962714562542658313569017 16472035921906993735176763)
          ·
            refine ⟨24708053882860490602765145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16472035921906993735176763 24708053882860490602765145)
            ·
              refine ⟨18531040412145367952073859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24708053882860490602765145 18531040412145367952073859)
              ·
                refine ⟨27796560618218051928110789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18531040412145367952073859 27796560618218051928110789)
                ·
                  refine ⟨5211855115915884736520773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27796560618218051928110789 5211855115915884736520773)
                  ·
                    refine ⟨977222834234228388097645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5211855115915884736520773 977222834234228388097645)
                    ·
                      rfl

theorem cell23_5709404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_5709404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709404 prefixEnd_5709404 := by exact prefixLift 5709404
  have htrace : WordTrace (prefixWord ++ tailWord_5709404) baseStart_5709404 baseEnd_5709404 := by
    simpa [prefixWord, tailWord_5709404, baseEnd_5709404] using wordTrace_append hprefix tailTrace_5709404
  have hstable : (prefixWord ++ tailWord_5709404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709404).length < 2 ^ (prefixWord ++ tailWord_5709404).sum := by decide
  have hdescent : baseEnd_5709404 < baseStart_5709404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709405 : List Nat := [1, 4, 4, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_5709405 : Nat := 118140960795 + 5709405 * 2 ^ 59
def prefixEnd_5709405 : Nat := 4983230072969 + 3 ^ 40 * 5709405 * 2
def baseEnd_5709405 : Nat := 2931669016183339660380431

theorem tailTrace_5709405 : CollatzResearch.WordTrace tailWord_5709405 prefixEnd_5709405 2931669016183339660380431 := by
  unfold tailWord_5709405
  simp only [CollatzResearch.WordTrace]
  refine ⟨208239107880808248588329669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138826071920538832392219779 208239107880808248588329669)
  ·
    refine ⟨39044832727651546610311813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208239107880808248588329669 39044832727651546610311813)
    ·
      refine ⟨7320906136434664989433465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39044832727651546610311813 7320906136434664989433465)
      ·
        refine ⟨5490679602325998742075099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7320906136434664989433465 5490679602325998742075099)
        ·
          refine ⟨8236019403488998113112649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5490679602325998742075099 8236019403488998113112649)
          ·
            refine ⟨6177014552616748584834487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8236019403488998113112649 6177014552616748584834487)
            ·
              refine ⟨9265521828925122877251731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6177014552616748584834487 9265521828925122877251731)
              ·
                refine ⟨13898282743387684315877597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9265521828925122877251731 13898282743387684315877597)
                ·
                  refine ⟨5211856028770381618454099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13898282743387684315877597 5211856028770381618454099)
                  ·
                    refine ⟨7817784043155572427681149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5211856028770381618454099 7817784043155572427681149)
                    ·
                      refine ⟨2931669016183339660380431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7817784043155572427681149 2931669016183339660380431)
                      ·
                        rfl

theorem cell23_5709405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_5709405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709405 prefixEnd_5709405 := by exact prefixLift 5709405
  have htrace : WordTrace (prefixWord ++ tailWord_5709405) baseStart_5709405 baseEnd_5709405 := by
    simpa [prefixWord, tailWord_5709405, baseEnd_5709405] using wordTrace_append hprefix tailTrace_5709405
  have hstable : (prefixWord ++ tailWord_5709405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709405).length < 2 ^ (prefixWord ++ tailWord_5709405).sum := by decide
  have hdescent : baseEnd_5709405 < baseStart_5709405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709411 : List Nat := [1, 1, 1, 5, 1, 3, 3, 1, 3, 2, 2]
def baseStart_5709411 : Nat := 118140960795 + 5709411 * 2 ^ 59
def prefixEnd_5709411 : Nat := 4983230072969 + 3 ^ 40 * 5709411 * 2
def baseEnd_5709411 : Nat := 2931672097067266636905403

theorem tailTrace_5709411 : CollatzResearch.WordTrace tailWord_5709411 prefixEnd_5709411 2931672097067266636905403 := by
  unfold tailWord_5709411
  simp only [CollatzResearch.WordTrace]
  refine ⟨208239326718786511613048087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138826217812524341075365391 208239326718786511613048087)
  ·
    refine ⟨312358990078179767419572131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208239326718786511613048087 312358990078179767419572131)
    ·
      refine ⟨468538485117269651129358197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312358990078179767419572131 468538485117269651129358197)
      ·
        refine ⟨43925482979744029793377331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 468538485117269651129358197 43925482979744029793377331)
        ·
          refine ⟨65888224469616044690065997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43925482979744029793377331 65888224469616044690065997)
          ·
            refine ⟨24708084176106016758774749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65888224469616044690065997 24708084176106016758774749)
            ·
              refine ⟨9265531566039756284540531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24708084176106016758774749 9265531566039756284540531)
              ·
                refine ⟨13898297349059634426810797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9265531566039756284540531 13898297349059634426810797)
                ·
                  refine ⟨5211861505897362910054049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13898297349059634426810797 5211861505897362910054049)
                  ·
                    refine ⟨3908896129423022182540537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5211861505897362910054049 3908896129423022182540537)
                    ·
                      refine ⟨2931672097067266636905403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3908896129423022182540537 2931672097067266636905403)
                      ·
                        rfl

theorem cell23_5709411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_5709411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709411 prefixEnd_5709411 := by exact prefixLift 5709411
  have htrace : WordTrace (prefixWord ++ tailWord_5709411) baseStart_5709411 baseEnd_5709411 := by
    simpa [prefixWord, tailWord_5709411, baseEnd_5709411] using wordTrace_append hprefix tailTrace_5709411
  have hstable : (prefixWord ++ tailWord_5709411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709411).length < 2 ^ (prefixWord ++ tailWord_5709411).sum := by decide
  have hdescent : baseEnd_5709411 < baseStart_5709411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709420 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 6]
def baseStart_5709420 : Nat := 118140960795 + 5709420 * 2 ^ 59
def prefixEnd_5709420 : Nat := 4983230072969 + 3 ^ 40 * 5709420 * 2
def baseEnd_5709420 : Nat := 2931676718393157101692861

theorem tailTrace_5709420 : CollatzResearch.WordTrace tailWord_5709420 prefixEnd_5709420 2931676718393157101692861 := by
  unfold tailWord_5709420
  simp only [CollatzResearch.WordTrace]
  refine ⟨104119827487876953075062857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138826436650502604100083809 104119827487876953075062857)
  ·
    refine ⟨78089870615907714806297143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104119827487876953075062857 78089870615907714806297143)
    ·
      refine ⟨117134805923861572209445715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78089870615907714806297143 117134805923861572209445715)
      ·
        refine ⟨175702208885792358314168573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117134805923861572209445715 175702208885792358314168573)
        ·
          refine ⟨65888328332172134367813215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175702208885792358314168573 65888328332172134367813215)
          ·
            refine ⟨98832492498258201551719823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65888328332172134367813215 98832492498258201551719823)
            ·
              refine ⟨148248738747387302327579735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98832492498258201551719823 148248738747387302327579735)
              ·
                refine ⟨222373108121080953491369603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148248738747387302327579735 222373108121080953491369603)
                ·
                  refine ⟨333559662181621430237054405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222373108121080953491369603 333559662181621430237054405)
                  ·
                    refine ⟨62542436659054018169447701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 333559662181621430237054405 62542436659054018169447701)
                    ·
                      refine ⟨2931676718393157101692861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62542436659054018169447701 2931676718393157101692861)
                      ·
                        rfl

theorem cell23_5709420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_5709420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709420 prefixEnd_5709420 := by exact prefixLift 5709420
  have htrace : WordTrace (prefixWord ++ tailWord_5709420) baseStart_5709420 baseEnd_5709420 := by
    simpa [prefixWord, tailWord_5709420, baseEnd_5709420] using wordTrace_append hprefix tailTrace_5709420
  have hstable : (prefixWord ++ tailWord_5709420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709420).length < 2 ^ (prefixWord ++ tailWord_5709420).sum := by decide
  have hdescent : baseEnd_5709420 < baseStart_5709420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709421 : List Nat := [1, 5, 1, 1, 4, 1, 1, 3, 2, 4]
def baseStart_5709421 : Nat := 118140960795 + 5709421 * 2 ^ 59
def prefixEnd_5709421 : Nat := 4983230072969 + 3 ^ 40 * 5709421 * 2
def baseEnd_5709421 : Nat := 977225743957937199260119

theorem tailTrace_5709421 : CollatzResearch.WordTrace tailWord_5709421 prefixEnd_5709421 977225743957937199260119 := by
  unfold tailWord_5709421
  simp only [CollatzResearch.WordTrace]
  refine ⟨208239691448750283320912117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138826460965833522213941411 208239691448750283320912117)
  ·
    refine ⟨19522471073320339061335511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 208239691448750283320912117 19522471073320339061335511)
    ·
      refine ⟨29283706609980508592003267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19522471073320339061335511 29283706609980508592003267)
      ·
        refine ⟨43925559914970762888004901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29283706609980508592003267 43925559914970762888004901)
        ·
          refine ⟨8236042484057018041500919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43925559914970762888004901 8236042484057018041500919)
          ·
            refine ⟨12354063726085527062251379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8236042484057018041500919 12354063726085527062251379)
            ·
              refine ⟨18531095589128290593377069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12354063726085527062251379 18531095589128290593377069)
              ·
                refine ⟨6949160845923108972516401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18531095589128290593377069 6949160845923108972516401)
                ·
                  refine ⟨5211870634442331729387301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6949160845923108972516401 5211870634442331729387301)
                  ·
                    refine ⟨977225743957937199260119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5211870634442331729387301 977225743957937199260119)
                    ·
                      rfl

theorem cell23_5709421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_5709421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709421 prefixEnd_5709421 := by exact prefixLift 5709421
  have htrace : WordTrace (prefixWord ++ tailWord_5709421) baseStart_5709421 baseEnd_5709421 := by
    simpa [prefixWord, tailWord_5709421, baseEnd_5709421] using wordTrace_append hprefix tailTrace_5709421
  have hstable : (prefixWord ++ tailWord_5709421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709421).length < 2 ^ (prefixWord ++ tailWord_5709421).sum := by decide
  have hdescent : baseEnd_5709421 < baseStart_5709421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709448 : List Nat := [2, 1, 3, 5, 2, 1, 1, 1, 1, 1, 5]
def baseStart_5709448 : Nat := 118140960795 + 5709448 * 2 ^ 59
def prefixEnd_5709448 : Nat := 4983230072969 + 3 ^ 40 * 5709448 * 2
def baseEnd_5709448 : Nat := 2931691095851482992142733

theorem tailTrace_5709448 : CollatzResearch.WordTrace tailWord_5709448 prefixEnd_5709448 2931691095851482992142733 := by
  unfold tailWord_5709448
  simp only [CollatzResearch.WordTrace]
  refine ⟨104120338109826233466072499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138827117479768311288096665 104120338109826233466072499)
  ·
    refine ⟨156180507164739350199108749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104120338109826233466072499 156180507164739350199108749)
    ·
      refine ⟨58567690186777256324665781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156180507164739350199108749 58567690186777256324665781)
      ·
        refine ⟨5490720955010367780437417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58567690186777256324665781 5490720955010367780437417)
        ·
          refine ⟨4118040716257775835328063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5490720955010367780437417 4118040716257775835328063)
          ·
            refine ⟨6177061074386663752992095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4118040716257775835328063 6177061074386663752992095)
            ·
              refine ⟨9265591611579995629488143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6177061074386663752992095 9265591611579995629488143)
              ·
                refine ⟨13898387417369993444232215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9265591611579995629488143 13898387417369993444232215)
                ·
                  refine ⟨20847581126054990166348323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13898387417369993444232215 20847581126054990166348323)
                  ·
                    refine ⟨31271371689082485249522485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20847581126054990166348323 31271371689082485249522485)
                    ·
                      refine ⟨2931691095851482992142733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31271371689082485249522485 2931691095851482992142733)
                      ·
                        rfl

theorem cell23_5709448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_5709448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709448 prefixEnd_5709448 := by exact prefixLift 5709448
  have htrace : WordTrace (prefixWord ++ tailWord_5709448) baseStart_5709448 baseEnd_5709448 := by
    simpa [prefixWord, tailWord_5709448, baseEnd_5709448] using wordTrace_append hprefix tailTrace_5709448
  have hstable : (prefixWord ++ tailWord_5709448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709448).length < 2 ^ (prefixWord ++ tailWord_5709448).sum := by decide
  have hdescent : baseEnd_5709448 < baseStart_5709448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709487 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 3]
def baseStart_5709487 : Nat := 118140960795 + 5709487 * 2 ^ 59
def prefixEnd_5709487 : Nat := 4983230072969 + 3 ^ 40 * 5709487 * 2
def baseEnd_5709487 : Nat := 2931711121597008339555053

theorem tailTrace_5709487 : CollatzResearch.WordTrace tailWord_5709487 prefixEnd_5709487 2931711121597008339555053 := by
  unfold tailWord_5709487
  simp only [CollatzResearch.WordTrace]
  refine ⟨208242098666511176592814715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138828065777674117728543143 208242098666511176592814715)
  ·
    refine ⟨312363147999766764889222073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208242098666511176592814715 312363147999766764889222073)
    ·
      refine ⟨234272360999825073666916555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312363147999766764889222073 234272360999825073666916555)
      ·
        refine ⟨351408541499737610500374833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234272360999825073666916555 351408541499737610500374833)
        ·
          refine ⟨263556406124803207875281125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351408541499737610500374833 263556406124803207875281125)
          ·
            refine ⟨49416826148400601476615211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 263556406124803207875281125 49416826148400601476615211)
            ·
              refine ⟨74125239222600902214922817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49416826148400601476615211 74125239222600902214922817)
              ·
                refine ⟨55593929416950676661192113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74125239222600902214922817 55593929416950676661192113)
                ·
                  refine ⟨41695447062713007495894085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55593929416950676661192113 41695447062713007495894085)
                  ·
                    refine ⟨7817896324258688905480141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41695447062713007495894085 7817896324258688905480141)
                    ·
                      refine ⟨2931711121597008339555053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7817896324258688905480141 2931711121597008339555053)
                      ·
                        rfl

theorem cell23_5709487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 3].length) (baseStart_5709487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709487 prefixEnd_5709487 := by exact prefixLift 5709487
  have htrace : WordTrace (prefixWord ++ tailWord_5709487) baseStart_5709487 baseEnd_5709487 := by
    simpa [prefixWord, tailWord_5709487, baseEnd_5709487] using wordTrace_append hprefix tailTrace_5709487
  have hstable : (prefixWord ++ tailWord_5709487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709487).length < 2 ^ (prefixWord ++ tailWord_5709487).sum := by decide
  have hdescent : baseEnd_5709487 < baseStart_5709487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709501 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 4, 2, 2]
def baseStart_5709501 : Nat := 118140960795 + 5709501 * 2 ^ 59
def prefixEnd_5709501 : Nat := 4983230072969 + 3 ^ 40 * 5709501 * 2
def baseEnd_5709501 : Nat := 2931718310326171284779989

theorem tailTrace_5709501 : CollatzResearch.WordTrace tailWord_5709501 prefixEnd_5709501 2931718310326171284779989 := by
  unfold tailWord_5709501
  simp only [CollatzResearch.WordTrace]
  refine ⟨208242609288460456983824357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138828406192306971322549571 208242609288460456983824357)
  ·
    refine ⟨39045489241586335684467067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208242609288460456983824357 39045489241586335684467067)
    ·
      refine ⟨58568233862379503526700601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39045489241586335684467067 58568233862379503526700601)
      ·
        refine ⟨43926175396784627645025451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58568233862379503526700601 43926175396784627645025451)
        ·
          refine ⟨65889263095176941467538177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43926175396784627645025451 65889263095176941467538177)
          ·
            refine ⟨49416947321382706100653633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65889263095176941467538177 49416947321382706100653633)
            ·
              refine ⟨37062710491037029575490225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49416947321382706100653633 37062710491037029575490225)
              ·
                refine ⟨27797032868277772181617669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37062710491037029575490225 27797032868277772181617669)
                ·
                  refine ⟨5211943662802082284053313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27797032868277772181617669 5211943662802082284053313)
                  ·
                    refine ⟨3908957747101561713039985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5211943662802082284053313 3908957747101561713039985)
                    ·
                      refine ⟨2931718310326171284779989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3908957747101561713039985 2931718310326171284779989)
                      ·
                        rfl

theorem cell23_5709501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_5709501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709501 prefixEnd_5709501 := by exact prefixLift 5709501
  have htrace : WordTrace (prefixWord ++ tailWord_5709501) baseStart_5709501 baseEnd_5709501 := by
    simpa [prefixWord, tailWord_5709501, baseEnd_5709501] using wordTrace_append hprefix tailTrace_5709501
  have hstable : (prefixWord ++ tailWord_5709501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709501).length < 2 ^ (prefixWord ++ tailWord_5709501).sum := by decide
  have hdescent : baseEnd_5709501 < baseStart_5709501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709524 : List Nat := [2, 4, 1, 3, 1, 1, 1, 3, 7]
def baseStart_5709524 : Nat := 118140960795 + 5709524 * 2 ^ 59
def prefixEnd_5709524 : Nat := 4983230072969 + 3 ^ 40 * 5709524 * 2
def baseEnd_5709524 : Nat := 325747791153469410532487

theorem tailTrace_5709524 : CollatzResearch.WordTrace tailWord_5709524 prefixEnd_5709524 325747791153469410532487 := by
  unfold tailWord_5709524
  simp only [CollatzResearch.WordTrace]
  refine ⟨104121724083688565955955813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138828965444918087941274417 104121724083688565955955813)
  ·
    refine ⟨19522823265691606116741715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104121724083688565955955813 19522823265691606116741715)
    ·
      refine ⟨29284234898537409175112573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19522823265691606116741715 29284234898537409175112573)
      ·
        refine ⟨10981588086951528440667215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29284234898537409175112573 10981588086951528440667215)
        ·
          refine ⟨16472382130427292661000823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10981588086951528440667215 16472382130427292661000823)
          ·
            refine ⟨24708573195640938991501235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16472382130427292661000823 24708573195640938991501235)
            ·
              refine ⟨37062859793461408487251853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24708573195640938991501235 37062859793461408487251853)
              ·
                refine ⟨13898572422548028182719445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37062859793461408487251853 13898572422548028182719445)
                ·
                  refine ⟨325747791153469410532487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13898572422548028182719445 325747791153469410532487)
                  ·
                    rfl

theorem cell23_5709524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_5709524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709524 prefixEnd_5709524 := by exact prefixLift 5709524
  have htrace : WordTrace (prefixWord ++ tailWord_5709524) baseStart_5709524 baseEnd_5709524 := by
    simpa [prefixWord, tailWord_5709524, baseEnd_5709524] using wordTrace_append hprefix tailTrace_5709524
  have hstable : (prefixWord ++ tailWord_5709524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709524).length < 2 ^ (prefixWord ++ tailWord_5709524).sum := by decide
  have hdescent : baseEnd_5709524 < baseStart_5709524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709554 : List Nat := [3, 2, 1, 3, 1, 1, 2, 3, 2, 5]
def baseStart_5709554 : Nat := 118140960795 + 5709554 * 2 ^ 59
def prefixEnd_5709554 : Nat := 4983230072969 + 3 ^ 40 * 5709554 * 2
def baseEnd_5709554 : Nat := 977248508266953192472415

theorem tailTrace_5709554 : CollatzResearch.WordTrace tailWord_5709554 prefixEnd_5709554 977248508266953192472415 := by
  unfold tailWord_5709554
  simp only [CollatzResearch.WordTrace]
  refine ⟨52061135589317111758875929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138829694904845631357002477 52061135589317111758875929)
  ·
    refine ⟨39045851691987833819156947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52061135589317111758875929 39045851691987833819156947)
    ·
      refine ⟨58568777537981750728735421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39045851691987833819156947 58568777537981750728735421)
      ·
        refine ⟨21963291576743156523275783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58568777537981750728735421 21963291576743156523275783)
        ·
          refine ⟨32944937365114734784913675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21963291576743156523275783 32944937365114734784913675)
          ·
            refine ⟨49417406047672102177370513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32944937365114734784913675 49417406047672102177370513)
            ·
              refine ⟨37063054535754076633027885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49417406047672102177370513 37063054535754076633027885)
              ·
                refine ⟨13898645450907778737385457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37063054535754076633027885 13898645450907778737385457)
                ·
                  refine ⟨10423984088180834053039093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13898645450907778737385457 10423984088180834053039093)
                  ·
                    refine ⟨977248508266953192472415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10423984088180834053039093 977248508266953192472415)
                    ·
                      rfl

theorem cell23_5709554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_5709554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709554 prefixEnd_5709554 := by exact prefixLift 5709554
  have htrace : WordTrace (prefixWord ++ tailWord_5709554) baseStart_5709554 baseEnd_5709554 := by
    simpa [prefixWord, tailWord_5709554, baseEnd_5709554] using wordTrace_append hprefix tailTrace_5709554
  have hstable : (prefixWord ++ tailWord_5709554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709554).length < 2 ^ (prefixWord ++ tailWord_5709554).sum := by decide
  have hdescent : baseEnd_5709554 < baseStart_5709554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709558 : List Nat := [5, 1, 1, 1, 1, 5, 1, 3, 5]
def baseStart_5709558 : Nat := 118140960795 + 5709558 * 2 ^ 59
def prefixEnd_5709558 : Nat := 4983230072969 + 3 ^ 40 * 5709558 * 2
def baseEnd_5709558 : Nat := 325749730969275284640803

theorem tailTrace_5709558 : CollatzResearch.WordTrace tailWord_5709558 prefixEnd_5709558 325749730969275284640803 := by
  unfold tailWord_5709558
  simp only [CollatzResearch.WordTrace]
  refine ⟨13015293015578372232415583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138829792166169303812432885 13015293015578372232415583)
  ·
    refine ⟨19522939523367558348623375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13015293015578372232415583 19522939523367558348623375)
    ·
      refine ⟨29284409285051337522935063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19522939523367558348623375 29284409285051337522935063)
      ·
        refine ⟨43926613927577006284402595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29284409285051337522935063 43926613927577006284402595)
        ·
          refine ⟨65889920891365509426603893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43926613927577006284402595 65889920891365509426603893)
          ·
            refine ⟨6177180083565516508744115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65889920891365509426603893 6177180083565516508744115)
            ·
              refine ⟨9265770125348274763116173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6177180083565516508744115 9265770125348274763116173)
              ·
                refine ⟨3474663797005603036168565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9265770125348274763116173 3474663797005603036168565)
                ·
                  refine ⟨325749730969275284640803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3474663797005603036168565 325749730969275284640803)
                  ·
                    rfl

theorem cell23_5709558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_5709558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709558 prefixEnd_5709558 := by exact prefixLift 5709558
  have htrace : WordTrace (prefixWord ++ tailWord_5709558) baseStart_5709558 baseEnd_5709558 := by
    simpa [prefixWord, tailWord_5709558, baseEnd_5709558] using wordTrace_append hprefix tailTrace_5709558
  have hstable : (prefixWord ++ tailWord_5709558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709558).length < 2 ^ (prefixWord ++ tailWord_5709558).sum := by decide
  have hdescent : baseEnd_5709558 < baseStart_5709558 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709587 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 4]
def baseStart_5709587 : Nat := 118140960795 + 5709587 * 2 ^ 59
def prefixEnd_5709587 : Nat := 4983230072969 + 3 ^ 40 * 5709587 * 2
def baseEnd_5709587 : Nat := 2931762469662457948304593

theorem tailTrace_5709587 : CollatzResearch.WordTrace tailWord_5709587 prefixEnd_5709587 2931762469662457948304593 := by
  unfold tailWord_5709587
  simp only [CollatzResearch.WordTrace]
  refine ⟨208245745966148893671455015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138830497310765929114303343 208245745966148893671455015)
  ·
    refine ⟨312368618949223340507182523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208245745966148893671455015 312368618949223340507182523)
    ·
      refine ⟨468552928423835010760773785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312368618949223340507182523 468552928423835010760773785)
      ·
        refine ⟨351414696317876258070580339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 468552928423835010760773785 351414696317876258070580339)
        ·
          refine ⟨527122044476814387105870509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351414696317876258070580339 527122044476814387105870509)
          ·
            refine ⟨197670766678805395164701441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 527122044476814387105870509 197670766678805395164701441)
            ·
              refine ⟨148253075009104046373526081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197670766678805395164701441 148253075009104046373526081)
              ·
                refine ⟨111189806256828034780144561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148253075009104046373526081 111189806256828034780144561)
                ·
                  refine ⟨83392354692621026085108421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111189806256828034780144561 83392354692621026085108421)
                  ·
                    refine ⟨15636066504866442390957829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83392354692621026085108421 15636066504866442390957829)
                    ·
                      refine ⟨2931762469662457948304593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15636066504866442390957829 2931762469662457948304593)
                      ·
                        rfl

theorem cell23_5709587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 4].length) (baseStart_5709587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709587 prefixEnd_5709587 := by exact prefixLift 5709587
  have htrace : WordTrace (prefixWord ++ tailWord_5709587) baseStart_5709587 baseEnd_5709587 := by
    simpa [prefixWord, tailWord_5709587, baseEnd_5709587] using wordTrace_append hprefix tailTrace_5709587
  have hstable : (prefixWord ++ tailWord_5709587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709587).length < 2 ^ (prefixWord ++ tailWord_5709587).sum := by decide
  have hdescent : baseEnd_5709587 < baseStart_5709587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709631 : List Nat := [1, 1, 2, 2, 6, 1, 2, 2, 6]
def baseStart_5709631 : Nat := 118140960795 + 5709631 * 2 ^ 59
def prefixEnd_5709631 : Nat := 4983230072969 + 3 ^ 40 * 5709631 * 2
def baseEnd_5709631 : Nat := 325753895867917308461599

theorem tailTrace_5709631 : CollatzResearch.WordTrace tailWord_5709631 prefixEnd_5709631 325753895867917308461599 := by
  unfold tailWord_5709631
  simp only [CollatzResearch.WordTrace]
  refine ⟨208247350777989489186056747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138831567185326326124037831 208247350777989489186056747)
  ·
    refine ⟨312371026166984233779085121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208247350777989489186056747 312371026166984233779085121)
    ·
      refine ⟨234278269625238175334313841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312371026166984233779085121 234278269625238175334313841)
      ·
        refine ⟨175708702218928631500735381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234278269625238175334313841 175708702218928631500735381)
        ·
          refine ⟨8236345416512279601596971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 175708702218928631500735381 8236345416512279601596971)
          ·
            refine ⟨12354518124768419402395457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8236345416512279601596971 12354518124768419402395457)
            ·
              refine ⟨9265888593576314551796593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12354518124768419402395457 9265888593576314551796593)
              ·
                refine ⟨6949416445182235913847445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9265888593576314551796593 6949416445182235913847445)
                ·
                  refine ⟨325753895867917308461599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6949416445182235913847445 325753895867917308461599)
                  ·
                    rfl

theorem cell23_5709631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 6].length) (baseStart_5709631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709631 prefixEnd_5709631 := by exact prefixLift 5709631
  have htrace : WordTrace (prefixWord ++ tailWord_5709631) baseStart_5709631 baseEnd_5709631 := by
    simpa [prefixWord, tailWord_5709631, baseEnd_5709631] using wordTrace_append hprefix tailTrace_5709631
  have hstable : (prefixWord ++ tailWord_5709631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709631).length < 2 ^ (prefixWord ++ tailWord_5709631).sum := by decide
  have hdescent : baseEnd_5709631 < baseStart_5709631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709635 : List Nat := [1, 1, 1, 3, 1, 7, 2, 2, 1, 4]
def baseStart_5709635 : Nat := 118140960795 + 5709635 * 2 ^ 59
def prefixEnd_5709635 : Nat := 4983230072969 + 3 ^ 40 * 5709635 * 2
def baseEnd_5709635 : Nat := 977262372244624586834791

theorem tailTrace_5709635 : CollatzResearch.WordTrace tailWord_5709635 prefixEnd_5709635 977262372244624586834791 := by
  unfold tailWord_5709635
  simp only [CollatzResearch.WordTrace]
  refine ⟨208247496669974997869202359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138831664446649998579468239 208247496669974997869202359)
  ·
    refine ⟨312371245004962496803803539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208247496669974997869202359 312371245004962496803803539)
    ·
      refine ⟨468556867507443745205705309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312371245004962496803803539 468556867507443745205705309)
      ·
        refine ⟨175708825315291404452139491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 468556867507443745205705309 175708825315291404452139491)
        ·
          refine ⟨263563237972937106678209237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175708825315291404452139491 263563237972937106678209237)
          ·
            refine ⟨6177263389990713437770529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 263563237972937106678209237 6177263389990713437770529)
            ·
              refine ⟨4632947542493035078327897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6177263389990713437770529 4632947542493035078327897)
              ·
                refine ⟨3474710656869776308745923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4632947542493035078327897 3474710656869776308745923)
                ·
                  refine ⟨5212065985304664463118885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3474710656869776308745923 5212065985304664463118885)
                  ·
                    refine ⟨977262372244624586834791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5212065985304664463118885 977262372244624586834791)
                    ·
                      rfl

theorem cell23_5709635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 1, 4].length) (baseStart_5709635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709635 prefixEnd_5709635 := by exact prefixLift 5709635
  have htrace : WordTrace (prefixWord ++ tailWord_5709635) baseStart_5709635 baseEnd_5709635 := by
    simpa [prefixWord, tailWord_5709635, baseEnd_5709635] using wordTrace_append hprefix tailTrace_5709635
  have hstable : (prefixWord ++ tailWord_5709635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709635).length < 2 ^ (prefixWord ++ tailWord_5709635).sum := by decide
  have hdescent : baseEnd_5709635 < baseStart_5709635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709641 : List Nat := [1, 2, 1, 1, 2, 4, 2, 3, 3, 1, 3]
def baseStart_5709641 : Nat := 118140960795 + 5709641 * 2 ^ 59
def prefixEnd_5709641 : Nat := 4983230072969 + 3 ^ 40 * 5709641 * 2
def baseEnd_5709641 : Nat := 2931790197617800737029345

theorem tailTrace_5709641 : CollatzResearch.WordTrace tailWord_5709641 prefixEnd_5709641 2931790197617800737029345 := by
  unfold tailWord_5709641
  simp only [CollatzResearch.WordTrace]
  refine ⟨208247715507953260893920777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138831810338635507262613851 208247715507953260893920777)
  ·
    refine ⟨156185786630964945670440583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208247715507953260893920777 156185786630964945670440583)
    ·
      refine ⟨234278679946447418505660875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156185786630964945670440583 234278679946447418505660875)
      ·
        refine ⟨351418019919671127758491313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234278679946447418505660875 351418019919671127758491313)
        ·
          refine ⟨263563514939753345818868485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351418019919671127758491313 263563514939753345818868485)
          ·
            refine ⟨49418159051203752341037841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 263563514939753345818868485 49418159051203752341037841)
            ·
              refine ⟨37063619288402814255778381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49418159051203752341037841 37063619288402814255778381)
              ·
                refine ⟨13898857233151055345916893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37063619288402814255778381 13898857233151055345916893)
                ·
                  refine ⟨5212071462431645754718835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13898857233151055345916893 5212071462431645754718835)
                  ·
                    refine ⟨7818107193647468632078253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5212071462431645754718835 7818107193647468632078253)
                    ·
                      refine ⟨2931790197617800737029345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7818107193647468632078253 2931790197617800737029345)
                      ·
                        rfl

theorem cell23_5709641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 1, 3].length) (baseStart_5709641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709641 prefixEnd_5709641 := by exact prefixLift 5709641
  have htrace : WordTrace (prefixWord ++ tailWord_5709641) baseStart_5709641 baseEnd_5709641 := by
    simpa [prefixWord, tailWord_5709641, baseEnd_5709641] using wordTrace_append hprefix tailTrace_5709641
  have hstable : (prefixWord ++ tailWord_5709641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709641).length < 2 ^ (prefixWord ++ tailWord_5709641).sum := by decide
  have hdescent : baseEnd_5709641 < baseStart_5709641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709668 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 1, 5, 2]
def baseStart_5709668 : Nat := 118140960795 + 5709668 * 2 ^ 59
def prefixEnd_5709668 : Nat := 4983230072969 + 3 ^ 40 * 5709668 * 2
def baseEnd_5709668 : Nat := 2931804061595472131391721

theorem tailTrace_5709668 : CollatzResearch.WordTrace tailWord_5709668 prefixEnd_5709668 2931804061595472131391721 := by
  unfold tailWord_5709668
  simp only [CollatzResearch.WordTrace]
  refine ⟨104124350139427722252576829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138832466852570296336769105 104124350139427722252576829)
  ·
    refine ⟨39046631302285395844716311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104124350139427722252576829 39046631302285395844716311)
    ·
      refine ⟨58569946953428093767074467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39046631302285395844716311 58569946953428093767074467)
      ·
        refine ⟨87854920430142140650611701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58569946953428093767074467 87854920430142140650611701)
        ·
          refine ⟨8236398790325825685994847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87854920430142140650611701 8236398790325825685994847)
          ·
            refine ⟨12354598185488738528992271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8236398790325825685994847 12354598185488738528992271)
            ·
              refine ⟨18531897278233107793488407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12354598185488738528992271 18531897278233107793488407)
              ·
                refine ⟨27797845917349661690232611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18531897278233107793488407 27797845917349661690232611)
                ·
                  refine ⟨41696768876024492535348917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27797845917349661690232611 41696768876024492535348917)
                  ·
                    refine ⟨3909072082127296175188961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41696768876024492535348917 3909072082127296175188961)
                    ·
                      refine ⟨2931804061595472131391721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3909072082127296175188961 2931804061595472131391721)
                      ·
                        rfl

theorem cell23_5709668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 1, 5, 2].length) (baseStart_5709668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709668 prefixEnd_5709668 := by exact prefixLift 5709668
  have htrace : WordTrace (prefixWord ++ tailWord_5709668) baseStart_5709668 baseEnd_5709668 := by
    simpa [prefixWord, tailWord_5709668, baseEnd_5709668] using wordTrace_append hprefix tailTrace_5709668
  have hstable : (prefixWord ++ tailWord_5709668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709668).length < 2 ^ (prefixWord ++ tailWord_5709668).sum := by decide
  have hdescent : baseEnd_5709668 < baseStart_5709668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709678 : List Nat := [4, 1, 2, 3, 1, 2, 1, 3, 1, 5]
def baseStart_5709678 : Nat := 118140960795 + 5709678 * 2 ^ 59
def prefixEnd_5709678 : Nat := 4983230072969 + 3 ^ 40 * 5709678 * 2
def baseEnd_5709678 : Nat := 977269732134005697422225

theorem tailTrace_5709678 : CollatzResearch.WordTrace tailWord_5709678 prefixEnd_5709678 977269732134005697422225 := by
  unfold tailWord_5709678
  simp only [CollatzResearch.WordTrace]
  refine ⟨26031133126102402026627211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138832710005879477475345125 26031133126102402026627211)
  ·
    refine ⟨39046699689153603039940817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26031133126102402026627211 39046699689153603039940817)
    ·
      refine ⟨29285024766865202279955613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39046699689153603039940817 29285024766865202279955613)
      ·
        refine ⟨10981884287574450854983355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29285024766865202279955613 10981884287574450854983355)
        ·
          refine ⟨16472826431361676282475033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10981884287574450854983355 16472826431361676282475033)
          ·
            refine ⟨12354619823521257211856275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16472826431361676282475033 12354619823521257211856275)
            ·
              refine ⟨18531929735281885817784413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12354619823521257211856275 18531929735281885817784413)
              ·
                refine ⟨6949473650730707181669155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18531929735281885817784413 6949473650730707181669155)
                ·
                  refine ⟨10424210476096060772503733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6949473650730707181669155 10424210476096060772503733)
                  ·
                    refine ⟨977269732134005697422225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10424210476096060772503733 977269732134005697422225)
                    ·
                      rfl

theorem cell23_5709678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_5709678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709678 prefixEnd_5709678 := by exact prefixLift 5709678
  have htrace : WordTrace (prefixWord ++ tailWord_5709678) baseStart_5709678 baseEnd_5709678 := by
    simpa [prefixWord, tailWord_5709678, baseEnd_5709678] using wordTrace_append hprefix tailTrace_5709678
  have hstable : (prefixWord ++ tailWord_5709678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709678).length < 2 ^ (prefixWord ++ tailWord_5709678).sum := by decide
  have hdescent : baseEnd_5709678 < baseStart_5709678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709681 : List Nat := [1, 2, 2, 2, 1, 3, 3, 3, 1, 1, 4]
def baseStart_5709681 : Nat := 118140960795 + 5709681 * 2 ^ 59
def prefixEnd_5709681 : Nat := 4983230072969 + 3 ^ 40 * 5709681 * 2
def baseEnd_5709681 : Nat := 2931810736843980580529161

theorem tailTrace_5709681 : CollatzResearch.WordTrace tailWord_5709681 prefixEnd_5709681 2931810736843980580529161 := by
  unfold tailWord_5709681
  simp only [CollatzResearch.WordTrace]
  refine ⟨208249174427808347725376897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138832782951872231816917931 208249174427808347725376897)
  ·
    refine ⟨156186880820856260794032673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208249174427808347725376897 156186880820856260794032673)
    ·
      refine ⟨117140160615642195595524505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156186880820856260794032673 117140160615642195595524505)
      ·
        refine ⟨87855120461731646696643379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117140160615642195595524505 87855120461731646696643379)
        ·
          refine ⟨131782680692597470044965069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87855120461731646696643379 131782680692597470044965069)
          ·
            refine ⟨49418505259724051266861901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131782680692597470044965069 49418505259724051266861901)
            ·
              refine ⟨18531939472396519225073213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49418505259724051266861901 18531939472396519225073213)
              ·
                refine ⟨6949477302148694709402455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18531939472396519225073213 6949477302148694709402455)
                ·
                  refine ⟨10424215953223042064103683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6949477302148694709402455 10424215953223042064103683)
                  ·
                    refine ⟨15636323929834563096155525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10424215953223042064103683 15636323929834563096155525)
                    ·
                      refine ⟨2931810736843980580529161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15636323929834563096155525 2931810736843980580529161)
                      ·
                        rfl

theorem cell23_5709681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_5709681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709681 prefixEnd_5709681 := by exact prefixLift 5709681
  have htrace : WordTrace (prefixWord ++ tailWord_5709681) baseStart_5709681 baseEnd_5709681 := by
    simpa [prefixWord, tailWord_5709681, baseEnd_5709681] using wordTrace_append hprefix tailTrace_5709681
  have hstable : (prefixWord ++ tailWord_5709681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709681).length < 2 ^ (prefixWord ++ tailWord_5709681).sum := by decide
  have hdescent : baseEnd_5709681 < baseStart_5709681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709726 : List Nat := [4, 3, 1, 3, 1, 2, 1, 3, 1, 1, 3]
def baseStart_5709726 : Nat := 118140960795 + 5709726 * 2 ^ 59
def prefixEnd_5709726 : Nat := 4983230072969 + 3 ^ 40 * 5709726 * 2
def baseEnd_5709726 : Nat := 2931833843473432904466455

theorem tailTrace_5709726 : CollatzResearch.WordTrace tailWord_5709726 prefixEnd_5709726 2931833843473432904466455 := by
  unfold tailWord_5709726
  simp only [CollatzResearch.WordTrace]
  refine ⟨26031351964080665051345629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138833877141763546940510021 26031351964080665051345629)
  ·
    refine ⟨9761756986530249394254611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26031351964080665051345629 9761756986530249394254611)
    ·
      refine ⟨14642635479795374091381917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9761756986530249394254611 14642635479795374091381917)
      ·
        refine ⟨5490988304923265284268219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14642635479795374091381917 5490988304923265284268219)
        ·
          refine ⟨8236482457384897926402329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5490988304923265284268219 8236482457384897926402329)
          ·
            refine ⟨6177361843038673444801747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8236482457384897926402329 6177361843038673444801747)
            ·
              refine ⟨9266042764558010167202621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6177361843038673444801747 9266042764558010167202621)
              ·
                refine ⟨3474766036709253812700983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9266042764558010167202621 3474766036709253812700983)
                ·
                  refine ⟨5212149055063880719051475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3474766036709253812700983 5212149055063880719051475)
                  ·
                    refine ⟨7818223582595821078577213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5212149055063880719051475 7818223582595821078577213)
                    ·
                      refine ⟨2931833843473432904466455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7818223582595821078577213 2931833843473432904466455)
                      ·
                        rfl

theorem cell23_5709726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_5709726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709726 prefixEnd_5709726 := by exact prefixLift 5709726
  have htrace : WordTrace (prefixWord ++ tailWord_5709726) baseStart_5709726 baseEnd_5709726 := by
    simpa [prefixWord, tailWord_5709726, baseEnd_5709726] using wordTrace_append hprefix tailTrace_5709726
  have hstable : (prefixWord ++ tailWord_5709726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709726).length < 2 ^ (prefixWord ++ tailWord_5709726).sum := by decide
  have hdescent : baseEnd_5709726 < baseStart_5709726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709732 : List Nat := [2, 3, 1, 2, 1, 3, 3, 3, 1, 2, 2]
def baseStart_5709732 : Nat := 118140960795 + 5709732 * 2 ^ 59
def prefixEnd_5709732 : Nat := 4983230072969 + 3 ^ 40 * 5709732 * 2
def baseEnd_5709732 : Nat := 2931836924357359880991427

theorem tailTrace_5709732 : CollatzResearch.WordTrace tailWord_5709732 prefixEnd_5709732 2931836924357359880991427 := by
  unfold tailWord_5709732
  simp only [CollatzResearch.WordTrace]
  refine ⟨104125517275311791717741725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138834023033749055623655633 104125517275311791717741725)
  ·
    refine ⟨39047068978241921894153147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104125517275311791717741725 39047068978241921894153147)
    ·
      refine ⟨58570603467362882841229721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39047068978241921894153147 58570603467362882841229721)
      ·
        refine ⟨43927952600522162130922291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58570603467362882841229721 43927952600522162130922291)
        ·
          refine ⟨65891928900783243196383437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43927952600522162130922291 65891928900783243196383437)
          ·
            refine ⟨24709473337793716198643789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65891928900783243196383437 24709473337793716198643789)
            ·
              refine ⟨9266052501672643574491421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24709473337793716198643789 9266052501672643574491421)
              ·
                refine ⟨3474769688127241340434283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9266052501672643574491421 3474769688127241340434283)
                ·
                  refine ⟨5212154532190862010651425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3474769688127241340434283 5212154532190862010651425)
                  ·
                    refine ⟨3909115899143146507988569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5212154532190862010651425 3909115899143146507988569)
                    ·
                      refine ⟨2931836924357359880991427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3909115899143146507988569 2931836924357359880991427)
                      ·
                        rfl

theorem cell23_5709732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_5709732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709732 prefixEnd_5709732 := by exact prefixLift 5709732
  have htrace : WordTrace (prefixWord ++ tailWord_5709732) baseStart_5709732 baseEnd_5709732 := by
    simpa [prefixWord, tailWord_5709732, baseEnd_5709732] using wordTrace_append hprefix tailTrace_5709732
  have hstable : (prefixWord ++ tailWord_5709732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709732).length < 2 ^ (prefixWord ++ tailWord_5709732).sum := by decide
  have hdescent : baseEnd_5709732 < baseStart_5709732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709749 : List Nat := [1, 3, 3, 2, 1, 3, 3, 2, 1, 2, 2]
def baseStart_5709749 : Nat := 118140960795 + 5709749 * 2 ^ 59
def prefixEnd_5709749 : Nat := 4983230072969 + 3 ^ 40 * 5709749 * 2
def baseEnd_5709749 : Nat := 2931845653528486314478849

theorem tailTrace_5709749 : CollatzResearch.WordTrace tailWord_5709749 prefixEnd_5709749 2931845653528486314478849 := by
  unfold tailWord_5709749
  simp only [CollatzResearch.WordTrace]
  refine ⟨208251654591561995338852301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138834436394374663559234867 208251654591561995338852301)
  ·
    refine ⟨78094370471835748252069613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208251654591561995338852301 78094370471835748252069613)
    ·
      refine ⟨29285388926938405594526105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78094370471835748252069613 29285388926938405594526105)
      ·
        refine ⟨21964041695203804195894579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29285388926938405594526105 21964041695203804195894579)
        ·
          refine ⟨32946062542805706293841869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21964041695203804195894579 32946062542805706293841869)
          ·
            refine ⟨12354773453552139860190701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32946062542805706293841869 12354773453552139860190701)
            ·
              refine ⟨4633040045082052447571513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12354773453552139860190701 4633040045082052447571513)
              ·
                refine ⟨3474780033811539335678635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4633040045082052447571513 3474780033811539335678635)
                ·
                  refine ⟨5212170050717309003517953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3474780033811539335678635 5212170050717309003517953)
                  ·
                    refine ⟨3909127538037981752638465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5212170050717309003517953 3909127538037981752638465)
                    ·
                      refine ⟨2931845653528486314478849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3909127538037981752638465 2931845653528486314478849)
                      ·
                        rfl

theorem cell23_5709749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_5709749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709749 prefixEnd_5709749 := by exact prefixLift 5709749
  have htrace : WordTrace (prefixWord ++ tailWord_5709749) baseStart_5709749 baseEnd_5709749 := by
    simpa [prefixWord, tailWord_5709749, baseEnd_5709749] using wordTrace_append hprefix tailTrace_5709749
  have hstable : (prefixWord ++ tailWord_5709749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709749).length < 2 ^ (prefixWord ++ tailWord_5709749).sum := by decide
  have hdescent : baseEnd_5709749 < baseStart_5709749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709791 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 5]
def baseStart_5709791 : Nat := 118140960795 + 5709791 * 2 ^ 59
def prefixEnd_5709791 : Nat := 4983230072969 + 3 ^ 40 * 5709791 * 2
def baseEnd_5709791 : Nat := 2931867219715975150153655

theorem tailTrace_5709791 : CollatzResearch.WordTrace tailWord_5709791 prefixEnd_5709791 2931867219715975150153655 := by
  unfold tailWord_5709791
  simp only [CollatzResearch.WordTrace]
  refine ⟨208253186457409836511881227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138835457638273224341254151 208253186457409836511881227)
  ·
    refine ⟨312379779686114754767821841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208253186457409836511881227 312379779686114754767821841)
    ·
      refine ⟨234284834764586066075866381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312379779686114754767821841 234284834764586066075866381)
      ·
        refine ⟨87856813036719774778449893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234284834764586066075866381 87856813036719774778449893)
        ·
          refine ⟨16473152444384957770959355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87856813036719774778449893 16473152444384957770959355)
          ·
            refine ⟨24709728666577436656439033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16473152444384957770959355 24709728666577436656439033)
            ·
              refine ⟨18532296499933077492329275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24709728666577436656439033 18532296499933077492329275)
              ·
                refine ⟨27798444749899616238493913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18532296499933077492329275 27798444749899616238493913)
                ·
                  refine ⟨20848833562424712178870435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27798444749899616238493913 20848833562424712178870435)
                  ·
                    refine ⟨31273250343637068268305653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20848833562424712178870435 31273250343637068268305653)
                    ·
                      refine ⟨2931867219715975150153655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31273250343637068268305653 2931867219715975150153655)
                      ·
                        rfl

theorem cell23_5709791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_5709791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709791 prefixEnd_5709791 := by exact prefixLift 5709791
  have htrace : WordTrace (prefixWord ++ tailWord_5709791) baseStart_5709791 baseEnd_5709791 := by
    simpa [prefixWord, tailWord_5709791, baseEnd_5709791] using wordTrace_append hprefix tailTrace_5709791
  have hstable : (prefixWord ++ tailWord_5709791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709791).length < 2 ^ (prefixWord ++ tailWord_5709791).sum := by decide
  have hdescent : baseEnd_5709791 < baseStart_5709791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709804 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 7]
def baseStart_5709804 : Nat := 118140960795 + 5709804 * 2 ^ 59
def prefixEnd_5709804 : Nat := 4983230072969 + 3 ^ 40 * 5709804 * 2
def baseEnd_5709804 : Nat := 2931873894964483599291095

theorem tailTrace_5709804 : CollatzResearch.WordTrace tailWord_5709804 prefixEnd_5709804 2931873894964483599291095 := by
  unfold tailWord_5709804
  simp only [CollatzResearch.WordTrace]
  refine ⟨104126830303181369866052233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138835773737575159821402977 104126830303181369866052233)
  ·
    refine ⟨78095122727386027399539175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104126830303181369866052233 78095122727386027399539175)
    ·
      refine ⟨117142684091079041099308763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78095122727386027399539175 117142684091079041099308763)
      ·
        refine ⟨175714026136618561648963145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117142684091079041099308763 175714026136618561648963145)
        ·
          refine ⟨131785519602463921236722359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175714026136618561648963145 131785519602463921236722359)
          ·
            refine ⟨197678279403695881855083539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131785519602463921236722359 197678279403695881855083539)
            ·
              refine ⟨296517419105543822782625309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197678279403695881855083539 296517419105543822782625309)
              ·
                refine ⟨111194032164578933543484491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 296517419105543822782625309 111194032164578933543484491)
                ·
                  refine ⟨166791048246868400315226737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111194032164578933543484491 166791048246868400315226737)
                  ·
                    refine ⟨125093286185151300236420053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 166791048246868400315226737 125093286185151300236420053)
                    ·
                      refine ⟨2931873894964483599291095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125093286185151300236420053 2931873894964483599291095)
                      ·
                        rfl

theorem cell23_5709804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_5709804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709804 prefixEnd_5709804 := by exact prefixLift 5709804
  have htrace : WordTrace (prefixWord ++ tailWord_5709804) baseStart_5709804 baseEnd_5709804 := by
    simpa [prefixWord, tailWord_5709804, baseEnd_5709804] using wordTrace_append hprefix tailTrace_5709804
  have hstable : (prefixWord ++ tailWord_5709804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709804).length < 2 ^ (prefixWord ++ tailWord_5709804).sum := by decide
  have hdescent : baseEnd_5709804 < baseStart_5709804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709821 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 1, 5, 3]
def baseStart_5709821 : Nat := 118140960795 + 5709821 * 2 ^ 59
def prefixEnd_5709821 : Nat := 4983230072969 + 3 ^ 40 * 5709821 * 2
def baseEnd_5709821 : Nat := 2931882624135610032778517

theorem tailTrace_5709821 : CollatzResearch.WordTrace tailWord_5709821 prefixEnd_5709821 2931882624135610032778517 := by
  unfold tailWord_5709821
  simp only [CollatzResearch.WordTrace]
  refine ⟨208254280647301151635473317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138836187098200767756982211 208254280647301151635473317)
  ·
    refine ⟨39047677621368965931651247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208254280647301151635473317 39047677621368965931651247)
    ·
      refine ⟨58571516432053448897476871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39047677621368965931651247 58571516432053448897476871)
      ·
        refine ⟨87857274648080173346215307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58571516432053448897476871 87857274648080173346215307)
        ·
          refine ⟨131785911972120260019322961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87857274648080173346215307 131785911972120260019322961)
          ·
            refine ⟨98839433979090195014492221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131785911972120260019322961 98839433979090195014492221)
            ·
              refine ⟨37064787742158823130434583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98839433979090195014492221 37064787742158823130434583)
              ·
                refine ⟨55597181613238234695651875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37064787742158823130434583 55597181613238234695651875)
                ·
                  refine ⟨83395772419857352043477813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55597181613238234695651875 83395772419857352043477813)
                  ·
                    refine ⟨7818353664361626754076045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 83395772419857352043477813 7818353664361626754076045)
                    ·
                      refine ⟨2931882624135610032778517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7818353664361626754076045 2931882624135610032778517)
                      ·
                        rfl

theorem cell23_5709821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_5709821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709821 prefixEnd_5709821 := by exact prefixLift 5709821
  have htrace : WordTrace (prefixWord ++ tailWord_5709821) baseStart_5709821 baseEnd_5709821 := by
    simpa [prefixWord, tailWord_5709821, baseEnd_5709821] using wordTrace_append hprefix tailTrace_5709821
  have hstable : (prefixWord ++ tailWord_5709821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709821).length < 2 ^ (prefixWord ++ tailWord_5709821).sum := by decide
  have hdescent : baseEnd_5709821 < baseStart_5709821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709822 : List Nat := [4, 2, 2, 2, 1, 2, 2, 1, 1, 4, 2]
def baseStart_5709822 : Nat := 118140960795 + 5709822 * 2 ^ 59
def prefixEnd_5709822 : Nat := 4983230072969 + 3 ^ 40 * 5709822 * 2
def baseEnd_5709822 : Nat := 2931883137616264528866013

theorem tailTrace_5709822 : CollatzResearch.WordTrace tailWord_5709822 prefixEnd_5709822 2931883137616264528866013 := by
  unfold tailWord_5709822
  simp only [CollatzResearch.WordTrace]
  refine ⟨26031789640037191100782465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138836211413531685870839813 26031789640037191100782465)
  ·
    refine ⟨19523842230027893325586849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26031789640037191100782465 19523842230027893325586849)
    ·
      refine ⟨14642881672520919994190137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19523842230027893325586849 14642881672520919994190137)
      ·
        refine ⟨10982161254390689995642603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14642881672520919994190137 10982161254390689995642603)
        ·
          refine ⟨16473241881586034993463905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10982161254390689995642603 16473241881586034993463905)
          ·
            refine ⟨12354931411189526245097929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16473241881586034993463905 12354931411189526245097929)
            ·
              refine ⟨9266198558392144683823447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12354931411189526245097929 9266198558392144683823447)
              ·
                refine ⟨13899297837588217025735171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9266198558392144683823447 13899297837588217025735171)
                ·
                  refine ⟨20848946756382325538602757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13899297837588217025735171 20848946756382325538602757)
                  ·
                    refine ⟨3909177516821686038488017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20848946756382325538602757 3909177516821686038488017)
                    ·
                      refine ⟨2931883137616264528866013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3909177516821686038488017 2931883137616264528866013)
                      ·
                        rfl

theorem cell23_5709822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_5709822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709822 prefixEnd_5709822 := by exact prefixLift 5709822
  have htrace : WordTrace (prefixWord ++ tailWord_5709822) baseStart_5709822 baseEnd_5709822 := by
    simpa [prefixWord, tailWord_5709822, baseEnd_5709822] using wordTrace_append hprefix tailTrace_5709822
  have hstable : (prefixWord ++ tailWord_5709822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709822).length < 2 ^ (prefixWord ++ tailWord_5709822).sum := by decide
  have hdescent : baseEnd_5709822 < baseStart_5709822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709845 : List Nat := [1, 3, 2, 1, 5, 1, 2, 3, 5]
def baseStart_5709845 : Nat := 118140960795 + 5709845 * 2 ^ 59
def prefixEnd_5709845 : Nat := 4983230072969 + 3 ^ 40 * 5709845 * 2
def baseEnd_5709845 : Nat := 325766105296813104319823

theorem tailTrace_5709845 : CollatzResearch.WordTrace tailWord_5709845 prefixEnd_5709845 325766105296813104319823 := by
  unfold tailWord_5709845
  simp only [CollatzResearch.WordTrace]
  refine ⟨208255155999214203734346989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138836770666142802489564659 208255155999214203734346989)
  ·
    refine ⟨78095683499705326400380121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208255155999214203734346989 78095683499705326400380121)
    ·
      refine ⟨58571762624778994800285091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78095683499705326400380121 58571762624778994800285091)
      ·
        refine ⟨87857643937168492200427637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58571762624778994800285091 87857643937168492200427637)
        ·
          refine ⟨8236654119109546143790091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87857643937168492200427637 8236654119109546143790091)
          ·
            refine ⟨12354981178664319215685137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8236654119109546143790091 12354981178664319215685137)
            ·
              refine ⟨9266235883998239411763853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12354981178664319215685137 9266235883998239411763853)
              ·
                refine ⟨3474838456499339779411445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9266235883998239411763853 3474838456499339779411445)
                ·
                  refine ⟨325766105296813104319823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3474838456499339779411445 325766105296813104319823)
                  ·
                    rfl

theorem cell23_5709845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 5].length) (baseStart_5709845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709845 prefixEnd_5709845 := by exact prefixLift 5709845
  have htrace : WordTrace (prefixWord ++ tailWord_5709845) baseStart_5709845 baseEnd_5709845 := by
    simpa [prefixWord, tailWord_5709845, baseEnd_5709845] using wordTrace_append hprefix tailTrace_5709845
  have hstable : (prefixWord ++ tailWord_5709845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709845).length < 2 ^ (prefixWord ++ tailWord_5709845).sum := by decide
  have hdescent : baseEnd_5709845 < baseStart_5709845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709878 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_5709878 : Nat := 118140960795 + 5709878 * 2 ^ 59
def prefixEnd_5709878 : Nat := 4983230072969 + 3 ^ 40 * 5709878 * 2
def baseEnd_5709878 : Nat := 2931911892532916309765755

theorem tailTrace_5709878 : CollatzResearch.WordTrace tailWord_5709878 prefixEnd_5709878 2931911892532916309765755 := by
  unfold tailWord_5709878
  simp only [CollatzResearch.WordTrace]
  refine ⟨13016022475505915648143643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138837573072063100246865525 13016022475505915648143643)
  ·
    refine ⟨19524033713258873472215465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13016022475505915648143643 19524033713258873472215465)
    ·
      refine ⟨14643025284944155104161599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19524033713258873472215465 14643025284944155104161599)
      ·
        refine ⟨21964537927416232656242399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14643025284944155104161599 21964537927416232656242399)
        ·
          refine ⟨32946806891124348984363599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21964537927416232656242399 32946806891124348984363599)
          ·
            refine ⟨49420210336686523476545399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32946806891124348984363599 49420210336686523476545399)
            ·
              refine ⟨74130315505029785214818099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49420210336686523476545399 74130315505029785214818099)
              ·
                refine ⟨111195473257544677822227149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74130315505029785214818099 111195473257544677822227149)
                ·
                  refine ⟨41698302471579254183335181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111195473257544677822227149 41698302471579254183335181)
                  ·
                    refine ⟨15636863426842220318750693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41698302471579254183335181 15636863426842220318750693)
                    ·
                      refine ⟨2931911892532916309765755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15636863426842220318750693 2931911892532916309765755)
                      ·
                        rfl

theorem cell23_5709878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_5709878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709878 prefixEnd_5709878 := by exact prefixLift 5709878
  have htrace : WordTrace (prefixWord ++ tailWord_5709878) baseStart_5709878 baseEnd_5709878 := by
    simpa [prefixWord, tailWord_5709878, baseEnd_5709878] using wordTrace_append hprefix tailTrace_5709878
  have hstable : (prefixWord ++ tailWord_5709878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709878).length < 2 ^ (prefixWord ++ tailWord_5709878).sum := by decide
  have hdescent : baseEnd_5709878 < baseStart_5709878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709888 : List Nat := [2, 1, 1, 2, 2, 4, 2, 2, 3, 4]
def baseStart_5709888 : Nat := 118140960795 + 5709888 * 2 ^ 59
def prefixEnd_5709888 : Nat := 4983230072969 + 3 ^ 40 * 5709888 * 2
def baseEnd_5709888 : Nat := 977305675779820423546903

theorem tailTrace_5709888 : CollatzResearch.WordTrace tailWord_5709888 prefixEnd_5709888 977305675779820423546903 := by
  unfold tailWord_5709888
  simp only [CollatzResearch.WordTrace]
  refine ⟨104128362169029211039081159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138837816225372281385441545 104128362169029211039081159)
  ·
    refine ⟨156192543253543816558621739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104128362169029211039081159 156192543253543816558621739)
    ·
      refine ⟨234288814880315724837932609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156192543253543816558621739 234288814880315724837932609)
      ·
        refine ⟨175716611160236793628449457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234288814880315724837932609 175716611160236793628449457)
        ·
          refine ⟨131787458370177595221337093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175716611160236793628449457 131787458370177595221337093)
          ·
            refine ⟨24710148444408299104000705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131787458370177595221337093 24710148444408299104000705)
            ·
              refine ⟨18532611333306224328000529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24710148444408299104000705 18532611333306224328000529)
              ·
                refine ⟨13899458499979668246000397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18532611333306224328000529 13899458499979668246000397)
                ·
                  refine ⟨5212296937492375592250149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13899458499979668246000397 5212296937492375592250149)
                  ·
                    refine ⟨977305675779820423546903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5212296937492375592250149 977305675779820423546903)
                    ·
                      rfl

theorem cell23_5709888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 3, 4].length) (baseStart_5709888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709888 prefixEnd_5709888 := by exact prefixLift 5709888
  have htrace : WordTrace (prefixWord ++ tailWord_5709888) baseStart_5709888 baseEnd_5709888 := by
    simpa [prefixWord, tailWord_5709888, baseEnd_5709888] using wordTrace_append hprefix tailTrace_5709888
  have hstable : (prefixWord ++ tailWord_5709888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709888).length < 2 ^ (prefixWord ++ tailWord_5709888).sum := by decide
  have hdescent : baseEnd_5709888 < baseStart_5709888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709898 : List Nat := [3, 1, 2, 1, 1, 2, 1, 5, 2, 2, 3]
def baseStart_5709898 : Nat := 118140960795 + 5709898 * 2 ^ 59
def prefixEnd_5709898 : Nat := 4983230072969 + 3 ^ 40 * 5709898 * 2
def baseEnd_5709898 : Nat := 2931922162146006231515663

theorem tailTrace_5709898 : CollatzResearch.WordTrace tailWord_5709898 prefixEnd_5709898 2931922162146006231515663 := by
  unfold tailWord_5709898
  simp only [CollatzResearch.WordTrace]
  refine ⟨52064272267005548446506587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138838059378681462524017565 52064272267005548446506587)
  ·
    refine ⟨78096408400508322669759881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52064272267005548446506587 78096408400508322669759881)
    ·
      refine ⟨58572306300381242002319911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78096408400508322669759881 58572306300381242002319911)
      ·
        refine ⟨87858459450571863003479867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58572306300381242002319911 87858459450571863003479867)
        ·
          refine ⟨131787689175857794505219801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87858459450571863003479867 131787689175857794505219801)
          ·
            refine ⟨98840766881893345878914851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131787689175857794505219801 98840766881893345878914851)
            ·
              refine ⟨148261150322840018818372277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98840766881893345878914851 148261150322840018818372277)
              ·
                refine ⟨13899482842766251764222401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 148261150322840018818372277 13899482842766251764222401)
                ·
                  refine ⟨10424612132074688823166801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13899482842766251764222401 10424612132074688823166801)
                  ·
                    refine ⟨7818459099056016617375101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10424612132074688823166801 7818459099056016617375101)
                    ·
                      refine ⟨2931922162146006231515663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7818459099056016617375101 2931922162146006231515663)
                      ·
                        rfl

theorem cell23_5709898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_5709898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709898 prefixEnd_5709898 := by exact prefixLift 5709898
  have htrace : WordTrace (prefixWord ++ tailWord_5709898) baseStart_5709898 baseEnd_5709898 := by
    simpa [prefixWord, tailWord_5709898, baseEnd_5709898] using wordTrace_append hprefix tailTrace_5709898
  have hstable : (prefixWord ++ tailWord_5709898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709898).length < 2 ^ (prefixWord ++ tailWord_5709898).sum := by decide
  have hdescent : baseEnd_5709898 < baseStart_5709898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709935 : List Nat := [1, 1, 2, 1, 3, 6, 2, 1, 6]
def baseStart_5709935 : Nat := 118140960795 + 5709935 * 2 ^ 59
def prefixEnd_5709935 : Nat := 4983230072969 + 3 ^ 40 * 5709935 * 2
def baseEnd_5709935 : Nat := 325771240103358065194777

theorem tailTrace_5709935 : CollatzResearch.WordTrace tailWord_5709935 prefixEnd_5709935 325771240103358065194777 := by
  unfold tailWord_5709935
  simp only [CollatzResearch.WordTrace]
  refine ⟨208258438568888149105123259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138838959045925432736748839 208258438568888149105123259)
  ·
    refine ⟨312387657853332223657684889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208258438568888149105123259 312387657853332223657684889)
    ·
      refine ⟨234290743389999167743263667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312387657853332223657684889 234290743389999167743263667)
      ·
        refine ⟨351436115084998751614895501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234290743389999167743263667 351436115084998751614895501)
        ·
          refine ⟨131788543156874531855585813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 351436115084998751614895501 131788543156874531855585813)
          ·
            refine ⟨6177587960478493680730585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 131788543156874531855585813 6177587960478493680730585)
            ·
              refine ⟨4633190970358870260547939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6177587960478493680730585 4633190970358870260547939)
              ·
                refine ⟨6949786455538305390821909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4633190970358870260547939 6949786455538305390821909)
                ·
                  refine ⟨325771240103358065194777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6949786455538305390821909 325771240103358065194777)
                  ·
                    rfl

theorem cell23_5709935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 6].length) (baseStart_5709935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709935 prefixEnd_5709935 := by exact prefixLift 5709935
  have htrace : WordTrace (prefixWord ++ tailWord_5709935) baseStart_5709935 baseEnd_5709935 := by
    simpa [prefixWord, tailWord_5709935, baseEnd_5709935] using wordTrace_append hprefix tailTrace_5709935
  have hstable : (prefixWord ++ tailWord_5709935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709935).length < 2 ^ (prefixWord ++ tailWord_5709935).sum := by decide
  have hdescent : baseEnd_5709935 < baseStart_5709935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709948 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 3, 5]
def baseStart_5709948 : Nat := 118140960795 + 5709948 * 2 ^ 59
def prefixEnd_5709948 : Nat := 4983230072969 + 3 ^ 40 * 5709948 * 2
def baseEnd_5709948 : Nat := 977315945392910345296811

theorem tailTrace_5709948 : CollatzResearch.WordTrace tailWord_5709948 prefixEnd_5709948 977315945392910345296811 := by
  unfold tailWord_5709948
  simp only [CollatzResearch.WordTrace]
  refine ⟨104129456358920526162673249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138839275145227368216897665 104129456358920526162673249)
  ·
    refine ⟨78097092269190394622004937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104129456358920526162673249 78097092269190394622004937)
    ·
      refine ⟨58572819201892795966503703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78097092269190394622004937 58572819201892795966503703)
      ·
        refine ⟨87859228802839193949755555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58572819201892795966503703 87859228802839193949755555)
        ·
          refine ⟨131788843204258790924633333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87859228802839193949755555 131788843204258790924633333)
          ·
            refine ⟨12355204050399261649184375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131788843204258790924633333 12355204050399261649184375)
            ·
              refine ⟨18532806075598892473776563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12355204050399261649184375 18532806075598892473776563)
              ·
                refine ⟨27799209113398338710664845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18532806075598892473776563 27799209113398338710664845)
                ·
                  refine ⟨10424703417524377016499317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27799209113398338710664845 10424703417524377016499317)
                  ·
                    refine ⟨977315945392910345296811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10424703417524377016499317 977315945392910345296811)
                    ·
                      rfl

theorem cell23_5709948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_5709948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709948 prefixEnd_5709948 := by exact prefixLift 5709948
  have htrace : WordTrace (prefixWord ++ tailWord_5709948) baseStart_5709948 baseEnd_5709948 := by
    simpa [prefixWord, tailWord_5709948, baseEnd_5709948] using wordTrace_append hprefix tailTrace_5709948
  have hstable : (prefixWord ++ tailWord_5709948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709948).length < 2 ^ (prefixWord ++ tailWord_5709948).sum := by decide
  have hdescent : baseEnd_5709948 < baseStart_5709948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709955 : List Nat := [1, 1, 1, 3, 3, 3, 1, 3, 2, 3, 2]
def baseStart_5709955 : Nat := 118140960795 + 5709955 * 2 ^ 59
def prefixEnd_5709955 : Nat := 4983230072969 + 3 ^ 40 * 5709955 * 2
def baseEnd_5709955 : Nat := 2931951430543312508502901

theorem tailTrace_5709955 : CollatzResearch.WordTrace tailWord_5709955 prefixEnd_5709955 2931951430543312508502901 := by
  unfold tailWord_5709955
  simp only [CollatzResearch.WordTrace]
  refine ⟨208259168028815692520851319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138839445352543795013900879 208259168028815692520851319)
  ·
    refine ⟨312388752043223538781276979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208259168028815692520851319 312388752043223538781276979)
    ·
      refine ⟨468583128064835308171915469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312388752043223538781276979 468583128064835308171915469)
      ·
        refine ⟨175718673024313240564468301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 468583128064835308171915469 175718673024313240564468301)
        ·
          refine ⟨65894502384117465211675613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175718673024313240564468301 65894502384117465211675613)
          ·
            refine ⟨24710438394044049454378355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65894502384117465211675613 24710438394044049454378355)
            ·
              refine ⟨37065657591066074181567533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24710438394044049454378355 37065657591066074181567533)
              ·
                refine ⟨13899621596649777818087825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37065657591066074181567533 13899621596649777818087825)
                ·
                  refine ⟨10424716197487333363565869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13899621596649777818087825 10424716197487333363565869)
                  ·
                    refine ⟨3909268574057750011337201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10424716197487333363565869 3909268574057750011337201)
                    ·
                      refine ⟨2931951430543312508502901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3909268574057750011337201 2931951430543312508502901)
                      ·
                        rfl

theorem cell23_5709955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 3, 2].length) (baseStart_5709955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709955 prefixEnd_5709955 := by exact prefixLift 5709955
  have htrace : WordTrace (prefixWord ++ tailWord_5709955) baseStart_5709955 baseEnd_5709955 := by
    simpa [prefixWord, tailWord_5709955, baseEnd_5709955] using wordTrace_append hprefix tailTrace_5709955
  have hstable : (prefixWord ++ tailWord_5709955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709955).length < 2 ^ (prefixWord ++ tailWord_5709955).sum := by decide
  have hdescent : baseEnd_5709955 < baseStart_5709955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710002 : List Nat := [3, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2]
def baseStart_5710002 : Nat := 118140960795 + 5710002 * 2 ^ 59
def prefixEnd_5710002 : Nat := 4983230072969 + 3 ^ 40 * 5710002 * 2
def baseEnd_5710002 : Nat := 2931975564134073824615185

theorem tailTrace_5710002 : CollatzResearch.WordTrace tailWord_5710002 prefixEnd_5710002 2931975564134073824615185 := by
  unfold tailWord_5710002
  simp only [CollatzResearch.WordTrace]
  refine ⟨52065220564911354886953065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138840588173096946365208173 52065220564911354886953065)
  ·
    refine ⟨39048915423683516165214799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52065220564911354886953065 39048915423683516165214799)
    ·
      refine ⟨58573373135525274247822199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39048915423683516165214799 58573373135525274247822199)
      ·
        refine ⟨87860059703287911371733299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58573373135525274247822199 87860059703287911371733299)
        ·
          refine ⟨131790089554931867057599949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87860059703287911371733299 131790089554931867057599949)
          ·
            refine ⟨49421283583099450146599981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131790089554931867057599949 49421283583099450146599981)
            ·
              refine ⟨18532981343662293804974993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49421283583099450146599981 18532981343662293804974993)
              ·
                refine ⟨13899736007746720353731245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18532981343662293804974993 13899736007746720353731245)
                ·
                  refine ⟨5212401002905020132649217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13899736007746720353731245 5212401002905020132649217)
                  ·
                    refine ⟨3909300752178765099486913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5212401002905020132649217 3909300752178765099486913)
                    ·
                      refine ⟨2931975564134073824615185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3909300752178765099486913 2931975564134073824615185)
                      ·
                        rfl

theorem cell23_5710002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2].length) (baseStart_5710002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710002 prefixEnd_5710002 := by exact prefixLift 5710002
  have htrace : WordTrace (prefixWord ++ tailWord_5710002) baseStart_5710002 baseEnd_5710002 := by
    simpa [prefixWord, tailWord_5710002, baseEnd_5710002] using wordTrace_append hprefix tailTrace_5710002
  have hstable : (prefixWord ++ tailWord_5710002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710002).length < 2 ^ (prefixWord ++ tailWord_5710002).sum := by decide
  have hdescent : baseEnd_5710002 < baseStart_5710002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710008 : List Nat := [2, 1, 2, 1, 2, 1, 7, 7]
def baseStart_5710008 : Nat := 118140960795 + 5710008 * 2 ^ 59
def prefixEnd_5710008 : Nat := 4983230072969 + 3 ^ 40 * 5710008 * 2
def baseEnd_5710008 : Nat := 108591801667333363005191

theorem tailTrace_5710008 : CollatzResearch.WordTrace tailWord_5710008 prefixEnd_5710008 108591801667333363005191 := by
  unfold tailWord_5710008
  simp only [CollatzResearch.WordTrace]
  refine ⟨104130550548811841286265339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138840734065082455048353785 104130550548811841286265339)
  ·
    refine ⟨156195825823217761929398009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104130550548811841286265339 156195825823217761929398009)
    ·
      refine ⟨117146869367413321447048507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156195825823217761929398009 117146869367413321447048507)
      ·
        refine ⟨175720304051119982170572761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117146869367413321447048507 175720304051119982170572761)
        ·
          refine ⟨131790228038339986627929571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175720304051119982170572761 131790228038339986627929571)
          ·
            refine ⟨197685342057509979941894357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131790228038339986627929571 197685342057509979941894357)
            ·
              refine ⟨4633250204472890154888149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 197685342057509979941894357 4633250204472890154888149)
              ·
                refine ⟨108591801667333363005191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4633250204472890154888149 108591801667333363005191)
                ·
                  rfl

theorem cell23_5710008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 7].length) (baseStart_5710008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710008 prefixEnd_5710008 := by exact prefixLift 5710008
  have htrace : WordTrace (prefixWord ++ tailWord_5710008) baseStart_5710008 baseEnd_5710008 := by
    simpa [prefixWord, tailWord_5710008, baseEnd_5710008] using wordTrace_append hprefix tailTrace_5710008
  have hstable : (prefixWord ++ tailWord_5710008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710008).length < 2 ^ (prefixWord ++ tailWord_5710008).sum := by decide
  have hdescent : baseEnd_5710008 < baseStart_5710008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710092 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 4, 2, 2]
def baseStart_5710092 : Nat := 118140960795 + 5710092 * 2 ^ 59
def prefixEnd_5710092 : Nat := 4983230072969 + 3 ^ 40 * 5710092 * 2
def baseEnd_5710092 : Nat := 2932021777392978472489771

theorem tailTrace_5710092 : CollatzResearch.WordTrace tailWord_5710092 prefixEnd_5710092 2932021777392978472489771 := by
  unfold tailWord_5710092
  simp only [CollatzResearch.WordTrace]
  refine ⟨104132082414659682459294265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138842776552879576612392353 104132082414659682459294265)
  ·
    refine ⟨78099061810994761844470699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104132082414659682459294265 78099061810994761844470699)
    ·
      refine ⟨117148592716492142766706049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78099061810994761844470699 117148592716492142766706049)
      ·
        refine ⟨87861444537369107075029537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117148592716492142766706049 87861444537369107075029537)
        ·
          refine ⟨65896083403026830306272153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87861444537369107075029537 65896083403026830306272153)
          ·
            refine ⟨49422062552270122729704115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65896083403026830306272153 49422062552270122729704115)
            ·
              refine ⟨74133093828405184094556173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49422062552270122729704115 74133093828405184094556173)
              ·
                refine ⟨27799910185651944035458565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74133093828405184094556173 27799910185651944035458565)
                ·
                  refine ⟨5212483159809739506648481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27799910185651944035458565 5212483159809739506648481)
                  ·
                    refine ⟨3909362369857304629986361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5212483159809739506648481 3909362369857304629986361)
                    ·
                      refine ⟨2932021777392978472489771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3909362369857304629986361 2932021777392978472489771)
                      ·
                        rfl

theorem cell23_5710092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 4, 2, 2].length) (baseStart_5710092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710092 prefixEnd_5710092 := by exact prefixLift 5710092
  have htrace : WordTrace (prefixWord ++ tailWord_5710092) baseStart_5710092 baseEnd_5710092 := by
    simpa [prefixWord, tailWord_5710092, baseEnd_5710092] using wordTrace_append hprefix tailTrace_5710092
  have hstable : (prefixWord ++ tailWord_5710092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710092).length < 2 ^ (prefixWord ++ tailWord_5710092).sum := by decide
  have hdescent : baseEnd_5710092 < baseStart_5710092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710126 : List Nat := [4, 1, 3, 3, 1, 1, 1, 2, 1, 4, 2]
def baseStart_5710126 : Nat := 118140960795 + 5710126 * 2 ^ 59
def prefixEnd_5710126 : Nat := 4983230072969 + 3 ^ 40 * 5710126 * 2
def baseEnd_5710126 : Nat := 2932039235735231339464615

theorem tailTrace_5710126 : CollatzResearch.WordTrace tailWord_5710126 prefixEnd_5710126 2932039235735231339464615 := by
  unfold tailWord_5710126
  simp only [CollatzResearch.WordTrace]
  refine ⟨26033175613899523590665779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138843603274130792483550821 26033175613899523590665779)
  ·
    refine ⟨39049763420849285385998669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26033175613899523590665779 39049763420849285385998669)
    ·
      refine ⟨14643661282818482019749501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39049763420849285385998669 14643661282818482019749501)
      ·
        refine ⟨5491372981056930757406063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14643661282818482019749501 5491372981056930757406063)
        ·
          refine ⟨8237059471585396136109095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5491372981056930757406063 8237059471585396136109095)
          ·
            refine ⟨12355589207378094204163643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8237059471585396136109095 12355589207378094204163643)
            ·
              refine ⟨18533383811067141306245465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12355589207378094204163643 18533383811067141306245465)
              ·
                refine ⟨13900037858300355979684099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18533383811067141306245465 13900037858300355979684099)
                ·
                  refine ⟨20850056787450533969526149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13900037858300355979684099 20850056787450533969526149)
                  ·
                    refine ⟨3909385647646975119286153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20850056787450533969526149 3909385647646975119286153)
                    ·
                      refine ⟨2932039235735231339464615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3909385647646975119286153 2932039235735231339464615)
                      ·
                        rfl

theorem cell23_5710126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_5710126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710126 prefixEnd_5710126 := by exact prefixLift 5710126
  have htrace : WordTrace (prefixWord ++ tailWord_5710126) baseStart_5710126 baseEnd_5710126 := by
    simpa [prefixWord, tailWord_5710126, baseEnd_5710126] using wordTrace_append hprefix tailTrace_5710126
  have hstable : (prefixWord ++ tailWord_5710126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710126).length < 2 ^ (prefixWord ++ tailWord_5710126).sum := by decide
  have hdescent : baseEnd_5710126 < baseStart_5710126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710135 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 4, 5, 2]
def baseStart_5710135 : Nat := 118140960795 + 5710135 * 2 ^ 59
def prefixEnd_5710135 : Nat := 4983230072969 + 3 ^ 40 * 5710135 * 2
def baseEnd_5710135 : Nat := 2932043857061121804252073

theorem tailTrace_5710135 : CollatzResearch.WordTrace tailWord_5710135 prefixEnd_5710135 2932043857061121804252073 := by
  unfold tailWord_5710135
  simp only [CollatzResearch.WordTrace]
  refine ⟨208265733168163583262403859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138843822112109055508269239 208265733168163583262403859)
  ·
    refine ⟨312398599752245374893605789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208265733168163583262403859 312398599752245374893605789)
    ·
      refine ⟨117149474907092015585102171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312398599752245374893605789 117149474907092015585102171)
      ·
        refine ⟨175724212360638023377653257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117149474907092015585102171 175724212360638023377653257)
        ·
          refine ⟨131793159270478517533239943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175724212360638023377653257 131793159270478517533239943)
          ·
            refine ⟨197689738905717776299859915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131793159270478517533239943 197689738905717776299859915)
            ·
              refine ⟨296534608358576664449789873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197689738905717776299859915 296534608358576664449789873)
              ·
                refine ⟨222400956268932498337342405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296534608358576664449789873 222400956268932498337342405)
                ·
                  refine ⟨41700179300424843438251701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 222400956268932498337342405 41700179300424843438251701)
                  ·
                    refine ⟨3909391809414829072336097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41700179300424843438251701 3909391809414829072336097)
                    ·
                      refine ⟨2932043857061121804252073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3909391809414829072336097 2932043857061121804252073)
                      ·
                        rfl

theorem cell23_5710135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 5, 2].length) (baseStart_5710135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710135 prefixEnd_5710135 := by exact prefixLift 5710135
  have htrace : WordTrace (prefixWord ++ tailWord_5710135) baseStart_5710135 baseEnd_5710135 := by
    simpa [prefixWord, tailWord_5710135, baseEnd_5710135] using wordTrace_append hprefix tailTrace_5710135
  have hstable : (prefixWord ++ tailWord_5710135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710135).length < 2 ^ (prefixWord ++ tailWord_5710135).sum := by decide
  have hdescent : baseEnd_5710135 < baseStart_5710135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710175 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 5, 4]
def baseStart_5710175 : Nat := 118140960795 + 5710175 * 2 ^ 59
def prefixEnd_5710175 : Nat := 4983230072969 + 3 ^ 40 * 5710175 * 2
def baseEnd_5710175 : Nat := 977354798762433882583963

theorem tailTrace_5710175 : CollatzResearch.WordTrace tailWord_5710175 prefixEnd_5710175 977354798762433882583963 := by
  unfold tailWord_5710175
  simp only [CollatzResearch.WordTrace]
  refine ⟨208267192088018670093859979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138844794725345780062573319 208267192088018670093859979)
  ·
    refine ⟨312400788132028005140789969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208267192088018670093859979 312400788132028005140789969)
    ·
      refine ⟨234300591099021003855592477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312400788132028005140789969 234300591099021003855592477)
      ·
        refine ⟨87862721662132876445847179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234300591099021003855592477 87862721662132876445847179)
        ·
          refine ⟨131794082493199314668770769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87862721662132876445847179 131794082493199314668770769)
          ·
            refine ⟨98845561869899486001578077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131794082493199314668770769 98845561869899486001578077)
            ·
              refine ⟨37067085701212307250591779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98845561869899486001578077 37067085701212307250591779)
              ·
                refine ⟨55600628551818460875887669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37067085701212307250591779 55600628551818460875887669)
                ·
                  refine ⟨5212558926732980707114469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55600628551818460875887669 5212558926732980707114469)
                  ·
                    refine ⟨977354798762433882583963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5212558926732980707114469 977354798762433882583963)
                    ·
                      rfl

theorem cell23_5710175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 4].length) (baseStart_5710175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710175 prefixEnd_5710175 := by exact prefixLift 5710175
  have htrace : WordTrace (prefixWord ++ tailWord_5710175) baseStart_5710175 baseEnd_5710175 := by
    simpa [prefixWord, tailWord_5710175, baseEnd_5710175] using wordTrace_append hprefix tailTrace_5710175
  have hstable : (prefixWord ++ tailWord_5710175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710175).length < 2 ^ (prefixWord ++ tailWord_5710175).sum := by decide
  have hdescent : baseEnd_5710175 < baseStart_5710175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710185 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 1, 4, 3]
def baseStart_5710185 : Nat := 118140960795 + 5710185 * 2 ^ 59
def prefixEnd_5710185 : Nat := 4983230072969 + 3 ^ 40 * 5710185 * 2
def baseEnd_5710185 : Nat := 2932069531093846608626843

theorem tailTrace_5710185 : CollatzResearch.WordTrace tailWord_5710185 prefixEnd_5710185 2932069531093846608626843 := by
  unfold tailWord_5710185
  simp only [CollatzResearch.WordTrace]
  refine ⟨208267556817982441801724009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138845037878654961201149339 208267556817982441801724009)
  ·
    refine ⟨156200667613486831351293007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208267556817982441801724009 156200667613486831351293007)
    ·
      refine ⟨234301001420230247026939511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156200667613486831351293007 234301001420230247026939511)
      ·
        refine ⟨351451502130345370540409267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234301001420230247026939511 351451502130345370540409267)
        ·
          refine ⟨527177253195518055810613901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351451502130345370540409267 527177253195518055810613901)
          ·
            refine ⟨197691469948319270928980213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 527177253195518055810613901 197691469948319270928980213)
            ·
              refine ⟨18533575307654931649591895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 197691469948319270928980213 18533575307654931649591895)
              ·
                refine ⟨27800362961482397474387843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18533575307654931649591895 27800362961482397474387843)
                ·
                  refine ⟨41700544442223596211581765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27800362961482397474387843 41700544442223596211581765)
                  ·
                    refine ⟨7818852082916924289671581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41700544442223596211581765 7818852082916924289671581)
                    ·
                      refine ⟨2932069531093846608626843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7818852082916924289671581 2932069531093846608626843)
                      ·
                        rfl

theorem cell23_5710185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 4, 3].length) (baseStart_5710185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710185 prefixEnd_5710185 := by exact prefixLift 5710185
  have htrace : WordTrace (prefixWord ++ tailWord_5710185) baseStart_5710185 baseEnd_5710185 := by
    simpa [prefixWord, tailWord_5710185, baseEnd_5710185] using wordTrace_append hprefix tailTrace_5710185
  have hstable : (prefixWord ++ tailWord_5710185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710185).length < 2 ^ (prefixWord ++ tailWord_5710185).sum := by decide
  have hdescent : baseEnd_5710185 < baseStart_5710185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710205 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 8]
def baseStart_5710205 : Nat := 118140960795 + 5710205 * 2 ^ 59
def prefixEnd_5710205 : Nat := 4983230072969 + 3 ^ 40 * 5710205 * 2
def baseEnd_5710205 : Nat := 325786644522992947819639

theorem tailTrace_5710205 : CollatzResearch.WordTrace tailWord_5710205 prefixEnd_5710205 325786644522992947819639 := by
  unfold tailWord_5710205
  simp only [CollatzResearch.WordTrace]
  refine ⟨208268286277909985217452069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138845524185273323478301379 208268286277909985217452069)
  ·
    refine ⟨39050303677108122228272263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208268286277909985217452069 39050303677108122228272263)
    ·
      refine ⟨58575455515662183342408395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39050303677108122228272263 58575455515662183342408395)
      ·
        refine ⟨87863183273493275013612593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58575455515662183342408395 87863183273493275013612593)
        ·
          refine ⟨65897387455119956260209445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87863183273493275013612593 65897387455119956260209445)
          ·
            refine ⟨12355760147834991798789271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65897387455119956260209445 12355760147834991798789271)
            ·
              refine ⟨18533640221752487698183907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12355760147834991798789271 18533640221752487698183907)
              ·
                refine ⟨27800460332628731547275861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18533640221752487698183907 27800460332628731547275861)
                ·
                  refine ⟨325786644522992947819639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27800460332628731547275861 325786644522992947819639)
                  ·
                    rfl

theorem cell23_5710205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_5710205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710205 prefixEnd_5710205 := by exact prefixLift 5710205
  have htrace : WordTrace (prefixWord ++ tailWord_5710205) baseStart_5710205 baseEnd_5710205 := by
    simpa [prefixWord, tailWord_5710205, baseEnd_5710205] using wordTrace_append hprefix tailTrace_5710205
  have hstable : (prefixWord ++ tailWord_5710205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710205).length < 2 ^ (prefixWord ++ tailWord_5710205).sum := by decide
  have hdescent : baseEnd_5710205 < baseStart_5710205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710209 : List Nat := [1, 2, 4, 3, 1, 2, 2, 1, 3, 4]
def baseStart_5710209 : Nat := 118140960795 + 5710209 * 2 ^ 59
def prefixEnd_5710209 : Nat := 4983230072969 + 3 ^ 40 * 5710209 * 2
def baseEnd_5710209 : Nat := 977360618209851504908911

theorem tailTrace_5710209 : CollatzResearch.WordTrace tailWord_5710209 prefixEnd_5710209 977360618209851504908911 := by
  unfold tailWord_5710209
  simp only [CollatzResearch.WordTrace]
  refine ⟨208268432169895493900597681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138845621446596995933731787 208268432169895493900597681)
  ·
    refine ⟨156201324127421620425448261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208268432169895493900597681 156201324127421620425448261)
    ·
      refine ⟨29287748273891553829771549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156201324127421620425448261 29287748273891553829771549)
      ·
        refine ⟨10982905602709332686164331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29287748273891553829771549 10982905602709332686164331)
        ·
          refine ⟨16474358404063999029246497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10982905602709332686164331 16474358404063999029246497)
          ·
            refine ⟨12355768803047999271934873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16474358404063999029246497 12355768803047999271934873)
            ·
              refine ⟨9266826602285999453951155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12355768803047999271934873 9266826602285999453951155)
              ·
                refine ⟨13900239903428999180926733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9266826602285999453951155 13900239903428999180926733)
                ·
                  refine ⟨5212589963785874692847525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13900239903428999180926733 5212589963785874692847525)
                  ·
                    refine ⟨977360618209851504908911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5212589963785874692847525 977360618209851504908911)
                    ·
                      rfl

theorem cell23_5710209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_5710209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710209 prefixEnd_5710209 := by exact prefixLift 5710209
  have htrace : WordTrace (prefixWord ++ tailWord_5710209) baseStart_5710209 baseEnd_5710209 := by
    simpa [prefixWord, tailWord_5710209, baseEnd_5710209] using wordTrace_append hprefix tailTrace_5710209
  have hstable : (prefixWord ++ tailWord_5710209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710209).length < 2 ^ (prefixWord ++ tailWord_5710209).sum := by decide
  have hdescent : baseEnd_5710209 < baseStart_5710209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710255 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 4]
def baseStart_5710255 : Nat := 118140960795 + 5710255 * 2 ^ 59
def prefixEnd_5710255 : Nat := 4983230072969 + 3 ^ 40 * 5710255 * 2
def baseEnd_5710255 : Nat := 2932105474739661334751521

theorem tailTrace_5710255 : CollatzResearch.WordTrace tailWord_5710255 prefixEnd_5710255 2932105474739661334751521 := by
  unfold tailWord_5710255
  simp only [CollatzResearch.WordTrace]
  refine ⟨208270109927728843756772219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138846739951819229171181479 208270109927728843756772219)
  ·
    refine ⟨312405164891593265635158329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208270109927728843756772219 312405164891593265635158329)
    ·
      refine ⟨234303873668694949226368747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312405164891593265635158329 234303873668694949226368747)
      ·
        refine ⟨351455810503042423839553121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234303873668694949226368747 351455810503042423839553121)
        ·
          refine ⟨263591857877281817879664841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351455810503042423839553121 263591857877281817879664841)
          ·
            refine ⟨197693893407961363409748631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263591857877281817879664841 197693893407961363409748631)
            ·
              refine ⟨296540840111942045114622947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197693893407961363409748631 296540840111942045114622947)
              ·
                refine ⟨444811260167913067671934421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296540840111942045114622947 444811260167913067671934421)
                ·
                  refine ⟨10425263910185462523560963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 444811260167913067671934421 10425263910185462523560963)
                  ·
                    refine ⟨15637895865278193785341445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10425263910185462523560963 15637895865278193785341445)
                    ·
                      refine ⟨2932105474739661334751521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15637895865278193785341445 2932105474739661334751521)
                      ·
                        rfl

theorem cell23_5710255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 4].length) (baseStart_5710255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710255 prefixEnd_5710255 := by exact prefixLift 5710255
  have htrace : WordTrace (prefixWord ++ tailWord_5710255) baseStart_5710255 baseEnd_5710255 := by
    simpa [prefixWord, tailWord_5710255, baseEnd_5710255] using wordTrace_append hprefix tailTrace_5710255
  have hstable : (prefixWord ++ tailWord_5710255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710255).length < 2 ^ (prefixWord ++ tailWord_5710255).sum := by decide
  have hdescent : baseEnd_5710255 < baseStart_5710255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710260 : List Nat := [2, 5, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_5710260 : Nat := 118140960795 + 5710260 * 2 ^ 59
def prefixEnd_5710260 : Nat := 4983230072969 + 3 ^ 40 * 5710260 * 2
def baseEnd_5710260 : Nat := 977369347380977938396333

theorem tailTrace_5710260 : CollatzResearch.WordTrace tailWord_5710260 prefixEnd_5710260 977369347380977938396333 := by
  unfold tailWord_5710260
  simp only [CollatzResearch.WordTrace]
  refine ⟨104135146146355364805352117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138846861528473819740469489 104135146146355364805352117)
  ·
    refine ⟨9762669951220815450501761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104135146146355364805352117 9762669951220815450501761)
    ·
      refine ⟨7322002463415611587876321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9762669951220815450501761 7322002463415611587876321)
      ·
        refine ⟨5491501847561708690907241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7322002463415611587876321 5491501847561708690907241)
        ·
          refine ⟨4118626385671281518180431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5491501847561708690907241 4118626385671281518180431)
          ·
            refine ⟨6177939578506922277270647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4118626385671281518180431 6177939578506922277270647)
            ·
              refine ⟨9266909367760383415905971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6177939578506922277270647 9266909367760383415905971)
              ·
                refine ⟨13900364051640575123858957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9266909367760383415905971 13900364051640575123858957)
                ·
                  refine ⟨5212636519365215671447109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13900364051640575123858957 5212636519365215671447109)
                  ·
                    refine ⟨977369347380977938396333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5212636519365215671447109 977369347380977938396333)
                    ·
                      rfl

theorem cell23_5710260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_5710260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710260 prefixEnd_5710260 := by exact prefixLift 5710260
  have htrace : WordTrace (prefixWord ++ tailWord_5710260) baseStart_5710260 baseEnd_5710260 := by
    simpa [prefixWord, tailWord_5710260, baseEnd_5710260] using wordTrace_append hprefix tailTrace_5710260
  have hstable : (prefixWord ++ tailWord_5710260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710260).length < 2 ^ (prefixWord ++ tailWord_5710260).sum := by decide
  have hdescent : baseEnd_5710260 < baseStart_5710260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710275 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 3]
def baseStart_5710275 : Nat := 118140960795 + 5710275 * 2 ^ 59
def prefixEnd_5710275 : Nat := 4983230072969 + 3 ^ 40 * 5710275 * 2
def baseEnd_5710275 : Nat := 2932115744352751256501429

theorem tailTrace_5710275 : CollatzResearch.WordTrace tailWord_5710275 prefixEnd_5710275 2932115744352751256501429 := by
  unfold tailWord_5710275
  simp only [CollatzResearch.WordTrace]
  refine ⟨208270839387656387172500279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138847226258437591448333519 208270839387656387172500279)
  ·
    refine ⟨312406259081484580758750419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208270839387656387172500279 312406259081484580758750419)
    ·
      refine ⟨468609388622226871138125629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312406259081484580758750419 468609388622226871138125629)
      ·
        refine ⟨175728520733335076676797111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 468609388622226871138125629 175728520733335076676797111)
        ·
          refine ⟨263592781100002615015195667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175728520733335076676797111 263592781100002615015195667)
          ·
            refine ⟨395389171650003922522793501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263592781100002615015195667 395389171650003922522793501)
            ·
              refine ⟨148270939368751470946047563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 395389171650003922522793501 148270939368751470946047563)
              ·
                refine ⟨222406409053127206419071345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148270939368751470946047563 222406409053127206419071345)
                ·
                  refine ⟨166804806789845404814303509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 222406409053127206419071345 166804806789845404814303509)
                  ·
                    refine ⟨7818975318274003350670477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 166804806789845404814303509 7818975318274003350670477)
                    ·
                      refine ⟨2932115744352751256501429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7818975318274003350670477 2932115744352751256501429)
                      ·
                        rfl

theorem cell23_5710275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 3].length) (baseStart_5710275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710275 prefixEnd_5710275 := by exact prefixLift 5710275
  have htrace : WordTrace (prefixWord ++ tailWord_5710275) baseStart_5710275 baseEnd_5710275 := by
    simpa [prefixWord, tailWord_5710275, baseEnd_5710275] using wordTrace_append hprefix tailTrace_5710275
  have hstable : (prefixWord ++ tailWord_5710275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710275).length < 2 ^ (prefixWord ++ tailWord_5710275).sum := by decide
  have hdescent : baseEnd_5710275 < baseStart_5710275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710289 : List Nat := [1, 2, 2, 1, 2, 1, 1, 6, 3, 2, 2]
def baseStart_5710289 : Nat := 118140960795 + 5710289 * 2 ^ 59
def prefixEnd_5710289 : Nat := 4983230072969 + 3 ^ 40 * 5710289 * 2
def baseEnd_5710289 : Nat := 2932122933081914201726365

theorem tailTrace_5710289 : CollatzResearch.WordTrace tailWord_5710289 prefixEnd_5710289 2932122933081914201726365 := by
  unfold tailWord_5710289
  simp only [CollatzResearch.WordTrace]
  refine ⟨208271350009605667563509921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138847566673070445042339947 208271350009605667563509921)
  ·
    refine ⟨156203512507204250672632441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208271350009605667563509921 156203512507204250672632441)
    ·
      refine ⟨117152634380403188004474331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156203512507204250672632441 117152634380403188004474331)
      ·
        refine ⟨175728951570604782006711497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117152634380403188004474331 175728951570604782006711497)
        ·
          refine ⟨131796713677953586505033623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175728951570604782006711497 131796713677953586505033623)
          ·
            refine ⟨197695070516930379757550435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131796713677953586505033623 197695070516930379757550435)
            ·
              refine ⟨296542605775395569636325653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197695070516930379757550435 296542605775395569636325653)
              ·
                refine ⟨13900434645721667326702765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 296542605775395569636325653 13900434645721667326702765)
                ·
                  refine ⟨5212662992145625247513537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13900434645721667326702765 5212662992145625247513537)
                  ·
                    refine ⟨3909497244109218935635153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5212662992145625247513537 3909497244109218935635153)
                    ·
                      refine ⟨2932122933081914201726365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3909497244109218935635153 2932122933081914201726365)
                      ·
                        rfl

theorem cell23_5710289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 2, 2].length) (baseStart_5710289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710289 prefixEnd_5710289 := by exact prefixLift 5710289
  have htrace : WordTrace (prefixWord ++ tailWord_5710289) baseStart_5710289 baseEnd_5710289 := by
    simpa [prefixWord, tailWord_5710289, baseEnd_5710289] using wordTrace_append hprefix tailTrace_5710289
  have hstable : (prefixWord ++ tailWord_5710289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710289).length < 2 ^ (prefixWord ++ tailWord_5710289).sum := by decide
  have hdescent : baseEnd_5710289 < baseStart_5710289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710339 : List Nat := [1, 1, 1, 3, 2, 1, 3, 5, 2, 1, 3]
def baseStart_5710339 : Nat := 118140960795 + 5710339 * 2 ^ 59
def prefixEnd_5710339 : Nat := 4983230072969 + 3 ^ 40 * 5710339 * 2
def baseEnd_5710339 : Nat := 2932148607114639006101135

theorem tailTrace_5710339 : CollatzResearch.WordTrace tailWord_5710339 prefixEnd_5710339 2932148607114639006101135 := by
  unfold tailWord_5710339
  simp only [CollatzResearch.WordTrace]
  refine ⟨208273173659424526102830071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138848782439616350735220047 208273173659424526102830071)
  ·
    refine ⟨312409760489136789154245107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208273173659424526102830071 312409760489136789154245107)
    ·
      refine ⟨468614640733705183731367661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312409760489136789154245107 468614640733705183731367661)
      ·
        refine ⟨175730490275139443899262873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 468614640733705183731367661 175730490275139443899262873)
        ·
          refine ⟨131797867706354582924447155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175730490275139443899262873 131797867706354582924447155)
          ·
            refine ⟨197696801559531874386670733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131797867706354582924447155 197696801559531874386670733)
            ·
              refine ⟨74136300584824452895001525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197696801559531874386670733 74136300584824452895001525)
              ·
                refine ⟨6950278179827292458906393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74136300584824452895001525 6950278179827292458906393)
                ·
                  refine ⟨5212708634870469344179795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6950278179827292458906393 5212708634870469344179795)
                  ·
                    refine ⟨7819062952305704016269693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5212708634870469344179795 7819062952305704016269693)
                    ·
                      refine ⟨2932148607114639006101135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7819062952305704016269693 2932148607114639006101135)
                      ·
                        rfl

theorem cell23_5710339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 1, 3].length) (baseStart_5710339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710339 prefixEnd_5710339 := by exact prefixLift 5710339
  have htrace : WordTrace (prefixWord ++ tailWord_5710339) baseStart_5710339 baseEnd_5710339 := by
    simpa [prefixWord, tailWord_5710339, baseEnd_5710339] using wordTrace_append hprefix tailTrace_5710339
  have hstable : (prefixWord ++ tailWord_5710339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710339).length < 2 ^ (prefixWord ++ tailWord_5710339).sum := by decide
  have hdescent : baseEnd_5710339 < baseStart_5710339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710355 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 1, 8]
def baseStart_5710355 : Nat := 118140960795 + 5710355 * 2 ^ 59
def prefixEnd_5710355 : Nat := 4983230072969 + 3 ^ 40 * 5710355 * 2
def baseEnd_5710355 : Nat := 977385607601703647833687

theorem tailTrace_5710355 : CollatzResearch.WordTrace tailWord_5710355 prefixEnd_5710355 977385607601703647833687 := by
  unfold tailWord_5710355
  simp only [CollatzResearch.WordTrace]
  refine ⟨208273757227366560835412519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138849171484911040556941679 208273757227366560835412519)
  ·
    refine ⟨312410635841049841253118779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208273757227366560835412519 312410635841049841253118779)
    ·
      refine ⟨468615953761574761879678169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312410635841049841253118779 468615953761574761879678169)
      ·
        refine ⟨351461965321181071409758627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 468615953761574761879678169 351461965321181071409758627)
        ·
          refine ⟨527192947981771607114637941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351461965321181071409758627 527192947981771607114637941)
          ·
            refine ⟨49424338873291088166997307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 527192947981771607114637941 49424338873291088166997307)
            ·
              refine ⟨74136508309936632250495961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49424338873291088166997307 74136508309936632250495961)
              ·
                refine ⟨55602381232452474187871971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74136508309936632250495961 55602381232452474187871971)
                ·
                  refine ⟨83403571848678711281807957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55602381232452474187871971 83403571848678711281807957)
                  ·
                    refine ⟨977385607601703647833687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83403571848678711281807957 977385607601703647833687)
                    ·
                      rfl

theorem cell23_5710355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 8].length) (baseStart_5710355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710355 prefixEnd_5710355 := by exact prefixLift 5710355
  have htrace : WordTrace (prefixWord ++ tailWord_5710355) baseStart_5710355 baseEnd_5710355 := by
    simpa [prefixWord, tailWord_5710355, baseEnd_5710355] using wordTrace_append hprefix tailTrace_5710355
  have hstable : (prefixWord ++ tailWord_5710355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710355).length < 2 ^ (prefixWord ++ tailWord_5710355).sum := by decide
  have hdescent : baseEnd_5710355 < baseStart_5710355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710356 : List Nat := [2, 4, 3, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_5710356 : Nat := 118140960795 + 5710356 * 2 ^ 59
def prefixEnd_5710356 : Nat := 4983230072969 + 3 ^ 40 * 5710356 * 2
def baseEnd_5710356 : Nat := 2932157336285765439588557

theorem tailTrace_5710356 : CollatzResearch.WordTrace tailWord_5710356 prefixEnd_5710356 2932157336285765439588557 := by
  unfold tailWord_5710356
  simp only [CollatzResearch.WordTrace]
  refine ⟨104136896850181469003099461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138849195800241958670799281 104136896850181469003099461)
  ·
    refine ⟨19525668159409025438081149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104136896850181469003099461 19525668159409025438081149)
    ·
      refine ⟨7322125559778384539280431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19525668159409025438081149 7322125559778384539280431)
      ·
        refine ⟨10983188339667576808920647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7322125559778384539280431 10983188339667576808920647)
        ·
          refine ⟨16474782509501365213380971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10983188339667576808920647 16474782509501365213380971)
          ·
            refine ⟨24712173764252047820071457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16474782509501365213380971 24712173764252047820071457)
            ·
              refine ⟨18534130323189035865053593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24712173764252047820071457 18534130323189035865053593)
              ·
                refine ⟨13900597742391776898790195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18534130323189035865053593 13900597742391776898790195)
                ·
                  refine ⟨20850896613587665348185293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13900597742391776898790195 20850896613587665348185293)
                  ·
                    refine ⟨7819086230095374505569485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20850896613587665348185293 7819086230095374505569485)
                    ·
                      refine ⟨2932157336285765439588557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7819086230095374505569485 2932157336285765439588557)
                      ·
                        rfl

theorem cell23_5710356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_5710356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710356 prefixEnd_5710356 := by exact prefixLift 5710356
  have htrace : WordTrace (prefixWord ++ tailWord_5710356) baseStart_5710356 baseEnd_5710356 := by
    simpa [prefixWord, tailWord_5710356, baseEnd_5710356] using wordTrace_append hprefix tailTrace_5710356
  have hstable : (prefixWord ++ tailWord_5710356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710356).length < 2 ^ (prefixWord ++ tailWord_5710356).sum := by decide
  have hdescent : baseEnd_5710356 < baseStart_5710356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710390 : List Nat := [5, 1, 2, 1, 2, 2, 3, 1, 2, 1, 3]
def baseStart_5710390 : Nat := 118140960795 + 5710390 * 2 ^ 59
def prefixEnd_5710390 : Nat := 4983230072969 + 3 ^ 40 * 5710390 * 2
def baseEnd_5710390 : Nat := 2932174794628018306563401

theorem tailTrace_5710390 : CollatzResearch.WordTrace tailWord_5710390 prefixEnd_5710390 2932174794628018306563401 := by
  unfold tailWord_5710390
  simp only [CollatzResearch.WordTrace]
  refine ⟨13017189611389985113308539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138850022521493174541957749 13017189611389985113308539)
  ·
    refine ⟨19525784417084977669962809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13017189611389985113308539 19525784417084977669962809)
    ·
      refine ⟨14644338312813733252472107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19525784417084977669962809 14644338312813733252472107)
      ·
        refine ⟨21966507469220599878708161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14644338312813733252472107 21966507469220599878708161)
        ·
          refine ⟨16474880601915449909031121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21966507469220599878708161 16474880601915449909031121)
          ·
            refine ⟨12356160451436587431773341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16474880601915449909031121 12356160451436587431773341)
            ·
              refine ⟨4633560169288720286915003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12356160451436587431773341 4633560169288720286915003)
              ·
                refine ⟨6950340253933080430372505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4633560169288720286915003 6950340253933080430372505)
                ·
                  refine ⟨5212755190449810322779379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6950340253933080430372505 5212755190449810322779379)
                  ·
                    refine ⟨7819132785674715484169069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5212755190449810322779379 7819132785674715484169069)
                    ·
                      refine ⟨2932174794628018306563401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7819132785674715484169069 2932174794628018306563401)
                      ·
                        rfl

theorem cell23_5710390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_5710390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710390 prefixEnd_5710390 := by exact prefixLift 5710390
  have htrace : WordTrace (prefixWord ++ tailWord_5710390) baseStart_5710390 baseEnd_5710390 := by
    simpa [prefixWord, tailWord_5710390, baseEnd_5710390] using wordTrace_append hprefix tailTrace_5710390
  have hstable : (prefixWord ++ tailWord_5710390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710390).length < 2 ^ (prefixWord ++ tailWord_5710390).sum := by decide
  have hdescent : baseEnd_5710390 < baseStart_5710390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710392 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 2, 2, 4]
def baseStart_5710392 : Nat := 118140960795 + 5710392 * 2 ^ 59
def prefixEnd_5710392 : Nat := 4983230072969 + 3 ^ 40 * 5710392 * 2
def baseEnd_5710392 : Nat := 2932175821589327298738391

theorem tailTrace_5710392 : CollatzResearch.WordTrace tailWord_5710392 prefixEnd_5710392 2932175821589327298738391 := by
  unfold tailWord_5710392
  simp only [CollatzResearch.WordTrace]
  refine ⟨104137553364116258077254715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138850071152155010769672953 104137553364116258077254715)
  ·
    refine ⟨156206330046174387115882073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104137553364116258077254715 156206330046174387115882073)
    ·
      refine ⟨117154747534630790336911555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156206330046174387115882073 117154747534630790336911555)
      ·
        refine ⟨175732121301946185505367333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117154747534630790336911555 175732121301946185505367333)
        ·
          refine ⟨32949772744114909782256375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175732121301946185505367333 32949772744114909782256375)
          ·
            refine ⟨49424659116172364673384563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32949772744114909782256375 49424659116172364673384563)
            ·
              refine ⟨74136988674258547010076845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49424659116172364673384563 74136988674258547010076845)
              ·
                refine ⟨27801370752846955128778817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74136988674258547010076845 27801370752846955128778817)
                ·
                  refine ⟨20851028064635216346584113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27801370752846955128778817 20851028064635216346584113)
                  ·
                    refine ⟨15638271048476412259938085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20851028064635216346584113 15638271048476412259938085)
                    ·
                      refine ⟨2932175821589327298738391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15638271048476412259938085 2932175821589327298738391)
                      ·
                        rfl

theorem cell23_5710392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_5710392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710392 prefixEnd_5710392 := by exact prefixLift 5710392
  have htrace : WordTrace (prefixWord ++ tailWord_5710392) baseStart_5710392 baseEnd_5710392 := by
    simpa [prefixWord, tailWord_5710392, baseEnd_5710392] using wordTrace_append hprefix tailTrace_5710392
  have hstable : (prefixWord ++ tailWord_5710392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710392).length < 2 ^ (prefixWord ++ tailWord_5710392).sum := by decide
  have hdescent : baseEnd_5710392 < baseStart_5710392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710396 : List Nat := [2, 2, 2, 2, 3, 1, 3, 1, 1, 4, 2]
def baseStart_5710396 : Nat := 118140960795 + 5710396 * 2 ^ 59
def prefixEnd_5710396 : Nat := 4983230072969 + 3 ^ 40 * 5710396 * 2
def baseEnd_5710396 : Nat := 2932177875511945283088373

theorem tailTrace_5710396 : CollatzResearch.WordTrace tailWord_5710396 prefixEnd_5710396 2932177875511945283088373 := by
  unfold tailWord_5710396
  simp only [CollatzResearch.WordTrace]
  refine ⟨104137626310109012418827521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138850168413478683225103361 104137626310109012418827521)
  ·
    refine ⟨78103219732581759314120641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104137626310109012418827521 78103219732581759314120641)
    ·
      refine ⟨58577414799436319485590481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78103219732581759314120641 58577414799436319485590481)
      ·
        refine ⟨43933061099577239614192861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58577414799436319485590481 43933061099577239614192861)
        ·
          refine ⟨16474897912341464855322323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43933061099577239614192861 16474897912341464855322323)
          ·
            refine ⟨24712346868512197282983485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16474897912341464855322323 24712346868512197282983485)
            ·
              refine ⟨9267130075692073981118807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24712346868512197282983485 9267130075692073981118807)
              ·
                refine ⟨13900695113538110971678211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9267130075692073981118807 13900695113538110971678211)
                ·
                  refine ⟨20851042670307166457517317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13900695113538110971678211 20851042670307166457517317)
                  ·
                    refine ⟨3909570500682593710784497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20851042670307166457517317 3909570500682593710784497)
                    ·
                      refine ⟨2932177875511945283088373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3909570500682593710784497 2932177875511945283088373)
                      ·
                        rfl

theorem cell23_5710396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_5710396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710396 prefixEnd_5710396 := by exact prefixLift 5710396
  have htrace : WordTrace (prefixWord ++ tailWord_5710396) baseStart_5710396 baseEnd_5710396 := by
    simpa [prefixWord, tailWord_5710396, baseEnd_5710396] using wordTrace_append hprefix tailTrace_5710396
  have hstable : (prefixWord ++ tailWord_5710396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710396).length < 2 ^ (prefixWord ++ tailWord_5710396).sum := by decide
  have hdescent : baseEnd_5710396 < baseStart_5710396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710413 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 4, 2, 2]
def baseStart_5710413 : Nat := 118140960795 + 5710413 * 2 ^ 59
def prefixEnd_5710413 : Nat := 4983230072969 + 3 ^ 40 * 5710413 * 2
def baseEnd_5710413 : Nat := 2932186604683071716575795

theorem tailTrace_5710413 : CollatzResearch.WordTrace tailWord_5710413 prefixEnd_5710413 2932186604683071716575795 := by
  unfold tailWord_5710413
  simp only [CollatzResearch.WordTrace]
  refine ⟨208275872661156436741023893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138850581774104291160682595 208275872661156436741023893)
  ·
    refine ⟨9762931530991707972235495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 208275872661156436741023893 9762931530991707972235495)
    ·
      refine ⟨14644397296487561958353243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9762931530991707972235495 14644397296487561958353243)
      ·
        refine ⟨21966595944731342937529865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14644397296487561958353243 21966595944731342937529865)
        ·
          refine ⟨16474946958548507203147399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21966595944731342937529865 16474946958548507203147399)
          ·
            refine ⟨24712420437822760804721099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16474946958548507203147399 24712420437822760804721099)
            ·
              refine ⟨37068630656734141207081649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24712420437822760804721099 37068630656734141207081649)
              ·
                refine ⟨27801472992550605905311237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37068630656734141207081649 27801472992550605905311237)
                ·
                  refine ⟨5212776186103238607245857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27801472992550605905311237 5212776186103238607245857)
                  ·
                    refine ⟨3909582139577428955434393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5212776186103238607245857 3909582139577428955434393)
                    ·
                      refine ⟨2932186604683071716575795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3909582139577428955434393 2932186604683071716575795)
                      ·
                        rfl

theorem cell23_5710413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_5710413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710413 prefixEnd_5710413 := by exact prefixLift 5710413
  have htrace : WordTrace (prefixWord ++ tailWord_5710413) baseStart_5710413 baseEnd_5710413 := by
    simpa [prefixWord, tailWord_5710413, baseEnd_5710413] using wordTrace_append hprefix tailTrace_5710413
  have hstable : (prefixWord ++ tailWord_5710413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710413).length < 2 ^ (prefixWord ++ tailWord_5710413).sum := by decide
  have hdescent : baseEnd_5710413 < baseStart_5710413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710432 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 4, 5]
def baseStart_5710432 : Nat := 118140960795 + 5710432 * 2 ^ 59
def prefixEnd_5710432 : Nat := 4983230072969 + 3 ^ 40 * 5710432 * 2
def baseEnd_5710432 : Nat := 977398786938502380746069

theorem tailTrace_5710432 : CollatzResearch.WordTrace tailWord_5710432 prefixEnd_5710432 977398786938502380746069 := by
  unfold tailWord_5710432
  simp only [CollatzResearch.WordTrace]
  refine ⟨104138282824043801492982775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138851043765391735323977033 104138282824043801492982775)
  ·
    refine ⟨156207424236065702239474163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104138282824043801492982775 156207424236065702239474163)
    ·
      refine ⟨234311136354098553359211245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156207424236065702239474163 234311136354098553359211245)
      ·
        refine ⟨87866676132786957509704217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234311136354098553359211245 87866676132786957509704217)
        ·
          refine ⟨65900007099590218132278163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87866676132786957509704217 65900007099590218132278163)
          ·
            refine ⟨98850010649385327198417245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65900007099590218132278163 98850010649385327198417245)
            ·
              refine ⟨37068753993519497699406467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98850010649385327198417245 37068753993519497699406467)
              ·
                refine ⟨55603130990279246549109701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37068753993519497699406467 55603130990279246549109701)
                ·
                  refine ⟨10425587060677358727958069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55603130990279246549109701 10425587060677358727958069)
                  ·
                    refine ⟨977398786938502380746069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10425587060677358727958069 977398786938502380746069)
                    ·
                      rfl

theorem cell23_5710432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 4, 5].length) (baseStart_5710432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710432 prefixEnd_5710432 := by exact prefixLift 5710432
  have htrace : WordTrace (prefixWord ++ tailWord_5710432) baseStart_5710432 baseEnd_5710432 := by
    simpa [prefixWord, tailWord_5710432, baseEnd_5710432] using wordTrace_append hprefix tailTrace_5710432
  have hstable : (prefixWord ++ tailWord_5710432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710432).length < 2 ^ (prefixWord ++ tailWord_5710432).sum := by decide
  have hdescent : baseEnd_5710432 < baseStart_5710432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710436 : List Nat := [2, 3, 1, 1, 2, 2, 5, 2, 5]
def baseStart_5710436 : Nat := 118140960795 + 5710436 * 2 ^ 59
def prefixEnd_5710436 : Nat := 4983230072969 + 3 ^ 40 * 5710436 * 2
def baseEnd_5710436 : Nat := 325799823859791680732021

theorem tailTrace_5710436 : CollatzResearch.WordTrace tailWord_5710436 prefixEnd_5710436 325799823859791680732021 := by
  unfold tailWord_5710436
  simp only [CollatzResearch.WordTrace]
  refine ⟨104138355770036555834555581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138851141026715407779407441 104138355770036555834555581)
  ·
    refine ⟨39051883413763708437958343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104138355770036555834555581 39051883413763708437958343)
    ·
      refine ⟨58577825120645562656937515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39051883413763708437958343 58577825120645562656937515)
      ·
        refine ⟨87866737680968343985406273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58577825120645562656937515 87866737680968343985406273)
        ·
          refine ⟨65900053260726257989054705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87866737680968343985406273 65900053260726257989054705)
          ·
            refine ⟨49425039945544693491791029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65900053260726257989054705 49425039945544693491791029)
            ·
              refine ⟨4633597494894815014855409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49425039945544693491791029 4633597494894815014855409)
              ·
                refine ⟨3475198121171111261141557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4633597494894815014855409 3475198121171111261141557)
                ·
                  refine ⟨325799823859791680732021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3475198121171111261141557 325799823859791680732021)
                  ·
                    rfl

theorem cell23_5710436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_5710436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710436 prefixEnd_5710436 := by exact prefixLift 5710436
  have htrace : WordTrace (prefixWord ++ tailWord_5710436) baseStart_5710436 baseEnd_5710436 := by
    simpa [prefixWord, tailWord_5710436, baseEnd_5710436] using wordTrace_append hprefix tailTrace_5710436
  have hstable : (prefixWord ++ tailWord_5710436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710436).length < 2 ^ (prefixWord ++ tailWord_5710436).sum := by decide
  have hdescent : baseEnd_5710436 < baseStart_5710436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710439 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 2, 5, 2]
def baseStart_5710439 : Nat := 118140960795 + 5710439 * 2 ^ 59
def prefixEnd_5710439 : Nat := 4983230072969 + 3 ^ 40 * 5710439 * 2
def baseEnd_5710439 : Nat := 2932199955180088614850675

theorem tailTrace_5710439 : CollatzResearch.WordTrace tailWord_5710439 prefixEnd_5710439 2932199955180088614850675 := by
  unfold tailWord_5710439
  simp only [CollatzResearch.WordTrace]
  refine ⟨208276820959062243181470371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138851213972708162120980247 208276820959062243181470371)
  ·
    refine ⟨312415231438593364772205557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208276820959062243181470371 312415231438593364772205557)
    ·
      refine ⟨29288927947368127947394271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 312415231438593364772205557 29288927947368127947394271)
      ·
        refine ⟨43933391921052191921091407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29288927947368127947394271 43933391921052191921091407)
        ·
          refine ⟨65900087881578287881637111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43933391921052191921091407 65900087881578287881637111)
          ·
            refine ⟨98850131822367431822455667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65900087881578287881637111 98850131822367431822455667)
            ·
              refine ⟨148275197733551147733683501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98850131822367431822455667 148275197733551147733683501)
              ·
                refine ⟨55603199150081680400131313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148275197733551147733683501 55603199150081680400131313)
                ·
                  refine ⟨41702399362561260300098485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55603199150081680400131313 41702399362561260300098485)
                  ·
                    refine ⟨3909599940240118153134233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41702399362561260300098485 3909599940240118153134233)
                    ·
                      refine ⟨2932199955180088614850675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3909599940240118153134233 2932199955180088614850675)
                      ·
                        rfl

theorem cell23_5710439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_5710439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710439 prefixEnd_5710439 := by exact prefixLift 5710439
  have htrace : WordTrace (prefixWord ++ tailWord_5710439) baseStart_5710439 baseEnd_5710439 := by
    simpa [prefixWord, tailWord_5710439, baseEnd_5710439] using wordTrace_append hprefix tailTrace_5710439
  have hstable : (prefixWord ++ tailWord_5710439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710439).length < 2 ^ (prefixWord ++ tailWord_5710439).sum := by decide
  have hdescent : baseEnd_5710439 < baseStart_5710439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710469 : List Nat := [1, 3, 1, 1, 4, 2, 1, 3, 2, 1, 4]
def baseStart_5710469 : Nat := 118140960795 + 5710469 * 2 ^ 59
def prefixEnd_5710469 : Nat := 4983230072969 + 3 ^ 40 * 5710469 * 2
def baseEnd_5710469 : Nat := 2932215359599723497475537

theorem tailTrace_5710469 : CollatzResearch.WordTrace tailWord_5710469 prefixEnd_5710469 2932215359599723497475537 := by
  unfold tailWord_5710469
  simp only [CollatzResearch.WordTrace]
  refine ⟨208277915148953558305062461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138851943432635705536708307 208277915148953558305062461)
  ·
    refine ⟨78104218180857584364398423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208277915148953558305062461 78104218180857584364398423)
    ·
      refine ⟨117156327271286376546597635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78104218180857584364398423 117156327271286376546597635)
      ·
        refine ⟨175734490906929564819896453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117156327271286376546597635 175734490906929564819896453)
        ·
          refine ⟨32950217045049293403730585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175734490906929564819896453 32950217045049293403730585)
          ·
            refine ⟨24712662783786970052797939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32950217045049293403730585 24712662783786970052797939)
            ·
              refine ⟨37068994175680455079196909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24712662783786970052797939 37068994175680455079196909)
              ·
                refine ⟨13900872815880170654698841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37068994175680455079196909 13900872815880170654698841)
                ·
                  refine ⟨10425654611910127991024131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13900872815880170654698841 10425654611910127991024131)
                  ·
                    refine ⟨15638481917865191986536197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10425654611910127991024131 15638481917865191986536197)
                    ·
                      refine ⟨2932215359599723497475537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15638481917865191986536197 2932215359599723497475537)
                      ·
                        rfl

theorem cell23_5710469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_5710469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710469 prefixEnd_5710469 := by exact prefixLift 5710469
  have htrace : WordTrace (prefixWord ++ tailWord_5710469) baseStart_5710469 baseEnd_5710469 := by
    simpa [prefixWord, tailWord_5710469, baseEnd_5710469] using wordTrace_append hprefix tailTrace_5710469
  have hstable : (prefixWord ++ tailWord_5710469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710469).length < 2 ^ (prefixWord ++ tailWord_5710469).sum := by decide
  have hdescent : baseEnd_5710469 < baseStart_5710469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710489 : List Nat := [1, 2, 1, 2, 1, 2, 3, 4, 2, 2, 3]
def baseStart_5710489 : Nat := 118140960795 + 5710489 * 2 ^ 59
def prefixEnd_5710489 : Nat := 4983230072969 + 3 ^ 40 * 5710489 * 2
def baseEnd_5710489 : Nat := 2932225629212813419225445

theorem tailTrace_5710489 : CollatzResearch.WordTrace tailWord_5710489 prefixEnd_5710489 2932225629212813419225445 := by
  unfold tailWord_5710489
  simp only [CollatzResearch.WordTrace]
  refine ⟨208278644608881101720790521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138852429739254067813860347 208278644608881101720790521)
  ·
    refine ⟨156208983456660826290592891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208278644608881101720790521 156208983456660826290592891)
    ·
      refine ⟨234313475184991239435889337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156208983456660826290592891 234313475184991239435889337)
      ·
        refine ⟨175735106388743429576917003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234313475184991239435889337 175735106388743429576917003)
        ·
          refine ⟨263602659583115144365375505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175735106388743429576917003 263602659583115144365375505)
          ·
            refine ⟨197701994687336358274031629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263602659583115144365375505 197701994687336358274031629)
            ·
              refine ⟨74138248007751134352761861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197701994687336358274031629 74138248007751134352761861)
              ·
                refine ⟨13900921501453337691142849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74138248007751134352761861 13900921501453337691142849)
                ·
                  refine ⟨10425691126090003268357137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13900921501453337691142849 10425691126090003268357137)
                  ·
                    refine ⟨7819268344567502451267853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10425691126090003268357137 7819268344567502451267853)
                    ·
                      refine ⟨2932225629212813419225445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7819268344567502451267853 2932225629212813419225445)
                      ·
                        rfl

theorem cell23_5710489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 2, 3].length) (baseStart_5710489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710489 prefixEnd_5710489 := by exact prefixLift 5710489
  have htrace : WordTrace (prefixWord ++ tailWord_5710489) baseStart_5710489 baseEnd_5710489 := by
    simpa [prefixWord, tailWord_5710489, baseEnd_5710489] using wordTrace_append hprefix tailTrace_5710489
  have hstable : (prefixWord ++ tailWord_5710489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710489).length < 2 ^ (prefixWord ++ tailWord_5710489).sum := by decide
  have hdescent : baseEnd_5710489 < baseStart_5710489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710513 : List Nat := [1, 2, 2, 6, 1, 1, 1, 2, 3, 4]
def baseStart_5710513 : Nat := 118140960795 + 5710513 * 2 ^ 59
def prefixEnd_5710513 : Nat := 4983230072969 + 3 ^ 40 * 5710513 * 2
def baseEnd_5710513 : Nat := 977412650916173775108445

theorem tailTrace_5710513 : CollatzResearch.WordTrace tailWord_5710513 prefixEnd_5710513 977412650916173775108445 := by
  unfold tailWord_5710513
  simp only [CollatzResearch.WordTrace]
  refine ⟨208279519960794153819664193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138853013307196102546442795 208279519960794153819664193)
  ·
    refine ⟨156209639970595615364748145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208279519960794153819664193 156209639970595615364748145)
    ·
      refine ⟨117157229977946711523561109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156209639970595615364748145 117157229977946711523561109)
      ·
        refine ⟨5491745155216252102666927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 117157229977946711523561109 5491745155216252102666927)
        ·
          refine ⟨8237617732824378154000391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5491745155216252102666927 8237617732824378154000391)
          ·
            refine ⟨12356426599236567231000587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8237617732824378154000391 12356426599236567231000587)
            ·
              refine ⟨18534639898854850846500881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12356426599236567231000587 18534639898854850846500881)
              ·
                refine ⟨13900979924141138134875661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18534639898854850846500881 13900979924141138134875661)
                ·
                  refine ⟨5212867471552926800578373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13900979924141138134875661 5212867471552926800578373)
                  ·
                    refine ⟨977412650916173775108445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5212867471552926800578373 977412650916173775108445)
                    ·
                      rfl

theorem cell23_5710513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 4].length) (baseStart_5710513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710513 prefixEnd_5710513 := by exact prefixLift 5710513
  have htrace : WordTrace (prefixWord ++ tailWord_5710513) baseStart_5710513 baseEnd_5710513 := by
    simpa [prefixWord, tailWord_5710513, baseEnd_5710513] using wordTrace_append hprefix tailTrace_5710513
  have hstable : (prefixWord ++ tailWord_5710513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710513).length < 2 ^ (prefixWord ++ tailWord_5710513).sum := by decide
  have hdescent : baseEnd_5710513 < baseStart_5710513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710553 : List Nat := [1, 2, 1, 2, 3, 2, 1, 6, 1, 1, 3]
def baseStart_5710553 : Nat := 118140960795 + 5710553 * 2 ^ 59
def prefixEnd_5710553 : Nat := 4983230072969 + 3 ^ 40 * 5710553 * 2
def baseEnd_5710553 : Nat := 2932258491974701168825151

theorem tailTrace_5710553 : CollatzResearch.WordTrace tailWord_5710553 prefixEnd_5710553 2932258491974701168825151 := by
  unfold tailWord_5710553
  simp only [CollatzResearch.WordTrace]
  refine ⟨208280978880649240651120313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138853985920432827100746875 208280978880649240651120313)
  ·
    refine ⟨156210734160486930488340235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208280978880649240651120313 156210734160486930488340235)
    ·
      refine ⟨234316101240730395732510353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156210734160486930488340235 234316101240730395732510353)
      ·
        refine ⟨175737075930547796799382765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234316101240730395732510353 175737075930547796799382765)
        ·
          refine ⟨65901403473955423799768537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175737075930547796799382765 65901403473955423799768537)
          ·
            refine ⟨49426052605466567849826403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65901403473955423799768537 49426052605466567849826403)
            ·
              refine ⟨74139078908199851774739605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49426052605466567849826403 74139078908199851774739605)
              ·
                refine ⟨3475269323821868051940919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74139078908199851774739605 3475269323821868051940919)
                ·
                  refine ⟨5212903985732802077911379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3475269323821868051940919 5212903985732802077911379)
                  ·
                    refine ⟨7819355978599203116867069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5212903985732802077911379 7819355978599203116867069)
                    ·
                      refine ⟨2932258491974701168825151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7819355978599203116867069 2932258491974701168825151)
                      ·
                        rfl

theorem cell23_5710553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 1, 1, 3].length) (baseStart_5710553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710553 prefixEnd_5710553 := by exact prefixLift 5710553
  have htrace : WordTrace (prefixWord ++ tailWord_5710553) baseStart_5710553 baseEnd_5710553 := by
    simpa [prefixWord, tailWord_5710553, baseEnd_5710553] using wordTrace_append hprefix tailTrace_5710553
  have hstable : (prefixWord ++ tailWord_5710553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710553).length < 2 ^ (prefixWord ++ tailWord_5710553).sum := by decide
  have hdescent : baseEnd_5710553 < baseStart_5710553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710569 : List Nat := [1, 2, 1, 1, 1, 2, 7, 1, 1, 6]
def baseStart_5710569 : Nat := 118140960795 + 5710569 * 2 ^ 59
def prefixEnd_5710569 : Nat := 4983230072969 + 3 ^ 40 * 5710569 * 2
def baseEnd_5710569 : Nat := 977422235888391035408359

theorem tailTrace_5710569 : CollatzResearch.WordTrace tailWord_5710569 prefixEnd_5710569 977422235888391035408359 := by
  unfold tailWord_5710569
  simp only [CollatzResearch.WordTrace]
  refine ⟨208281562448591275383702761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138854374965727516922468507 208281562448591275383702761)
  ·
    refine ⟨156211171836443456537777071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208281562448591275383702761 156211171836443456537777071)
    ·
      refine ⟨234316757754665184806665607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156211171836443456537777071 234316757754665184806665607)
      ·
        refine ⟨351475136631997777209998411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234316757754665184806665607 351475136631997777209998411)
        ·
          refine ⟨527212704947996665814997617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351475136631997777209998411 527212704947996665814997617)
          ·
            refine ⟨395409528710997499361248213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 527212704947996665814997617 395409528710997499361248213)
            ·
              refine ⟨9267410829164003891279255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 395409528710997499361248213 9267410829164003891279255)
              ·
                refine ⟨13901116243746005836918883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9267410829164003891279255 13901116243746005836918883)
                ·
                  refine ⟨20851674365619008755378325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13901116243746005836918883 20851674365619008755378325)
                  ·
                    refine ⟨977422235888391035408359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20851674365619008755378325 977422235888391035408359)
                    ·
                      rfl

theorem cell23_5710569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 6].length) (baseStart_5710569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710569 prefixEnd_5710569 := by exact prefixLift 5710569
  have htrace : WordTrace (prefixWord ++ tailWord_5710569) baseStart_5710569 baseEnd_5710569 := by
    simpa [prefixWord, tailWord_5710569, baseEnd_5710569] using wordTrace_append hprefix tailTrace_5710569
  have hstable : (prefixWord ++ tailWord_5710569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710569).length < 2 ^ (prefixWord ++ tailWord_5710569).sum := by decide
  have hdescent : baseEnd_5710569 < baseStart_5710569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710576 : List Nat := [2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 4]
def baseStart_5710576 : Nat := 118140960795 + 5710576 * 2 ^ 59
def prefixEnd_5710576 : Nat := 4983230072969 + 3 ^ 40 * 5710576 * 2
def baseEnd_5710576 : Nat := 2932270302029754578837545

theorem tailTrace_5710576 : CollatzResearch.WordTrace tailWord_5710576 prefixEnd_5710576 2932270302029754578837545 := by
  unfold tailWord_5710576
  simp only [CollatzResearch.WordTrace]
  refine ⟨104140908879782957789603791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138854545173043943719471721 104140908879782957789603791)
  ·
    refine ⟨156211363319674436684405687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104140908879782957789603791 156211363319674436684405687)
    ·
      refine ⟨234317044979511655026608531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156211363319674436684405687 234317044979511655026608531)
      ·
        refine ⟨351475567469267482539912797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234317044979511655026608531 351475567469267482539912797)
        ·
          refine ⟨131803337800975305952467299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 351475567469267482539912797 131803337800975305952467299)
          ·
            refine ⟨197705006701462958928700949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131803337800975305952467299 197705006701462958928700949)
            ·
              refine ⟨9267422189131076199782857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 197705006701462958928700949 9267422189131076199782857)
              ·
                refine ⟨6950566641848307149837143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9267422189131076199782857 6950566641848307149837143)
                ·
                  refine ⟨10425849962772460724755715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6950566641848307149837143 10425849962772460724755715)
                  ·
                    refine ⟨15638774944158691087133573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10425849962772460724755715 15638774944158691087133573)
                    ·
                      refine ⟨2932270302029754578837545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15638774944158691087133573 2932270302029754578837545)
                      ·
                        rfl

theorem cell23_5710576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 4].length) (baseStart_5710576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710576 prefixEnd_5710576 := by exact prefixLift 5710576
  have htrace : WordTrace (prefixWord ++ tailWord_5710576) baseStart_5710576 baseEnd_5710576 := by
    simpa [prefixWord, tailWord_5710576, baseEnd_5710576] using wordTrace_append hprefix tailTrace_5710576
  have hstable : (prefixWord ++ tailWord_5710576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710576).length < 2 ^ (prefixWord ++ tailWord_5710576).sum := by decide
  have hdescent : baseEnd_5710576 < baseStart_5710576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710581 : List Nat := [1, 3, 6, 1, 2, 1, 1, 3, 1, 4]
def baseStart_5710581 : Nat := 118140960795 + 5710581 * 2 ^ 59
def prefixEnd_5710581 : Nat := 4983230072969 + 3 ^ 40 * 5710581 * 2
def baseEnd_5710581 : Nat := 977424289811009019758341

theorem tailTrace_5710581 : CollatzResearch.WordTrace tailWord_5710581 prefixEnd_5710581 977424289811009019758341 := by
  unfold tailWord_5710581
  simp only [CollatzResearch.WordTrace]
  refine ⟨208282000124547801433139597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138854666749698534288759731 208282000124547801433139597)
  ·
    refine ⟨78105750046705425537427349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208282000124547801433139597 78105750046705425537427349)
    ·
      refine ⟨3661207033439316822066907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 78105750046705425537427349 3661207033439316822066907)
      ·
        refine ⟨5491810550158975233100361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3661207033439316822066907 5491810550158975233100361)
        ·
          refine ⟨4118857912619231424825271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5491810550158975233100361 4118857912619231424825271)
          ·
            refine ⟨6178286868928847137237907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4118857912619231424825271 6178286868928847137237907)
            ·
              refine ⟨9267430303393270705856861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6178286868928847137237907 9267430303393270705856861)
              ·
                refine ⟨3475286363772476514696323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9267430303393270705856861 3475286363772476514696323)
                ·
                  refine ⟨5212929545658714772044485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3475286363772476514696323 5212929545658714772044485)
                  ·
                    refine ⟨977424289811009019758341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5212929545658714772044485 977424289811009019758341)
                    ·
                      rfl

theorem cell23_5710581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_5710581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710581 prefixEnd_5710581 := by exact prefixLift 5710581
  have htrace : WordTrace (prefixWord ++ tailWord_5710581) baseStart_5710581 baseEnd_5710581 := by
    simpa [prefixWord, tailWord_5710581, baseEnd_5710581] using wordTrace_append hprefix tailTrace_5710581
  have hstable : (prefixWord ++ tailWord_5710581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710581).length < 2 ^ (prefixWord ++ tailWord_5710581).sum := by decide
  have hdescent : baseEnd_5710581 < baseStart_5710581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710589 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 3, 2, 4]
def baseStart_5710589 : Nat := 118140960795 + 5710589 * 2 ^ 59
def prefixEnd_5710589 : Nat := 4983230072969 + 3 ^ 40 * 5710589 * 2
def baseEnd_5710589 : Nat := 2932276977278263027974985

theorem tailTrace_5710589 : CollatzResearch.WordTrace tailWord_5710589 prefixEnd_5710589 2932276977278263027974985 := by
  unfold tailWord_5710589
  simp only [CollatzResearch.WordTrace]
  refine ⟨208282291908518818799430821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138854861272345879199620547 208282291908518818799430821)
  ·
    refine ⟨39052929732847278524893279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208282291908518818799430821 39052929732847278524893279)
    ·
      refine ⟨58579394599270917787339919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39052929732847278524893279 58579394599270917787339919)
      ·
        refine ⟨87869091898906376681009879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58579394599270917787339919 87869091898906376681009879)
        ·
          refine ⟨131803637848359565021514819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87869091898906376681009879 131803637848359565021514819)
          ·
            refine ⟨197705456772539347532272229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131803637848359565021514819 197705456772539347532272229)
            ·
              refine ⟨37069773144851127662301043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 197705456772539347532272229 37069773144851127662301043)
              ·
                refine ⟨55604659717276691493451565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37069773144851127662301043 55604659717276691493451565)
                ·
                  refine ⟨20851747393978759310044337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55604659717276691493451565 20851747393978759310044337)
                  ·
                    refine ⟨15638810545484069482533253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20851747393978759310044337 15638810545484069482533253)
                    ·
                      refine ⟨2932276977278263027974985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15638810545484069482533253 2932276977278263027974985)
                      ·
                        rfl

theorem cell23_5710589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_5710589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710589 prefixEnd_5710589 := by exact prefixLift 5710589
  have htrace : WordTrace (prefixWord ++ tailWord_5710589) baseStart_5710589 baseEnd_5710589 := by
    simpa [prefixWord, tailWord_5710589, baseEnd_5710589] using wordTrace_append hprefix tailTrace_5710589
  have hstable : (prefixWord ++ tailWord_5710589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710589).length < 2 ^ (prefixWord ++ tailWord_5710589).sum := by decide
  have hdescent : baseEnd_5710589 < baseStart_5710589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710596 : List Nat := [2, 3, 2, 2, 1, 1, 4, 1, 1, 1, 5]
def baseStart_5710596 : Nat := 118140960795 + 5710596 * 2 ^ 59
def prefixEnd_5710596 : Nat := 4983230072969 + 3 ^ 40 * 5710596 * 2
def baseEnd_5710596 : Nat := 2932280571642844500587453

theorem tailTrace_5710596 : CollatzResearch.WordTrace tailWord_5710596 prefixEnd_5710596 2932280571642844500587453 := by
  unfold tailWord_5710596
  simp only [CollatzResearch.WordTrace]
  refine ⟨104141273609746729497467821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138855031479662305996623761 104141273609746729497467821)
  ·
    refine ⟨39052977603655023561550433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104141273609746729497467821 39052977603655023561550433)
    ·
      refine ⟨29289733202741267671162825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39052977603655023561550433 29289733202741267671162825)
      ·
        refine ⟨21967299902055950753372119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29289733202741267671162825 21967299902055950753372119)
        ·
          refine ⟨32950949853083926130058179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21967299902055950753372119 32950949853083926130058179)
          ·
            refine ⟨49426424779625889195087269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32950949853083926130058179 49426424779625889195087269)
            ·
              refine ⟨9267454646179854224078863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49426424779625889195087269 9267454646179854224078863)
              ·
                refine ⟨13901181969269781336118295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9267454646179854224078863 13901181969269781336118295)
                ·
                  refine ⟨20851772953904672004177443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13901181969269781336118295 20851772953904672004177443)
                  ·
                    refine ⟨31277659430857008006266165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20851772953904672004177443 31277659430857008006266165)
                    ·
                      refine ⟨2932280571642844500587453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31277659430857008006266165 2932280571642844500587453)
                      ·
                        rfl

theorem cell23_5710596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_5710596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710596 prefixEnd_5710596 := by exact prefixLift 5710596
  have htrace : WordTrace (prefixWord ++ tailWord_5710596) baseStart_5710596 baseEnd_5710596 := by
    simpa [prefixWord, tailWord_5710596, baseEnd_5710596] using wordTrace_append hprefix tailTrace_5710596
  have hstable : (prefixWord ++ tailWord_5710596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710596).length < 2 ^ (prefixWord ++ tailWord_5710596).sum := by decide
  have hdescent : baseEnd_5710596 < baseStart_5710596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710599 : List Nat := [1, 1, 4, 4, 1, 1, 11]
def baseStart_5710599 : Nat := 118140960795 + 5710599 * 2 ^ 59
def prefixEnd_5710599 : Nat := 4983230072969 + 3 ^ 40 * 5710599 * 2
def baseEnd_5710599 : Nat := 36201013729442073936419

theorem tailTrace_5710599 : CollatzResearch.WordTrace tailWord_5710599 prefixEnd_5710599 36201013729442073936419 := by
  unfold tailWord_5710599
  simp only [CollatzResearch.WordTrace]
  refine ⟨208282656638482590507294851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138855104425655060338196567 208282656638482590507294851)
  ·
    refine ⟨312423984957723885760942277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208282656638482590507294851 312423984957723885760942277)
    ·
      refine ⟨58579497179573228580176677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 312423984957723885760942277 58579497179573228580176677)
      ·
        refine ⟨10983655721169980358783127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58579497179573228580176677 10983655721169980358783127)
        ·
          refine ⟨16475483581754970538174691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10983655721169980358783127 16475483581754970538174691)
          ·
            refine ⟨24713225372632455807262037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16475483581754970538174691 24713225372632455807262037)
            ·
              refine ⟨36201013729442073936419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24713225372632455807262037 36201013729442073936419)
              ·
                rfl

theorem cell23_5710599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 11].length) (baseStart_5710599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710599 prefixEnd_5710599 := by exact prefixLift 5710599
  have htrace : WordTrace (prefixWord ++ tailWord_5710599) baseStart_5710599 baseEnd_5710599 := by
    simpa [prefixWord, tailWord_5710599, baseEnd_5710599] using wordTrace_append hprefix tailTrace_5710599
  have hstable : (prefixWord ++ tailWord_5710599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710599).length < 2 ^ (prefixWord ++ tailWord_5710599).sum := by decide
  have hdescent : baseEnd_5710599 < baseStart_5710599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710620 : List Nat := [2, 2, 3, 1, 1, 5, 2, 1, 2, 4]
def baseStart_5710620 : Nat := 118140960795 + 5710620 * 2 ^ 59
def prefixEnd_5710620 : Nat := 4983230072969 + 3 ^ 40 * 5710620 * 2
def baseEnd_5710620 : Nat := 977430965059517468895781

theorem tailTrace_5710620 : CollatzResearch.WordTrace tailWord_5710620 prefixEnd_5710620 977430965059517468895781 := by
  unfold tailWord_5710620
  simp only [CollatzResearch.WordTrace]
  refine ⟨104141711285703255546904657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138855615047604340729206209 104141711285703255546904657)
  ·
    refine ⟨78106283464277441660178493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104141711285703255546904657 78106283464277441660178493)
    ·
      refine ⟨29289856299104040622566935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78106283464277441660178493 29289856299104040622566935)
      ·
        refine ⟨43934784448656060933850403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29289856299104040622566935 43934784448656060933850403)
        ·
          refine ⟨65902176672984091400775605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43934784448656060933850403 65902176672984091400775605)
          ·
            refine ⟨6178329063092258568822713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65902176672984091400775605 6178329063092258568822713)
            ·
              refine ⟨4633746797319193926617035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6178329063092258568822713 4633746797319193926617035)
              ·
                refine ⟨6950620195978790889925553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4633746797319193926617035 6950620195978790889925553)
                ·
                  refine ⟨5212965146984093167444165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6950620195978790889925553 5212965146984093167444165)
                  ·
                    refine ⟨977430965059517468895781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5212965146984093167444165 977430965059517468895781)
                    ·
                      rfl

theorem cell23_5710620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_5710620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710620 prefixEnd_5710620 := by exact prefixLift 5710620
  have htrace : WordTrace (prefixWord ++ tailWord_5710620) baseStart_5710620 baseEnd_5710620 := by
    simpa [prefixWord, tailWord_5710620, baseEnd_5710620] using wordTrace_append hprefix tailTrace_5710620
  have hstable : (prefixWord ++ tailWord_5710620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710620).length < 2 ^ (prefixWord ++ tailWord_5710620).sum := by decide
  have hdescent : baseEnd_5710620 < baseStart_5710620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710659 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 2, 6]
def baseStart_5710659 : Nat := 118140960795 + 5710659 * 2 ^ 59
def prefixEnd_5710659 : Nat := 4983230072969 + 3 ^ 40 * 5710659 * 2
def baseEnd_5710659 : Nat := 977437640308025918033221

theorem tailTrace_5710659 : CollatzResearch.WordTrace tailWord_5710659 prefixEnd_5710659 977437640308025918033221 := by
  unfold tailWord_5710659
  simp only [CollatzResearch.WordTrace]
  refine ⟨208284845018265220754479031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138856563345510147169652687 208284845018265220754479031)
  ·
    refine ⟨312427267527397831131718547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208284845018265220754479031 312427267527397831131718547)
    ·
      refine ⟨468640901291096746697577821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312427267527397831131718547 468640901291096746697577821)
      ·
        refine ⟨175740337984161280011591683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 468640901291096746697577821 175740337984161280011591683)
        ·
          refine ⟨263610506976241920017387525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175740337984161280011591683 263610506976241920017387525)
          ·
            refine ⟨49426970058045360003260161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 263610506976241920017387525 49426970058045360003260161)
            ·
              refine ⟨37070227543534020002445121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49426970058045360003260161 37070227543534020002445121)
              ·
                refine ⟨27802670657650515001833841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37070227543534020002445121 27802670657650515001833841)
                ·
                  refine ⟨20852002993237886251375381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27802670657650515001833841 20852002993237886251375381)
                  ·
                    refine ⟨977437640308025918033221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20852002993237886251375381 977437640308025918033221)
                    ·
                      rfl

theorem cell23_5710659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 6].length) (baseStart_5710659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710659 prefixEnd_5710659 := by exact prefixLift 5710659
  have htrace : WordTrace (prefixWord ++ tailWord_5710659) baseStart_5710659 baseEnd_5710659 := by
    simpa [prefixWord, tailWord_5710659, baseEnd_5710659] using wordTrace_append hprefix tailTrace_5710659
  have hstable : (prefixWord ++ tailWord_5710659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710659).length < 2 ^ (prefixWord ++ tailWord_5710659).sum := by decide
  have hdescent : baseEnd_5710659 < baseStart_5710659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710756 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 1, 3, 4]
def baseStart_5710756 : Nat := 118140960795 + 5710756 * 2 ^ 59
def prefixEnd_5710756 : Nat := 4983230072969 + 3 ^ 40 * 5710756 * 2
def baseEnd_5710756 : Nat := 2932362728547563874586717

theorem tailTrace_5710756 : CollatzResearch.WordTrace tailWord_5710756 prefixEnd_5710756 2932362728547563874586717 := by
  unfold tailWord_5710756
  simp only [CollatzResearch.WordTrace]
  refine ⟨104144191449456903160380061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138858921932609204213840081 104144191449456903160380061)
  ·
    refine ⟨39054071793546338685142523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104144191449456903160380061 39054071793546338685142523)
    ·
      refine ⟨58581107690319508027713785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39054071793546338685142523 58581107690319508027713785)
      ·
        refine ⟨43935830767739631020785339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58581107690319508027713785 43935830767739631020785339)
        ·
          refine ⟨65903746151609446531178009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43935830767739631020785339 65903746151609446531178009)
          ·
            refine ⟨49427809613707084898383507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65903746151609446531178009 49427809613707084898383507)
            ·
              refine ⟨74141714420560627347575261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49427809613707084898383507 74141714420560627347575261)
              ·
                refine ⟨27803142907710235255340723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74141714420560627347575261 27803142907710235255340723)
                ·
                  refine ⟨41704714361565352883011085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27803142907710235255340723 41704714361565352883011085)
                  ·
                    refine ⟨15639267885587007331129157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41704714361565352883011085 15639267885587007331129157)
                    ·
                      refine ⟨2932362728547563874586717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15639267885587007331129157 2932362728547563874586717)
                      ·
                        rfl

theorem cell23_5710756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_5710756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710756 prefixEnd_5710756 := by exact prefixLift 5710756
  have htrace : WordTrace (prefixWord ++ tailWord_5710756) baseStart_5710756 baseEnd_5710756 := by
    simpa [prefixWord, tailWord_5710756, baseEnd_5710756] using wordTrace_append hprefix tailTrace_5710756
  have hstable : (prefixWord ++ tailWord_5710756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710756).length < 2 ^ (prefixWord ++ tailWord_5710756).sum := by decide
  have hdescent : baseEnd_5710756 < baseStart_5710756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710773 : List Nat := [1, 3, 3, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_5710773 : Nat := 118140960795 + 5710773 * 2 ^ 59
def prefixEnd_5710773 : Nat := 4983230072969 + 3 ^ 40 * 5710773 * 2
def baseEnd_5710773 : Nat := 2932371457718690308074139

theorem tailTrace_5710773 : CollatzResearch.WordTrace tailWord_5710773 prefixEnd_5710773 2932371457718690308074139 := by
  unfold tailWord_5710773
  simp only [CollatzResearch.WordTrace]
  refine ⟨208289002939852218224128973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138859335293234812149419315 208289002939852218224128973)
  ·
    refine ⟨78108376102444581834048365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208289002939852218224128973 78108376102444581834048365)
    ·
      refine ⟨29290641038416718187768137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78108376102444581834048365 29290641038416718187768137)
      ·
        refine ⟨21967980778812538640826103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29290641038416718187768137 21967980778812538640826103)
        ·
          refine ⟨32951971168218807961239155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21967980778812538640826103 32951971168218807961239155)
          ·
            refine ⟨49427956752328211941858733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32951971168218807961239155 49427956752328211941858733)
            ·
              refine ⟨18535483782123079478197025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49427956752328211941858733 18535483782123079478197025)
              ·
                refine ⟨13901612836592309608647769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18535483782123079478197025 13901612836592309608647769)
                ·
                  refine ⟨10426209627444232206485827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13901612836592309608647769 10426209627444232206485827)
                  ·
                    refine ⟨15639314441166348309728741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10426209627444232206485827 15639314441166348309728741)
                    ·
                      refine ⟨2932371457718690308074139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15639314441166348309728741 2932371457718690308074139)
                      ·
                        rfl

theorem cell23_5710773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_5710773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710773 prefixEnd_5710773 := by exact prefixLift 5710773
  have htrace : WordTrace (prefixWord ++ tailWord_5710773) baseStart_5710773 baseEnd_5710773 := by
    simpa [prefixWord, tailWord_5710773, baseEnd_5710773] using wordTrace_append hprefix tailTrace_5710773
  have hstable : (prefixWord ++ tailWord_5710773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710773).length < 2 ^ (prefixWord ++ tailWord_5710773).sum := by decide
  have hdescent : baseEnd_5710773 < baseStart_5710773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710774 : List Nat := [5, 1, 4, 1, 1, 2, 1, 1, 7]
def baseStart_5710774 : Nat := 118140960795 + 5710774 * 2 ^ 59
def prefixEnd_5710774 : Nat := 4983230072969 + 3 ^ 40 * 5710774 * 2
def baseEnd_5710774 : Nat := 325819107911038311573515

theorem tailTrace_5710774 : CollatzResearch.WordTrace tailWord_5710774 prefixEnd_5710774 325819107911038311573515 := by
  unfold tailWord_5710774
  simp only [CollatzResearch.WordTrace]
  refine ⟨13018064963303037212182211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138859359608565730263276917 13018064963303037212182211)
  ·
    refine ⟨19527097444954555818273317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13018064963303037212182211 19527097444954555818273317)
    ·
      refine ⟨3661330770928979215926247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19527097444954555818273317 3661330770928979215926247)
      ·
        refine ⟨5491996156393468823889371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3661330770928979215926247 5491996156393468823889371)
        ·
          refine ⟨8237994234590203235834057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5491996156393468823889371 8237994234590203235834057)
          ·
            refine ⟨6178495675942652426875543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8237994234590203235834057 6178495675942652426875543)
            ·
              refine ⟨9267743513913978640313315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6178495675942652426875543 9267743513913978640313315)
              ·
                refine ⟨13901615270870967960469973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9267743513913978640313315 13901615270870967960469973)
                ·
                  refine ⟨325819107911038311573515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13901615270870967960469973 325819107911038311573515)
                  ·
                    rfl

theorem cell23_5710774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_5710774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710774 prefixEnd_5710774 := by exact prefixLift 5710774
  have htrace : WordTrace (prefixWord ++ tailWord_5710774) baseStart_5710774 baseEnd_5710774 := by
    simpa [prefixWord, tailWord_5710774, baseEnd_5710774] using wordTrace_append hprefix tailTrace_5710774
  have hstable : (prefixWord ++ tailWord_5710774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710774).length < 2 ^ (prefixWord ++ tailWord_5710774).sum := by decide
  have hdescent : baseEnd_5710774 < baseStart_5710774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710779 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 12]
def baseStart_5710779 : Nat := 118140960795 + 5710779 * 2 ^ 59
def prefixEnd_5710779 : Nat := 4983230072969 + 3 ^ 40 * 5710779 * 2
def baseEnd_5710779 : Nat := 325819393178068587177679

theorem tailTrace_5710779 : CollatzResearch.WordTrace tailWord_5710779 prefixEnd_5710779 325819393178068587177679 := by
  unfold tailWord_5710779
  simp only [CollatzResearch.WordTrace]
  refine ⟨208289221777830481248847391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138859481185220320832564927 208289221777830481248847391)
  ·
    refine ⟨312433832666745721873271087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208289221777830481248847391 312433832666745721873271087)
    ·
      refine ⟨468650749000118582809906631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312433832666745721873271087 468650749000118582809906631)
      ·
        refine ⟨702976123500177874214859947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468650749000118582809906631 702976123500177874214859947)
        ·
          refine ⟨1054464185250266811322289921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 702976123500177874214859947 1054464185250266811322289921)
          ·
            refine ⟨790848138937700108491717441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1054464185250266811322289921 790848138937700108491717441)
            ·
              refine ⟨593136104203275081368788081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 790848138937700108491717441 593136104203275081368788081)
              ·
                refine ⟨444852078152456311026591061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 593136104203275081368788081 444852078152456311026591061)
                ·
                  refine ⟨325819393178068587177679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 444852078152456311026591061 325819393178068587177679)
                  ·
                    rfl

theorem cell23_5710779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 12].length) (baseStart_5710779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710779 prefixEnd_5710779 := by exact prefixLift 5710779
  have htrace : WordTrace (prefixWord ++ tailWord_5710779) baseStart_5710779 baseEnd_5710779 := by
    simpa [prefixWord, tailWord_5710779, baseEnd_5710779] using wordTrace_append hprefix tailTrace_5710779
  have hstable : (prefixWord ++ tailWord_5710779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710779).length < 2 ^ (prefixWord ++ tailWord_5710779).sum := by decide
  have hdescent : baseEnd_5710779 < baseStart_5710779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710810 : List Nat := [3, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3]
def baseStart_5710810 : Nat := 118140960795 + 5710810 * 2 ^ 59
def prefixEnd_5710810 : Nat := 4983230072969 + 3 ^ 40 * 5710810 * 2
def baseEnd_5710810 : Nat := 2932390456502906663311469

theorem tailTrace_5710810 : CollatzResearch.WordTrace tailWord_5710810 prefixEnd_5710810 2932390456502906663311469 := by
  unfold tailWord_5710810
  simp only [CollatzResearch.WordTrace]
  refine ⟨52072588110179543385806471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138860234960478782362150589 52072588110179543385806471)
  ·
    refine ⟨78108882165269315078709707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52072588110179543385806471 78108882165269315078709707)
    ·
      refine ⟨117163323247903972618064561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78108882165269315078709707 117163323247903972618064561)
      ·
        refine ⟨87872492435927979463548421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117163323247903972618064561 87872492435927979463548421)
        ·
          refine ⟨16476092331736496149415329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87872492435927979463548421 16476092331736496149415329)
          ·
            refine ⟨12357069248802372112061497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16476092331736496149415329 12357069248802372112061497)
            ·
              refine ⟨9267801936601779084046123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12357069248802372112061497 9267801936601779084046123)
              ·
                refine ⟨13901702904902668626069185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9267801936601779084046123 13901702904902668626069185)
                ·
                  refine ⟨10426277178677001469551889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13901702904902668626069185 10426277178677001469551889)
                  ·
                    refine ⟨7819707884007751102163917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10426277178677001469551889 7819707884007751102163917)
                    ·
                      refine ⟨2932390456502906663311469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7819707884007751102163917 2932390456502906663311469)
                      ·
                        rfl

theorem cell23_5710810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_5710810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710810 prefixEnd_5710810 := by exact prefixLift 5710810
  have htrace : WordTrace (prefixWord ++ tailWord_5710810) baseStart_5710810 baseEnd_5710810 := by
    simpa [prefixWord, tailWord_5710810, baseEnd_5710810] using wordTrace_append hprefix tailTrace_5710810
  have hstable : (prefixWord ++ tailWord_5710810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710810).length < 2 ^ (prefixWord ++ tailWord_5710810).sum := by decide
  have hdescent : baseEnd_5710810 < baseStart_5710810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710830 : List Nat := [4, 1, 2, 1, 4, 1, 2, 2, 6]
def baseStart_5710830 : Nat := 118140960795 + 5710830 * 2 ^ 59
def prefixEnd_5710830 : Nat := 4983230072969 + 3 ^ 40 * 5710830 * 2
def baseEnd_5710830 : Nat := 325822302901777398340153

theorem tailTrace_5710830 : CollatzResearch.WordTrace tailWord_5710830 prefixEnd_5710830 325822302901777398340153 := by
  unfold tailWord_5710830
  simp only [CollatzResearch.WordTrace]
  refine ⟨26036385237580714619869243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138860721267097144639302629 26036385237580714619869243)
  ·
    refine ⟨39054577856371071929803865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26036385237580714619869243 39054577856371071929803865)
    ·
      refine ⟨29290933392278303947352899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39054577856371071929803865 29290933392278303947352899)
      ·
        refine ⟨43936400088417455921029349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29290933392278303947352899 43936400088417455921029349)
        ·
          refine ⟨8238075016578272985193003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43936400088417455921029349 8238075016578272985193003)
          ·
            refine ⟨12357112524867409477789505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8238075016578272985193003 12357112524867409477789505)
            ·
              refine ⟨9267834393650557108342129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12357112524867409477789505 9267834393650557108342129)
              ·
                refine ⟨6950875795237917831256597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9267834393650557108342129 6950875795237917831256597)
                ·
                  refine ⟨325822302901777398340153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6950875795237917831256597 325822302901777398340153)
                  ·
                    rfl

theorem cell23_5710830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_5710830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710830 prefixEnd_5710830 := by exact prefixLift 5710830
  have htrace : WordTrace (prefixWord ++ tailWord_5710830) baseStart_5710830 baseEnd_5710830 := by
    simpa [prefixWord, tailWord_5710830, baseEnd_5710830] using wordTrace_append hprefix tailTrace_5710830
  have hstable : (prefixWord ++ tailWord_5710830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710830).length < 2 ^ (prefixWord ++ tailWord_5710830).sum := by decide
  have hdescent : baseEnd_5710830 < baseStart_5710830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710834 : List Nat := [3, 2, 1, 5, 1, 1, 1, 4, 1, 4]
def baseStart_5710834 : Nat := 118140960795 + 5710834 * 2 ^ 59
def prefixEnd_5710834 : Nat := 4983230072969 + 3 ^ 40 * 5710834 * 2
def baseEnd_5710834 : Nat := 977467593346204856470453

theorem tailTrace_5710834 : CollatzResearch.WordTrace tailWord_5710834 prefixEnd_5710834 977467593346204856470453 := by
  unfold tailWord_5710834
  simp only [CollatzResearch.WordTrace]
  refine ⟨52072806948157806410524889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138860818528420817094733037 52072806948157806410524889)
  ·
    refine ⟨39054605211118354807893667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52072806948157806410524889 39054605211118354807893667)
    ·
      refine ⟨58581907816677532211840501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39054605211118354807893667 58581907816677532211840501)
      ·
        refine ⟨5492053857813518644860047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58581907816677532211840501 5492053857813518644860047)
        ·
          refine ⟨8238080786720277967290071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5492053857813518644860047 8238080786720277967290071)
          ·
            refine ⟨12357121180080416950935107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8238080786720277967290071 12357121180080416950935107)
            ·
              refine ⟨18535681770120625426402661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12357121180080416950935107 18535681770120625426402661)
              ·
                refine ⟨3475440331897617267450499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18535681770120625426402661 3475440331897617267450499)
                ·
                  refine ⟨5213160497846425901175749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3475440331897617267450499 5213160497846425901175749)
                  ·
                    refine ⟨977467593346204856470453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5213160497846425901175749 977467593346204856470453)
                    ·
                      rfl

theorem cell23_5710834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_5710834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710834 prefixEnd_5710834 := by exact prefixLift 5710834
  have htrace : WordTrace (prefixWord ++ tailWord_5710834) baseStart_5710834 baseEnd_5710834 := by
    simpa [prefixWord, tailWord_5710834, baseEnd_5710834] using wordTrace_append hprefix tailTrace_5710834
  have hstable : (prefixWord ++ tailWord_5710834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710834).length < 2 ^ (prefixWord ++ tailWord_5710834).sum := by decide
  have hdescent : baseEnd_5710834 < baseStart_5710834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710897 : List Nat := [1, 2, 2, 3, 1, 2, 4, 1, 3, 2, 2]
def baseStart_5710897 : Nat := 118140960795 + 5710897 * 2 ^ 59
def prefixEnd_5710897 : Nat := 4983230072969 + 3 ^ 40 * 5710897 * 2
def baseEnd_5710897 : Nat := 2932435129319847822923569

theorem tailTrace_5710897 : CollatzResearch.WordTrace tailWord_5710897 prefixEnd_5710897 2932435129319847822923569 := by
  unfold tailWord_5710897
  simp only [CollatzResearch.WordTrace]
  refine ⟨208293525591402987401642945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138862350394268658267761963 208293525591402987401642945)
  ·
    refine ⟨156220144193552240551232209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208293525591402987401642945 156220144193552240551232209)
    ·
      refine ⟨117165108145164180413424157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156220144193552240551232209 117165108145164180413424157)
      ·
        refine ⟨43936915554436567655034059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117165108145164180413424157 43936915554436567655034059)
        ·
          refine ⟨65905373331654851482551089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43936915554436567655034059 65905373331654851482551089)
          ·
            refine ⟨49429029998741138611913317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65905373331654851482551089 49429029998741138611913317)
            ·
              refine ⟨9267943124763963489733747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49429029998741138611913317 9267943124763963489733747)
              ·
                refine ⟨13901914687145945234600621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9267943124763963489733747 13901914687145945234600621)
                ·
                  refine ⟨5213218007679729462975233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13901914687145945234600621 5213218007679729462975233)
                  ·
                    refine ⟨3909913505759797097231425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5213218007679729462975233 3909913505759797097231425)
                    ·
                      refine ⟨2932435129319847822923569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3909913505759797097231425 2932435129319847822923569)
                      ·
                        rfl

theorem cell23_5710897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_5710897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710897 prefixEnd_5710897 := by exact prefixLift 5710897
  have htrace : WordTrace (prefixWord ++ tailWord_5710897) baseStart_5710897 baseEnd_5710897 := by
    simpa [prefixWord, tailWord_5710897, baseEnd_5710897] using wordTrace_append hprefix tailTrace_5710897
  have hstable : (prefixWord ++ tailWord_5710897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710897).length < 2 ^ (prefixWord ++ tailWord_5710897).sum := by decide
  have hdescent : baseEnd_5710897 < baseStart_5710897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710900 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_5710900 : Nat := 118140960795 + 5710900 * 2 ^ 59
def prefixEnd_5710900 : Nat := 4983230072969 + 3 ^ 40 * 5710900 * 2
def baseEnd_5710900 : Nat := 2932436669761811311186055

theorem tailTrace_5710900 : CollatzResearch.WordTrace tailWord_5710900 prefixEnd_5710900 2932436669761811311186055 := by
  unfold tailWord_5710900
  simp only [CollatzResearch.WordTrace]
  refine ⟨104146817505196059457001077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138862423340261412609334769 104146817505196059457001077)
  ·
    refine ⟨9763764141112130574093851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104146817505196059457001077 9763764141112130574093851)
    ·
      refine ⟨14645646211668195861140777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9763764141112130574093851 14645646211668195861140777)
      ·
        refine ⟨10984234658751146895855583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14645646211668195861140777 10984234658751146895855583)
        ·
          refine ⟨16476351988126720343783375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10984234658751146895855583 16476351988126720343783375)
          ·
            refine ⟨24714527982190080515675063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16476351988126720343783375 24714527982190080515675063)
            ·
              refine ⟨37071791973285120773512595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24714527982190080515675063 37071791973285120773512595)
              ·
                refine ⟨55607687959927681160268893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37071791973285120773512595 55607687959927681160268893)
                ·
                  refine ⟨20852882984972880435100835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55607687959927681160268893 20852882984972880435100835)
                  ·
                    refine ⟨31279324477459320652651253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20852882984972880435100835 31279324477459320652651253)
                    ·
                      refine ⟨2932436669761811311186055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31279324477459320652651253 2932436669761811311186055)
                      ·
                        rfl

theorem cell23_5710900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_5710900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710900 prefixEnd_5710900 := by exact prefixLift 5710900
  have htrace : WordTrace (prefixWord ++ tailWord_5710900) baseStart_5710900 baseEnd_5710900 := by
    simpa [prefixWord, tailWord_5710900, baseEnd_5710900] using wordTrace_append hprefix tailTrace_5710900
  have hstable : (prefixWord ++ tailWord_5710900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710900).length < 2 ^ (prefixWord ++ tailWord_5710900).sum := by decide
  have hdescent : baseEnd_5710900 < baseStart_5710900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710910 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_5710910 : Nat := 118140960795 + 5710910 * 2 ^ 59
def prefixEnd_5710910 : Nat := 4983230072969 + 3 ^ 40 * 5710910 * 2
def baseEnd_5710910 : Nat := 2932441804568356272061009

theorem tailTrace_5710910 : CollatzResearch.WordTrace tailWord_5710910 prefixEnd_5710910 2932441804568356272061009 := by
  unfold tailWord_5710910
  simp only [CollatzResearch.WordTrace]
  refine ⟨26036749967544486327733273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138862666493570593747910789 26036749967544486327733273)
  ·
    refine ⟨19527562475658364745799955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26036749967544486327733273 19527562475658364745799955)
    ·
      refine ⟨29291343713487547118699933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19527562475658364745799955 29291343713487547118699933)
      ·
        refine ⟨10984253892557830169512475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29291343713487547118699933 10984253892557830169512475)
        ·
          refine ⟨16476380838836745254268713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10984253892557830169512475 16476380838836745254268713)
          ·
            refine ⟨12357285629127558940701535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16476380838836745254268713 12357285629127558940701535)
            ·
              refine ⟨18535928443691338411052303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12357285629127558940701535 18535928443691338411052303)
              ·
                refine ⟨27803892665537007616578455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18535928443691338411052303 27803892665537007616578455)
                ·
                  refine ⟨41705838998305511424867683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27803892665537007616578455 41705838998305511424867683)
                  ·
                    refine ⟨62558758497458267137301525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41705838998305511424867683 62558758497458267137301525)
                    ·
                      refine ⟨2932441804568356272061009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62558758497458267137301525 2932441804568356272061009)
                      ·
                        rfl

theorem cell23_5710910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_5710910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710910 prefixEnd_5710910 := by exact prefixLift 5710910
  have htrace : WordTrace (prefixWord ++ tailWord_5710910) baseStart_5710910 baseEnd_5710910 := by
    simpa [prefixWord, tailWord_5710910, baseEnd_5710910] using wordTrace_append hprefix tailTrace_5710910
  have hstable : (prefixWord ++ tailWord_5710910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710910).length < 2 ^ (prefixWord ++ tailWord_5710910).sum := by decide
  have hdescent : baseEnd_5710910 < baseStart_5710910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710934 : List Nat := [5, 2, 2, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_5710934 : Nat := 118140960795 + 5710934 * 2 ^ 59
def prefixEnd_5710934 : Nat := 4983230072969 + 3 ^ 40 * 5710934 * 2
def baseEnd_5710934 : Nat := 2932454128104064178160899

theorem tailTrace_5710934 : CollatzResearch.WordTrace tailWord_5710934 prefixEnd_5710934 2932454128104064178160899 := by
  unfold tailWord_5710934
  simp only [CollatzResearch.WordTrace]
  refine ⟨13018429693266808920046241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138863250061512628480493237 13018429693266808920046241)
  ·
    refine ⟨9763822269950106690034681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13018429693266808920046241 9763822269950106690034681)
    ·
      refine ⟨7322866702462580017526011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9763822269950106690034681 7322866702462580017526011)
      ·
        refine ⟨10984300053693870026289017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7322866702462580017526011 10984300053693870026289017)
        ·
          refine ⟨8238225040270402519716763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10984300053693870026289017 8238225040270402519716763)
          ·
            refine ⟨12357337560405603779575145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8238225040270402519716763 12357337560405603779575145)
            ·
              refine ⟨9268003170304202834681359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12357337560405603779575145 9268003170304202834681359)
              ·
                refine ⟨13902004755456304252022039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9268003170304202834681359 13902004755456304252022039)
                ·
                  refine ⟨20853007133184456378033059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13902004755456304252022039 20853007133184456378033059)
                  ·
                    refine ⟨31279510699776684567049589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20853007133184456378033059 31279510699776684567049589)
                    ·
                      refine ⟨2932454128104064178160899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31279510699776684567049589 2932454128104064178160899)
                      ·
                        rfl

theorem cell23_5710934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_5710934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710934 prefixEnd_5710934 := by exact prefixLift 5710934
  have htrace : WordTrace (prefixWord ++ tailWord_5710934) baseStart_5710934 baseEnd_5710934 := by
    simpa [prefixWord, tailWord_5710934, baseEnd_5710934] using wordTrace_append hprefix tailTrace_5710934
  have hstable : (prefixWord ++ tailWord_5710934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710934).length < 2 ^ (prefixWord ++ tailWord_5710934).sum := by decide
  have hdescent : baseEnd_5710934 < baseStart_5710934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710973 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 4, 1, 5]
def baseStart_5710973 : Nat := 118140960795 + 5710973 * 2 ^ 59
def prefixEnd_5710973 : Nat := 4983230072969 + 3 ^ 40 * 5710973 * 2
def baseEnd_5710973 : Nat := 2932474153849589525573219

theorem tailTrace_5710973 : CollatzResearch.WordTrace tailWord_5710973 prefixEnd_5710973 2932474153849589525573219 := by
  unfold tailWord_5710973
  simp only [CollatzResearch.WordTrace]
  refine ⟨208296297539127652381409573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138864198359418434920939715 208296297539127652381409573)
  ·
    refine ⟨39055555788586434821514295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208296297539127652381409573 39055555788586434821514295)
    ·
      refine ⟨58583333682879652232271443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39055555788586434821514295 58583333682879652232271443)
      ·
        refine ⟨87875000524319478348407165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58583333682879652232271443 87875000524319478348407165)
        ·
          refine ⟨32953125196619804380652687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87875000524319478348407165 32953125196619804380652687)
          ·
            refine ⟨49429687794929706570979031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32953125196619804380652687 49429687794929706570979031)
            ·
              refine ⟨74144531692394559856468547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49429687794929706570979031 74144531692394559856468547)
              ·
                refine ⟨111216797538591839784702821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74144531692394559856468547 111216797538591839784702821)
                ·
                  refine ⟨20853149538485969959631779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111216797538591839784702821 20853149538485969959631779)
                  ·
                    refine ⟨31279724307728954939447669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20853149538485969959631779 31279724307728954939447669)
                    ·
                      refine ⟨2932474153849589525573219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31279724307728954939447669 2932474153849589525573219)
                      ·
                        rfl

theorem cell23_5710973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_5710973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710973 prefixEnd_5710973 := by exact prefixLift 5710973
  have htrace : WordTrace (prefixWord ++ tailWord_5710973) baseStart_5710973 baseEnd_5710973 := by
    simpa [prefixWord, tailWord_5710973, baseEnd_5710973] using wordTrace_append hprefix tailTrace_5710973
  have hstable : (prefixWord ++ tailWord_5710973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710973).length < 2 ^ (prefixWord ++ tailWord_5710973).sum := by decide
  have hdescent : baseEnd_5710973 < baseStart_5710973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710983 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 4]
def baseStart_5710983 : Nat := 118140960795 + 5710983 * 2 ^ 59
def prefixEnd_5710983 : Nat := 4983230072969 + 3 ^ 40 * 5710983 * 2
def baseEnd_5710983 : Nat := 2932479288656134486448173

theorem tailTrace_5710983 : CollatzResearch.WordTrace tailWord_5710983 prefixEnd_5710983 2932479288656134486448173 := by
  unfold tailWord_5710983
  simp only [CollatzResearch.WordTrace]
  refine ⟨208296662269091424089273603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138864441512727616059515735 208296662269091424089273603)
  ·
    refine ⟨312444993403637136133910405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208296662269091424089273603 312444993403637136133910405)
    ·
      refine ⟨58583436263181963025108201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 312444993403637136133910405 58583436263181963025108201)
      ·
        refine ⟨43937577197386472268831151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58583436263181963025108201 43937577197386472268831151)
        ·
          refine ⟨65906365796079708403246727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43937577197386472268831151 65906365796079708403246727)
          ·
            refine ⟨98859548694119562604870091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65906365796079708403246727 98859548694119562604870091)
            ·
              refine ⟨148289323041179343907305137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98859548694119562604870091 148289323041179343907305137)
              ·
                refine ⟨111216992280884507930478853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148289323041179343907305137 111216992280884507930478853)
                ·
                  refine ⟨20853186052665845236964785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111216992280884507930478853 20853186052665845236964785)
                  ·
                    refine ⟨15639889539499383927723589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20853186052665845236964785 15639889539499383927723589)
                    ·
                      refine ⟨2932479288656134486448173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15639889539499383927723589 2932479288656134486448173)
                      ·
                        rfl

theorem cell23_5710983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_5710983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710983 prefixEnd_5710983 := by exact prefixLift 5710983
  have htrace : WordTrace (prefixWord ++ tailWord_5710983) baseStart_5710983 baseEnd_5710983 := by
    simpa [prefixWord, tailWord_5710983, baseEnd_5710983] using wordTrace_append hprefix tailTrace_5710983
  have hstable : (prefixWord ++ tailWord_5710983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710983).length < 2 ^ (prefixWord ++ tailWord_5710983).sum := by decide
  have hdescent : baseEnd_5710983 < baseStart_5710983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5710990 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5]
def baseStart_5710990 : Nat := 118140960795 + 5710990 * 2 ^ 59
def prefixEnd_5710990 : Nat := 4983230072969 + 3 ^ 40 * 5710990 * 2
def baseEnd_5710990 : Nat := 2932482883020715959060641

theorem tailTrace_5710990 : CollatzResearch.WordTrace tailWord_5710990 prefixEnd_5710990 2932482883020715959060641 := by
  unfold tailWord_5710990
  simp only [CollatzResearch.WordTrace]
  refine ⟨26037114697508258035597303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138864611720044042856518949 26037114697508258035597303)
  ·
    refine ⟨39055672046262387053395955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26037114697508258035597303 39055672046262387053395955)
    ·
      refine ⟨58583508069393580580093933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39055672046262387053395955 58583508069393580580093933)
      ·
        refine ⟨21968815526022592717535225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58583508069393580580093933 21968815526022592717535225)
        ·
          refine ⟨16476611644516944538151419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21968815526022592717535225 16476611644516944538151419)
          ·
            refine ⟨24714917466775416807227129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16476611644516944538151419 24714917466775416807227129)
            ·
              refine ⟨18536188100081562605420347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24714917466775416807227129 18536188100081562605420347)
              ·
                refine ⟨27804282150122343908130521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18536188100081562605420347 27804282150122343908130521)
                ·
                  refine ⟨20853211612591757931097891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27804282150122343908130521 20853211612591757931097891)
                  ·
                    refine ⟨31279817418887636896646837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20853211612591757931097891 31279817418887636896646837)
                    ·
                      refine ⟨2932482883020715959060641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31279817418887636896646837 2932482883020715959060641)
                      ·
                        rfl

theorem cell23_5710990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_5710990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5710990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5710990 prefixEnd_5710990 := by exact prefixLift 5710990
  have htrace : WordTrace (prefixWord ++ tailWord_5710990) baseStart_5710990 baseEnd_5710990 := by
    simpa [prefixWord, tailWord_5710990, baseEnd_5710990] using wordTrace_append hprefix tailTrace_5710990
  have hstable : (prefixWord ++ tailWord_5710990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5710990).length < 2 ^ (prefixWord ++ tailWord_5710990).sum := by decide
  have hdescent : baseEnd_5710990 < baseStart_5710990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5710990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711004 : List Nat := [2, 2, 3, 2, 1, 2, 1, 4, 2, 2, 2]
def baseStart_5711004 : Nat := 118140960795 + 5711004 * 2 ^ 59
def prefixEnd_5711004 : Nat := 4983230072969 + 3 ^ 40 * 5711004 * 2
def baseEnd_5711004 : Nat := 2932490071749878904285577

theorem tailTrace_5711004 : CollatzResearch.WordTrace tailWord_5711004 prefixEnd_5711004 2932490071749878904285577 := by
  unfold tailWord_5711004
  simp only [CollatzResearch.WordTrace]
  refine ⟨104148714101007672337894033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138864952134676896450525377 104148714101007672337894033)
  ·
    refine ⟨78111535575755754253420525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104148714101007672337894033 78111535575755754253420525)
    ·
      refine ⟨29291825840908407845032697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78111535575755754253420525 29291825840908407845032697)
      ·
        refine ⟨21968869380681305883774523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29291825840908407845032697 21968869380681305883774523)
        ·
          refine ⟨32953304071021958825661785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21968869380681305883774523 32953304071021958825661785)
          ·
            refine ⟨24714978053266469119246339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32953304071021958825661785 24714978053266469119246339)
            ·
              refine ⟨37072467079899703678869509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24714978053266469119246339 37072467079899703678869509)
              ·
                refine ⟨6951087577481194439788033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37072467079899703678869509 6951087577481194439788033)
                ·
                  refine ⟨5213315683110895829841025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6951087577481194439788033 5213315683110895829841025)
                  ·
                    refine ⟨3909986762333171872380769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5213315683110895829841025 3909986762333171872380769)
                    ·
                      refine ⟨2932490071749878904285577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3909986762333171872380769 2932490071749878904285577)
                      ·
                        rfl

theorem cell23_5711004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_5711004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711004 prefixEnd_5711004 := by exact prefixLift 5711004
  have htrace : WordTrace (prefixWord ++ tailWord_5711004) baseStart_5711004 baseEnd_5711004 := by
    simpa [prefixWord, tailWord_5711004, baseEnd_5711004] using wordTrace_append hprefix tailTrace_5711004
  have hstable : (prefixWord ++ tailWord_5711004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711004).length < 2 ^ (prefixWord ++ tailWord_5711004).sum := by decide
  have hdescent : baseEnd_5711004 < baseStart_5711004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711023 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 4, 5]
def baseStart_5711023 : Nat := 118140960795 + 5711023 * 2 ^ 59
def prefixEnd_5711023 : Nat := 4983230072969 + 3 ^ 40 * 5711023 * 2
def baseEnd_5711023 : Nat := 977499942627438109982663

theorem tailTrace_5711023 : CollatzResearch.WordTrace tailWord_5711023 prefixEnd_5711023 977499942627438109982663 := by
  unfold tailWord_5711023
  simp only [CollatzResearch.WordTrace]
  refine ⟨208298121188946510920729723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138865414125964340613819815 208298121188946510920729723)
  ·
    refine ⟨312447181783419766381094585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208298121188946510920729723 312447181783419766381094585)
    ·
      refine ⟨234335386337564824785820939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312447181783419766381094585 234335386337564824785820939)
      ·
        refine ⟨351503079506347237178731409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234335386337564824785820939 351503079506347237178731409)
        ·
          refine ⟨263627309629760427884048557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351503079506347237178731409 263627309629760427884048557)
          ·
            refine ⟨98860241111160160456518209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263627309629760427884048557 98860241111160160456518209)
            ·
              refine ⟨74145180833370120342388657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98860241111160160456518209 74145180833370120342388657)
              ·
                refine ⟨55608885625027590256791493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74145180833370120342388657 55608885625027590256791493)
                ·
                  refine ⟨10426666054692673173148405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55608885625027590256791493 10426666054692673173148405)
                  ·
                    refine ⟨977499942627438109982663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10426666054692673173148405 977499942627438109982663)
                    ·
                      rfl

theorem cell23_5711023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 5].length) (baseStart_5711023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711023 prefixEnd_5711023 := by exact prefixLift 5711023
  have htrace : WordTrace (prefixWord ++ tailWord_5711023) baseStart_5711023 baseEnd_5711023 := by
    simpa [prefixWord, tailWord_5711023, baseEnd_5711023] using wordTrace_append hprefix tailTrace_5711023
  have hstable : (prefixWord ++ tailWord_5711023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711023).length < 2 ^ (prefixWord ++ tailWord_5711023).sum := by decide
  have hdescent : baseEnd_5711023 < baseStart_5711023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711040 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 1, 7]
def baseStart_5711040 : Nat := 118140960795 + 5711040 * 2 ^ 59
def prefixEnd_5711040 : Nat := 4983230072969 + 3 ^ 40 * 5711040 * 2
def baseEnd_5711040 : Nat := 977502852351146921145137

theorem tailTrace_5711040 : CollatzResearch.WordTrace tailWord_5711040 prefixEnd_5711040 977502852351146921145137 := by
  unfold tailWord_5711040
  simp only [CollatzResearch.WordTrace]
  refine ⟨104149370614942461412049287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138865827486589948549399049 104149370614942461412049287)
  ·
    refine ⟨156224055922413692118073931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104149370614942461412049287 156224055922413692118073931)
    ·
      refine ⟨234336083883620538177110897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156224055922413692118073931 234336083883620538177110897)
      ·
        refine ⟨175752062912715403632833173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234336083883620538177110897 175752062912715403632833173)
        ·
          refine ⟨8238377949033534545289055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 175752062912715403632833173 8238377949033534545289055)
          ·
            refine ⟨12357566923550301817933583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8238377949033534545289055 12357566923550301817933583)
            ·
              refine ⟨18536350385325452726900375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12357566923550301817933583 18536350385325452726900375)
              ·
                refine ⟨27804525577988179090350563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18536350385325452726900375 27804525577988179090350563)
                ·
                  refine ⟨41706788366982268635525845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27804525577988179090350563 41706788366982268635525845)
                  ·
                    refine ⟨977502852351146921145137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41706788366982268635525845 977502852351146921145137)
                    ·
                      rfl

theorem cell23_5711040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 1, 7].length) (baseStart_5711040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711040 prefixEnd_5711040 := by exact prefixLift 5711040
  have htrace : WordTrace (prefixWord ++ tailWord_5711040) baseStart_5711040 baseEnd_5711040 := by
    simpa [prefixWord, tailWord_5711040, baseEnd_5711040] using wordTrace_append hprefix tailTrace_5711040
  have hstable : (prefixWord ++ tailWord_5711040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711040).length < 2 ^ (prefixWord ++ tailWord_5711040).sum := by decide
  have hdescent : baseEnd_5711040 < baseStart_5711040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711042 : List Nat := [3, 5, 1, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_5711042 : Nat := 118140960795 + 5711042 * 2 ^ 59
def prefixEnd_5711042 : Nat := 4983230072969 + 3 ^ 40 * 5711042 * 2
def baseEnd_5711042 : Nat := 2932509584014749755610403

theorem tailTrace_5711042 : CollatzResearch.WordTrace tailWord_5711042 prefixEnd_5711042 2932509584014749755610403 := by
  unfold tailWord_5711042
  simp only [CollatzResearch.WordTrace]
  refine ⟨52074703543969419291417845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138865876117251784777114253 52074703543969419291417845)
  ·
    refine ⟨4882003457247133058570423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52074703543969419291417845 4882003457247133058570423)
    ·
      refine ⟨7323005185870699587855635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4882003457247133058570423 7323005185870699587855635)
      ·
        refine ⟨10984507778806049381783453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7323005185870699587855635 10984507778806049381783453)
        ·
          refine ⟨4119190417052268518168795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10984507778806049381783453 4119190417052268518168795)
          ·
            refine ⟨6178785625578402777253193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4119190417052268518168795 6178785625578402777253193)
            ·
              refine ⟨4634089219183802082939895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6178785625578402777253193 4634089219183802082939895)
              ·
                refine ⟨6951133828775703124409843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4634089219183802082939895 6951133828775703124409843)
                ·
                  refine ⟨10426700743163554686614765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6951133828775703124409843 10426700743163554686614765)
                  ·
                    refine ⟨3910012778686333007480537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10426700743163554686614765 3910012778686333007480537)
                    ·
                      refine ⟨2932509584014749755610403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3910012778686333007480537 2932509584014749755610403)
                      ·
                        rfl

theorem cell23_5711042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_5711042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711042 prefixEnd_5711042 := by exact prefixLift 5711042
  have htrace : WordTrace (prefixWord ++ tailWord_5711042) baseStart_5711042 baseEnd_5711042 := by
    simpa [prefixWord, tailWord_5711042, baseEnd_5711042] using wordTrace_append hprefix tailTrace_5711042
  have hstable : (prefixWord ++ tailWord_5711042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711042).length < 2 ^ (prefixWord ++ tailWord_5711042).sum := by decide
  have hdescent : baseEnd_5711042 < baseStart_5711042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711044 : List Nat := [2, 3, 3, 1, 3, 1, 2, 3, 5]
def baseStart_5711044 : Nat := 118140960795 + 5711044 * 2 ^ 59
def prefixEnd_5711044 : Nat := 4983230072969 + 3 ^ 40 * 5711044 * 2
def baseEnd_5711044 : Nat := 325834512330673194198377

theorem tailTrace_5711044 : CollatzResearch.WordTrace tailWord_5711044 prefixEnd_5711044 325834512330673194198377 := by
  unfold tailWord_5711044
  simp only [CollatzResearch.WordTrace]
  refine ⟨104149443560935215753622093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138865924747913621004829457 104149443560935215753622093)
  ·
    refine ⟨39056041335350705907608285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104149443560935215753622093 39056041335350705907608285)
    ·
      refine ⟨14646015500756514715353107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39056041335350705907608285 14646015500756514715353107)
      ·
        refine ⟨21969023251134772073029661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14646015500756514715353107 21969023251134772073029661)
        ·
          refine ⟨8238383719175539527386123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21969023251134772073029661 8238383719175539527386123)
          ·
            refine ⟨12357575578763309291079185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8238383719175539527386123 12357575578763309291079185)
            ·
              refine ⟨9268181684072481968309389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12357575578763309291079185 9268181684072481968309389)
              ·
                refine ⟨3475568131527180738116021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9268181684072481968309389 3475568131527180738116021)
                ·
                  refine ⟨325834512330673194198377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3475568131527180738116021 325834512330673194198377)
                  ·
                    rfl

theorem cell23_5711044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_5711044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711044 prefixEnd_5711044 := by exact prefixLift 5711044
  have htrace : WordTrace (prefixWord ++ tailWord_5711044) baseStart_5711044 baseEnd_5711044 := by
    simpa [prefixWord, tailWord_5711044, baseEnd_5711044] using wordTrace_append hprefix tailTrace_5711044
  have hstable : (prefixWord ++ tailWord_5711044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711044).length < 2 ^ (prefixWord ++ tailWord_5711044).sum := by decide
  have hdescent : baseEnd_5711044 < baseStart_5711044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711063 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 5]
def baseStart_5711063 : Nat := 118140960795 + 5711063 * 2 ^ 59
def prefixEnd_5711063 : Nat := 4983230072969 + 3 ^ 40 * 5711063 * 2
def baseEnd_5711063 : Nat := 2932520367108494173447805

theorem tailTrace_5711063 : CollatzResearch.WordTrace tailWord_5711063 prefixEnd_5711063 2932520367108494173447805 := by
  unfold tailWord_5711063
  simp only [CollatzResearch.WordTrace]
  refine ⟨208299580108801597752185843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138866386739201065168123895 208299580108801597752185843)
  ·
    refine ⟨312449370163202396628278765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208299580108801597752185843 312449370163202396628278765)
    ·
      refine ⟨117168513811200898735604537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312449370163202396628278765 117168513811200898735604537)
      ·
        refine ⟨87876385358400674051703403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117168513811200898735604537 87876385358400674051703403)
        ·
          refine ⟨131814578037601011077555105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87876385358400674051703403 131814578037601011077555105)
          ·
            refine ⟨98860933528200758308166329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131814578037601011077555105 98860933528200758308166329)
            ·
              refine ⟨74145700146150568731124747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98860933528200758308166329 74145700146150568731124747)
              ·
                refine ⟨111218550219225853096687121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74145700146150568731124747 111218550219225853096687121)
                ·
                  refine ⟨83413912664419389822515341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111218550219225853096687121 83413912664419389822515341)
                  ·
                    refine ⟨31280217249157271183443253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83413912664419389822515341 31280217249157271183443253)
                    ·
                      refine ⟨2932520367108494173447805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31280217249157271183443253 2932520367108494173447805)
                      ·
                        rfl

theorem cell23_5711063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_5711063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711063 prefixEnd_5711063 := by exact prefixLift 5711063
  have htrace : WordTrace (prefixWord ++ tailWord_5711063) baseStart_5711063 baseEnd_5711063 := by
    simpa [prefixWord, tailWord_5711063, baseEnd_5711063] using wordTrace_append hprefix tailTrace_5711063
  have hstable : (prefixWord ++ tailWord_5711063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711063).length < 2 ^ (prefixWord ++ tailWord_5711063).sum := by decide
  have hdescent : baseEnd_5711063 < baseStart_5711063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711080 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 3, 4, 3]
def baseStart_5711080 : Nat := 118140960795 + 5711080 * 2 ^ 59
def prefixEnd_5711080 : Nat := 4983230072969 + 3 ^ 40 * 5711080 * 2
def baseEnd_5711080 : Nat := 2932529096279620606935227

theorem tailTrace_5711080 : CollatzResearch.WordTrace tailWord_5711080 prefixEnd_5711080 2932529096279620606935227 := by
  unfold tailWord_5711080
  simp only [CollatzResearch.WordTrace]
  refine ⟨104150100074870004827777347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138866800099826673103703129 104150100074870004827777347)
  ·
    refine ⟨156225150112305007241666021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104150100074870004827777347 156225150112305007241666021)
    ·
      refine ⟨29292215646057188857812379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156225150112305007241666021 29292215646057188857812379)
      ·
        refine ⟨43938323469085783286718569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29292215646057188857812379 43938323469085783286718569)
        ·
          refine ⟨32953742601814337465038927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43938323469085783286718569 32953742601814337465038927)
          ·
            refine ⟨49430613902721506197558391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32953742601814337465038927 49430613902721506197558391)
            ·
              refine ⟨74145920854082259296337587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49430613902721506197558391 74145920854082259296337587)
              ·
                refine ⟨111218881281123388944506381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74145920854082259296337587 111218881281123388944506381)
                ·
                  refine ⟨41707080480421270854189893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111218881281123388944506381 41707080480421270854189893)
                  ·
                    refine ⟨7820077590078988285160605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41707080480421270854189893 7820077590078988285160605)
                    ·
                      refine ⟨2932529096279620606935227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7820077590078988285160605 2932529096279620606935227)
                      ·
                        rfl

theorem cell23_5711080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_5711080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711080 prefixEnd_5711080 := by exact prefixLift 5711080
  have htrace : WordTrace (prefixWord ++ tailWord_5711080) baseStart_5711080 baseEnd_5711080 := by
    simpa [prefixWord, tailWord_5711080, baseEnd_5711080] using wordTrace_append hprefix tailTrace_5711080
  have hstable : (prefixWord ++ tailWord_5711080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711080).length < 2 ^ (prefixWord ++ tailWord_5711080).sum := by decide
  have hdescent : baseEnd_5711080 < baseStart_5711080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711123 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 7]
def baseStart_5711123 : Nat := 118140960795 + 5711123 * 2 ^ 59
def prefixEnd_5711123 : Nat := 4983230072969 + 3 ^ 40 * 5711123 * 2
def baseEnd_5711123 : Nat := 2932551175947763938697529

theorem tailTrace_5711123 : CollatzResearch.WordTrace tailWord_5711123 prefixEnd_5711123 2932551175947763938697529 := by
  unfold tailWord_5711123
  simp only [CollatzResearch.WordTrace]
  refine ⟨208301768488584227999370023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138867845659056151999580015 208301768488584227999370023)
  ·
    refine ⟨312452652732876341999055035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208301768488584227999370023 312452652732876341999055035)
    ·
      refine ⟨468678979099314512998582553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312452652732876341999055035 468678979099314512998582553)
      ·
        refine ⟨351509234324485884748936915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 468678979099314512998582553 351509234324485884748936915)
        ·
          refine ⟨527263851486728827123405373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351509234324485884748936915 527263851486728827123405373)
          ·
            refine ⟨197723944307523310171277015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 527263851486728827123405373 197723944307523310171277015)
            ·
              refine ⟨296585916461284965256915523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197723944307523310171277015 296585916461284965256915523)
              ·
                refine ⟨444878874691927447885373285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296585916461284965256915523 444878874691927447885373285)
                ·
                  refine ⟨83414789004736396478507491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 444878874691927447885373285 83414789004736396478507491)
                  ·
                    refine ⟨125122183507104594717761237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83414789004736396478507491 125122183507104594717761237)
                    ·
                      refine ⟨2932551175947763938697529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125122183507104594717761237 2932551175947763938697529)
                      ·
                        rfl

theorem cell23_5711123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_5711123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711123 prefixEnd_5711123 := by exact prefixLift 5711123
  have htrace : WordTrace (prefixWord ++ tailWord_5711123) baseStart_5711123 baseEnd_5711123 := by
    simpa [prefixWord, tailWord_5711123, baseEnd_5711123] using wordTrace_append hprefix tailTrace_5711123
  have hstable : (prefixWord ++ tailWord_5711123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711123).length < 2 ^ (prefixWord ++ tailWord_5711123).sum := by decide
  have hdescent : baseEnd_5711123 < baseStart_5711123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711137 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 6, 3, 2]
def baseStart_5711137 : Nat := 118140960795 + 5711137 * 2 ^ 59
def prefixEnd_5711137 : Nat := 4983230072969 + 3 ^ 40 * 5711137 * 2
def baseEnd_5711137 : Nat := 2932558364676926883922465

theorem tailTrace_5711137 : CollatzResearch.WordTrace tailWord_5711137 prefixEnd_5711137 2932558364676926883922465 := by
  unfold tailWord_5711137
  simp only [CollatzResearch.WordTrace]
  refine ⟨208302279110533508390379665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138868186073689005593586443 208302279110533508390379665)
  ·
    refine ⟨156226709332900131292784749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208302279110533508390379665 156226709332900131292784749)
    ·
      refine ⟨58585015999837549234794281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156226709332900131292784749 58585015999837549234794281)
      ·
        refine ⟨43938761999878161926095711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58585015999837549234794281 43938761999878161926095711)
        ·
          refine ⟨65908142999817242889143567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43938761999878161926095711 65908142999817242889143567)
          ·
            refine ⟨98862214499725864333715351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65908142999817242889143567 98862214499725864333715351)
            ·
              refine ⟨148293321749588796500573027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98862214499725864333715351 148293321749588796500573027)
              ·
                refine ⟨222439982624383194750859541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148293321749588796500573027 222439982624383194750859541)
                ·
                  refine ⟨10426874185517962253946541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 222439982624383194750859541 10426874185517962253946541)
                  ·
                    refine ⟨3910077819569235845229953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10426874185517962253946541 3910077819569235845229953)
                    ·
                      refine ⟨2932558364676926883922465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3910077819569235845229953 2932558364676926883922465)
                      ·
                        rfl

theorem cell23_5711137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_5711137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711137 prefixEnd_5711137 := by exact prefixLift 5711137
  have htrace : WordTrace (prefixWord ++ tailWord_5711137) baseStart_5711137 baseEnd_5711137 := by
    simpa [prefixWord, tailWord_5711137, baseEnd_5711137] using wordTrace_append hprefix tailTrace_5711137
  have hstable : (prefixWord ++ tailWord_5711137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711137).length < 2 ^ (prefixWord ++ tailWord_5711137).sum := by decide
  have hdescent : baseEnd_5711137 < baseStart_5711137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711154 : List Nat := [3, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2]
def baseStart_5711154 : Nat := 118140960795 + 5711154 * 2 ^ 59
def prefixEnd_5711154 : Nat := 4983230072969 + 3 ^ 40 * 5711154 * 2
def baseEnd_5711154 : Nat := 2932567093848053317409887

theorem tailTrace_5711154 : CollatzResearch.WordTrace tailWord_5711154 prefixEnd_5711154 2932567093848053317409887 := by
  unfold tailWord_5711154
  simp only [CollatzResearch.WordTrace]
  refine ⟨52075724787867980073437129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138868599434314613529165677 52075724787867980073437129)
  ·
    refine ⟨39056793590900985055077847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52075724787867980073437129 39056793590900985055077847)
    ·
      refine ⟨58585190386351477582616771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39056793590900985055077847 58585190386351477582616771)
      ·
        refine ⟨87877785579527216373925157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58585190386351477582616771 87877785579527216373925157)
        ·
          refine ⟨16477084796161353070110967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87877785579527216373925157 16477084796161353070110967)
          ·
            refine ⟨24715627194242029605166451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16477084796161353070110967 24715627194242029605166451)
            ·
              refine ⟨37073440791363044407749677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24715627194242029605166451 37073440791363044407749677)
              ·
                refine ⟨13902540296761141652906129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37073440791363044407749677 13902540296761141652906129)
                ·
                  refine ⟨10426905222570856239679597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13902540296761141652906129 10426905222570856239679597)
                  ·
                    refine ⟨3910089458464071089879849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10426905222570856239679597 3910089458464071089879849)
                    ·
                      refine ⟨2932567093848053317409887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3910089458464071089879849 2932567093848053317409887)
                      ·
                        rfl

theorem cell23_5711154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2].length) (baseStart_5711154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711154 prefixEnd_5711154 := by exact prefixLift 5711154
  have htrace : WordTrace (prefixWord ++ tailWord_5711154) baseStart_5711154 baseEnd_5711154 := by
    simpa [prefixWord, tailWord_5711154, baseEnd_5711154] using wordTrace_append hprefix tailTrace_5711154
  have hstable : (prefixWord ++ tailWord_5711154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711154).length < 2 ^ (prefixWord ++ tailWord_5711154).sum := by decide
  have hdescent : baseEnd_5711154 < baseStart_5711154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711164 : List Nat := [2, 2, 2, 2, 1, 4, 3, 1, 1, 5]
def baseStart_5711164 : Nat := 118140960795 + 5711164 * 2 ^ 59
def prefixEnd_5711164 : Nat := 4983230072969 + 3 ^ 40 * 5711164 * 2
def baseEnd_5711164 : Nat := 977524076218199426094947

theorem tailTrace_5711164 : CollatzResearch.WordTrace tailWord_5711164 prefixEnd_5711164 977524076218199426094947 := by
  unfold tailWord_5711164
  simp only [CollatzResearch.WordTrace]
  refine ⟨104151631940717846000806273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138868842587623794667741697 104151631940717846000806273)
  ·
    refine ⟨78113723955538384500604705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104151631940717846000806273 78113723955538384500604705)
    ·
      refine ⟨58585292966653788375453529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78113723955538384500604705 58585292966653788375453529)
      ·
        refine ⟨43938969724990341281590147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58585292966653788375453529 43938969724990341281590147)
        ·
          refine ⟨65908454587485511922385221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43938969724990341281590147 65908454587485511922385221)
          ·
            refine ⟨12357835235153533485447229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65908454587485511922385221 12357835235153533485447229)
            ·
              refine ⟨4634188213182575057042711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12357835235153533485447229 4634188213182575057042711)
              ·
                refine ⟨6951282319773862585564067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4634188213182575057042711 6951282319773862585564067)
                ·
                  refine ⟨10426923479660793878346101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6951282319773862585564067 10426923479660793878346101)
                  ·
                    refine ⟨977524076218199426094947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10426923479660793878346101 977524076218199426094947)
                    ·
                      rfl

theorem cell23_5711164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_5711164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711164 prefixEnd_5711164 := by exact prefixLift 5711164
  have htrace : WordTrace (prefixWord ++ tailWord_5711164) baseStart_5711164 baseEnd_5711164 := by
    simpa [prefixWord, tailWord_5711164, baseEnd_5711164] using wordTrace_append hprefix tailTrace_5711164
  have hstable : (prefixWord ++ tailWord_5711164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711164).length < 2 ^ (prefixWord ++ tailWord_5711164).sum := by decide
  have hdescent : baseEnd_5711164 < baseStart_5711164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711177 : List Nat := [1, 2, 1, 1, 2, 3, 3, 4, 2, 4]
def baseStart_5711177 : Nat := 118140960795 + 5711177 * 2 ^ 59
def prefixEnd_5711177 : Nat := 4983230072969 + 3 ^ 40 * 5711177 * 2
def baseEnd_5711177 : Nat := 977526301301035575807427

theorem tailTrace_5711177 : CollatzResearch.WordTrace tailWord_5711177 prefixEnd_5711177 977526301301035575807427 := by
  unfold tailWord_5711177
  simp only [CollatzResearch.WordTrace]
  refine ⟨208303738030388595221835785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138869158686925730147890523 208303738030388595221835785)
  ·
    refine ⟨156227803522791446416376839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208303738030388595221835785 156227803522791446416376839)
    ·
      refine ⟨234341705284187169624565259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156227803522791446416376839 234341705284187169624565259)
      ·
        refine ⟨351512557926280754436847889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234341705284187169624565259 351512557926280754436847889)
        ·
          refine ⟨263634418444710565827635917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351512557926280754436847889 263634418444710565827635917)
          ·
            refine ⟨98862906916766462185363469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263634418444710565827635917 98862906916766462185363469)
            ·
              refine ⟨37073590093787423319511301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98862906916766462185363469 37073590093787423319511301)
              ·
                refine ⟨6951298142585141872408369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37073590093787423319511301 6951298142585141872408369)
                ·
                  refine ⟨5213473606938856404306277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6951298142585141872408369 5213473606938856404306277)
                  ·
                    refine ⟨977526301301035575807427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5213473606938856404306277 977526301301035575807427)
                    ·
                      rfl

theorem cell23_5711177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 4].length) (baseStart_5711177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711177 prefixEnd_5711177 := by exact prefixLift 5711177
  have htrace : WordTrace (prefixWord ++ tailWord_5711177) baseStart_5711177 baseEnd_5711177 := by
    simpa [prefixWord, tailWord_5711177, baseEnd_5711177] using wordTrace_append hprefix tailTrace_5711177
  have hstable : (prefixWord ++ tailWord_5711177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711177).length < 2 ^ (prefixWord ++ tailWord_5711177).sum := by decide
  have hdescent : baseEnd_5711177 < baseStart_5711177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711184 : List Nat := [2, 1, 1, 1, 1, 5, 2, 3, 3, 2, 2]
def baseStart_5711184 : Nat := 118140960795 + 5711184 * 2 ^ 59
def prefixEnd_5711184 : Nat := 4983230072969 + 3 ^ 40 * 5711184 * 2
def baseEnd_5711184 : Nat := 2932582498267688200034749

theorem tailTrace_5711184 : CollatzResearch.WordTrace tailWord_5711184 prefixEnd_5711184 2932582498267688200034749 := by
  unfold tailWord_5711184
  simp only [CollatzResearch.WordTrace]
  refine ⟨104151996670681617708670303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138869328894242156944893737 104151996670681617708670303)
  ·
    refine ⟨156227995006022426563005455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104151996670681617708670303 156227995006022426563005455)
    ·
      refine ⟨234341992509033639844508183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156227995006022426563005455 234341992509033639844508183)
      ·
        refine ⟨351512988763550459766762275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234341992509033639844508183 351512988763550459766762275)
        ·
          refine ⟨527269483145325689650143413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351512988763550459766762275 527269483145325689650143413)
          ·
            refine ⟨49431514044874283404700945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 527269483145325689650143413 49431514044874283404700945)
            ·
              refine ⟨37073635533655712553525709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49431514044874283404700945 37073635533655712553525709)
              ·
                refine ⟨13902613325120892207572141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37073635533655712553525709 13902613325120892207572141)
                ·
                  refine ⟨5213479996920334577839553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13902613325120892207572141 5213479996920334577839553)
                  ·
                    refine ⟨3910109997690250933379665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5213479996920334577839553 3910109997690250933379665)
                    ·
                      refine ⟨2932582498267688200034749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3910109997690250933379665 2932582498267688200034749)
                      ·
                        rfl

theorem cell23_5711184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 3, 2, 2].length) (baseStart_5711184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711184 prefixEnd_5711184 := by exact prefixLift 5711184
  have htrace : WordTrace (prefixWord ++ tailWord_5711184) baseStart_5711184 baseEnd_5711184 := by
    simpa [prefixWord, tailWord_5711184, baseEnd_5711184] using wordTrace_append hprefix tailTrace_5711184
  have hstable : (prefixWord ++ tailWord_5711184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711184).length < 2 ^ (prefixWord ++ tailWord_5711184).sum := by decide
  have hdescent : baseEnd_5711184 < baseStart_5711184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711217 : List Nat := [1, 2, 2, 2, 1, 2, 4, 2, 1, 3, 3]
def baseStart_5711217 : Nat := 118140960795 + 5711217 * 2 ^ 59
def prefixEnd_5711217 : Nat := 4983230072969 + 3 ^ 40 * 5711217 * 2
def baseEnd_5711217 : Nat := 2932599443129286570922097

theorem tailTrace_5711217 : CollatzResearch.WordTrace tailWord_5711217 prefixEnd_5711217 2932599443129286570922097 := by
  unfold tailWord_5711217
  simp only [CollatzResearch.WordTrace]
  refine ⟨208305196950243682053291905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138870131300162454702194603 208305196950243682053291905)
  ·
    refine ⟨156228897712682761539968929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208305196950243682053291905 156228897712682761539968929)
    ·
      refine ⟨117171673284512071154976697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156228897712682761539968929 117171673284512071154976697)
      ·
        refine ⟨87878754963384053366232523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117171673284512071154976697 87878754963384053366232523)
        ·
          refine ⟨131818132445076080049348785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87878754963384053366232523 131818132445076080049348785)
          ·
            refine ⟨98863599333807060037011589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131818132445076080049348785 98863599333807060037011589)
            ·
              refine ⟨18536924875088823756939673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98863599333807060037011589 18536924875088823756939673)
              ·
                refine ⟨13902693656316617817704755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18536924875088823756939673 13902693656316617817704755)
                ·
                  refine ⟨20854040484474926726557133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13902693656316617817704755 20854040484474926726557133)
                  ·
                    refine ⟨7820265181678097522458925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20854040484474926726557133 7820265181678097522458925)
                    ·
                      refine ⟨2932599443129286570922097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7820265181678097522458925 2932599443129286570922097)
                      ·
                        rfl

theorem cell23_5711217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_5711217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711217 prefixEnd_5711217 := by exact prefixLift 5711217
  have htrace : WordTrace (prefixWord ++ tailWord_5711217) baseStart_5711217 baseEnd_5711217 := by
    simpa [prefixWord, tailWord_5711217, baseEnd_5711217] using wordTrace_append hprefix tailTrace_5711217
  have hstable : (prefixWord ++ tailWord_5711217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711217).length < 2 ^ (prefixWord ++ tailWord_5711217).sum := by decide
  have hdescent : baseEnd_5711217 < baseStart_5711217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711218 : List Nat := [3, 2, 1, 2, 1, 2, 4, 3, 1, 2, 2]
def baseStart_5711218 : Nat := 118140960795 + 5711218 * 2 ^ 59
def prefixEnd_5711218 : Nat := 4983230072969 + 3 ^ 40 * 5711218 * 2
def baseEnd_5711218 : Nat := 2932599956609941067009593

theorem tailTrace_5711218 : CollatzResearch.WordTrace tailWord_5711218 prefixEnd_5711218 2932599956609941067009593 := by
  unfold tailWord_5711218
  simp only [CollatzResearch.WordTrace]
  refine ⟨52076308355810014806019577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138870155615493372816052205 52076308355810014806019577)
  ·
    refine ⟨39057231266857511104514683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52076308355810014806019577 39057231266857511104514683)
    ·
      refine ⟨58585846900286266656772025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39057231266857511104514683 58585846900286266656772025)
      ·
        refine ⟨43939385175214699992579019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58585846900286266656772025 43939385175214699992579019)
        ·
          refine ⟨65909077762822049988868529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43939385175214699992579019 65909077762822049988868529)
          ·
            refine ⟨49431808322116537491651397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65909077762822049988868529 49431808322116537491651397)
            ·
              refine ⟨9268464060396850779684637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49431808322116537491651397 9268464060396850779684637)
              ·
                refine ⟨3475674022648819042381739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9268464060396850779684637 3475674022648819042381739)
                ·
                  refine ⟨5213511033973228563572609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3475674022648819042381739 5213511033973228563572609)
                  ·
                    refine ⟨3910133275479921422679457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5213511033973228563572609 3910133275479921422679457)
                    ·
                      refine ⟨2932599956609941067009593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3910133275479921422679457 2932599956609941067009593)
                      ·
                        rfl

theorem cell23_5711218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_5711218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711218 prefixEnd_5711218 := by exact prefixLift 5711218
  have htrace : WordTrace (prefixWord ++ tailWord_5711218) baseStart_5711218 baseEnd_5711218 := by
    simpa [prefixWord, tailWord_5711218, baseEnd_5711218] using wordTrace_append hprefix tailTrace_5711218
  have hstable : (prefixWord ++ tailWord_5711218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711218).length < 2 ^ (prefixWord ++ tailWord_5711218).sum := by decide
  have hdescent : baseEnd_5711218 < baseStart_5711218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711221 : List Nat := [1, 3, 4, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_5711221 : Nat := 118140960795 + 5711221 * 2 ^ 59
def prefixEnd_5711221 : Nat := 4983230072969 + 3 ^ 40 * 5711221 * 2
def baseEnd_5711221 : Nat := 2932601497051904555272079

theorem tailTrace_5711221 : CollatzResearch.WordTrace tailWord_5711221 prefixEnd_5711221 2932601497051904555272079 := by
  unfold tailWord_5711221
  simp only [CollatzResearch.WordTrace]
  refine ⟨208305342842229190736437517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138870228561486127157625011 208305342842229190736437517)
  ·
    refine ⟨78114503565835946526164069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208305342842229190736437517 78114503565835946526164069)
    ·
      refine ⟨14646469418594239973655763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78114503565835946526164069 14646469418594239973655763)
      ·
        refine ⟨21969704127891359960483645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14646469418594239973655763 21969704127891359960483645)
        ·
          refine ⟨8238639047959259985181367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21969704127891359960483645 8238639047959259985181367)
          ·
            refine ⟨12357958571938889977772051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8238639047959259985181367 12357958571938889977772051)
            ·
              refine ⟨18536937857908334966658077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12357958571938889977772051 18536937857908334966658077)
              ·
                refine ⟨6951351696715625612496779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18536937857908334966658077 6951351696715625612496779)
                ·
                  refine ⟨10427027545073438418745169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6951351696715625612496779 10427027545073438418745169)
                  ·
                    refine ⟨7820270658805078814058877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10427027545073438418745169 7820270658805078814058877)
                    ·
                      refine ⟨2932601497051904555272079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7820270658805078814058877 2932601497051904555272079)
                      ·
                        rfl

theorem cell23_5711221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_5711221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711221 prefixEnd_5711221 := by exact prefixLift 5711221
  have htrace : WordTrace (prefixWord ++ tailWord_5711221) baseStart_5711221 baseEnd_5711221 := by
    simpa [prefixWord, tailWord_5711221, baseEnd_5711221] using wordTrace_append hprefix tailTrace_5711221
  have hstable : (prefixWord ++ tailWord_5711221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711221).length < 2 ^ (prefixWord ++ tailWord_5711221).sum := by decide
  have hdescent : baseEnd_5711221 < baseStart_5711221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711261 : List Nat := [1, 4, 2, 1, 3, 1, 1, 4, 1, 3, 2]
def baseStart_5711261 : Nat := 118140960795 + 5711261 * 2 ^ 59
def prefixEnd_5711261 : Nat := 4983230072969 + 3 ^ 40 * 5711261 * 2
def baseEnd_5711261 : Nat := 2932622036278084398771895

theorem tailTrace_5711261 : CollatzResearch.WordTrace tailWord_5711261 prefixEnd_5711261 2932622036278084398771895 := by
  unfold tailWord_5711261
  simp only [CollatzResearch.WordTrace]
  refine ⟨208306801762084277567893637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138871201174722851711929091 208306801762084277567893637)
  ·
    refine ⟨39057525330390802043980057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208306801762084277567893637 39057525330390802043980057)
    ·
      refine ⟨29293143997793101532985043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39057525330390802043980057 29293143997793101532985043)
      ·
        refine ⟨43939715996689652299477565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29293143997793101532985043 43939715996689652299477565)
        ·
          refine ⟨16477393498758619612304087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43939715996689652299477565 16477393498758619612304087)
          ·
            refine ⟨24716090248137929418456131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16477393498758619612304087 24716090248137929418456131)
            ·
              refine ⟨37074135372206894127684197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24716090248137929418456131 37074135372206894127684197)
              ·
                refine ⟨6951400382288792648940787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37074135372206894127684197 6951400382288792648940787)
                ·
                  refine ⟨10427100573433188973411181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6951400382288792648940787 10427100573433188973411181)
                  ·
                    refine ⟨3910162715037445865029193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10427100573433188973411181 3910162715037445865029193)
                    ·
                      refine ⟨2932622036278084398771895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3910162715037445865029193 2932622036278084398771895)
                      ·
                        rfl

theorem cell23_5711261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_5711261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711261 prefixEnd_5711261 := by exact prefixLift 5711261
  have htrace : WordTrace (prefixWord ++ tailWord_5711261) baseStart_5711261 baseEnd_5711261 := by
    simpa [prefixWord, tailWord_5711261, baseEnd_5711261] using wordTrace_append hprefix tailTrace_5711261
  have hstable : (prefixWord ++ tailWord_5711261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711261).length < 2 ^ (prefixWord ++ tailWord_5711261).sum := by decide
  have hdescent : baseEnd_5711261 < baseStart_5711261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711307 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 3]
def baseStart_5711307 : Nat := 118140960795 + 5711307 * 2 ^ 59
def prefixEnd_5711307 : Nat := 4983230072969 + 3 ^ 40 * 5711307 * 2
def baseEnd_5711307 : Nat := 2932645656388191218796683

theorem tailTrace_5711307 : CollatzResearch.WordTrace tailWord_5711307 prefixEnd_5711307 2932645656388191218796683 := by
  unfold tailWord_5711307
  simp only [CollatzResearch.WordTrace]
  refine ⟨208308479519917627424068175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138872319679945084949378783 208308479519917627424068175)
  ·
    refine ⟨312462719279876441136102263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208308479519917627424068175 312462719279876441136102263)
    ·
      refine ⟨468694078919814661704153395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312462719279876441136102263 468694078919814661704153395)
      ·
        refine ⟨703041118379721992556230093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468694078919814661704153395 703041118379721992556230093)
        ·
          refine ⟨263640419392395747208586285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 703041118379721992556230093 263640419392395747208586285)
          ·
            refine ⟨98865157272148405203219857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263640419392395747208586285 98865157272148405203219857)
            ·
              refine ⟨74148867954111303902414893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98865157272148405203219857 74148867954111303902414893)
              ·
                refine ⟨27805825482791738963405585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74148867954111303902414893 27805825482791738963405585)
                ·
                  refine ⟨20854369112093804222554189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27805825482791738963405585 20854369112093804222554189)
                  ·
                    refine ⟨7820388417035176583457821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20854369112093804222554189 7820388417035176583457821)
                    ·
                      refine ⟨2932645656388191218796683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7820388417035176583457821 2932645656388191218796683)
                      ·
                        rfl

theorem cell23_5711307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 3].length) (baseStart_5711307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711307 prefixEnd_5711307 := by exact prefixLift 5711307
  have htrace : WordTrace (prefixWord ++ tailWord_5711307) baseStart_5711307 baseEnd_5711307 := by
    simpa [prefixWord, tailWord_5711307, baseEnd_5711307] using wordTrace_append hprefix tailTrace_5711307
  have hstable : (prefixWord ++ tailWord_5711307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711307).length < 2 ^ (prefixWord ++ tailWord_5711307).sum := by decide
  have hdescent : baseEnd_5711307 < baseStart_5711307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711308 : List Nat := [2, 2, 1, 4, 2, 2, 1, 3, 2, 2, 2]
def baseStart_5711308 : Nat := 118140960795 + 5711308 * 2 ^ 59
def prefixEnd_5711308 : Nat := 4983230072969 + 3 ^ 40 * 5711308 * 2
def baseEnd_5711308 : Nat := 2932646169868845714884179

theorem tailTrace_5711308 : CollatzResearch.WordTrace tailWord_5711308 prefixEnd_5711308 2932646169868845714884179 := by
  unfold tailWord_5711308
  simp only [CollatzResearch.WordTrace]
  refine ⟨104154257996457002297427289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138872343995276003063236385 104154257996457002297427289)
  ·
    refine ⟨78115693497342751723070467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104154257996457002297427289 78115693497342751723070467)
    ·
      refine ⟨117173540246014127584605701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78115693497342751723070467 117173540246014127584605701)
      ·
        refine ⟨21970038796127648922113569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117173540246014127584605701 21970038796127648922113569)
        ·
          refine ⟨16477529097095736691585177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21970038796127648922113569 16477529097095736691585177)
          ·
            refine ⟨12358146822821802518688883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16477529097095736691585177 12358146822821802518688883)
            ·
              refine ⟨18537220234232703778033325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12358146822821802518688883 18537220234232703778033325)
              ·
                refine ⟨6951457587837263916762497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18537220234232703778033325 6951457587837263916762497)
                ·
                  refine ⟨5213593190877947937571873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6951457587837263916762497 5213593190877947937571873)
                  ·
                    refine ⟨3910194893158460953178905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5213593190877947937571873 3910194893158460953178905)
                    ·
                      refine ⟨2932646169868845714884179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3910194893158460953178905 2932646169868845714884179)
                      ·
                        rfl

theorem cell23_5711308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_5711308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711308 prefixEnd_5711308 := by exact prefixLift 5711308
  have htrace : WordTrace (prefixWord ++ tailWord_5711308) baseStart_5711308 baseEnd_5711308 := by
    simpa [prefixWord, tailWord_5711308, baseEnd_5711308] using wordTrace_append hprefix tailTrace_5711308
  have hstable : (prefixWord ++ tailWord_5711308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711308).length < 2 ^ (prefixWord ++ tailWord_5711308).sum := by decide
  have hdescent : baseEnd_5711308 < baseStart_5711308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711347 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 4]
def baseStart_5711347 : Nat := 118140960795 + 5711347 * 2 ^ 59
def prefixEnd_5711347 : Nat := 4983230072969 + 3 ^ 40 * 5711347 * 2
def baseEnd_5711347 : Nat := 2932666195614371062296499

theorem tailTrace_5711347 : CollatzResearch.WordTrace tailWord_5711347 prefixEnd_5711347 2932666195614371062296499 := by
  unfold tailWord_5711347
  simp only [CollatzResearch.WordTrace]
  refine ⟨208309938439772714255524295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138873292293181809503682863 208309938439772714255524295)
  ·
    refine ⟨312464907659659071383286443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208309938439772714255524295 312464907659659071383286443)
    ·
      refine ⟨468697361489488607074929665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312464907659659071383286443 468697361489488607074929665)
      ·
        refine ⟨351523021117116455306197249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 468697361489488607074929665 351523021117116455306197249)
        ·
          refine ⟨263642265837837341479647937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351523021117116455306197249 263642265837837341479647937)
          ·
            refine ⟨197731699378378006109735953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263642265837837341479647937 197731699378378006109735953)
            ·
              refine ⟨148298774533783504582301965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197731699378378006109735953 148298774533783504582301965)
              ·
                refine ⟨55612040450168814218363237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148298774533783504582301965 55612040450168814218363237)
                ·
                  refine ⟨10427257584406652665943107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55612040450168814218363237 10427257584406652665943107)
                  ·
                    refine ⟨15640886376609978998914661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10427257584406652665943107 15640886376609978998914661)
                    ·
                      refine ⟨2932666195614371062296499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15640886376609978998914661 2932666195614371062296499)
                      ·
                        rfl

theorem cell23_5711347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 4].length) (baseStart_5711347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711347 prefixEnd_5711347 := by exact prefixLift 5711347
  have htrace : WordTrace (prefixWord ++ tailWord_5711347) baseStart_5711347 baseEnd_5711347 := by
    simpa [prefixWord, tailWord_5711347, baseEnd_5711347] using wordTrace_append hprefix tailTrace_5711347
  have hstable : (prefixWord ++ tailWord_5711347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711347).length < 2 ^ (prefixWord ++ tailWord_5711347).sum := by decide
  have hdescent : baseEnd_5711347 < baseStart_5711347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711358 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_5711358 : Nat := 118140960795 + 5711358 * 2 ^ 59
def prefixEnd_5711358 : Nat := 4983230072969 + 3 ^ 40 * 5711358 * 2
def baseEnd_5711358 : Nat := 2932671843901570519258949

theorem tailTrace_5711358 : CollatzResearch.WordTrace tailWord_5711358 prefixEnd_5711358 2932671843901570519258949 := by
  unfold tailWord_5711358
  simp only [CollatzResearch.WordTrace]
  refine ⟨26038792455341607891771841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138873559761821908756116485 26038792455341607891771841)
  ·
    refine ⟨19529094341506205918828881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26038792455341607891771841 19529094341506205918828881)
    ·
      refine ⟨14646820756129654439121661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19529094341506205918828881 14646820756129654439121661)
      ·
        refine ⟨5492557783548620414670623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14646820756129654439121661 5492557783548620414670623)
        ·
          refine ⟨8238836675322930622005935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5492557783548620414670623 8238836675322930622005935)
          ·
            refine ⟨12358255012984395933008903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8238836675322930622005935 12358255012984395933008903)
            ·
              refine ⟨18537382519476593899513355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12358255012984395933008903 18537382519476593899513355)
              ·
                refine ⟨27806073779214890849270033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18537382519476593899513355 27806073779214890849270033)
                ·
                  refine ⟨20854555334411168136952525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27806073779214890849270033 20854555334411168136952525)
                  ·
                    refine ⟨7820458250404188051357197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20854555334411168136952525 7820458250404188051357197)
                    ·
                      refine ⟨2932671843901570519258949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7820458250404188051357197 2932671843901570519258949)
                      ·
                        rfl

theorem cell23_5711358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_5711358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711358 prefixEnd_5711358 := by exact prefixLift 5711358
  have htrace : WordTrace (prefixWord ++ tailWord_5711358) baseStart_5711358 baseEnd_5711358 := by
    simpa [prefixWord, tailWord_5711358, baseEnd_5711358] using wordTrace_append hprefix tailTrace_5711358
  have hstable : (prefixWord ++ tailWord_5711358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711358).length < 2 ^ (prefixWord ++ tailWord_5711358).sum := by decide
  have hdescent : baseEnd_5711358 < baseStart_5711358 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711381 : List Nat := [1, 3, 2, 1, 3, 4, 1, 1, 2, 1, 4]
def baseStart_5711381 : Nat := 118140960795 + 5711381 * 2 ^ 59
def prefixEnd_5711381 : Nat := 4983230072969 + 3 ^ 40 * 5711381 * 2
def baseEnd_5711381 : Nat := 2932683653956623929271343

theorem tailTrace_5711381 : CollatzResearch.WordTrace tailWord_5711381 prefixEnd_5711381 2932683653956623929271343 := by
  unfold tailWord_5711381
  simp only [CollatzResearch.WordTrace]
  refine ⟨208311178521649538062261997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138874119014433025374841331 208311178521649538062261997)
  ·
    refine ⟨78116691945618576773348249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208311178521649538062261997 78116691945618576773348249)
    ·
      refine ⟨58587518959213932580011187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78116691945618576773348249 58587518959213932580011187)
      ·
        refine ⟨87881278438820898870016781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58587518959213932580011187 87881278438820898870016781)
        ·
          refine ⟨32955479414557837076256293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87881278438820898870016781 32955479414557837076256293)
          ·
            refine ⟨6179152390229594451798055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32955479414557837076256293 6179152390229594451798055)
            ·
              refine ⟨9268728585344391677697083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6179152390229594451798055 9268728585344391677697083)
              ·
                refine ⟨13903092878016587516545625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9268728585344391677697083 13903092878016587516545625)
                ·
                  refine ⟨10427319658512440637409219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13903092878016587516545625 10427319658512440637409219)
                  ·
                    refine ⟨15640979487768660956113829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10427319658512440637409219 15640979487768660956113829)
                    ·
                      refine ⟨2932683653956623929271343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15640979487768660956113829 2932683653956623929271343)
                      ·
                        rfl

theorem cell23_5711381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_5711381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711381 prefixEnd_5711381 := by exact prefixLift 5711381
  have htrace : WordTrace (prefixWord ++ tailWord_5711381) baseStart_5711381 baseEnd_5711381 := by
    simpa [prefixWord, tailWord_5711381, baseEnd_5711381] using wordTrace_append hprefix tailTrace_5711381
  have hstable : (prefixWord ++ tailWord_5711381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711381).length < 2 ^ (prefixWord ++ tailWord_5711381).sum := by decide
  have hdescent : baseEnd_5711381 < baseStart_5711381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711391 : List Nat := [1, 1, 2, 4, 1, 1, 3, 5, 1, 4]
def baseStart_5711391 : Nat := 118140960795 + 5711391 * 2 ^ 59
def prefixEnd_5711391 : Nat := 4983230072969 + 3 ^ 40 * 5711391 * 2
def baseEnd_5711391 : Nat := 977562929587722963382099

theorem tailTrace_5711391 : CollatzResearch.WordTrace tailWord_5711391 prefixEnd_5711391 977562929587722963382099 := by
  unfold tailWord_5711391
  simp only [CollatzResearch.WordTrace]
  refine ⟨208311543251613309770126027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138874362167742206513417351 208311543251613309770126027)
  ·
    refine ⟨312467314877419964655189041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208311543251613309770126027 312467314877419964655189041)
    ·
      refine ⟨234350486158064973491391781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312467314877419964655189041 234350486158064973491391781)
      ·
        refine ⟨43940716154637182529635959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234350486158064973491391781 43940716154637182529635959)
        ·
          refine ⟨65911074231955773794453939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43940716154637182529635959 65911074231955773794453939)
          ·
            refine ⟨98866611347933660691680909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65911074231955773794453939 98866611347933660691680909)
            ·
              refine ⟨37074979255475122759380341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98866611347933660691680909 37074979255475122759380341)
              ·
                refine ⟨3475779305200792758691907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37074979255475122759380341 3475779305200792758691907)
                ·
                  refine ⟨5213668957801189138037861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3475779305200792758691907 5213668957801189138037861)
                  ·
                    refine ⟨977562929587722963382099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5213668957801189138037861 977562929587722963382099)
                    ·
                      rfl

theorem cell23_5711391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 1, 4].length) (baseStart_5711391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711391 prefixEnd_5711391 := by exact prefixLift 5711391
  have htrace : WordTrace (prefixWord ++ tailWord_5711391) baseStart_5711391 baseEnd_5711391 := by
    simpa [prefixWord, tailWord_5711391, baseEnd_5711391] using wordTrace_append hprefix tailTrace_5711391
  have hstable : (prefixWord ++ tailWord_5711391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711391).length < 2 ^ (prefixWord ++ tailWord_5711391).sum := by decide
  have hdescent : baseEnd_5711391 < baseStart_5711391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711441 : List Nat := [1, 2, 2, 1, 3, 2, 2, 3, 2, 3, 2]
def baseStart_5711441 : Nat := 118140960795 + 5711441 * 2 ^ 59
def prefixEnd_5711441 : Nat := 4983230072969 + 3 ^ 40 * 5711441 * 2
def baseEnd_5711441 : Nat := 2932714462795893694521067

theorem tailTrace_5711441 : CollatzResearch.WordTrace tailWord_5711441 prefixEnd_5711441 2932714462795893694521067 := by
  unfold tailWord_5711441
  simp only [CollatzResearch.WordTrace]
  refine ⟨208313366901432168309446177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138875577934288112206297451 208313366901432168309446177)
  ·
    refine ⟨156235025176074126232084633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208313366901432168309446177 156235025176074126232084633)
    ·
      refine ⟨117176268882055594674063475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156235025176074126232084633 117176268882055594674063475)
      ·
        refine ⟨175764403323083392011095213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117176268882055594674063475 175764403323083392011095213)
        ·
          refine ⟨65911651246156272004160705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175764403323083392011095213 65911651246156272004160705)
          ·
            refine ⟨49433738434617204003120529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65911651246156272004160705 49433738434617204003120529)
            ·
              refine ⟨37075303825962903002340397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49433738434617204003120529 37075303825962903002340397)
              ·
                refine ⟨13903238934736088625877649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37075303825962903002340397 13903238934736088625877649)
                ·
                  refine ⟨10427429201052066469408237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13903238934736088625877649 10427429201052066469408237)
                  ·
                    refine ⟨3910285950394524926028089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10427429201052066469408237 3910285950394524926028089)
                    ·
                      refine ⟨2932714462795893694521067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3910285950394524926028089 2932714462795893694521067)
                      ·
                        rfl

theorem cell23_5711441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 3, 2].length) (baseStart_5711441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711441 prefixEnd_5711441 := by exact prefixLift 5711441
  have htrace : WordTrace (prefixWord ++ tailWord_5711441) baseStart_5711441 baseEnd_5711441 := by
    simpa [prefixWord, tailWord_5711441, baseEnd_5711441] using wordTrace_append hprefix tailTrace_5711441
  have hstable : (prefixWord ++ tailWord_5711441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711441).length < 2 ^ (prefixWord ++ tailWord_5711441).sum := by decide
  have hdescent : baseEnd_5711441 < baseStart_5711441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711481 : List Nat := [1, 2, 1, 3, 3, 1, 3, 3, 2, 4]
def baseStart_5711481 : Nat := 118140960795 + 5711481 * 2 ^ 59
def prefixEnd_5711481 : Nat := 4983230072969 + 3 ^ 40 * 5711481 * 2
def baseEnd_5711481 : Nat := 977578334007357846006961

theorem tailTrace_5711481 : CollatzResearch.WordTrace tailWord_5711481 prefixEnd_5711481 977578334007357846006961 := by
  unfold tailWord_5711481
  simp only [CollatzResearch.WordTrace]
  refine ⟨208314825821287255140902297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138876550547524836760601531 208314825821287255140902297)
  ·
    refine ⟨156236119365965441355676723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208314825821287255140902297 156236119365965441355676723)
    ·
      refine ⟨234354179048948162033515085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156236119365965441355676723 234354179048948162033515085)
      ·
        refine ⟨87882817143355560762568157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234354179048948162033515085 87882817143355560762568157)
        ·
          refine ⟨32956056428758335285963059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87882817143355560762568157 32956056428758335285963059)
          ·
            refine ⟨49434084643137502928944589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32956056428758335285963059 49434084643137502928944589)
            ·
              refine ⟨18537781741176563598354221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49434084643137502928944589 18537781741176563598354221)
              ·
                refine ⟨6951668152941211349382833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18537781741176563598354221 6951668152941211349382833)
                ·
                  refine ⟨5213751114705908512037125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6951668152941211349382833 5213751114705908512037125)
                  ·
                    refine ⟨977578334007357846006961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5213751114705908512037125 977578334007357846006961)
                    ·
                      rfl

theorem cell23_5711481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 4].length) (baseStart_5711481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711481 prefixEnd_5711481 := by exact prefixLift 5711481
  have htrace : WordTrace (prefixWord ++ tailWord_5711481) baseStart_5711481 baseEnd_5711481 := by
    simpa [prefixWord, tailWord_5711481, baseEnd_5711481] using wordTrace_append hprefix tailTrace_5711481
  have hstable : (prefixWord ++ tailWord_5711481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711481).length < 2 ^ (prefixWord ++ tailWord_5711481).sum := by decide
  have hdescent : baseEnd_5711481 < baseStart_5711481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711484 : List Nat := [2, 2, 2, 1, 1, 2, 1, 5, 1, 2, 4]
def baseStart_5711484 : Nat := 118140960795 + 5711484 * 2 ^ 59
def prefixEnd_5711484 : Nat := 4983230072969 + 3 ^ 40 * 5711484 * 2
def baseEnd_5711484 : Nat := 2932736542464037026283369

theorem tailTrace_5711484 : CollatzResearch.WordTrace tailWord_5711484 prefixEnd_5711484 2932736542464037026283369 := by
  unfold tailWord_5711484
  simp only [CollatzResearch.WordTrace]
  refine ⟨104157467620138193326630753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138876623493517591102174337 104157467620138193326630753)
  ·
    refine ⟨78118100715103644994973065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104157467620138193326630753 78118100715103644994973065)
    ·
      refine ⟨58588575536327733746229799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78118100715103644994973065 58588575536327733746229799)
      ·
        refine ⟨87882863304491600619344699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58588575536327733746229799 87882863304491600619344699)
        ·
          refine ⟨131824294956737400929017049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87882863304491600619344699 131824294956737400929017049)
          ·
            refine ⟨98868221217553050696762787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131824294956737400929017049 98868221217553050696762787)
            ·
              refine ⟨148302331826329576045144181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98868221217553050696762787 148302331826329576045144181)
              ·
                refine ⟨13903343608718397754232267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 148302331826329576045144181 13903343608718397754232267)
                ·
                  refine ⟨20855015413077596631348401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13903343608718397754232267 20855015413077596631348401)
                  ·
                    refine ⟨15641261559808197473511301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20855015413077596631348401 15641261559808197473511301)
                    ·
                      refine ⟨2932736542464037026283369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15641261559808197473511301 2932736542464037026283369)
                      ·
                        rfl

theorem cell23_5711484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_5711484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711484 prefixEnd_5711484 := by exact prefixLift 5711484
  have htrace : WordTrace (prefixWord ++ tailWord_5711484) baseStart_5711484 baseEnd_5711484 := by
    simpa [prefixWord, tailWord_5711484, baseEnd_5711484] using wordTrace_append hprefix tailTrace_5711484
  have hstable : (prefixWord ++ tailWord_5711484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711484).length < 2 ^ (prefixWord ++ tailWord_5711484).sum := by decide
  have hdescent : baseEnd_5711484 < baseStart_5711484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711507 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 3, 9]
def baseStart_5711507 : Nat := 118140960795 + 5711507 * 2 ^ 59
def prefixEnd_5711507 : Nat := 4983230072969 + 3 ^ 40 * 5711507 * 2
def baseEnd_5711507 : Nat := 977582784173030145431921

theorem tailTrace_5711507 : CollatzResearch.WordTrace tailWord_5711507 prefixEnd_5711507 977582784173030145431921 := by
  unfold tailWord_5711507
  simp only [CollatzResearch.WordTrace]
  refine ⟨208315774119193061581348775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138877182746128707720899183 208315774119193061581348775)
  ·
    refine ⟨312473661178789592372023163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208315774119193061581348775 312473661178789592372023163)
    ·
      refine ⟨468710491768184388558034745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312473661178789592372023163 468710491768184388558034745)
      ·
        refine ⟨351532868826138291418526059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 468710491768184388558034745 351532868826138291418526059)
        ·
          refine ⟨527299303239207437127789089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351532868826138291418526059 527299303239207437127789089)
          ·
            refine ⟨395474477429405577845841817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 527299303239207437127789089 395474477429405577845841817)
            ·
              refine ⟨296605858072054183384381363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395474477429405577845841817 296605858072054183384381363)
              ·
                refine ⟨444908787108081275076572045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296605858072054183384381363 444908787108081275076572045)
                ·
                  refine ⟨166840795165530478153714517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 444908787108081275076572045 166840795165530478153714517)
                  ·
                    refine ⟨977582784173030145431921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 166840795165530478153714517 977582784173030145431921)
                    ·
                      rfl

theorem cell23_5711507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 9].length) (baseStart_5711507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711507 prefixEnd_5711507 := by exact prefixLift 5711507
  have htrace : WordTrace (prefixWord ++ tailWord_5711507) baseStart_5711507 baseEnd_5711507 := by
    simpa [prefixWord, tailWord_5711507, baseEnd_5711507] using wordTrace_append hprefix tailTrace_5711507
  have hstable : (prefixWord ++ tailWord_5711507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711507).length < 2 ^ (prefixWord ++ tailWord_5711507).sum := by decide
  have hdescent : baseEnd_5711507 < baseStart_5711507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711524 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 2, 7]
def baseStart_5711524 : Nat := 118140960795 + 5711524 * 2 ^ 59
def prefixEnd_5711524 : Nat := 4983230072969 + 3 ^ 40 * 5711524 * 2
def baseEnd_5711524 : Nat := 977585693896738956594395

theorem tailTrace_5711524 : CollatzResearch.WordTrace tailWord_5711524 prefixEnd_5711524 977585693896738956594395 := by
  unfold tailWord_5711524
  simp only [CollatzResearch.WordTrace]
  refine ⟨104158197080065736742358813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138877596106754315656478417 104158197080065736742358813)
  ·
    refine ⟨39059323905024651278384555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104158197080065736742358813 39059323905024651278384555)
    ·
      refine ⟨58588985857536976917576833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39059323905024651278384555 58588985857536976917576833)
      ·
        refine ⟨43941739393152732688182625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58588985857536976917576833 43941739393152732688182625)
        ·
          refine ⟨32956304544864549516136969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43941739393152732688182625 32956304544864549516136969)
          ·
            refine ⟨24717228408648412137102727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32956304544864549516136969 24717228408648412137102727)
            ·
              refine ⟨37075842612972618205654091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24717228408648412137102727 37075842612972618205654091)
              ·
                refine ⟨55613763919458927308481137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37075842612972618205654091 55613763919458927308481137)
                ·
                  refine ⟨41710322939594195481360853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55613763919458927308481137 41710322939594195481360853)
                  ·
                    refine ⟨977585693896738956594395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41710322939594195481360853 977585693896738956594395)
                    ·
                      rfl

theorem cell23_5711524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_5711524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711524 prefixEnd_5711524 := by exact prefixLift 5711524
  have htrace : WordTrace (prefixWord ++ tailWord_5711524) baseStart_5711524 baseEnd_5711524 := by
    simpa [prefixWord, tailWord_5711524, baseEnd_5711524] using wordTrace_append hprefix tailTrace_5711524
  have hstable : (prefixWord ++ tailWord_5711524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711524).length < 2 ^ (prefixWord ++ tailWord_5711524).sum := by decide
  have hdescent : baseEnd_5711524 < baseStart_5711524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711538 : List Nat := [3, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3]
def baseStart_5711538 : Nat := 118140960795 + 5711538 * 2 ^ 59
def prefixEnd_5711538 : Nat := 4983230072969 + 3 ^ 40 * 5711538 * 2
def baseEnd_5711538 : Nat := 2932764270419379815008121

theorem tailTrace_5711538 : CollatzResearch.WordTrace tailWord_5711538 prefixEnd_5711538 2932764270419379815008121 := by
  unfold tailWord_5711538
  simp only [CollatzResearch.WordTrace]
  refine ⟨52079226195520188468931817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138877936521387169250484845 52079226195520188468931817)
  ·
    refine ⟨39059419646640141351698863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52079226195520188468931817 39059419646640141351698863)
    ·
      refine ⟨58589129469960212027548295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39059419646640141351698863 58589129469960212027548295)
      ·
        refine ⟨87883694204940318041322443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58589129469960212027548295 87883694204940318041322443)
        ·
          refine ⟨131825541307410477061983665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87883694204940318041322443 131825541307410477061983665)
          ·
            refine ⟨98869155980557857796487749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131825541307410477061983665 98869155980557857796487749)
            ·
              refine ⟨18537966746354598336841453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98869155980557857796487749 18537966746354598336841453)
              ·
                refine ⟨6951737529882974376315545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18537966746354598336841453 6951737529882974376315545)
                ·
                  refine ⟨5213803147412230782236659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6951737529882974376315545 5213803147412230782236659)
                  ·
                    refine ⟨7820704721118346173354989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5213803147412230782236659 7820704721118346173354989)
                    ·
                      refine ⟨2932764270419379815008121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7820704721118346173354989 2932764270419379815008121)
                      ·
                        rfl

theorem cell23_5711538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_5711538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711538 prefixEnd_5711538 := by exact prefixLift 5711538
  have htrace : WordTrace (prefixWord ++ tailWord_5711538) baseStart_5711538 baseEnd_5711538 := by
    simpa [prefixWord, tailWord_5711538, baseEnd_5711538] using wordTrace_append hprefix tailTrace_5711538
  have hstable : (prefixWord ++ tailWord_5711538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711538).length < 2 ^ (prefixWord ++ tailWord_5711538).sum := by decide
  have hdescent : baseEnd_5711538 < baseStart_5711538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711548 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 3, 3, 2]
def baseStart_5711548 : Nat := 118140960795 + 5711548 * 2 ^ 59
def prefixEnd_5711548 : Nat := 4983230072969 + 3 ^ 40 * 5711548 * 2
def baseEnd_5711548 : Nat := 2932769405225924775883075

theorem tailTrace_5711548 : CollatzResearch.WordTrace tailWord_5711548 prefixEnd_5711548 2932769405225924775883075 := by
  unfold tailWord_5711548
  simp only [CollatzResearch.WordTrace]
  refine ⟨104158634756022262791795649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138878179674696350389060865 104158634756022262791795649)
  ·
    refine ⟨78118976067016697093846737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104158634756022262791795649 78118976067016697093846737)
    ·
      refine ⟨58589232050262522820385053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78118976067016697093846737 58589232050262522820385053)
      ·
        refine ⟨21970962018848446057644395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58589232050262522820385053 21970962018848446057644395)
        ·
          refine ⟨32956443028272669086466593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21970962018848446057644395 32956443028272669086466593)
          ·
            refine ⟨24717332271204501814849945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32956443028272669086466593 24717332271204501814849945)
            ·
              refine ⟨18537999203403376361137459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24717332271204501814849945 18537999203403376361137459)
              ·
                refine ⟨27806998805105064541706189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18537999203403376361137459 27806998805105064541706189)
                ·
                  refine ⟨10427624551914399203139821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27806998805105064541706189 10427624551914399203139821)
                  ·
                    refine ⟨3910359206967899701177433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10427624551914399203139821 3910359206967899701177433)
                    ·
                      refine ⟨2932769405225924775883075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3910359206967899701177433 2932769405225924775883075)
                      ·
                        rfl

theorem cell23_5711548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_5711548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711548 prefixEnd_5711548 := by exact prefixLift 5711548
  have htrace : WordTrace (prefixWord ++ tailWord_5711548) baseStart_5711548 baseEnd_5711548 := by
    simpa [prefixWord, tailWord_5711548, baseEnd_5711548] using wordTrace_append hprefix tailTrace_5711548
  have hstable : (prefixWord ++ tailWord_5711548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711548).length < 2 ^ (prefixWord ++ tailWord_5711548).sum := by decide
  have hdescent : baseEnd_5711548 < baseStart_5711548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711572 : List Nat := [2, 4, 1, 3, 1, 3, 1, 2, 2, 1, 3]
def baseStart_5711572 : Nat := 118140960795 + 5711572 * 2 ^ 59
def prefixEnd_5711572 : Nat := 4983230072969 + 3 ^ 40 * 5711572 * 2
def baseEnd_5711572 : Nat := 2932781728761632681982965

theorem tailTrace_5711572 : CollatzResearch.WordTrace tailWord_5711572 prefixEnd_5711572 2932781728761632681982965 := by
  unfold tailWord_5711572
  simp only [CollatzResearch.WordTrace]
  refine ⟨104159072431978788841232485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138878763242638385121643313 104159072431978788841232485)
  ·
    refine ⟨19529826080996022907731091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104159072431978788841232485 19529826080996022907731091)
    ·
      refine ⟨29294739121494034361596637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19529826080996022907731091 29294739121494034361596637)
      ·
        refine ⟨10985527170560262885598739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29294739121494034361596637 10985527170560262885598739)
        ·
          refine ⟨16478290755840394328398109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10985527170560262885598739 16478290755840394328398109)
          ·
            refine ⟨6179359033440147873149291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16478290755840394328398109 6179359033440147873149291)
            ·
              refine ⟨9269038550160221809723937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6179359033440147873149291 9269038550160221809723937)
              ·
                refine ⟨6951778912620166357292953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9269038550160221809723937 6951778912620166357292953)
                ·
                  refine ⟨5213834184465124767969715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6951778912620166357292953 5213834184465124767969715)
                  ·
                    refine ⟨7820751276697687151954573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5213834184465124767969715 7820751276697687151954573)
                    ·
                      refine ⟨2932781728761632681982965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7820751276697687151954573 2932781728761632681982965)
                      ·
                        rfl

theorem cell23_5711572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_5711572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711572 prefixEnd_5711572 := by exact prefixLift 5711572
  have htrace : WordTrace (prefixWord ++ tailWord_5711572) baseStart_5711572 baseEnd_5711572 := by
    simpa [prefixWord, tailWord_5711572, baseEnd_5711572] using wordTrace_append hprefix tailTrace_5711572
  have hstable : (prefixWord ++ tailWord_5711572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711572).length < 2 ^ (prefixWord ++ tailWord_5711572).sum := by decide
  have hdescent : baseEnd_5711572 < baseStart_5711572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711584 : List Nat := [2, 1, 1, 3, 1, 2, 3, 3, 7]
def baseStart_5711584 : Nat := 118140960795 + 5711584 * 2 ^ 59
def prefixEnd_5711584 : Nat := 4983230072969 + 3 ^ 40 * 5711584 * 2
def baseEnd_5711584 : Nat := 325865321169942959448101

theorem tailTrace_5711584 : CollatzResearch.WordTrace tailWord_5711584 prefixEnd_5711584 325865321169942959448101 := by
  unfold tailWord_5711584
  simp only [CollatzResearch.WordTrace]
  refine ⟨104159291269957051865950903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138879055026609402487934537 104159291269957051865950903)
  ·
    refine ⟨156238936904935577798926355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104159291269957051865950903 156238936904935577798926355)
    ·
      refine ⟨234358405357403366698389533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156238936904935577798926355 234358405357403366698389533)
      ·
        refine ⟨87884402009026262511896075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234358405357403366698389533 87884402009026262511896075)
        ·
          refine ⟨131826603013539393767844113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87884402009026262511896075 131826603013539393767844113)
          ·
            refine ⟨98869952260154545325883085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131826603013539393767844113 98869952260154545325883085)
            ·
              refine ⟨37076232097557954497206157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98869952260154545325883085 37076232097557954497206157)
              ·
                refine ⟨13903587036584232936452309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37076232097557954497206157 13903587036584232936452309)
                ·
                  refine ⟨325865321169942959448101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13903587036584232936452309 325865321169942959448101)
                  ·
                    rfl

theorem cell23_5711584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 7].length) (baseStart_5711584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711584 prefixEnd_5711584 := by exact prefixLift 5711584
  have htrace : WordTrace (prefixWord ++ tailWord_5711584) baseStart_5711584 baseEnd_5711584 := by
    simpa [prefixWord, tailWord_5711584, baseEnd_5711584] using wordTrace_append hprefix tailTrace_5711584
  have hstable : (prefixWord ++ tailWord_5711584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711584).length < 2 ^ (prefixWord ++ tailWord_5711584).sum := by decide
  have hdescent : baseEnd_5711584 < baseStart_5711584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711621 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 3, 7, 2]
def baseStart_5711621 : Nat := 118140960795 + 5711621 * 2 ^ 59
def prefixEnd_5711621 : Nat := 4983230072969 + 3 ^ 40 * 5711621 * 2
def baseEnd_5711621 : Nat := 2932806889313702990270239

theorem tailTrace_5711621 : CollatzResearch.WordTrace tailWord_5711621 prefixEnd_5711621 2932806889313702990270239 := by
  unfold tailWord_5711621
  simp only [CollatzResearch.WordTrace]
  refine ⟨208319932040780059050998717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138879954693853372700665811 208319932040780059050998717)
  ·
    refine ⟨78119974515292522144124519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208319932040780059050998717 78119974515292522144124519)
    ·
      refine ⟨117179961772938783216186779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78119974515292522144124519 117179961772938783216186779)
      ·
        refine ⟨175769942659408174824280169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117179961772938783216186779 175769942659408174824280169)
        ·
          refine ⟨131827456994556131118210127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175769942659408174824280169 131827456994556131118210127)
          ·
            refine ⟨197741185491834196677315191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131827456994556131118210127 197741185491834196677315191)
            ·
              refine ⟨296611778237751295015972787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197741185491834196677315191 296611778237751295015972787)
              ·
                refine ⟨444917667356626942523959181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296611778237751295015972787 444917667356626942523959181)
                ·
                  refine ⟨166844125258735103446484693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 444917667356626942523959181 166844125258735103446484693)
                  ·
                    refine ⟨3910409185751603987026985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 166844125258735103446484693 3910409185751603987026985)
                    ·
                      refine ⟨2932806889313702990270239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3910409185751603987026985 2932806889313702990270239)
                      ·
                        rfl

theorem cell23_5711621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 7, 2].length) (baseStart_5711621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711621 prefixEnd_5711621 := by exact prefixLift 5711621
  have htrace : WordTrace (prefixWord ++ tailWord_5711621) baseStart_5711621 baseEnd_5711621 := by
    simpa [prefixWord, tailWord_5711621, baseEnd_5711621] using wordTrace_append hprefix tailTrace_5711621
  have hstable : (prefixWord ++ tailWord_5711621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711621).length < 2 ^ (prefixWord ++ tailWord_5711621).sum := by decide
  have hdescent : baseEnd_5711621 < baseStart_5711621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711646 : List Nat := [4, 3, 2, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_5711646 : Nat := 118140960795 + 5711646 * 2 ^ 59
def prefixEnd_5711646 : Nat := 4983230072969 + 3 ^ 40 * 5711646 * 2
def baseEnd_5711646 : Nat := 2932819726330065392457625

theorem tailTrace_5711646 : CollatzResearch.WordTrace tailWord_5711646 prefixEnd_5711646 2932819726330065392457625 := by
  unfold tailWord_5711646
  simp only [CollatzResearch.WordTrace]
  refine ⟨26040105483211186040082349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138880562577126325547105861 26040105483211186040082349)
  ·
    refine ⟨9765039556204194765030881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26040105483211186040082349 9765039556204194765030881)
    ·
      refine ⟨7323779667153146073773161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9765039556204194765030881 7323779667153146073773161)
      ·
        refine ⟨5492834750364859555329871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7323779667153146073773161 5492834750364859555329871)
        ·
          refine ⟨8239252125547289332994807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5492834750364859555329871 8239252125547289332994807)
          ·
            refine ⟨12358878188320933999492211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8239252125547289332994807 12358878188320933999492211)
            ·
              refine ⟨18538317282481400999238317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12358878188320933999492211 18538317282481400999238317)
              ·
                refine ⟨6951868980930525374714369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18538317282481400999238317 6951868980930525374714369)
                ·
                  refine ⟨5213901735697894031035777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6951868980930525374714369 5213901735697894031035777)
                  ·
                    refine ⟨3910426301773420523276833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5213901735697894031035777 3910426301773420523276833)
                    ·
                      refine ⟨2932819726330065392457625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3910426301773420523276833 2932819726330065392457625)
                      ·
                        rfl

theorem cell23_5711646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_5711646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711646 prefixEnd_5711646 := by exact prefixLift 5711646
  have htrace : WordTrace (prefixWord ++ tailWord_5711646) baseStart_5711646 baseEnd_5711646 := by
    simpa [prefixWord, tailWord_5711646, baseEnd_5711646] using wordTrace_append hprefix tailTrace_5711646
  have hstable : (prefixWord ++ tailWord_5711646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711646).length < 2 ^ (prefixWord ++ tailWord_5711646).sum := by decide
  have hdescent : baseEnd_5711646 < baseStart_5711646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711664 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 6]
def baseStart_5711664 : Nat := 118140960795 + 5711664 * 2 ^ 59
def prefixEnd_5711664 : Nat := 4983230072969 + 3 ^ 40 * 5711664 * 2
def baseEnd_5711664 : Nat := 2932828968981846322032541

theorem tailTrace_5711664 : CollatzResearch.WordTrace tailWord_5711664 prefixEnd_5711664 2932828968981846322032541 := by
  unfold tailWord_5711664
  simp only [CollatzResearch.WordTrace]
  refine ⟨104160750189812138697407023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138881000253082851596542697 104160750189812138697407023)
  ·
    refine ⟨156241125284718208046110535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104160750189812138697407023 156241125284718208046110535)
    ·
      refine ⟨234361687927077312069165803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156241125284718208046110535 234361687927077312069165803)
      ·
        refine ⟨351542531890615968103748705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234361687927077312069165803 351542531890615968103748705)
        ·
          refine ⟨263656898917961976077811529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351542531890615968103748705 263656898917961976077811529)
          ·
            refine ⟨197742674188471482058358647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263656898917961976077811529 197742674188471482058358647)
            ·
              refine ⟨296614011282707223087537971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197742674188471482058358647 296614011282707223087537971)
              ·
                refine ⟨444921016924060834631306957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296614011282707223087537971 444921016924060834631306957)
                ·
                  refine ⟨166845381346522812986740109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 444921016924060834631306957 166845381346522812986740109)
                  ·
                    refine ⟨62567018004946054870027541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 166845381346522812986740109 62567018004946054870027541)
                    ·
                      refine ⟨2932828968981846322032541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62567018004946054870027541 2932828968981846322032541)
                      ·
                        rfl

theorem cell23_5711664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_5711664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711664 prefixEnd_5711664 := by exact prefixLift 5711664
  have htrace : WordTrace (prefixWord ++ tailWord_5711664) baseStart_5711664 baseEnd_5711664 := by
    simpa [prefixWord, tailWord_5711664, baseEnd_5711664] using wordTrace_append hprefix tailTrace_5711664
  have hstable : (prefixWord ++ tailWord_5711664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711664).length < 2 ^ (prefixWord ++ tailWord_5711664).sum := by decide
  have hdescent : baseEnd_5711664 < baseStart_5711664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711688 : List Nat := [2, 1, 3, 1, 1, 4, 2, 2, 2, 2, 3]
def baseStart_5711688 : Nat := 118140960795 + 5711688 * 2 ^ 59
def prefixEnd_5711688 : Nat := 4983230072969 + 3 ^ 40 * 5711688 * 2
def baseEnd_5711688 : Nat := 2932841292517554228132431

theorem tailTrace_5711688 : CollatzResearch.WordTrace tailWord_5711688 prefixEnd_5711688 2932841292517554228132431 := by
  unfold tailWord_5711688
  simp only [CollatzResearch.WordTrace]
  refine ⟨104161187865768664746843859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138881583821024886329125145 104161187865768664746843859)
  ·
    refine ⟨156241781798652997120265789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104161187865768664746843859 156241781798652997120265789)
    ·
      refine ⟨58590668174494873920099671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156241781798652997120265789 58590668174494873920099671)
      ·
        refine ⟨87886002261742310880149507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58590668174494873920099671 87886002261742310880149507)
        ·
          refine ⟨131829003392613466320224261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87886002261742310880149507 131829003392613466320224261)
          ·
            refine ⟨24717938136115024935042049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131829003392613466320224261 24717938136115024935042049)
            ·
              refine ⟨18538453602086268701281537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24717938136115024935042049 18538453602086268701281537)
              ·
                refine ⟨13903840201564701525961153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18538453602086268701281537 13903840201564701525961153)
                ·
                  refine ⟨10427880151173526144470865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13903840201564701525961153 10427880151173526144470865)
                  ·
                    refine ⟨7820910113380144608353149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10427880151173526144470865 7820910113380144608353149)
                    ·
                      refine ⟨2932841292517554228132431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7820910113380144608353149 2932841292517554228132431)
                      ·
                        rfl

theorem cell23_5711688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_5711688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711688 prefixEnd_5711688 := by exact prefixLift 5711688
  have htrace : WordTrace (prefixWord ++ tailWord_5711688) baseStart_5711688 baseEnd_5711688 := by
    simpa [prefixWord, tailWord_5711688, baseEnd_5711688] using wordTrace_append hprefix tailTrace_5711688
  have hstable : (prefixWord ++ tailWord_5711688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711688).length < 2 ^ (prefixWord ++ tailWord_5711688).sum := by decide
  have hdescent : baseEnd_5711688 < baseStart_5711688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711742 : List Nat := [4, 2, 3, 1, 1, 3, 1, 2, 6]
def baseStart_5711742 : Nat := 118140960795 + 5711742 * 2 ^ 59
def prefixEnd_5711742 : Nat := 4983230072969 + 3 ^ 40 * 5711742 * 2
def baseEnd_5711742 : Nat := 325874335608099668539687

theorem tailTrace_5711742 : CollatzResearch.WordTrace tailWord_5711742 prefixEnd_5711742 325874335608099668539687 := by
  unfold tailWord_5711742
  simp only [CollatzResearch.WordTrace]
  refine ⟨26040543159167712089519185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138882896848894464477435653 26040543159167712089519185)
  ·
    refine ⟨19530407369375784067139389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26040543159167712089519185 19530407369375784067139389)
    ·
      refine ⟨7323902763515919025177271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19530407369375784067139389 7323902763515919025177271)
      ·
        refine ⟨10985854145273878537765907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7323902763515919025177271 10985854145273878537765907)
        ·
          refine ⟨16478781217910817806648861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10985854145273878537765907 16478781217910817806648861)
          ·
            refine ⟨6179542956716556677493323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16478781217910817806648861 6179542956716556677493323)
            ·
              refine ⟨9269314435074835016239985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6179542956716556677493323 9269314435074835016239985)
              ·
                refine ⟨6951985826306126262179989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9269314435074835016239985 6951985826306126262179989)
                ·
                  refine ⟨325874335608099668539687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6951985826306126262179989 325874335608099668539687)
                  ·
                    rfl

theorem cell23_5711742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_5711742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711742 prefixEnd_5711742 := by exact prefixLift 5711742
  have htrace : WordTrace (prefixWord ++ tailWord_5711742) baseStart_5711742 baseEnd_5711742 := by
    simpa [prefixWord, tailWord_5711742, baseEnd_5711742] using wordTrace_append hprefix tailTrace_5711742
  have hstable : (prefixWord ++ tailWord_5711742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711742).length < 2 ^ (prefixWord ++ tailWord_5711742).sum := by decide
  have hdescent : baseEnd_5711742 < baseStart_5711742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711752 : List Nat := [2, 1, 3, 3, 3, 1, 2, 1, 3, 1, 3]
def baseStart_5711752 : Nat := 118140960795 + 5711752 * 2 ^ 59
def prefixEnd_5711752 : Nat := 4983230072969 + 3 ^ 40 * 5711752 * 2
def baseEnd_5711752 : Nat := 2932874155279441977732137

theorem tailTrace_5711752 : CollatzResearch.WordTrace tailWord_5711752 prefixEnd_5711752 2932874155279441977732137 := by
  unfold tailWord_5711752
  simp only [CollatzResearch.WordTrace]
  refine ⟨104162355001652734212008755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138883140002203645616011673 104162355001652734212008755)
  ·
    refine ⟨156243532502479101318013133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104162355001652734212008755 156243532502479101318013133)
    ·
      refine ⟨58591324688429662994254925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156243532502479101318013133 58591324688429662994254925)
      ·
        refine ⟨21971746758161123622845597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58591324688429662994254925 21971746758161123622845597)
        ·
          refine ⟨8239405034310421358567099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21971746758161123622845597 8239405034310421358567099)
          ·
            refine ⟨12359107551465632037850649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8239405034310421358567099 12359107551465632037850649)
            ·
              refine ⟨9269330663599224028387987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12359107551465632037850649 9269330663599224028387987)
              ·
                refine ⟨13903995995398836042581981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9269330663599224028387987 13903995995398836042581981)
                ·
                  refine ⟨5213998498274563515968243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13903995995398836042581981 5213998498274563515968243)
                  ·
                    refine ⟨7820997747411845273952365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5213998498274563515968243 7820997747411845273952365)
                    ·
                      refine ⟨2932874155279441977732137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7820997747411845273952365 2932874155279441977732137)
                      ·
                        rfl

theorem cell23_5711752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_5711752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711752 prefixEnd_5711752 := by exact prefixLift 5711752
  have htrace : WordTrace (prefixWord ++ tailWord_5711752) baseStart_5711752 baseEnd_5711752 := by
    simpa [prefixWord, tailWord_5711752, baseEnd_5711752] using wordTrace_append hprefix tailTrace_5711752
  have hstable : (prefixWord ++ tailWord_5711752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711752).length < 2 ^ (prefixWord ++ tailWord_5711752).sum := by decide
  have hdescent : baseEnd_5711752 < baseStart_5711752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711761 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 5]
def baseStart_5711761 : Nat := 118140960795 + 5711761 * 2 ^ 59
def prefixEnd_5711761 : Nat := 4983230072969 + 3 ^ 40 * 5711761 * 2
def baseEnd_5711761 : Nat := 2932878776605332442519595

theorem tailTrace_5711761 : CollatzResearch.WordTrace tailWord_5711761 prefixEnd_5711761 2932878776605332442519595 := by
  unfold tailWord_5711761
  simp only [CollatzResearch.WordTrace]
  refine ⟨208325038260272862961095137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138883358840181908640730091 208325038260272862961095137)
  ·
    refine ⟨156243778695204647220821353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208325038260272862961095137 156243778695204647220821353)
    ·
      refine ⟨117182834021403485415616015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156243778695204647220821353 117182834021403485415616015)
      ·
        refine ⟨175774251032105228123424023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117182834021403485415616015 175774251032105228123424023)
        ·
          refine ⟨263661376548157842185136035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175774251032105228123424023 263661376548157842185136035)
          ·
            refine ⟨395492064822236763277704053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263661376548157842185136035 395492064822236763277704053)
            ·
              refine ⟨37077381077084696557284755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 395492064822236763277704053 37077381077084696557284755)
              ·
                refine ⟨55616071615627044835927133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37077381077084696557284755 55616071615627044835927133)
                ·
                  refine ⟨20856026855860141813472675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55616071615627044835927133 20856026855860141813472675)
                  ·
                    refine ⟨31284040283790212720209013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20856026855860141813472675 31284040283790212720209013)
                    ·
                      refine ⟨2932878776605332442519595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31284040283790212720209013 2932878776605332442519595)
                      ·
                        rfl

theorem cell23_5711761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_5711761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711761 prefixEnd_5711761 := by exact prefixLift 5711761
  have htrace : WordTrace (prefixWord ++ tailWord_5711761) baseStart_5711761 baseEnd_5711761 := by
    simpa [prefixWord, tailWord_5711761, baseEnd_5711761] using wordTrace_append hprefix tailTrace_5711761
  have hstable : (prefixWord ++ tailWord_5711761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711761).length < 2 ^ (prefixWord ++ tailWord_5711761).sum := by decide
  have hdescent : baseEnd_5711761 < baseStart_5711761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711868 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 1, 6, 3]
def baseStart_5711868 : Nat := 118140960795 + 5711868 * 2 ^ 59
def prefixEnd_5711868 : Nat := 4983230072969 + 3 ^ 40 * 5711868 * 2
def baseEnd_5711868 : Nat := 2932933719035363523881603

theorem tailTrace_5711868 : CollatzResearch.WordTrace tailWord_5711868 prefixEnd_5711868 2932933719035363523881603 := by
  unfold tailWord_5711868
  simp only [CollatzResearch.WordTrace]
  refine ⟨104164470435442610117620129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138885960580590146823493505 104164470435442610117620129)
  ·
    refine ⟨78123352826581957588215097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104164470435442610117620129 78123352826581957588215097)
    ·
      refine ⟨58592514619936468191161323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78123352826581957588215097 58592514619936468191161323)
      ·
        refine ⟨87888771929904702286741985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58592514619936468191161323 87888771929904702286741985)
        ·
          refine ⟨65916578947428526715056489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87888771929904702286741985 65916578947428526715056489)
          ·
            refine ⟨49437434210571395036292367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65916578947428526715056489 49437434210571395036292367)
            ·
              refine ⟨74156151315857092554438551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49437434210571395036292367 74156151315857092554438551)
              ·
                refine ⟨111234226973785638831657827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74156151315857092554438551 111234226973785638831657827)
                ·
                  refine ⟨166851340460678458247486741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111234226973785638831657827 166851340460678458247486741)
                  ·
                    refine ⟨7821156584094302730350941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 166851340460678458247486741 7821156584094302730350941)
                    ·
                      refine ⟨2932933719035363523881603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7821156584094302730350941 2932933719035363523881603)
                      ·
                        rfl

theorem cell23_5711868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_5711868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711868 prefixEnd_5711868 := by exact prefixLift 5711868
  have htrace : WordTrace (prefixWord ++ tailWord_5711868) baseStart_5711868 baseEnd_5711868 := by
    simpa [prefixWord, tailWord_5711868, baseEnd_5711868] using wordTrace_append hprefix tailTrace_5711868
  have hstable : (prefixWord ++ tailWord_5711868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711868).length < 2 ^ (prefixWord ++ tailWord_5711868).sum := by decide
  have hdescent : baseEnd_5711868 < baseStart_5711868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711871 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 11]
def baseStart_5711871 : Nat := 118140960795 + 5711871 * 2 ^ 59
def prefixEnd_5711871 : Nat := 4983230072969 + 3 ^ 40 * 5711871 * 2
def baseEnd_5711871 : Nat := 325881695497480779127121

theorem tailTrace_5711871 : CollatzResearch.WordTrace tailWord_5711871 prefixEnd_5711871 325881695497480779127121 := by
  unfold tailWord_5711871
  simp only [CollatzResearch.WordTrace]
  refine ⟨208329050289874351747599467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138886033526582901165066311 208329050289874351747599467)
  ·
    refine ⟨312493575434811527621399201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208329050289874351747599467 312493575434811527621399201)
    ·
      refine ⟨234370181576108645716049401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312493575434811527621399201 234370181576108645716049401)
      ·
        refine ⟨175777636182081484287037051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234370181576108645716049401 175777636182081484287037051)
        ·
          refine ⟨263666454273122226430555577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175777636182081484287037051 263666454273122226430555577)
          ·
            refine ⟨197749840704841669822916683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263666454273122226430555577 197749840704841669822916683)
            ·
              refine ⟨296624761057262504734375025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197749840704841669822916683 296624761057262504734375025)
              ·
                refine ⟨222468570792946878550781269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296624761057262504734375025 222468570792946878550781269)
                ·
                  refine ⟨325881695497480779127121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 222468570792946878550781269 325881695497480779127121)
                  ·
                    rfl

theorem cell23_5711871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 11].length) (baseStart_5711871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711871 prefixEnd_5711871 := by exact prefixLift 5711871
  have htrace : WordTrace (prefixWord ++ tailWord_5711871) baseStart_5711871 baseEnd_5711871 := by
    simpa [prefixWord, tailWord_5711871, baseEnd_5711871] using wordTrace_append hprefix tailTrace_5711871
  have hstable : (prefixWord ++ tailWord_5711871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711871).length < 2 ^ (prefixWord ++ tailWord_5711871).sum := by decide
  have hdescent : baseEnd_5711871 < baseStart_5711871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5711925 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 1, 7, 2]
def baseStart_5711925 : Nat := 118140960795 + 5711925 * 2 ^ 59
def prefixEnd_5711925 : Nat := 4983230072969 + 3 ^ 40 * 5711925 * 2
def baseEnd_5711925 : Nat := 2932962987432669800868841

theorem tailTrace_5711925 : CollatzResearch.WordTrace tailWord_5711925 prefixEnd_5711925 2932962987432669800868841 := by
  unfold tailWord_5711925
  simp only [CollatzResearch.WordTrace]
  refine ⟨208331019831678718970065229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138887346554452479313376819 208331019831678718970065229)
  ·
    refine ⟨78124132436879519613774461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208331019831678718970065229 78124132436879519613774461)
    ·
      refine ⟨29296549663829819855165423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78124132436879519613774461 29296549663829819855165423)
      ·
        refine ⟨43944824495744729782748135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29296549663829819855165423 43944824495744729782748135)
        ·
          refine ⟨65917236743617094674122203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43944824495744729782748135 65917236743617094674122203)
          ·
            refine ⟨98875855115425642011183305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65917236743617094674122203 98875855115425642011183305)
            ·
              refine ⟨74156891336569231508387479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98875855115425642011183305 74156891336569231508387479)
              ·
                refine ⟨111235337004853847262581219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74156891336569231508387479 111235337004853847262581219)
                ·
                  refine ⟨166853005507280770893871829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111235337004853847262581219 166853005507280770893871829)
                  ·
                    refine ⟨3910617316576893067825121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 166853005507280770893871829 3910617316576893067825121)
                    ·
                      refine ⟨2932962987432669800868841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3910617316576893067825121 2932962987432669800868841)
                      ·
                        rfl

theorem cell23_5711925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_5711925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5711925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5711925 prefixEnd_5711925 := by exact prefixLift 5711925
  have htrace : WordTrace (prefixWord ++ tailWord_5711925) baseStart_5711925 baseEnd_5711925 := by
    simpa [prefixWord, tailWord_5711925, baseEnd_5711925] using wordTrace_append hprefix tailTrace_5711925
  have hstable : (prefixWord ++ tailWord_5711925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5711925).length < 2 ^ (prefixWord ++ tailWord_5711925).sum := by decide
  have hdescent : baseEnd_5711925 < baseStart_5711925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5711925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712025 : List Nat := [1, 2, 1, 2, 1, 2, 1, 7, 1, 5]
def baseStart_5712025 : Nat := 118140960795 + 5712025 * 2 ^ 59
def prefixEnd_5712025 : Nat := 4983230072969 + 3 ^ 40 * 5712025 * 2
def baseEnd_5712025 : Nat := 977671445166039803206127

theorem tailTrace_5712025 : CollatzResearch.WordTrace tailWord_5712025 prefixEnd_5712025 977671445166039803206127 := by
  unfold tailWord_5712025
  simp only [CollatzResearch.WordTrace]
  refine ⟨208334667131316436048705529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138889778087544290699137019 208334667131316436048705529)
  ·
    refine ⟨156251000348487327036529147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208334667131316436048705529 156251000348487327036529147)
    ·
      refine ⟨234376500522730990554793721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156251000348487327036529147 234376500522730990554793721)
      ·
        refine ⟨175782375392048242916095291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234376500522730990554793721 175782375392048242916095291)
        ·
          refine ⟨263673563088072364374142937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175782375392048242916095291 263673563088072364374142937)
          ·
            refine ⟨197755172316054273280607203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263673563088072364374142937 197755172316054273280607203)
            ·
              refine ⟨296632758474081409920910805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197755172316054273280607203 296632758474081409920910805)
              ·
                refine ⟨6952330276736283045021347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 296632758474081409920910805 6952330276736283045021347)
                ·
                  refine ⟨10428495415104424567532021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6952330276736283045021347 10428495415104424567532021)
                  ·
                    refine ⟨977671445166039803206127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10428495415104424567532021 977671445166039803206127)
                    ·
                      rfl

theorem cell23_5712025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 5].length) (baseStart_5712025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712025 prefixEnd_5712025 := by exact prefixLift 5712025
  have htrace : WordTrace (prefixWord ++ tailWord_5712025) baseStart_5712025 baseEnd_5712025 := by
    simpa [prefixWord, tailWord_5712025, baseEnd_5712025] using wordTrace_append hprefix tailTrace_5712025
  have hstable : (prefixWord ++ tailWord_5712025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712025).length < 2 ^ (prefixWord ++ tailWord_5712025).sum := by decide
  have hdescent : baseEnd_5712025 < baseStart_5712025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712055 : List Nat := [1, 1, 3, 1, 4, 2, 1, 3, 1, 6]
def baseStart_5712055 : Nat := 118140960795 + 5712055 * 2 ^ 59
def prefixEnd_5712055 : Nat := 4983230072969 + 3 ^ 40 * 5712055 * 2
def baseEnd_5712055 : Nat := 977676579972584764081081

theorem tailTrace_5712055 : CollatzResearch.WordTrace tailWord_5712055 prefixEnd_5712055 977676579972584764081081 := by
  unfold tailWord_5712055
  simp only [CollatzResearch.WordTrace]
  refine ⟨208335761321207751172297619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138890507547471834114865079 208335761321207751172297619)
  ·
    refine ⟨312503641981811626758446429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208335761321207751172297619 312503641981811626758446429)
    ·
      refine ⟨117188865743179360034417411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312503641981811626758446429 117188865743179360034417411)
      ·
        refine ⟨175783298614769040051626117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117188865743179360034417411 175783298614769040051626117)
        ·
          refine ⟨32959368490269195009679897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175783298614769040051626117 32959368490269195009679897)
          ·
            refine ⟨24719526367701896257259923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32959368490269195009679897 24719526367701896257259923)
            ·
              refine ⟨37079289551552844385889885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24719526367701896257259923 37079289551552844385889885)
              ·
                refine ⟨13904733581832316644708707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37079289551552844385889885 13904733581832316644708707)
                ·
                  refine ⟨20857100372748474967063061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13904733581832316644708707 20857100372748474967063061)
                  ·
                    refine ⟨977676579972584764081081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20857100372748474967063061 977676579972584764081081)
                    ·
                      rfl

theorem cell23_5712055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_5712055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712055 prefixEnd_5712055 := by exact prefixLift 5712055
  have htrace : WordTrace (prefixWord ++ tailWord_5712055) baseStart_5712055 baseEnd_5712055 := by
    simpa [prefixWord, tailWord_5712055, baseEnd_5712055] using wordTrace_append hprefix tailTrace_5712055
  have hstable : (prefixWord ++ tailWord_5712055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712055).length < 2 ^ (prefixWord ++ tailWord_5712055).sum := by decide
  have hdescent : baseEnd_5712055 < baseStart_5712055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712075 : List Nat := [1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 4]
def baseStart_5712075 : Nat := 118140960795 + 5712075 * 2 ^ 59
def prefixEnd_5712075 : Nat := 4983230072969 + 3 ^ 40 * 5712075 * 2
def baseEnd_5712075 : Nat := 2933040009530844213993151

theorem tailTrace_5712075 : CollatzResearch.WordTrace tailWord_5712075 prefixEnd_5712075 2933040009530844213993151 := by
  unfold tailWord_5712075
  simp only [CollatzResearch.WordTrace]
  refine ⟨208336490781135294588025679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138890993854090196392017119 208336490781135294588025679)
  ·
    refine ⟨312504736171702941882038519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208336490781135294588025679 312504736171702941882038519)
    ·
      refine ⟨468757104257554412823057779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312504736171702941882038519 468757104257554412823057779)
      ·
        refine ⟨703135656386331619234586669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468757104257554412823057779 703135656386331619234586669)
        ·
          refine ⟨263675871144874357212970001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 703135656386331619234586669 263675871144874357212970001)
          ·
            refine ⟨197756903358655767909727501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263675871144874357212970001 197756903358655767909727501)
            ·
              refine ⟨74158838759495912966147813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197756903358655767909727501 74158838759495912966147813)
              ·
                refine ⟨13904782267405483681152715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74158838759495912966147813 13904782267405483681152715)
                ·
                  refine ⟨20857173401108225521729073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13904782267405483681152715 20857173401108225521729073)
                  ·
                    refine ⟨15642880050831169141296805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20857173401108225521729073 15642880050831169141296805)
                    ·
                      refine ⟨2933040009530844213993151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15642880050831169141296805 2933040009530844213993151)
                      ·
                        rfl

theorem cell23_5712075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 4].length) (baseStart_5712075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712075 prefixEnd_5712075 := by exact prefixLift 5712075
  have htrace : WordTrace (prefixWord ++ tailWord_5712075) baseStart_5712075 baseEnd_5712075 := by
    simpa [prefixWord, tailWord_5712075, baseEnd_5712075] using wordTrace_append hprefix tailTrace_5712075
  have hstable : (prefixWord ++ tailWord_5712075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712075).length < 2 ^ (prefixWord ++ tailWord_5712075).sum := by decide
  have hdescent : baseEnd_5712075 < baseStart_5712075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712096 : List Nat := [2, 1, 1, 3, 1, 3, 1, 6, 1, 2, 2]
def baseStart_5712096 : Nat := 118140960795 + 5712096 * 2 ^ 59
def prefixEnd_5712096 : Nat := 4983230072969 + 3 ^ 40 * 5712096 * 2
def baseEnd_5712096 : Nat := 2933050792624588631830555

theorem tailTrace_5712096 : CollatzResearch.WordTrace tailWord_5712096 prefixEnd_5712096 2933050792624588631830555 := by
  unfold tailWord_5712096
  simp only [CollatzResearch.WordTrace]
  refine ⟨104168628357029607587270071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138891504476039476783026761 104168628357029607587270071)
  ·
    refine ⟨156252942535544411380905107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104168628357029607587270071 156252942535544411380905107)
    ·
      refine ⟨234379413803316617071357661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156252942535544411380905107 234379413803316617071357661)
      ·
        refine ⟨87892280176243731401759123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234379413803316617071357661 87892280176243731401759123)
        ·
          refine ⟨131838420264365597102638685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87892280176243731401759123 131838420264365597102638685)
          ·
            refine ⟨49439407599137098913489507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131838420264365597102638685 49439407599137098913489507)
            ·
              refine ⟨74159111398705648370234261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49439407599137098913489507 74159111398705648370234261)
              ·
                refine ⟨3476208346814327267354731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74159111398705648370234261 3476208346814327267354731)
                ·
                  refine ⟨5214312520221490901032097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3476208346814327267354731 5214312520221490901032097)
                  ·
                    refine ⟨3910734390166118175774073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5214312520221490901032097 3910734390166118175774073)
                    ·
                      refine ⟨2933050792624588631830555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3910734390166118175774073 2933050792624588631830555)
                      ·
                        rfl

theorem cell23_5712096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 1, 2, 2].length) (baseStart_5712096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712096 prefixEnd_5712096 := by exact prefixLift 5712096
  have htrace : WordTrace (prefixWord ++ tailWord_5712096) baseStart_5712096 baseEnd_5712096 := by
    simpa [prefixWord, tailWord_5712096, baseEnd_5712096] using wordTrace_append hprefix tailTrace_5712096
  have hstable : (prefixWord ++ tailWord_5712096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712096).length < 2 ^ (prefixWord ++ tailWord_5712096).sum := by decide
  have hdescent : baseEnd_5712096 < baseStart_5712096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712099 : List Nat := [1, 1, 1, 8, 1, 1, 1, 2, 1, 1, 5]
def baseStart_5712099 : Nat := 118140960795 + 5712099 * 2 ^ 59
def prefixEnd_5712099 : Nat := 4983230072969 + 3 ^ 40 * 5712099 * 2
def baseEnd_5712099 : Nat := 2933052333066552120093041

theorem tailTrace_5712099 : CollatzResearch.WordTrace tailWord_5712099 prefixEnd_5712099 2933052333066552120093041 := by
  unfold tailWord_5712099
  simp only [CollatzResearch.WordTrace]
  refine ⟨208337366133048346686899351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138891577422032231124599567 208337366133048346686899351)
  ·
    refine ⟨312506049199572520030349027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208337366133048346686899351 312506049199572520030349027)
    ·
      refine ⟨468759073799358780045523541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312506049199572520030349027 468759073799358780045523541)
      ·
        refine ⟨5493270396086235703658479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 468759073799358780045523541 5493270396086235703658479)
        ·
          refine ⟨8239905594129353555487719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5493270396086235703658479 8239905594129353555487719)
          ·
            refine ⟨12359858391194030333231579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8239905594129353555487719 12359858391194030333231579)
            ·
              refine ⟨18539787586791045499847369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12359858391194030333231579 18539787586791045499847369)
              ·
                refine ⟨13904840690093284124885527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18539787586791045499847369 13904840690093284124885527)
                ·
                  refine ⟨20857261035139926187328291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13904840690093284124885527 20857261035139926187328291)
                  ·
                    refine ⟨31285891552709889280992437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20857261035139926187328291 31285891552709889280992437)
                    ·
                      refine ⟨2933052333066552120093041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31285891552709889280992437 2933052333066552120093041)
                      ·
                        rfl

theorem cell23_5712099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_5712099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712099 prefixEnd_5712099 := by exact prefixLift 5712099
  have htrace : WordTrace (prefixWord ++ tailWord_5712099) baseStart_5712099 baseEnd_5712099 := by
    simpa [prefixWord, tailWord_5712099, baseEnd_5712099] using wordTrace_append hprefix tailTrace_5712099
  have hstable : (prefixWord ++ tailWord_5712099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712099).length < 2 ^ (prefixWord ++ tailWord_5712099).sum := by decide
  have hdescent : baseEnd_5712099 < baseStart_5712099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712130 : List Nat := [3, 4, 1, 1, 2, 1, 3, 3, 1, 2, 2]
def baseStart_5712130 : Nat := 118140960795 + 5712130 * 2 ^ 59
def prefixEnd_5712130 : Nat := 4983230072969 + 3 ^ 40 * 5712130 * 2
def baseEnd_5712130 : Nat := 2933068250966841498805399

theorem tailTrace_5712130 : CollatzResearch.WordTrace tailWord_5712130 prefixEnd_5712130 2933068250966841498805399 := by
  unfold tailWord_5712130
  simp only [CollatzResearch.WordTrace]
  refine ⟨52084624198984009745319461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138892331197290692654185229 52084624198984009745319461)
  ·
    refine ⟨9765867037309501827247399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52084624198984009745319461 9765867037309501827247399)
    ·
      refine ⟨14648800555964252740871099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9765867037309501827247399 14648800555964252740871099)
      ·
        refine ⟨21973200833946379111306649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14648800555964252740871099 21973200833946379111306649)
        ·
          refine ⟨16479900625459784333479987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21973200833946379111306649 16479900625459784333479987)
          ·
            refine ⟨24719850938189676500219981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16479900625459784333479987 24719850938189676500219981)
            ·
              refine ⟨9269944101821128687582493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24719850938189676500219981 9269944101821128687582493)
              ·
                refine ⟨3476229038182923257843435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9269944101821128687582493 3476229038182923257843435)
                ·
                  refine ⟨5214343557274384886765153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3476229038182923257843435 5214343557274384886765153)
                  ·
                    refine ⟨3910757667955788665073865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5214343557274384886765153 3910757667955788665073865)
                    ·
                      refine ⟨2933068250966841498805399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3910757667955788665073865 2933068250966841498805399)
                      ·
                        rfl

theorem cell23_5712130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_5712130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712130 prefixEnd_5712130 := by exact prefixLift 5712130
  have htrace : WordTrace (prefixWord ++ tailWord_5712130) baseStart_5712130 baseEnd_5712130 := by
    simpa [prefixWord, tailWord_5712130, baseEnd_5712130] using wordTrace_append hprefix tailTrace_5712130
  have hstable : (prefixWord ++ tailWord_5712130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712130).length < 2 ^ (prefixWord ++ tailWord_5712130).sum := by decide
  have hdescent : baseEnd_5712130 < baseStart_5712130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712139 : List Nat := [1, 1, 1, 1, 5, 2, 1, 5, 1, 3, 2]
def baseStart_5712139 : Nat := 118140960795 + 5712139 * 2 ^ 59
def prefixEnd_5712139 : Nat := 4983230072969 + 3 ^ 40 * 5712139 * 2
def baseEnd_5712139 : Nat := 2933072872292731963592857

theorem tailTrace_5712139 : CollatzResearch.WordTrace tailWord_5712139 prefixEnd_5712139 2933072872292731963592857 := by
  unfold tailWord_5712139
  simp only [CollatzResearch.WordTrace]
  refine ⟨208338825052903433518355471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138892550035268955678903647 208338825052903433518355471)
  ·
    refine ⟨312508237579355150277533207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208338825052903433518355471 312508237579355150277533207)
    ·
      refine ⟨468762356369032725416299811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312508237579355150277533207 468762356369032725416299811)
      ·
        refine ⟨703143534553549088124449717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468762356369032725416299811 703143534553549088124449717)
        ·
          refine ⟨65919706364395227011667161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 703143534553549088124449717 65919706364395227011667161)
          ·
            refine ⟨49439779773296420258750371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65919706364395227011667161 49439779773296420258750371)
            ·
              refine ⟨74159669659944630388125557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49439779773296420258750371 74159669659944630388125557)
              ·
                refine ⟨6952469030619809098886771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74159669659944630388125557 6952469030619809098886771)
                ·
                  refine ⟨10428703545929713648330157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6952469030619809098886771 10428703545929713648330157)
                  ·
                    refine ⟨3910763829723642618123809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10428703545929713648330157 3910763829723642618123809)
                    ·
                      refine ⟨2933072872292731963592857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3910763829723642618123809 2933072872292731963592857)
                      ·
                        rfl

theorem cell23_5712139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 3, 2].length) (baseStart_5712139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712139 prefixEnd_5712139 := by exact prefixLift 5712139
  have htrace : WordTrace (prefixWord ++ tailWord_5712139) baseStart_5712139 baseEnd_5712139 := by
    simpa [prefixWord, tailWord_5712139, baseEnd_5712139] using wordTrace_append hprefix tailTrace_5712139
  have hstable : (prefixWord ++ tailWord_5712139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712139).length < 2 ^ (prefixWord ++ tailWord_5712139).sum := by decide
  have hdescent : baseEnd_5712139 < baseStart_5712139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712167 : List Nat := [1, 1, 8, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_5712167 : Nat := 118140960795 + 5712167 * 2 ^ 59
def prefixEnd_5712167 : Nat := 4983230072969 + 3 ^ 40 * 5712167 * 2
def baseEnd_5712167 : Nat := 2933087249751057854042729

theorem tailTrace_5712167 : CollatzResearch.WordTrace tailWord_5712167 prefixEnd_5712167 2933087249751057854042729 := by
  unfold tailWord_5712167
  simp only [CollatzResearch.WordTrace]
  refine ⟨208339846296801994300374755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138893230864534662866916503 208339846296801994300374755)
  ·
    refine ⟨312509769445202991450562133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208339846296801994300374755 312509769445202991450562133)
    ·
      refine ⟨3662223860685972556061275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 312509769445202991450562133 3662223860685972556061275)
      ·
        refine ⟨5493335791028958834091913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3662223860685972556061275 5493335791028958834091913)
        ·
          refine ⟨4120001843271719125568935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5493335791028958834091913 4120001843271719125568935)
          ·
            refine ⟨6180002764907578688353403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4120001843271719125568935 6180002764907578688353403)
            ·
              refine ⟨9270004147361368032530105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6180002764907578688353403 9270004147361368032530105)
              ·
                refine ⟨6952503110521026024397579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9270004147361368032530105 6952503110521026024397579)
                ·
                  refine ⟨10428754665781539036596369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6952503110521026024397579 10428754665781539036596369)
                  ·
                    refine ⟨7821565999336154277447277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10428754665781539036596369 7821565999336154277447277)
                    ·
                      refine ⟨2933087249751057854042729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7821565999336154277447277 2933087249751057854042729)
                      ·
                        rfl

theorem cell23_5712167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_5712167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712167 prefixEnd_5712167 := by exact prefixLift 5712167
  have htrace : WordTrace (prefixWord ++ tailWord_5712167) baseStart_5712167 baseEnd_5712167 := by
    simpa [prefixWord, tailWord_5712167, baseEnd_5712167] using wordTrace_append hprefix tailTrace_5712167
  have hstable : (prefixWord ++ tailWord_5712167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712167).length < 2 ^ (prefixWord ++ tailWord_5712167).sum := by decide
  have hdescent : baseEnd_5712167 < baseStart_5712167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712173 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_5712173 : Nat := 118140960795 + 5712173 * 2 ^ 59
def prefixEnd_5712173 : Nat := 4983230072969 + 3 ^ 40 * 5712173 * 2
def baseEnd_5712173 : Nat := 2933090330634984830567701

theorem tailTrace_5712173 : CollatzResearch.WordTrace tailWord_5712173 prefixEnd_5712173 2933090330634984830567701 := by
  unfold tailWord_5712173
  simp only [CollatzResearch.WordTrace]
  refine ⟨208340065134780257325093173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138893376756520171550062115 208340065134780257325093173)
  ·
    refine ⟨19531881106385649124227485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 208340065134780257325093173 19531881106385649124227485)
    ·
      refine ⟨7324455414894618421585307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19531881106385649124227485 7324455414894618421585307)
      ·
        refine ⟨10986683122341927632377961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7324455414894618421585307 10986683122341927632377961)
        ·
          refine ⟨8240012341756445724283471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10986683122341927632377961 8240012341756445724283471)
          ·
            refine ⟨12360018512634668586425207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8240012341756445724283471 12360018512634668586425207)
            ·
              refine ⟨18540027768952002879637811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12360018512634668586425207 18540027768952002879637811)
              ·
                refine ⟨27810041653428004319456717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18540027768952002879637811 27810041653428004319456717)
                ·
                  refine ⟨10428765620035501619796269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27810041653428004319456717 10428765620035501619796269)
                  ·
                    refine ⟨3910787107513313107423601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10428765620035501619796269 3910787107513313107423601)
                    ·
                      refine ⟨2933090330634984830567701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3910787107513313107423601 2933090330634984830567701)
                      ·
                        rfl

theorem cell23_5712173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_5712173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712173 prefixEnd_5712173 := by exact prefixLift 5712173
  have htrace : WordTrace (prefixWord ++ tailWord_5712173) baseStart_5712173 baseEnd_5712173 := by
    simpa [prefixWord, tailWord_5712173, baseEnd_5712173] using wordTrace_append hprefix tailTrace_5712173
  have hstable : (prefixWord ++ tailWord_5712173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712173).length < 2 ^ (prefixWord ++ tailWord_5712173).sum := by decide
  have hdescent : baseEnd_5712173 < baseStart_5712173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712175 : List Nat := [1, 1, 2, 1, 2, 1, 4, 4, 7]
def baseStart_5712175 : Nat := 118140960795 + 5712175 * 2 ^ 59
def prefixEnd_5712175 : Nat := 4983230072969 + 3 ^ 40 * 5712175 * 2
def baseEnd_5712175 : Nat := 325899039732921535860299

theorem tailTrace_5712175 : CollatzResearch.WordTrace tailWord_5712175 prefixEnd_5712175 325899039732921535860299 := by
  unfold tailWord_5712175
  simp only [CollatzResearch.WordTrace]
  refine ⟨208340138080773011666665979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138893425387182007777777319 208340138080773011666665979)
  ·
    refine ⟨312510207121159517499998969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208340138080773011666665979 312510207121159517499998969)
    ·
      refine ⟨234382655340869638124999227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312510207121159517499998969 234382655340869638124999227)
      ·
        refine ⟨351573983011304457187498841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234382655340869638124999227 351573983011304457187498841)
        ·
          refine ⟨263680487258478342890624131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351573983011304457187498841 263680487258478342890624131)
          ·
            refine ⟨395520730887717514335936197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263680487258478342890624131 395520730887717514335936197)
            ·
              refine ⟨74160137041447033937988037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 395520730887717514335936197 74160137041447033937988037)
              ·
                refine ⟨13905025695271318863372757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74160137041447033937988037 13905025695271318863372757)
                ·
                  refine ⟨325899039732921535860299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13905025695271318863372757 325899039732921535860299)
                  ·
                    rfl

theorem cell23_5712175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 7].length) (baseStart_5712175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712175 prefixEnd_5712175 := by exact prefixLift 5712175
  have htrace : WordTrace (prefixWord ++ tailWord_5712175) baseStart_5712175 baseEnd_5712175 := by
    simpa [prefixWord, tailWord_5712175, baseEnd_5712175] using wordTrace_append hprefix tailTrace_5712175
  have hstable : (prefixWord ++ tailWord_5712175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712175).length < 2 ^ (prefixWord ++ tailWord_5712175).sum := by decide
  have hdescent : baseEnd_5712175 < baseStart_5712175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712209 : List Nat := [1, 2, 2, 1, 4, 3, 1, 4, 5]
def baseStart_5712209 : Nat := 118140960795 + 5712209 * 2 ^ 59
def prefixEnd_5712209 : Nat := 4983230072969 + 3 ^ 40 * 5712209 * 2
def baseEnd_5712209 : Nat := 325900979548727409968615

theorem tailTrace_5712209 : CollatzResearch.WordTrace tailWord_5712209 prefixEnd_5712209 325900979548727409968615 := by
  unfold tailWord_5712209
  simp only [CollatzResearch.WordTrace]
  refine ⟨208341378162649835473403681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138894252108433223648935787 208341378162649835473403681)
  ·
    refine ⟨156256033621987376605052761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208341378162649835473403681 156256033621987376605052761)
    ·
      refine ⟨117192025216490532453789571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156256033621987376605052761 117192025216490532453789571)
      ·
        refine ⟨175788037824735798680684357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117192025216490532453789571 175788037824735798680684357)
        ·
          refine ⟨32960257092137962252628317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175788037824735798680684357 32960257092137962252628317)
          ·
            refine ⟨12360096409551735844735619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32960257092137962252628317 12360096409551735844735619)
            ·
              refine ⟨18540144614327603767103429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12360096409551735844735619 18540144614327603767103429)
              ·
                refine ⟨3476277115186425706331893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18540144614327603767103429 3476277115186425706331893)
                ·
                  refine ⟨325900979548727409968615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3476277115186425706331893 325900979548727409968615)
                  ·
                    rfl

theorem cell23_5712209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 5].length) (baseStart_5712209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712209 prefixEnd_5712209 := by exact prefixLift 5712209
  have htrace : WordTrace (prefixWord ++ tailWord_5712209) baseStart_5712209 baseEnd_5712209 := by
    simpa [prefixWord, tailWord_5712209, baseEnd_5712209] using wordTrace_append hprefix tailTrace_5712209
  have hstable : (prefixWord ++ tailWord_5712209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712209).length < 2 ^ (prefixWord ++ tailWord_5712209).sum := by decide
  have hdescent : baseEnd_5712209 < baseStart_5712209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712235 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 2, 8]
def baseStart_5712235 : Nat := 118140960795 + 5712235 * 2 ^ 59
def prefixEnd_5712235 : Nat := 4983230072969 + 3 ^ 40 * 5712235 * 2
def baseEnd_5712235 : Nat := 977707388811854529330805

theorem tailTrace_5712235 : CollatzResearch.WordTrace tailWord_5712235 prefixEnd_5712235 977707388811854529330805 := by
  unfold tailWord_5712235
  simp only [CollatzResearch.WordTrace]
  refine ⟨208342326460555641913850159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138894884307037094609233439 208342326460555641913850159)
  ·
    refine ⟨312513489690833462870775239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208342326460555641913850159 312513489690833462870775239)
    ·
      refine ⟨468770234536250194306162859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312513489690833462870775239 468770234536250194306162859)
      ·
        refine ⟨703155351804375291459244289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468770234536250194306162859 703155351804375291459244289)
        ·
          refine ⟨527366513853281468594433217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 703155351804375291459244289 527366513853281468594433217)
          ·
            refine ⟨395524885389961101445824913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 527366513853281468594433217 395524885389961101445824913)
            ·
              refine ⟨296643664042470826084368685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395524885389961101445824913 296643664042470826084368685)
              ·
                refine ⟨111241374015926559781638257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 296643664042470826084368685 111241374015926559781638257)
                ·
                  refine ⟨83431030511944919836228693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111241374015926559781638257 83431030511944919836228693)
                  ·
                    refine ⟨977707388811854529330805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83431030511944919836228693 977707388811854529330805)
                    ·
                      rfl

theorem cell23_5712235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 8].length) (baseStart_5712235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712235 prefixEnd_5712235 := by exact prefixLift 5712235
  have htrace : WordTrace (prefixWord ++ tailWord_5712235) baseStart_5712235 baseEnd_5712235 := by
    simpa [prefixWord, tailWord_5712235, baseEnd_5712235] using wordTrace_append hprefix tailTrace_5712235
  have hstable : (prefixWord ++ tailWord_5712235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712235).length < 2 ^ (prefixWord ++ tailWord_5712235).sum := by decide
  have hdescent : baseEnd_5712235 < baseStart_5712235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712296 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_5712296 : Nat := 118140960795 + 5712296 * 2 ^ 59
def prefixEnd_5712296 : Nat := 4983230072969 + 3 ^ 40 * 5712296 * 2
def baseEnd_5712296 : Nat := 2933153488755487849329635

theorem tailTrace_5712296 : CollatzResearch.WordTrace tailWord_5712296 prefixEnd_5712296 2933153488755487849329635 := by
  unfold tailWord_5712296
  simp only [CollatzResearch.WordTrace]
  refine ⟨104172275656667324665910371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138896367542223099554547161 104172275656667324665910371)
  ·
    refine ⟨156258413485000986998865557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104172275656667324665910371 156258413485000986998865557)
    ·
      refine ⟨7324613132109421265571823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 156258413485000986998865557 7324613132109421265571823)
      ·
        refine ⟨10986919698164131898357735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7324613132109421265571823 10986919698164131898357735)
        ·
          refine ⟨16480379547246197847536603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10986919698164131898357735 16480379547246197847536603)
          ·
            refine ⟨24720569320869296771304905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16480379547246197847536603 24720569320869296771304905)
            ·
              refine ⟨18540426990651972578478679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24720569320869296771304905 18540426990651972578478679)
              ·
                refine ⟨27810640485977958867718019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18540426990651972578478679 27810640485977958867718019)
                ·
                  refine ⟨41715960728966938301577029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27810640485977958867718019 41715960728966938301577029)
                  ·
                    refine ⟨7821742636681300931545693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41715960728966938301577029 7821742636681300931545693)
                    ·
                      refine ⟨2933153488755487849329635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7821742636681300931545693 2933153488755487849329635)
                      ·
                        rfl

theorem cell23_5712296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_5712296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712296 prefixEnd_5712296 := by exact prefixLift 5712296
  have htrace : WordTrace (prefixWord ++ tailWord_5712296) baseStart_5712296 baseEnd_5712296 := by
    simpa [prefixWord, tailWord_5712296, baseEnd_5712296] using wordTrace_append hprefix tailTrace_5712296
  have hstable : (prefixWord ++ tailWord_5712296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712296).length < 2 ^ (prefixWord ++ tailWord_5712296).sum := by decide
  have hdescent : baseEnd_5712296 < baseStart_5712296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712312 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 5, 5]
def baseStart_5712312 : Nat := 118140960795 + 5712312 * 2 ^ 59
def prefixEnd_5712312 : Nat := 4983230072969 + 3 ^ 40 * 5712312 * 2
def baseEnd_5712312 : Nat := 977720568148653262243187

theorem tailTrace_5712312 : CollatzResearch.WordTrace tailWord_5712312 prefixEnd_5712312 977720568148653262243187 := by
  unfold tailWord_5712312
  simp only [CollatzResearch.WordTrace]
  refine ⟨104172567440638342032201595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138896756587517789376268793 104172567440638342032201595)
  ·
    refine ⟨156258851160957513048302393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104172567440638342032201595 156258851160957513048302393)
    ·
      refine ⟨117194138370718134786226795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156258851160957513048302393 117194138370718134786226795)
      ·
        refine ⟨175791207556077202179340193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117194138370718134786226795 175791207556077202179340193)
        ·
          refine ⟨131843405667057901634505145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175791207556077202179340193 131843405667057901634505145)
          ·
            refine ⟨98882554250293426225878859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131843405667057901634505145 98882554250293426225878859)
            ·
              refine ⟨148323831375440139338818289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98882554250293426225878859 148323831375440139338818289)
              ·
                refine ⟨111242873531580104504113717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148323831375440139338818289 111242873531580104504113717)
                ·
                  refine ⟨10429019393585634797260661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111242873531580104504113717 10429019393585634797260661)
                  ·
                    refine ⟨977720568148653262243187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10429019393585634797260661 977720568148653262243187)
                    ·
                      rfl

theorem cell23_5712312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_5712312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712312 prefixEnd_5712312 := by exact prefixLift 5712312
  have htrace : WordTrace (prefixWord ++ tailWord_5712312) baseStart_5712312 baseEnd_5712312 := by
    simpa [prefixWord, tailWord_5712312, baseEnd_5712312] using wordTrace_append hprefix tailTrace_5712312
  have hstable : (prefixWord ++ tailWord_5712312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712312).length < 2 ^ (prefixWord ++ tailWord_5712312).sum := by decide
  have hdescent : baseEnd_5712312 < baseStart_5712312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712359 : List Nat := [1, 1, 5, 2, 1, 1, 3, 2, 1, 6]
def baseStart_5712359 : Nat := 118140960795 + 5712359 * 2 ^ 59
def prefixEnd_5712359 : Nat := 4983230072969 + 3 ^ 40 * 5712359 * 2
def baseEnd_5712359 : Nat := 977728612678907034280615

theorem tailTrace_5712359 : CollatzResearch.WordTrace tailWord_5712359 prefixEnd_5712359 977728612678907034280615 := by
  unfold tailWord_5712359
  simp only [CollatzResearch.WordTrace]
  refine ⟨208346849112106411091364131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138897899408070940727576087 208346849112106411091364131)
  ·
    refine ⟨312520273668159616637046197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208346849112106411091364131 312520273668159616637046197)
    ·
      refine ⟨29298775656389964059723081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 312520273668159616637046197 29298775656389964059723081)
      ·
        refine ⟨21974081742292473044792311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29298775656389964059723081 21974081742292473044792311)
        ·
          refine ⟨32961122613438709567188467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21974081742292473044792311 32961122613438709567188467)
          ·
            refine ⟨49441683920158064350782701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32961122613438709567188467 49441683920158064350782701)
            ·
              refine ⟨18540631470059274131543513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49441683920158064350782701 18540631470059274131543513)
              ·
                refine ⟨13905473602544455598657635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18540631470059274131543513 13905473602544455598657635)
                ·
                  refine ⟨20858210403816683397986453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13905473602544455598657635 20858210403816683397986453)
                  ·
                    refine ⟨977728612678907034280615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20858210403816683397986453 977728612678907034280615)
                    ·
                      rfl

theorem cell23_5712359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_5712359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712359 prefixEnd_5712359 := by exact prefixLift 5712359
  have htrace : WordTrace (prefixWord ++ tailWord_5712359) baseStart_5712359 baseEnd_5712359 := by
    simpa [prefixWord, tailWord_5712359, baseEnd_5712359] using wordTrace_append hprefix tailTrace_5712359
  have hstable : (prefixWord ++ tailWord_5712359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712359).length < 2 ^ (prefixWord ++ tailWord_5712359).sum := by decide
  have hdescent : baseEnd_5712359 < baseStart_5712359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712376 : List Nat := [2, 1, 2, 1, 1, 4, 4, 2, 2, 4]
def baseStart_5712376 : Nat := 118140960795 + 5712376 * 2 ^ 59
def prefixEnd_5712376 : Nat := 4983230072969 + 3 ^ 40 * 5712376 * 2
def baseEnd_5712376 : Nat := 977731522402615845443089

theorem tailTrace_5712376 : CollatzResearch.WordTrace tailWord_5712376 prefixEnd_5712376 977731522402615845443089 := by
  unfold tailWord_5712376
  simp only [CollatzResearch.WordTrace]
  refine ⟨104173734576522411497366491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138898312768696548663155321 104173734576522411497366491)
  ·
    refine ⟨156260601864783617246049737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104173734576522411497366491 156260601864783617246049737)
    ·
      refine ⟨117195451398587712934537303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156260601864783617246049737 117195451398587712934537303)
      ·
        refine ⟨175793177097881569401805955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117195451398587712934537303 175793177097881569401805955)
        ·
          refine ⟨263689765646822354102708933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175793177097881569401805955 263689765646822354102708933)
          ·
            refine ⟨49441831058779191394257925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 263689765646822354102708933 49441831058779191394257925)
            ·
              refine ⟨9270343323521098386423361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49441831058779191394257925 9270343323521098386423361)
              ·
                refine ⟨6952757492640823789817521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9270343323521098386423361 6952757492640823789817521)
                ·
                  refine ⟨5214568119480617842363141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6952757492640823789817521 5214568119480617842363141)
                  ·
                    refine ⟨977731522402615845443089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5214568119480617842363141 977731522402615845443089)
                    ·
                      rfl

theorem cell23_5712376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 2, 4].length) (baseStart_5712376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712376 prefixEnd_5712376 := by exact prefixLift 5712376
  have htrace : WordTrace (prefixWord ++ tailWord_5712376) baseStart_5712376 baseEnd_5712376 := by
    simpa [prefixWord, tailWord_5712376, baseEnd_5712376] using wordTrace_append hprefix tailTrace_5712376
  have hstable : (prefixWord ++ tailWord_5712376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712376).length < 2 ^ (prefixWord ++ tailWord_5712376).sum := by decide
  have hdescent : baseEnd_5712376 < baseStart_5712376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712396 : List Nat := [2, 2, 1, 2, 4, 2, 2, 1, 1, 2, 4]
def baseStart_5712396 : Nat := 118140960795 + 5712396 * 2 ^ 59
def prefixEnd_5712396 : Nat := 4983230072969 + 3 ^ 40 * 5712396 * 2
def baseEnd_5712396 : Nat := 2933204836820937458079175

theorem tailTrace_5712396 : CollatzResearch.WordTrace tailWord_5712396 prefixEnd_5712396 2933204836820937458079175 := by
  unfold tailWord_5712396
  simp only [CollatzResearch.WordTrace]
  refine ⟨104174099306486183205230521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138898799075314910940307361 104174099306486183205230521)
  ·
    refine ⟨78130574479864637403922891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104174099306486183205230521 78130574479864637403922891)
    ·
      refine ⟨117195861719796956105884337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78130574479864637403922891 117195861719796956105884337)
      ·
        refine ⟨87896896289847717079413253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117195861719796956105884337 87896896289847717079413253)
        ·
          refine ⟨16480668054346446952389985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87896896289847717079413253 16480668054346446952389985)
          ·
            refine ⟨12360501040759835214292489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16480668054346446952389985 12360501040759835214292489)
            ·
              refine ⟨9270375780569876410719367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12360501040759835214292489 9270375780569876410719367)
              ·
                refine ⟨13905563670854814616079051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9270375780569876410719367 13905563670854814616079051)
                ·
                  refine ⟨20858345506282221924118577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13905563670854814616079051 20858345506282221924118577)
                  ·
                    refine ⟨15643759129711666443088933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20858345506282221924118577 15643759129711666443088933)
                    ·
                      refine ⟨2933204836820937458079175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15643759129711666443088933 2933204836820937458079175)
                      ·
                        rfl

theorem cell23_5712396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_5712396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712396 prefixEnd_5712396 := by exact prefixLift 5712396
  have htrace : WordTrace (prefixWord ++ tailWord_5712396) baseStart_5712396 baseEnd_5712396 := by
    simpa [prefixWord, tailWord_5712396, baseEnd_5712396] using wordTrace_append hprefix tailTrace_5712396
  have hstable : (prefixWord ++ tailWord_5712396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712396).length < 2 ^ (prefixWord ++ tailWord_5712396).sum := by decide
  have hdescent : baseEnd_5712396 < baseStart_5712396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712399 : List Nat := [1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 3]
def baseStart_5712399 : Nat := 118140960795 + 5712399 * 2 ^ 59
def prefixEnd_5712399 : Nat := 4983230072969 + 3 ^ 40 * 5712399 * 2
def baseEnd_5712399 : Nat := 2933206377262900946341661

theorem tailTrace_5712399 : CollatzResearch.WordTrace tailWord_5712399 prefixEnd_5712399 2933206377262900946341661 := by
  unfold tailWord_5712399
  simp only [CollatzResearch.WordTrace]
  refine ⟨208348308031961497922820251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138898872021307665281880167 208348308031961497922820251)
  ·
    refine ⟨312522462047942246884230377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208348308031961497922820251 312522462047942246884230377)
    ·
      refine ⟨234391846535956685163172783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312522462047942246884230377 234391846535956685163172783)
      ·
        refine ⟨351587769803935027744759175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234391846535956685163172783 351587769803935027744759175)
        ·
          refine ⟨527381654705902541617138763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351587769803935027744759175 527381654705902541617138763)
          ·
            refine ⟨791072482058853812425708145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527381654705902541617138763 791072482058853812425708145)
            ·
              refine ⟨593304361544140359319281109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 791072482058853812425708145 593304361544140359319281109)
              ·
                refine ⟨13905570973690789671545651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 593304361544140359319281109 13905570973690789671545651)
                ·
                  refine ⟨20858356460536184507318477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13905570973690789671545651 20858356460536184507318477)
                  ·
                    refine ⟨7821883672701069190244429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20858356460536184507318477 7821883672701069190244429)
                    ·
                      refine ⟨2933206377262900946341661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7821883672701069190244429 2933206377262900946341661)
                      ·
                        rfl

theorem cell23_5712399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 3].length) (baseStart_5712399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712399 prefixEnd_5712399 := by exact prefixLift 5712399
  have htrace : WordTrace (prefixWord ++ tailWord_5712399) baseStart_5712399 baseEnd_5712399 := by
    simpa [prefixWord, tailWord_5712399, baseEnd_5712399] using wordTrace_append hprefix tailTrace_5712399
  have hstable : (prefixWord ++ tailWord_5712399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712399).length < 2 ^ (prefixWord ++ tailWord_5712399).sum := by decide
  have hdescent : baseEnd_5712399 < baseStart_5712399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712420 : List Nat := [2, 3, 1, 5, 1, 1, 1, 3, 1, 2, 3]
def baseStart_5712420 : Nat := 118140960795 + 5712420 * 2 ^ 59
def prefixEnd_5712420 : Nat := 4983230072969 + 3 ^ 40 * 5712420 * 2
def baseEnd_5712420 : Nat := 2933217160356645364179065

theorem tailTrace_5712420 : CollatzResearch.WordTrace tailWord_5712420 prefixEnd_5712420 2933217160356645364179065 := by
  unfold tailWord_5712420
  simp only [CollatzResearch.WordTrace]
  refine ⟨104174536982442709254667357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138899382643256945672889809 104174536982442709254667357)
  ·
    refine ⟨39065451368416015970500259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104174536982442709254667357 39065451368416015970500259)
    ·
      refine ⟨58598177052624023955750389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39065451368416015970500259 58598177052624023955750389)
      ·
        refine ⟨5493579098683502245851599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58598177052624023955750389 5493579098683502245851599)
        ·
          refine ⟨8240368648025253368777399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5493579098683502245851599 8240368648025253368777399)
          ·
            refine ⟨12360552972037880053166099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8240368648025253368777399 12360552972037880053166099)
            ·
              refine ⟨18540829458056820079749149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12360552972037880053166099 18540829458056820079749149)
              ·
                refine ⟨6952811046771307529905931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18540829458056820079749149 6952811046771307529905931)
                ·
                  refine ⟨10429216570156961294858897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6952811046771307529905931 10429216570156961294858897)
                  ·
                    refine ⟨7821912427617720971144173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10429216570156961294858897 7821912427617720971144173)
                    ·
                      refine ⟨2933217160356645364179065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7821912427617720971144173 2933217160356645364179065)
                      ·
                        rfl

theorem cell23_5712420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_5712420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712420 prefixEnd_5712420 := by exact prefixLift 5712420
  have htrace : WordTrace (prefixWord ++ tailWord_5712420) baseStart_5712420 baseEnd_5712420 := by
    simpa [prefixWord, tailWord_5712420, baseEnd_5712420] using wordTrace_append hprefix tailTrace_5712420
  have hstable : (prefixWord ++ tailWord_5712420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712420).length < 2 ^ (prefixWord ++ tailWord_5712420).sum := by decide
  have hdescent : baseEnd_5712420 < baseStart_5712420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712433 : List Nat := [1, 2, 2, 3, 1, 1, 5, 2, 2, 1, 3]
def baseStart_5712433 : Nat := 118140960795 + 5712433 * 2 ^ 59
def prefixEnd_5712433 : Nat := 4983230072969 + 3 ^ 40 * 5712433 * 2
def baseEnd_5712433 : Nat := 2933223835605153813316505

theorem tailTrace_5712433 : CollatzResearch.WordTrace tailWord_5712433 prefixEnd_5712433 2933223835605153813316505 := by
  unfold tailWord_5712433
  simp only [CollatzResearch.WordTrace]
  refine ⟨208349548113838321729557953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138899698742558881153038635 208349548113838321729557953)
  ·
    refine ⟨156262161085378741297168465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208349548113838321729557953 156262161085378741297168465)
    ·
      refine ⟨117196620814034055972876349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156262161085378741297168465 117196620814034055972876349)
      ·
        refine ⟨43948732805262770989828631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117196620814034055972876349 43948732805262770989828631)
        ·
          refine ⟨65923099207894156484742947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43948732805262770989828631 65923099207894156484742947)
          ·
            refine ⟨98884648811841234727114421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65923099207894156484742947 98884648811841234727114421)
            ·
              refine ⟨9270435826110115755666977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98884648811841234727114421 9270435826110115755666977)
              ·
                refine ⟨6952826869582586816750233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9270435826110115755666977 6952826869582586816750233)
                ·
                  refine ⟨5214620152186940112562675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6952826869582586816750233 5214620152186940112562675)
                  ·
                    refine ⟨7821930228280410168844013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5214620152186940112562675 7821930228280410168844013)
                    ·
                      refine ⟨2933223835605153813316505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7821930228280410168844013 2933223835605153813316505)
                      ·
                        rfl

theorem cell23_5712433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_5712433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712433 prefixEnd_5712433 := by exact prefixLift 5712433
  have htrace : WordTrace (prefixWord ++ tailWord_5712433) baseStart_5712433 baseEnd_5712433 := by
    simpa [prefixWord, tailWord_5712433, baseEnd_5712433] using wordTrace_append hprefix tailTrace_5712433
  have hstable : (prefixWord ++ tailWord_5712433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712433).length < 2 ^ (prefixWord ++ tailWord_5712433).sum := by decide
  have hdescent : baseEnd_5712433 < baseStart_5712433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712459 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 3]
def baseStart_5712459 : Nat := 118140960795 + 5712459 * 2 ^ 59
def prefixEnd_5712459 : Nat := 4983230072969 + 3 ^ 40 * 5712459 * 2
def baseEnd_5712459 : Nat := 2933237186102170711591385

theorem tailTrace_5712459 : CollatzResearch.WordTrace tailWord_5712459 prefixEnd_5712459 2933237186102170711591385 := by
  unfold tailWord_5712459
  simp only [CollatzResearch.WordTrace]
  refine ⟨208350496411744128170004431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138900330941162752113336287 208350496411744128170004431)
  ·
    refine ⟨312525744617616192255006647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208350496411744128170004431 312525744617616192255006647)
    ·
      refine ⟨468788616926424288382509971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312525744617616192255006647 468788616926424288382509971)
      ·
        refine ⟨703182925389636432573764957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468788616926424288382509971 703182925389636432573764957)
        ·
          refine ⟨263693597021113662215161859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 703182925389636432573764957 263693597021113662215161859)
          ·
            refine ⟨395540395531670493322742789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263693597021113662215161859 395540395531670493322742789)
            ·
              refine ⟨74163824162188217498014273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 395540395531670493322742789 74163824162188217498014273)
              ·
                refine ⟨55622868121641163123510705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74163824162188217498014273 55622868121641163123510705)
                ·
                  refine ⟨41717151091230872342633029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55622868121641163123510705 41717151091230872342633029)
                  ·
                    refine ⟨7821965829605788564243693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41717151091230872342633029 7821965829605788564243693)
                    ·
                      refine ⟨2933237186102170711591385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7821965829605788564243693 2933237186102170711591385)
                      ·
                        rfl

theorem cell23_5712459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 3].length) (baseStart_5712459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712459 prefixEnd_5712459 := by exact prefixLift 5712459
  have htrace : WordTrace (prefixWord ++ tailWord_5712459) baseStart_5712459 baseEnd_5712459 := by
    simpa [prefixWord, tailWord_5712459, baseEnd_5712459] using wordTrace_append hprefix tailTrace_5712459
  have hstable : (prefixWord ++ tailWord_5712459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712459).length < 2 ^ (prefixWord ++ tailWord_5712459).sum := by decide
  have hdescent : baseEnd_5712459 < baseStart_5712459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712469 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 1, 4, 4]
def baseStart_5712469 : Nat := 118140960795 + 5712469 * 2 ^ 59
def prefixEnd_5712469 : Nat := 4983230072969 + 3 ^ 40 * 5712469 * 2
def baseEnd_5712469 : Nat := 2933242320908715672466339

theorem tailTrace_5712469 : CollatzResearch.WordTrace tailWord_5712469 prefixEnd_5712469 2933242320908715672466339 := by
  unfold tailWord_5712469
  simp only [CollatzResearch.WordTrace]
  refine ⟨208350861141707899877868461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138900574094471933251912307 208350861141707899877868461)
  ·
    refine ⟨78131572928140462454200673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208350861141707899877868461 78131572928140462454200673)
    ·
      refine ⟨58598679696105346840650505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78131572928140462454200673 58598679696105346840650505)
      ·
        refine ⟨43949009772079010130487879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58598679696105346840650505 43949009772079010130487879)
        ·
          refine ⟨65923514658118515195731819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43949009772079010130487879 65923514658118515195731819)
          ·
            refine ⟨98885271987177772793597729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65923514658118515195731819 98885271987177772793597729)
            ·
              refine ⟨74163953990383329595198297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98885271987177772793597729 74163953990383329595198297)
              ·
                refine ⟨55622965492787497196398723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74163953990383329595198297 55622965492787497196398723)
                ·
                  refine ⟨83434448239181245794598085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55622965492787497196398723 83434448239181245794598085)
                  ·
                    refine ⟨15643959044846483586487141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83434448239181245794598085 15643959044846483586487141)
                    ·
                      refine ⟨2933242320908715672466339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15643959044846483586487141 2933242320908715672466339)
                      ·
                        rfl

theorem cell23_5712469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_5712469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712469 prefixEnd_5712469 := by exact prefixLift 5712469
  have htrace : WordTrace (prefixWord ++ tailWord_5712469) baseStart_5712469 baseEnd_5712469 := by
    simpa [prefixWord, tailWord_5712469, baseEnd_5712469] using wordTrace_append hprefix tailTrace_5712469
  have hstable : (prefixWord ++ tailWord_5712469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712469).length < 2 ^ (prefixWord ++ tailWord_5712469).sum := by decide
  have hdescent : baseEnd_5712469 < baseStart_5712469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712490 : List Nat := [3, 1, 3, 2, 1, 1, 2, 4, 2, 2, 2]
def baseStart_5712490 : Nat := 118140960795 + 5712490 * 2 ^ 59
def prefixEnd_5712490 : Nat := 4983230072969 + 3 ^ 40 * 5712490 * 2
def baseEnd_5712490 : Nat := 2933253104002460090303743

theorem tailTrace_5712490 : CollatzResearch.WordTrace tailWord_5712490 prefixEnd_5712490 2933253104002460090303743 := by
  unfold tailWord_5712490
  simp only [CollatzResearch.WordTrace]
  refine ⟨52087906768657955116095731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138901084716421213642921949 52087906768657955116095731)
  ·
    refine ⟨78131860152986932674143597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52087906768657955116095731 78131860152986932674143597)
    ·
      refine ⟨29299447557370099752803849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78131860152986932674143597 29299447557370099752803849)
      ·
        refine ⟨21974585668027574814602887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29299447557370099752803849 21974585668027574814602887)
        ·
          refine ⟨32961878502041362221904331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21974585668027574814602887 32961878502041362221904331)
          ·
            refine ⟨49442817753062043332856497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32961878502041362221904331 49442817753062043332856497)
            ·
              refine ⟨37082113314796532499642373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49442817753062043332856497 37082113314796532499642373)
              ·
                refine ⟨6952896246524349843682945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37082113314796532499642373 6952896246524349843682945)
                ·
                  refine ⟨5214672184893262382762209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6952896246524349843682945 5214672184893262382762209)
                  ·
                    refine ⟨3911004138669946787071657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5214672184893262382762209 3911004138669946787071657)
                    ·
                      refine ⟨2933253104002460090303743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3911004138669946787071657 2933253104002460090303743)
                      ·
                        rfl

theorem cell23_5712490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_5712490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712490 prefixEnd_5712490 := by exact prefixLift 5712490
  have htrace : WordTrace (prefixWord ++ tailWord_5712490) baseStart_5712490 baseEnd_5712490 := by
    simpa [prefixWord, tailWord_5712490, baseEnd_5712490] using wordTrace_append hprefix tailTrace_5712490
  have hstable : (prefixWord ++ tailWord_5712490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712490).length < 2 ^ (prefixWord ++ tailWord_5712490).sum := by decide
  have hdescent : baseEnd_5712490 < baseStart_5712490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712519 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 7]
def baseStart_5712519 : Nat := 118140960795 + 5712519 * 2 ^ 59
def prefixEnd_5712519 : Nat := 4983230072969 + 3 ^ 40 * 5712519 * 2
def baseEnd_5712519 : Nat := 2933267994941440476841109

theorem tailTrace_5712519 : CollatzResearch.WordTrace tailWord_5712519 prefixEnd_5712519 2933267994941440476841109 := by
  unfold tailWord_5712519
  simp only [CollatzResearch.WordTrace]
  refine ⟨208352684791526758417188611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138901789861017838944792407 208352684791526758417188611)
  ·
    refine ⟨312529027187290137625782917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208352684791526758417188611 312529027187290137625782917)
    ·
      refine ⟨58599192597616900804834297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 312529027187290137625782917 58599192597616900804834297)
      ·
        refine ⟨43949394448212675603625723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58599192597616900804834297 43949394448212675603625723)
        ·
          refine ⟨65924091672319013405438585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43949394448212675603625723 65924091672319013405438585)
          ·
            refine ⟨49443068754239260054078939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65924091672319013405438585 49443068754239260054078939)
            ·
              refine ⟨74164603131358890081118409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49443068754239260054078939 74164603131358890081118409)
              ·
                refine ⟨55623452348519167560838807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74164603131358890081118409 55623452348519167560838807)
                ·
                  refine ⟨83435178522778751341258211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55623452348519167560838807 83435178522778751341258211)
                  ·
                    refine ⟨125152767784168127011887317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83435178522778751341258211 125152767784168127011887317)
                    ·
                      refine ⟨2933267994941440476841109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125152767784168127011887317 2933267994941440476841109)
                      ·
                        rfl

theorem cell23_5712519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_5712519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712519 prefixEnd_5712519 := by exact prefixLift 5712519
  have htrace : WordTrace (prefixWord ++ tailWord_5712519) baseStart_5712519 baseEnd_5712519 := by
    simpa [prefixWord, tailWord_5712519, baseEnd_5712519] using wordTrace_append hprefix tailTrace_5712519
  have hstable : (prefixWord ++ tailWord_5712519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712519).length < 2 ^ (prefixWord ++ tailWord_5712519).sum := by decide
  have hdescent : baseEnd_5712519 < baseStart_5712519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712529 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 4]
def baseStart_5712529 : Nat := 118140960795 + 5712529 * 2 ^ 59
def prefixEnd_5712529 : Nat := 4983230072969 + 3 ^ 40 * 5712529 * 2
def baseEnd_5712529 : Nat := 2933273129747985437716063

theorem tailTrace_5712529 : CollatzResearch.WordTrace tailWord_5712529 prefixEnd_5712529 2933273129747985437716063 := by
  unfold tailWord_5712529
  simp only [CollatzResearch.WordTrace]
  refine ⟨208353049521490530125052641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138902033014327020083368427 208353049521490530125052641)
  ·
    refine ⟨156264787141117897593789481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208353049521490530125052641 156264787141117897593789481)
    ·
      refine ⟨117198590355838423195342111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156264787141117897593789481 117198590355838423195342111)
      ·
        refine ⟨175797885533757634793013167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117198590355838423195342111 175797885533757634793013167)
        ·
          refine ⟨263696828300636452189519751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175797885533757634793013167 263696828300636452189519751)
          ·
            refine ⟨395545242450954678284279627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263696828300636452189519751 395545242450954678284279627)
            ·
              refine ⟨593317863676432017426419441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395545242450954678284279627 593317863676432017426419441)
              ·
                refine ⟨444988397757324013069814581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 593317863676432017426419441 444988397757324013069814581)
                ·
                  refine ⟨41717662289749126225295117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 444988397757324013069814581 41717662289749126225295117)
                  ·
                    refine ⟨15644123358655922334485669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41717662289749126225295117 15644123358655922334485669)
                    ·
                      refine ⟨2933273129747985437716063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15644123358655922334485669 2933273129747985437716063)
                      ·
                        rfl

theorem cell23_5712529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_5712529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712529 prefixEnd_5712529 := by exact prefixLift 5712529
  have htrace : WordTrace (prefixWord ++ tailWord_5712529) baseStart_5712529 baseEnd_5712529 := by
    simpa [prefixWord, tailWord_5712529, baseEnd_5712529] using wordTrace_append hprefix tailTrace_5712529
  have hstable : (prefixWord ++ tailWord_5712529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712529).length < 2 ^ (prefixWord ++ tailWord_5712529).sum := by decide
  have hdescent : baseEnd_5712529 < baseStart_5712529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712549 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 1, 5, 5]
def baseStart_5712549 : Nat := 118140960795 + 5712549 * 2 ^ 59
def prefixEnd_5712549 : Nat := 4983230072969 + 3 ^ 40 * 5712549 * 2
def baseEnd_5712549 : Nat := 2933283399361075359465971

theorem tailTrace_5712549 : CollatzResearch.WordTrace tailWord_5712549 prefixEnd_5712549 2933283399361075359465971 := by
  unfold tailWord_5712549
  simp only [CollatzResearch.WordTrace]
  refine ⟨208353778981418073540780701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138902519320945382360520467 208353778981418073540780701)
  ·
    refine ⟨78132667118031777577792763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208353778981418073540780701 78132667118031777577792763)
    ·
      refine ⟨117199000677047666366689145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78132667118031777577792763 117199000677047666366689145)
      ·
        refine ⟨87899250507785749775016859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117199000677047666366689145 87899250507785749775016859)
        ·
          refine ⟨131848875761678624662525289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87899250507785749775016859 131848875761678624662525289)
          ·
            refine ⟨98886656821258968496893967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131848875761678624662525289 98886656821258968496893967)
            ·
              refine ⟨148329985231888452745340951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98886656821258968496893967 148329985231888452745340951)
              ·
                refine ⟨222494977847832679118011427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148329985231888452745340951 222494977847832679118011427)
                ·
                  refine ⟨333742466771749018677017141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222494977847832679118011427 333742466771749018677017141)
                  ·
                    refine ⟨31288356259851470500970357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 333742466771749018677017141 31288356259851470500970357)
                    ·
                      refine ⟨2933283399361075359465971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31288356259851470500970357 2933283399361075359465971)
                      ·
                        rfl

theorem cell23_5712549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_5712549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712549 prefixEnd_5712549 := by exact prefixLift 5712549
  have htrace : WordTrace (prefixWord ++ tailWord_5712549) baseStart_5712549 baseEnd_5712549 := by
    simpa [prefixWord, tailWord_5712549, baseEnd_5712549] using wordTrace_append hprefix tailTrace_5712549
  have hstable : (prefixWord ++ tailWord_5712549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712549).length < 2 ^ (prefixWord ++ tailWord_5712549).sum := by decide
  have hdescent : baseEnd_5712549 < baseStart_5712549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712563 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 2, 4, 2]
def baseStart_5712563 : Nat := 118140960795 + 5712563 * 2 ^ 59
def prefixEnd_5712563 : Nat := 4983230072969 + 3 ^ 40 * 5712563 * 2
def baseEnd_5712563 : Nat := 2933290588090238304690907

theorem tailTrace_5712563 : CollatzResearch.WordTrace tailWord_5712563 prefixEnd_5712563 2933290588090238304690907 := by
  unfold tailWord_5712563
  simp only [CollatzResearch.WordTrace]
  refine ⟨208354289603367353931790343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138902859735578235954526895 208354289603367353931790343)
  ·
    refine ⟨312531434405051030897685515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208354289603367353931790343 312531434405051030897685515)
    ·
      refine ⟨468797151607576546346528273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312531434405051030897685515 468797151607576546346528273)
      ·
        refine ⟨351597863705682409759896205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 468797151607576546346528273 351597863705682409759896205)
        ·
          refine ⟨131849198889630903659961077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 351597863705682409759896205 131849198889630903659961077)
          ·
            refine ⟨12360862395902897218121351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131849198889630903659961077 12360862395902897218121351)
            ·
              refine ⟨18541293593854345827182027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12360862395902897218121351 18541293593854345827182027)
              ·
                refine ⟨27811940390781518740773041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18541293593854345827182027 27811940390781518740773041)
                ·
                  refine ⟨20858955293086139055579781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27811940390781518740773041 20858955293086139055579781)
                  ·
                    refine ⟨3911054117453651072921209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20858955293086139055579781 3911054117453651072921209)
                    ·
                      refine ⟨2933290588090238304690907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3911054117453651072921209 2933290588090238304690907)
                      ·
                        rfl

theorem cell23_5712563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 4, 2].length) (baseStart_5712563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712563 prefixEnd_5712563 := by exact prefixLift 5712563
  have htrace : WordTrace (prefixWord ++ tailWord_5712563) baseStart_5712563 baseEnd_5712563 := by
    simpa [prefixWord, tailWord_5712563, baseEnd_5712563] using wordTrace_append hprefix tailTrace_5712563
  have hstable : (prefixWord ++ tailWord_5712563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712563).length < 2 ^ (prefixWord ++ tailWord_5712563).sum := by decide
  have hdescent : baseEnd_5712563 < baseStart_5712563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712569 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 10]
def baseStart_5712569 : Nat := 118140960795 + 5712569 * 2 ^ 59
def prefixEnd_5712569 : Nat := 4983230072969 + 3 ^ 40 * 5712569 * 2
def baseEnd_5712569 : Nat := 325921518774907253468431

theorem tailTrace_5712569 : CollatzResearch.WordTrace tailWord_5712569 prefixEnd_5712569 325921518774907253468431 := by
  unfold tailWord_5712569
  simp only [CollatzResearch.WordTrace]
  refine ⟨208354508441345616956508761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138903005627563744637672507 208354508441345616956508761)
  ·
    refine ⟨156265881331009212717381571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208354508441345616956508761 156265881331009212717381571)
    ·
      refine ⟨234398821996513819076072357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156265881331009212717381571 234398821996513819076072357)
      ·
        refine ⟨43949779124346341076763567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234398821996513819076072357 43949779124346341076763567)
        ·
          refine ⟨65924668686519511615145351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43949779124346341076763567 65924668686519511615145351)
          ·
            refine ⟨98887003029779267422718027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65924668686519511615145351 98887003029779267422718027)
            ·
              refine ⟨148330504544668901134077041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98887003029779267422718027 148330504544668901134077041)
              ·
                refine ⟨111247878408501675850557781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148330504544668901134077041 111247878408501675850557781)
                ·
                  refine ⟨325921518774907253468431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 111247878408501675850557781 325921518774907253468431)
                  ·
                    rfl

theorem cell23_5712569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 10].length) (baseStart_5712569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712569 prefixEnd_5712569 := by exact prefixLift 5712569
  have htrace : WordTrace (prefixWord ++ tailWord_5712569) baseStart_5712569 baseEnd_5712569 := by
    simpa [prefixWord, tailWord_5712569, baseEnd_5712569] using wordTrace_append hprefix tailTrace_5712569
  have hstable : (prefixWord ++ tailWord_5712569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712569).length < 2 ^ (prefixWord ++ tailWord_5712569).sum := by decide
  have hdescent : baseEnd_5712569 < baseStart_5712569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712573 : List Nat := [1, 4, 1, 2, 1, 4, 1, 2, 3, 4]
def baseStart_5712573 : Nat := 118140960795 + 5712573 * 2 ^ 59
def prefixEnd_5712573 : Nat := 4983230072969 + 3 ^ 40 * 5712573 * 2
def baseEnd_5712573 : Nat := 977765240965594421855287

theorem tailTrace_5712573 : CollatzResearch.WordTrace tailWord_5712573 prefixEnd_5712573 977765240965594421855287 := by
  unfold tailWord_5712573
  simp only [CollatzResearch.WordTrace]
  refine ⟨208354654333331125639654373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138903102888887417093102915 208354654333331125639654373)
  ·
    refine ⟨39066497687499586057435195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208354654333331125639654373 39066497687499586057435195)
    ·
      refine ⟨58599746531249379086152793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39066497687499586057435195 58599746531249379086152793)
      ·
        refine ⟨43949809898437034314614595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58599746531249379086152793 43949809898437034314614595)
        ·
          refine ⟨65924714847655551471921893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43949809898437034314614595 65924714847655551471921893)
          ·
            refine ⟨12360884033935415900985355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65924714847655551471921893 12360884033935415900985355)
            ·
              refine ⟨18541326050903123851478033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12360884033935415900985355 18541326050903123851478033)
              ·
                refine ⟨13905994538177342888608525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18541326050903123851478033 13905994538177342888608525)
                ·
                  refine ⟨5214747951816503583228197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13905994538177342888608525 5214747951816503583228197)
                  ·
                    refine ⟨977765240965594421855287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5214747951816503583228197 977765240965594421855287)
                    ·
                      rfl

theorem cell23_5712573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_5712573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712573 prefixEnd_5712573 := by exact prefixLift 5712573
  have htrace : WordTrace (prefixWord ++ tailWord_5712573) baseStart_5712573 baseEnd_5712573 := by
    simpa [prefixWord, tailWord_5712573, baseEnd_5712573] using wordTrace_append hprefix tailTrace_5712573
  have hstable : (prefixWord ++ tailWord_5712573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712573).length < 2 ^ (prefixWord ++ tailWord_5712573).sum := by decide
  have hdescent : baseEnd_5712573 < baseStart_5712573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712577 : List Nat := [1, 2, 6, 2, 1, 2, 1, 1, 2, 5]
def baseStart_5712577 : Nat := 118140960795 + 5712577 * 2 ^ 59
def prefixEnd_5712577 : Nat := 4983230072969 + 3 ^ 40 * 5712577 * 2
def baseEnd_5712577 : Nat := 977765925606467083305281

theorem tailTrace_5712577 : CollatzResearch.WordTrace tailWord_5712577 prefixEnd_5712577 977765925606467083305281 := by
  unfold tailWord_5712577
  simp only [CollatzResearch.WordTrace]
  refine ⟨208354800225316634322799985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138903200150211089548533323 208354800225316634322799985)
  ·
    refine ⟨156266100168987475742099989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208354800225316634322799985 156266100168987475742099989)
    ·
      refine ⟨7324973445421287925410937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 156266100168987475742099989 7324973445421287925410937)
      ·
        refine ⟨5493730084065965944058203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7324973445421287925410937 5493730084065965944058203)
        ·
          refine ⟨8240595126098948916087305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5493730084065965944058203 8240595126098948916087305)
          ·
            refine ⟨6180446344574211687065479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8240595126098948916087305 6180446344574211687065479)
            ·
              refine ⟨9270669516861317530598219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6180446344574211687065479 9270669516861317530598219)
              ·
                refine ⟨13906004275291976295897329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9270669516861317530598219 13906004275291976295897329)
                ·
                  refine ⟨10429503206468982221922997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13906004275291976295897329 10429503206468982221922997)
                  ·
                    refine ⟨977765925606467083305281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10429503206468982221922997 977765925606467083305281)
                    ·
                      rfl

theorem cell23_5712577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_5712577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712577 prefixEnd_5712577 := by exact prefixLift 5712577
  have htrace : WordTrace (prefixWord ++ tailWord_5712577) baseStart_5712577 baseEnd_5712577 := by
    simpa [prefixWord, tailWord_5712577, baseEnd_5712577] using wordTrace_append hprefix tailTrace_5712577
  have hstable : (prefixWord ++ tailWord_5712577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712577).length < 2 ^ (prefixWord ++ tailWord_5712577).sum := by decide
  have hdescent : baseEnd_5712577 < baseStart_5712577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712580 : List Nat := [2, 3, 3, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_5712580 : Nat := 118140960795 + 5712580 * 2 ^ 59
def prefixEnd_5712580 : Nat := 4983230072969 + 3 ^ 40 * 5712580 * 2
def baseEnd_5712580 : Nat := 2933299317261364738178329

theorem tailTrace_5712580 : CollatzResearch.WordTrace tailWord_5712580 prefixEnd_5712580 2933299317261364738178329 := by
  unfold tailWord_5712580
  simp only [CollatzResearch.WordTrace]
  refine ⟨104177454822152882917579597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138903273096203843890106129 104177454822152882917579597)
  ·
    refine ⟨39066545558307331094092349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104177454822152882917579597 39066545558307331094092349)
    ·
      refine ⟨14649954584365249160284631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39066545558307331094092349 14649954584365249160284631)
      ·
        refine ⟨21974931876547873740426947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14649954584365249160284631 21974931876547873740426947)
        ·
          refine ⟨32962397814821810610640421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21974931876547873740426947 32962397814821810610640421)
          ·
            refine ⟨6180449590279089489495079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32962397814821810610640421 6180449590279089489495079)
            ·
              refine ⟨9270674385418634234242619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6180449590279089489495079 9270674385418634234242619)
              ·
                refine ⟨13906011578127951351363929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9270674385418634234242619 13906011578127951351363929)
                ·
                  refine ⟨10429508683595963513522947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13906011578127951351363929 10429508683595963513522947)
                  ·
                    refine ⟨15644263025393945270284421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10429508683595963513522947 15644263025393945270284421)
                    ·
                      refine ⟨2933299317261364738178329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15644263025393945270284421 2933299317261364738178329)
                      ·
                        rfl

theorem cell23_5712580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_5712580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712580 prefixEnd_5712580 := by exact prefixLift 5712580
  have htrace : WordTrace (prefixWord ++ tailWord_5712580) baseStart_5712580 baseEnd_5712580 := by
    simpa [prefixWord, tailWord_5712580, baseEnd_5712580] using wordTrace_append hprefix tailTrace_5712580
  have hstable : (prefixWord ++ tailWord_5712580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712580).length < 2 ^ (prefixWord ++ tailWord_5712580).sum := by decide
  have hdescent : baseEnd_5712580 < baseStart_5712580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712590 : List Nat := [4, 1, 1, 1, 3, 2, 1, 5, 1, 4]
def baseStart_5712590 : Nat := 118140960795 + 5712590 * 2 ^ 59
def prefixEnd_5712590 : Nat := 4983230072969 + 3 ^ 40 * 5712590 * 2
def baseEnd_5712590 : Nat := 977768150689303233017761

theorem tailTrace_5712590 : CollatzResearch.WordTrace tailWord_5712590 prefixEnd_5712590 977768150689303233017761 := by
  unfold tailWord_5712590
  simp only [CollatzResearch.WordTrace]
  refine ⟨26044409296783692192877903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138903516249513025028682149 26044409296783692192877903)
  ·
    refine ⟨39066613945175538289316855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26044409296783692192877903 39066613945175538289316855)
    ·
      refine ⟨58599920917763307433975283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39066613945175538289316855 58599920917763307433975283)
      ·
        refine ⟨87899881376644961150962925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58599920917763307433975283 87899881376644961150962925)
        ·
          refine ⟨32962455516241860431611097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87899881376644961150962925 32962455516241860431611097)
          ·
            refine ⟨24721841637181395323708323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32962455516241860431611097 24721841637181395323708323)
            ·
              refine ⟨37082762455772092985562485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24721841637181395323708323 37082762455772092985562485)
              ·
                refine ⟨3476508980228633717396483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37082762455772092985562485 3476508980228633717396483)
                ·
                  refine ⟨5214763470342950576094725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3476508980228633717396483 5214763470342950576094725)
                  ·
                    refine ⟨977768150689303233017761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5214763470342950576094725 977768150689303233017761)
                    ·
                      rfl

theorem cell23_5712590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_5712590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712590 prefixEnd_5712590 := by exact prefixLift 5712590
  have htrace : WordTrace (prefixWord ++ tailWord_5712590) baseStart_5712590 baseEnd_5712590 := by
    simpa [prefixWord, tailWord_5712590, baseEnd_5712590] using wordTrace_append hprefix tailTrace_5712590
  have hstable : (prefixWord ++ tailWord_5712590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712590).length < 2 ^ (prefixWord ++ tailWord_5712590).sum := by decide
  have hdescent : baseEnd_5712590 < baseStart_5712590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712623 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 1, 5, 2]
def baseStart_5712623 : Nat := 118140960795 + 5712623 * 2 ^ 59
def prefixEnd_5712623 : Nat := 4983230072969 + 3 ^ 40 * 5712623 * 2
def baseEnd_5712623 : Nat := 2933321396929508069940631

theorem tailTrace_5712623 : CollatzResearch.WordTrace tailWord_5712623 prefixEnd_5712623 2933321396929508069940631 := by
  unfold tailWord_5712623
  simp only [CollatzResearch.WordTrace]
  refine ⟨208356477983149984178974523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138904318655433322785983015 208356477983149984178974523)
  ·
    refine ⟨312534716974724976268461785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208356477983149984178974523 312534716974724976268461785)
    ·
      refine ⟨234401037731043732201346339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312534716974724976268461785 234401037731043732201346339)
      ·
        refine ⟨351601556596565598302019509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234401037731043732201346339 351601556596565598302019509)
        ·
          refine ⟨32962645930928024840814329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 351601556596565598302019509 32962645930928024840814329)
          ·
            refine ⟨24721984448196018630610747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32962645930928024840814329 24721984448196018630610747)
            ·
              refine ⟨37082976672294027945916121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24721984448196018630610747 37082976672294027945916121)
              ·
                refine ⟨27812232504220520959437091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37082976672294027945916121 27812232504220520959437091)
                ·
                  refine ⟨41718348756330781439155637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27812232504220520959437091 41718348756330781439155637)
                  ·
                    refine ⟨3911095195906010759920841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41718348756330781439155637 3911095195906010759920841)
                    ·
                      refine ⟨2933321396929508069940631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3911095195906010759920841 2933321396929508069940631)
                      ·
                        rfl

theorem cell23_5712623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 5, 2].length) (baseStart_5712623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712623 prefixEnd_5712623 := by exact prefixLift 5712623
  have htrace : WordTrace (prefixWord ++ tailWord_5712623) baseStart_5712623 baseEnd_5712623 := by
    simpa [prefixWord, tailWord_5712623, baseEnd_5712623] using wordTrace_append hprefix tailTrace_5712623
  have hstable : (prefixWord ++ tailWord_5712623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712623).length < 2 ^ (prefixWord ++ tailWord_5712623).sum := by decide
  have hdescent : baseEnd_5712623 < baseStart_5712623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712630 : List Nat := [5, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3]
def baseStart_5712630 : Nat := 118140960795 + 5712630 * 2 ^ 59
def prefixEnd_5712630 : Nat := 4983230072969 + 3 ^ 40 * 5712630 * 2
def baseEnd_5712630 : Nat := 2933324991294089542553099

theorem tailTrace_5712630 : CollatzResearch.WordTrace tailWord_5712630 prefixEnd_5712630 2933324991294089542553099 := by
  unfold tailWord_5712630
  simp only [CollatzResearch.WordTrace]
  refine ⟨13022295830882789023404959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138904488862749749582986229 13022295830882789023404959)
  ·
    refine ⟨19533443746324183535107439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13022295830882789023404959 19533443746324183535107439)
    ·
      refine ⟨29300165619486275302661159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19533443746324183535107439 29300165619486275302661159)
      ·
        refine ⟨43950248429229412953991739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29300165619486275302661159 43950248429229412953991739)
        ·
          refine ⟨65925372643844119430987609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43950248429229412953991739 65925372643844119430987609)
          ·
            refine ⟨49444029482883089573240707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65925372643844119430987609 49444029482883089573240707)
            ·
              refine ⟨74166044224324634359861061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49444029482883089573240707 74166044224324634359861061)
              ·
                refine ⟨13906133292060868942473949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74166044224324634359861061 13906133292060868942473949)
                ·
                  refine ⟨5214799984522825853427731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13906133292060868942473949 5214799984522825853427731)
                  ·
                    refine ⟨7822199976784238780141597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5214799984522825853427731 7822199976784238780141597)
                    ·
                      refine ⟨2933324991294089542553099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7822199976784238780141597 2933324991294089542553099)
                      ·
                        rfl

theorem cell23_5712630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_5712630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712630 prefixEnd_5712630 := by exact prefixLift 5712630
  have htrace : WordTrace (prefixWord ++ tailWord_5712630) baseStart_5712630 baseEnd_5712630 := by
    simpa [prefixWord, tailWord_5712630, baseEnd_5712630] using wordTrace_append hprefix tailTrace_5712630
  have hstable : (prefixWord ++ tailWord_5712630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712630).length < 2 ^ (prefixWord ++ tailWord_5712630).sum := by decide
  have hdescent : baseEnd_5712630 < baseStart_5712630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712666 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6]
def baseStart_5712666 : Nat := 118140960795 + 5712666 * 2 ^ 59
def prefixEnd_5712666 : Nat := 4983230072969 + 3 ^ 40 * 5712666 * 2
def baseEnd_5712666 : Nat := 2933343476597651401702933

theorem tailTrace_5712666 : CollatzResearch.WordTrace tailWord_5712666 prefixEnd_5712666 2933343476597651401702933 := by
  unfold tailWord_5712666
  simp only [CollatzResearch.WordTrace]
  refine ⟨52089511580498550630697463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138905364214662801681859901 52089511580498550630697463)
  ·
    refine ⟨78134267370747825946046195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52089511580498550630697463 78134267370747825946046195)
    ·
      refine ⟨117201401056121738919069293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78134267370747825946046195 117201401056121738919069293)
      ·
        refine ⟨43950525396045652094650985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117201401056121738919069293 43950525396045652094650985)
        ·
          refine ⟨32962894047034239070988239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43950525396045652094650985 32962894047034239070988239)
          ·
            refine ⟨49444341070551358606482359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32962894047034239070988239 49444341070551358606482359)
            ·
              refine ⟨74166511605827037909723539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49444341070551358606482359 74166511605827037909723539)
              ·
                refine ⟨111249767408740556864585309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74166511605827037909723539 111249767408740556864585309)
                ·
                  refine ⟨41718662778277708824219491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111249767408740556864585309 41718662778277708824219491)
                  ·
                    refine ⟨62577994167416563236329237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41718662778277708824219491 62577994167416563236329237)
                    ·
                      refine ⟨2933343476597651401702933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62577994167416563236329237 2933343476597651401702933)
                      ·
                        rfl

theorem cell23_5712666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_5712666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712666 prefixEnd_5712666 := by exact prefixLift 5712666
  have htrace : WordTrace (prefixWord ++ tailWord_5712666) baseStart_5712666 baseEnd_5712666 := by
    simpa [prefixWord, tailWord_5712666, baseEnd_5712666] using wordTrace_append hprefix tailTrace_5712666
  have hstable : (prefixWord ++ tailWord_5712666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712666).length < 2 ^ (prefixWord ++ tailWord_5712666).sum := by decide
  have hdescent : baseEnd_5712666 < baseStart_5712666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712673 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 3, 2, 3]
def baseStart_5712673 : Nat := 118140960795 + 5712673 * 2 ^ 59
def prefixEnd_5712673 : Nat := 4983230072969 + 3 ^ 40 * 5712673 * 2
def baseEnd_5712673 : Nat := 2933347070962232874315401

theorem tailTrace_5712673 : CollatzResearch.WordTrace tailWord_5712673 prefixEnd_5712673 2933347070962232874315401 := by
  unfold tailWord_5712673
  simp only [CollatzResearch.WordTrace]
  refine ⟨208358301632968842718294673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138905534421979228478863115 208358301632968842718294673)
  ·
    refine ⟨156268726224726632038721005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208358301632968842718294673 156268726224726632038721005)
    ·
      refine ⟨58600772334272487014520377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156268726224726632038721005 58600772334272487014520377)
      ·
        refine ⟨43950579250704365260890283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58600772334272487014520377 43950579250704365260890283)
        ·
          refine ⟨65925868876056547891335425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43950579250704365260890283 65925868876056547891335425)
          ·
            refine ⟨49444401657042410918501569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65925868876056547891335425 49444401657042410918501569)
            ·
              refine ⟨37083301242781808188876177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49444401657042410918501569 37083301242781808188876177)
              ·
                refine ⟨27812475932086356141657133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37083301242781808188876177 27812475932086356141657133)
                ·
                  refine ⟨10429678474532383553121425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27812475932086356141657133 10429678474532383553121425)
                  ·
                    refine ⟨7822258855899287664841069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10429678474532383553121425 7822258855899287664841069)
                    ·
                      refine ⟨2933347070962232874315401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7822258855899287664841069 2933347070962232874315401)
                      ·
                        rfl

theorem cell23_5712673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_5712673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712673 prefixEnd_5712673 := by exact prefixLift 5712673
  have htrace : WordTrace (prefixWord ++ tailWord_5712673) baseStart_5712673 baseEnd_5712673 := by
    simpa [prefixWord, tailWord_5712673, baseEnd_5712673] using wordTrace_append hprefix tailTrace_5712673
  have hstable : (prefixWord ++ tailWord_5712673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712673).length < 2 ^ (prefixWord ++ tailWord_5712673).sum := by decide
  have hdescent : baseEnd_5712673 < baseStart_5712673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712680 : List Nat := [2, 1, 5, 1, 1, 1, 3, 3, 2, 4]
def baseStart_5712680 : Nat := 118140960795 + 5712680 * 2 ^ 59
def prefixEnd_5712680 : Nat := 4983230072969 + 3 ^ 40 * 5712680 * 2
def baseEnd_5712680 : Nat := 977783555108938115642623

theorem tailTrace_5712680 : CollatzResearch.WordTrace tailWord_5712680 prefixEnd_5712680 977783555108938115642623 := by
  unfold tailWord_5712680
  simp only [CollatzResearch.WordTrace]
  refine ⟨104179278471971741456899747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138905704629295655275866329 104179278471971741456899747)
  ·
    refine ⟨156268917707957612185349621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104179278471971741456899747 156268917707957612185349621)
    ·
      refine ⟨14650211035121026142376527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 156268917707957612185349621 14650211035121026142376527)
      ·
        refine ⟨21975316552681539213564791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14650211035121026142376527 21975316552681539213564791)
        ·
          refine ⟨32962974829022308820347187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21975316552681539213564791 32962974829022308820347187)
          ·
            refine ⟨49444462243533463230520781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32962974829022308820347187 49444462243533463230520781)
            ·
              refine ⟨18541673341325048711445293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49444462243533463230520781 18541673341325048711445293)
              ·
                refine ⟨6953127502996893266791985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18541673341325048711445293 6953127502996893266791985)
                ·
                  refine ⟨5214845627247669950093989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6953127502996893266791985 5214845627247669950093989)
                  ·
                    refine ⟨977783555108938115642623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5214845627247669950093989 977783555108938115642623)
                    ·
                      rfl

theorem cell23_5712680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_5712680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712680 prefixEnd_5712680 := by exact prefixLift 5712680
  have htrace : WordTrace (prefixWord ++ tailWord_5712680) baseStart_5712680 baseEnd_5712680 := by
    simpa [prefixWord, tailWord_5712680, baseEnd_5712680] using wordTrace_append hprefix tailTrace_5712680
  have hstable : (prefixWord ++ tailWord_5712680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712680).length < 2 ^ (prefixWord ++ tailWord_5712680).sum := by decide
  have hdescent : baseEnd_5712680 < baseStart_5712680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712703 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 3]
def baseStart_5712703 : Nat := 118140960795 + 5712703 * 2 ^ 59
def prefixEnd_5712703 : Nat := 4983230072969 + 3 ^ 40 * 5712703 * 2
def baseEnd_5712703 : Nat := 2933362475381867756940263

theorem tailTrace_5712703 : CollatzResearch.WordTrace tailWord_5712703 prefixEnd_5712703 2933362475381867756940263 := by
  unfold tailWord_5712703
  simp only [CollatzResearch.WordTrace]
  refine ⟨208359395822860157841886763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138906263881906771894591175 208359395822860157841886763)
  ·
    refine ⟨312539093734290236762830145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208359395822860157841886763 312539093734290236762830145)
    ·
      refine ⟨234404320300717677572122609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312539093734290236762830145 234404320300717677572122609)
      ·
        refine ⟨175803240225538258179091957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234404320300717677572122609 175803240225538258179091957)
        ·
          refine ⟨16481553771144211704289871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 175803240225538258179091957 16481553771144211704289871)
          ·
            refine ⟨24722330656716317556434807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16481553771144211704289871 24722330656716317556434807)
            ·
              refine ⟨37083495985074476334652211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24722330656716317556434807 37083495985074476334652211)
              ·
                refine ⟨55625243977611714501978317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37083495985074476334652211 55625243977611714501978317)
                ·
                  refine ⟨20859466491604392938241869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55625243977611714501978317 20859466491604392938241869)
                  ·
                    refine ⟨7822299934351647351840701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20859466491604392938241869 7822299934351647351840701)
                    ·
                      refine ⟨2933362475381867756940263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7822299934351647351840701 2933362475381867756940263)
                      ·
                        rfl

theorem cell23_5712703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 3].length) (baseStart_5712703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712703 prefixEnd_5712703 := by exact prefixLift 5712703
  have htrace : WordTrace (prefixWord ++ tailWord_5712703) baseStart_5712703 baseEnd_5712703 := by
    simpa [prefixWord, tailWord_5712703, baseEnd_5712703] using wordTrace_append hprefix tailTrace_5712703
  have hstable : (prefixWord ++ tailWord_5712703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712703).length < 2 ^ (prefixWord ++ tailWord_5712703).sum := by decide
  have hdescent : baseEnd_5712703 < baseStart_5712703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712710 : List Nat := [6, 1, 1, 2, 2, 11]
def baseStart_5712710 : Nat := 118140960795 + 5712710 * 2 ^ 59
def prefixEnd_5712710 : Nat := 4983230072969 + 3 ^ 40 * 5712710 * 2
def baseEnd_5712710 : Nat := 12071465307598556500217

theorem tailTrace_5712710 : CollatzResearch.WordTrace tailWord_5712710 prefixEnd_5712710 12071465307598556500217 := by
  unfold tailWord_5712710
  simp only [CollatzResearch.WordTrace]
  refine ⟨6511239097932337438668487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 138906434089223198691594389 6511239097932337438668487)
  ·
    refine ⟨9766858646898506158002731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6511239097932337438668487 9766858646898506158002731)
    ·
      refine ⟨14650287970347759237004097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9766858646898506158002731 14650287970347759237004097)
      ·
        refine ⟨10987715977760819427753073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14650287970347759237004097 10987715977760819427753073)
        ·
          refine ⟨8240786983320614570814805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10987715977760819427753073 8240786983320614570814805)
          ·
            refine ⟨12071465307598556500217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8240786983320614570814805 12071465307598556500217)
            ·
              rfl

theorem cell23_5712710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 11].length) (baseStart_5712710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712710 prefixEnd_5712710 := by exact prefixLift 5712710
  have htrace : WordTrace (prefixWord ++ tailWord_5712710) baseStart_5712710 baseEnd_5712710 := by
    simpa [prefixWord, tailWord_5712710, baseEnd_5712710] using wordTrace_append hprefix tailTrace_5712710
  have hstable : (prefixWord ++ tailWord_5712710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712710).length < 2 ^ (prefixWord ++ tailWord_5712710).sum := by decide
  have hdescent : baseEnd_5712710 < baseStart_5712710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712720 : List Nat := [2, 1, 1, 1, 1, 4, 3, 4, 2, 1, 3]
def baseStart_5712720 : Nat := 118140960795 + 5712720 * 2 ^ 59
def prefixEnd_5712720 : Nat := 4983230072969 + 3 ^ 40 * 5712720 * 2
def baseEnd_5712720 : Nat := 2933371204552994190427685

theorem tailTrace_5712720 : CollatzResearch.WordTrace tailWord_5712720 prefixEnd_5712720 2933371204552994190427685 := by
  unfold tailWord_5712720
  simp only [CollatzResearch.WordTrace]
  refine ⟨104180007931899284872627807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138906677242532379830170409 104180007931899284872627807)
  ·
    refine ⟨156270011897848927308941711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104180007931899284872627807 156270011897848927308941711)
    ·
      refine ⟨234405017846773390963412567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156270011897848927308941711 234405017846773390963412567)
      ·
        refine ⟨351607526770160086445118851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234405017846773390963412567 351607526770160086445118851)
        ·
          refine ⟨527411290155240129667678277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351607526770160086445118851 527411290155240129667678277)
          ·
            refine ⟨98889616904107524312689677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 527411290155240129667678277 98889616904107524312689677)
            ·
              refine ⟨37083606339040321617258629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98889616904107524312689677 37083606339040321617258629)
              ·
                refine ⟨6953176188570060303235993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37083606339040321617258629 6953176188570060303235993)
                ·
                  refine ⟨5214882141427545227426995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6953176188570060303235993 5214882141427545227426995)
                  ·
                    refine ⟨7822323212141317841140493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5214882141427545227426995 7822323212141317841140493)
                    ·
                      refine ⟨2933371204552994190427685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7822323212141317841140493 2933371204552994190427685)
                      ·
                        rfl

theorem cell23_5712720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 2, 1, 3].length) (baseStart_5712720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712720 prefixEnd_5712720 := by exact prefixLift 5712720
  have htrace : WordTrace (prefixWord ++ tailWord_5712720) baseStart_5712720 baseEnd_5712720 := by
    simpa [prefixWord, tailWord_5712720, baseEnd_5712720] using wordTrace_append hprefix tailTrace_5712720
  have hstable : (prefixWord ++ tailWord_5712720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712720).length < 2 ^ (prefixWord ++ tailWord_5712720).sum := by decide
  have hdescent : baseEnd_5712720 < baseStart_5712720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712730 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2]
def baseStart_5712730 : Nat := 118140960795 + 5712730 * 2 ^ 59
def prefixEnd_5712730 : Nat := 4983230072969 + 3 ^ 40 * 5712730 * 2
def baseEnd_5712730 : Nat := 2933376339359539151302639

theorem tailTrace_5712730 : CollatzResearch.WordTrace tailWord_5712730 prefixEnd_5712730 2933376339359539151302639 := by
  unfold tailWord_5712730
  simp only [CollatzResearch.WordTrace]
  refine ⟨52090095148440585363279911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138906920395841560968746429 52090095148440585363279911)
  ·
    refine ⟨78135142722660878044919867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52090095148440585363279911 78135142722660878044919867)
    ·
      refine ⟨117202714083991317067379801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78135142722660878044919867 117202714083991317067379801)
      ·
        refine ⟨87902035562993487800534851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117202714083991317067379801 87902035562993487800534851)
        ·
          refine ⟨131853053344490231700802277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87902035562993487800534851 131853053344490231700802277)
          ·
            refine ⟨24722447502091918443900427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131853053344490231700802277 24722447502091918443900427)
            ·
              refine ⟨37083671253137877665850641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24722447502091918443900427 37083671253137877665850641)
              ·
                refine ⟨27812753439853408249387981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37083671253137877665850641 27812753439853408249387981)
                ·
                  refine ⟨10429782539945028093520493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27812753439853408249387981 10429782539945028093520493)
                  ·
                    refine ⟨3911168452479385535070185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10429782539945028093520493 3911168452479385535070185)
                    ·
                      refine ⟨2933376339359539151302639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3911168452479385535070185 2933376339359539151302639)
                      ·
                        rfl

theorem cell23_5712730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2].length) (baseStart_5712730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712730 prefixEnd_5712730 := by exact prefixLift 5712730
  have htrace : WordTrace (prefixWord ++ tailWord_5712730) baseStart_5712730 baseEnd_5712730 := by
    simpa [prefixWord, tailWord_5712730, baseEnd_5712730] using wordTrace_append hprefix tailTrace_5712730
  have hstable : (prefixWord ++ tailWord_5712730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712730).length < 2 ^ (prefixWord ++ tailWord_5712730).sum := by decide
  have hdescent : baseEnd_5712730 < baseStart_5712730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712773 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 2, 2, 4]
def baseStart_5712773 : Nat := 118140960795 + 5712773 * 2 ^ 59
def prefixEnd_5712773 : Nat := 4983230072969 + 3 ^ 40 * 5712773 * 2
def baseEnd_5712773 : Nat := 2933398419027682483064941

theorem tailTrace_5712773 : CollatzResearch.WordTrace tailWord_5712773 prefixEnd_5712773 2933398419027682483064941 := by
  unfold tailWord_5712773
  simp only [CollatzResearch.WordTrace]
  refine ⟨208361948932606559796934973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138907965955071039864623315 208361948932606559796934973)
  ·
    refine ⟨78135730849727459923850615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208361948932606559796934973 78135730849727459923850615)
    ·
      refine ⟨117203596274591189885775923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78135730849727459923850615 117203596274591189885775923)
      ·
        refine ⟨175805394411886784828663885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117203596274591189885775923 175805394411886784828663885)
        ·
          refine ⟨65927022904457544310748957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175805394411886784828663885 65927022904457544310748957)
          ·
            refine ⟨24722633589171579116530859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65927022904457544310748957 24722633589171579116530859)
            ·
              refine ⟨37083950383757368674796289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24722633589171579116530859 37083950383757368674796289)
              ·
                refine ⟨27812962787818026506097217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37083950383757368674796289 27812962787818026506097217)
                ·
                  refine ⟨20859722090863519879572913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27812962787818026506097217 20859722090863519879572913)
                  ·
                    refine ⟨15644791568147639909679685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20859722090863519879572913 15644791568147639909679685)
                    ·
                      refine ⟨2933398419027682483064941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15644791568147639909679685 2933398419027682483064941)
                      ·
                        rfl

theorem cell23_5712773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_5712773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712773 prefixEnd_5712773 := by exact prefixLift 5712773
  have htrace : WordTrace (prefixWord ++ tailWord_5712773) baseStart_5712773 baseEnd_5712773 := by
    simpa [prefixWord, tailWord_5712773, baseEnd_5712773] using wordTrace_append hprefix tailTrace_5712773
  have hstable : (prefixWord ++ tailWord_5712773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712773).length < 2 ^ (prefixWord ++ tailWord_5712773).sum := by decide
  have hdescent : baseEnd_5712773 < baseStart_5712773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712777 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 4, 2, 2]
def baseStart_5712777 : Nat := 118140960795 + 5712777 * 2 ^ 59
def prefixEnd_5712777 : Nat := 4983230072969 + 3 ^ 40 * 5712777 * 2
def baseEnd_5712777 : Nat := 2933400472950300467414923

theorem tailTrace_5712777 : CollatzResearch.WordTrace tailWord_5712777 prefixEnd_5712777 2933400472950300467414923 := by
  unfold tailWord_5712777
  simp only [CollatzResearch.WordTrace]
  refine ⟨208362094824592068480080585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138908063216394712320053723 208362094824592068480080585)
  ·
    refine ⟨156271571118444051360060439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208362094824592068480080585 156271571118444051360060439)
    ·
      refine ⟨234407356677666077040090659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156271571118444051360060439 234407356677666077040090659)
      ·
        refine ⟨351611035016499115560135989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234407356677666077040090659 351611035016499115560135989)
        ·
          refine ⟨32963534532796792083762749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 351611035016499115560135989 32963534532796792083762749)
          ·
            refine ⟨12361325449798797031411031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32963534532796792083762749 12361325449798797031411031)
            ·
              refine ⟨18541988174698195547116547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12361325449798797031411031 18541988174698195547116547)
              ·
                refine ⟨27812982262047293320674821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18541988174698195547116547 27812982262047293320674821)
                ·
                  refine ⟨5214934174133867497626529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27812982262047293320674821 5214934174133867497626529)
                  ·
                    refine ⟨3911200630600400623219897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5214934174133867497626529 3911200630600400623219897)
                    ·
                      refine ⟨2933400472950300467414923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3911200630600400623219897 2933400472950300467414923)
                      ·
                        rfl

theorem cell23_5712777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 2, 2].length) (baseStart_5712777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712777 prefixEnd_5712777 := by exact prefixLift 5712777
  have htrace : WordTrace (prefixWord ++ tailWord_5712777) baseStart_5712777 baseEnd_5712777 := by
    simpa [prefixWord, tailWord_5712777, baseEnd_5712777] using wordTrace_append hprefix tailTrace_5712777
  have hstable : (prefixWord ++ tailWord_5712777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712777).length < 2 ^ (prefixWord ++ tailWord_5712777).sum := by decide
  have hdescent : baseEnd_5712777 < baseStart_5712777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
