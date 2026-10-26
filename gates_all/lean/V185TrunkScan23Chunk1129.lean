import V185TrunkScan23Chunk1128

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6687274 : List Nat := [3, 1, 4, 1, 1, 2, 4, 1, 1, 2, 3]
def baseStart_6687274 : Nat := 118140960795 + 6687274 * 2 ^ 59
def prefixEnd_6687274 : Nat := 4983230072969 + 3 ^ 40 * 6687274 * 2
def baseEnd_6687274 : Nat := 3433785830314774243420793

theorem tailTrace_6687274 : CollatzResearch.WordTrace tailWord_6687274 prefixEnd_6687274 3433785830314774243420793 := by
  unfold tailWord_6687274
  simp only [CollatzResearch.WordTrace]
  refine ⟨60976230093788967079361219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162603280250103912211629917 60976230093788967079361219)
  ·
    refine ⟨91464345140683450619041829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60976230093788967079361219 91464345140683450619041829)
    ·
      refine ⟨17149564713878146991070343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91464345140683450619041829 17149564713878146991070343)
      ·
        refine ⟨25724347070817220486605515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17149564713878146991070343 25724347070817220486605515)
        ·
          refine ⟨38586520606225830729908273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25724347070817220486605515 38586520606225830729908273)
          ·
            refine ⟨28939890454669373047431205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38586520606225830729908273 28939890454669373047431205)
            ·
              refine ⟨5426229460250507446393351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28939890454669373047431205 5426229460250507446393351)
              ·
                refine ⟨8139344190375761169590027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5426229460250507446393351 8139344190375761169590027)
                ·
                  refine ⟨12209016285563641754385041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8139344190375761169590027 12209016285563641754385041)
                  ·
                    refine ⟨9156762214172731315788781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12209016285563641754385041 9156762214172731315788781)
                    ·
                      refine ⟨3433785830314774243420793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9156762214172731315788781 3433785830314774243420793)
                      ·
                        rfl

theorem cell23_6687274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_6687274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687274 prefixEnd_6687274 := by exact prefixLift 6687274
  have htrace : WordTrace (prefixWord ++ tailWord_6687274) baseStart_6687274 baseEnd_6687274 := by
    simpa [prefixWord, tailWord_6687274, baseEnd_6687274] using wordTrace_append hprefix tailTrace_6687274
  have hstable : (prefixWord ++ tailWord_6687274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687274).length < 2 ^ (prefixWord ++ tailWord_6687274).sum := by decide
  have hdescent : baseEnd_6687274 < baseStart_6687274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687314 : List Nat := [3, 2, 2, 1, 2, 1, 4, 2, 1, 3, 2]
def baseStart_6687314 : Nat := 118140960795 + 6687314 * 2 ^ 59
def prefixEnd_6687314 : Nat := 4983230072969 + 3 ^ 40 * 6687314 * 2
def baseEnd_6687314 : Nat := 3433806369540954086920609

theorem tailTrace_6687314 : CollatzResearch.WordTrace tailWord_6687314 prefixEnd_6687314 3433806369540954086920609 := by
  unfold tailWord_6687314
  simp only [CollatzResearch.WordTrace]
  refine ⟨60976594823752738787225249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162604252863340636765933997 60976594823752738787225249)
  ·
    refine ⟨45732446117814554090418937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60976594823752738787225249 45732446117814554090418937)
    ·
      refine ⟨34299334588360915567814203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45732446117814554090418937 34299334588360915567814203)
      ·
        refine ⟨51449001882541373351721305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34299334588360915567814203 51449001882541373351721305)
        ·
          refine ⟨38586751411906030013790979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51449001882541373351721305 38586751411906030013790979)
          ·
            refine ⟨57880127117859045020686469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38586751411906030013790979 57880127117859045020686469)
            ·
              refine ⟨10852523834598570941378713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57880127117859045020686469 10852523834598570941378713)
              ·
                refine ⟨8139392875948928206034035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10852523834598570941378713 8139392875948928206034035)
                ·
                  refine ⟨12209089313923392309051053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8139392875948928206034035 12209089313923392309051053)
                  ·
                    refine ⟨4578408492721272115894145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12209089313923392309051053 4578408492721272115894145)
                    ·
                      refine ⟨3433806369540954086920609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4578408492721272115894145 3433806369540954086920609)
                      ·
                        rfl

theorem cell23_6687314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_6687314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687314 prefixEnd_6687314 := by exact prefixLift 6687314
  have htrace : WordTrace (prefixWord ++ tailWord_6687314) baseStart_6687314 baseEnd_6687314 := by
    simpa [prefixWord, tailWord_6687314, baseEnd_6687314] using wordTrace_append hprefix tailTrace_6687314
  have hstable : (prefixWord ++ tailWord_6687314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687314).length < 2 ^ (prefixWord ++ tailWord_6687314).sum := by decide
  have hdescent : baseEnd_6687314 < baseStart_6687314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687363 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 3, 7]
def baseStart_6687363 : Nat := 118140960795 + 6687363 * 2 ^ 59
def prefixEnd_6687363 : Nat := 4983230072969 + 3 ^ 40 * 6687363 * 2
def baseEnd_6687363 : Nat := 1144610510031008131735961

theorem tailTrace_6687363 : CollatzResearch.WordTrace tailWord_6687363 prefixEnd_6687363 1144610510031008131735961 := by
  unfold tailWord_6687363
  simp only [CollatzResearch.WordTrace]
  refine ⟨243908166471833436517434743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162605444314555624344956495 243908166471833436517434743)
  ·
    refine ⟨365862249707750154776152115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243908166471833436517434743 365862249707750154776152115)
    ·
      refine ⟨548793374561625232164228173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365862249707750154776152115 548793374561625232164228173)
      ·
        refine ⟨205797515460609462061585565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 548793374561625232164228173 205797515460609462061585565)
        ·
          refine ⟨77174068297728548273094587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205797515460609462061585565 77174068297728548273094587)
          ·
            refine ⟨115761102446592822409641881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77174068297728548273094587 115761102446592822409641881)
            ·
              refine ⟨86820826834944616807231411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115761102446592822409641881 86820826834944616807231411)
              ·
                refine ⟨130231240252416925210847117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86820826834944616807231411 130231240252416925210847117)
                ·
                  refine ⟨48836715094656346954067669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130231240252416925210847117 48836715094656346954067669)
                  ·
                    refine ⟨1144610510031008131735961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48836715094656346954067669 1144610510031008131735961)
                    ·
                      rfl

theorem cell23_6687363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 7].length) (baseStart_6687363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687363 prefixEnd_6687363 := by exact prefixLift 6687363
  have htrace : WordTrace (prefixWord ++ tailWord_6687363) baseStart_6687363 baseEnd_6687363 := by
    simpa [prefixWord, tailWord_6687363, baseEnd_6687363] using wordTrace_append hprefix tailTrace_6687363
  have hstable : (prefixWord ++ tailWord_6687363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687363).length < 2 ^ (prefixWord ++ tailWord_6687363).sum := by decide
  have hdescent : baseEnd_6687363 < baseStart_6687363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687434 : List Nat := [3, 1, 2, 1, 4, 3, 1, 1, 2, 1, 4]
def baseStart_6687434 : Nat := 118140960795 + 6687434 * 2 ^ 59
def prefixEnd_6687434 : Nat := 4983230072969 + 3 ^ 40 * 6687434 * 2
def baseEnd_6687434 : Nat := 3433867987219493617420057

theorem tailTrace_6687434 : CollatzResearch.WordTrace tailWord_6687434 prefixEnd_6687434 3433867987219493617420057 := by
  unfold tailWord_6687434
  simp only [CollatzResearch.WordTrace]
  refine ⟨60977689013644053910817339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162607170703050810428846237 60977689013644053910817339)
  ·
    refine ⟨91466533520466080866226009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60977689013644053910817339 91466533520466080866226009)
    ·
      refine ⟨68599900140349560649669507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91466533520466080866226009 68599900140349560649669507)
      ·
        refine ⟨102899850210524340974504261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68599900140349560649669507 102899850210524340974504261)
        ·
          refine ⟨19293721914473313932719549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102899850210524340974504261 19293721914473313932719549)
          ·
            refine ⟨7235145717927492724769831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19293721914473313932719549 7235145717927492724769831)
            ·
              refine ⟨10852718576891239087154747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7235145717927492724769831 10852718576891239087154747)
              ·
                refine ⟨16279077865336858630732121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10852718576891239087154747 16279077865336858630732121)
                ·
                  refine ⟨12209308399002643973049091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16279077865336858630732121 12209308399002643973049091)
                  ·
                    refine ⟨18313962598503965959573637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12209308399002643973049091 18313962598503965959573637)
                    ·
                      refine ⟨3433867987219493617420057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18313962598503965959573637 3433867987219493617420057)
                      ·
                        rfl

theorem cell23_6687434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_6687434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687434 prefixEnd_6687434 := by exact prefixLift 6687434
  have htrace : WordTrace (prefixWord ++ tailWord_6687434) baseStart_6687434 baseEnd_6687434 := by
    simpa [prefixWord, tailWord_6687434, baseEnd_6687434] using wordTrace_append hprefix tailTrace_6687434
  have hstable : (prefixWord ++ tailWord_6687434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687434).length < 2 ^ (prefixWord ++ tailWord_6687434).sum := by decide
  have hdescent : baseEnd_6687434 < baseStart_6687434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687457 : List Nat := [1, 2, 3, 1, 4, 1, 3, 2, 6]
def baseStart_6687457 : Nat := 118140960795 + 6687457 * 2 ^ 59
def prefixEnd_6687457 : Nat := 4983230072969 + 3 ^ 40 * 6687457 * 2
def baseEnd_6687457 : Nat := 381542199697171891936939

theorem tailTrace_6687457 : CollatzResearch.WordTrace tailWord_6687457 prefixEnd_6687457 381542199697171891936939 := by
  unfold tailWord_6687457
  simp only [CollatzResearch.WordTrace]
  refine ⟨243911594933492890571356625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162607729955661927047571083 243911594933492890571356625)
  ·
    refine ⟨182933696200119667928517469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243911594933492890571356625 182933696200119667928517469)
    ·
      refine ⟨68600136075044875473194051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182933696200119667928517469 68600136075044875473194051)
      ·
        refine ⟨102900204112567313209791077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68600136075044875473194051 102900204112567313209791077)
        ·
          refine ⟨19293788271106371226835827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102900204112567313209791077 19293788271106371226835827)
          ·
            refine ⟨28940682406659556840253741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19293788271106371226835827 28940682406659556840253741)
            ·
              refine ⟨10852755902497333815095153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28940682406659556840253741 10852755902497333815095153)
              ·
                refine ⟨8139566926873000361321365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10852755902497333815095153 8139566926873000361321365)
                ·
                  refine ⟨381542199697171891936939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8139566926873000361321365 381542199697171891936939)
                  ·
                    rfl

theorem cell23_6687457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 6].length) (baseStart_6687457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687457 prefixEnd_6687457 := by exact prefixLift 6687457
  have htrace : WordTrace (prefixWord ++ tailWord_6687457) baseStart_6687457 baseEnd_6687457 := by
    simpa [prefixWord, tailWord_6687457, baseEnd_6687457] using wordTrace_append hprefix tailTrace_6687457
  have hstable : (prefixWord ++ tailWord_6687457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687457).length < 2 ^ (prefixWord ++ tailWord_6687457).sum := by decide
  have hdescent : baseEnd_6687457 < baseStart_6687457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687460 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 1, 2, 6]
def baseStart_6687460 : Nat := 118140960795 + 6687460 * 2 ^ 59
def prefixEnd_6687460 : Nat := 4983230072969 + 3 ^ 40 * 6687460 * 2
def baseEnd_6687460 : Nat := 3433881337716510515694937

theorem tailTrace_6687460 : CollatzResearch.WordTrace tailWord_6687460 prefixEnd_6687460 3433881337716510515694937 := by
  unfold tailWord_6687460
  simp only [CollatzResearch.WordTrace]
  refine ⟨121955852176241011041857917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162607802901654681389143889 121955852176241011041857917)
  ·
    refine ⟨45733444566090379140696719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121955852176241011041857917 45733444566090379140696719)
    ·
      refine ⟨68600166849135568711045079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45733444566090379140696719 68600166849135568711045079)
      ·
        refine ⟨102900250273703353066567619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68600166849135568711045079 102900250273703353066567619)
        ·
          refine ⟨154350375410555029599851429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102900250273703353066567619 154350375410555029599851429)
          ·
            refine ⟨28940695389479068049972143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154350375410555029599851429 28940695389479068049972143)
            ·
              refine ⟨43411043084218602074958215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28940695389479068049972143 43411043084218602074958215)
              ·
                refine ⟨65116564626327903112437323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43411043084218602074958215 65116564626327903112437323)
                ·
                  refine ⟨97674846939491854668655985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65116564626327903112437323 97674846939491854668655985)
                  ·
                    refine ⟨73256135204618891001491989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97674846939491854668655985 73256135204618891001491989)
                    ·
                      refine ⟨3433881337716510515694937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73256135204618891001491989 3433881337716510515694937)
                      ·
                        rfl

theorem cell23_6687460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_6687460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687460 prefixEnd_6687460 := by exact prefixLift 6687460
  have htrace : WordTrace (prefixWord ++ tailWord_6687460) baseStart_6687460 baseEnd_6687460 := by
    simpa [prefixWord, tailWord_6687460, baseEnd_6687460] using wordTrace_append hprefix tailTrace_6687460
  have hstable : (prefixWord ++ tailWord_6687460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687460).length < 2 ^ (prefixWord ++ tailWord_6687460).sum := by decide
  have hdescent : baseEnd_6687460 < baseStart_6687460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687474 : List Nat := [3, 2, 1, 3, 1, 3, 3, 1, 6]
def baseStart_6687474 : Nat := 118140960795 + 6687474 * 2 ^ 59
def prefixEnd_6687474 : Nat := 4983230072969 + 3 ^ 40 * 6687474 * 2
def baseEnd_6687474 : Nat := 381543169605074828991097

theorem tailTrace_6687474 : CollatzResearch.WordTrace tailWord_6687474 prefixEnd_6687474 381543169605074828991097 := by
  unfold tailWord_6687474
  simp only [CollatzResearch.WordTrace]
  refine ⟨60978053743607825618681369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162608143316287534983150317 60978053743607825618681369)
  ·
    refine ⟨45733540307705869214011027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60978053743607825618681369 45733540307705869214011027)
    ·
      refine ⟨68600310461558803821016541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45733540307705869214011027 68600310461558803821016541)
      ·
        refine ⟨25725116423084551432881203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68600310461558803821016541 25725116423084551432881203)
        ·
          refine ⟨38587674634626827149321805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25725116423084551432881203 38587674634626827149321805)
          ·
            refine ⟨14470377987985060180995677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38587674634626827149321805 14470377987985060180995677)
            ·
              refine ⟨5426391745494397567873379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14470377987985060180995677 5426391745494397567873379)
              ·
                refine ⟨8139587618241596351810069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5426391745494397567873379 8139587618241596351810069)
                ·
                  refine ⟨381543169605074828991097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8139587618241596351810069 381543169605074828991097)
                  ·
                    rfl

theorem cell23_6687474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_6687474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687474 prefixEnd_6687474 := by exact prefixLift 6687474
  have htrace : WordTrace (prefixWord ++ tailWord_6687474) baseStart_6687474 baseEnd_6687474 := by
    simpa [prefixWord, tailWord_6687474, baseEnd_6687474] using wordTrace_append hprefix tailTrace_6687474
  have hstable : (prefixWord ++ tailWord_6687474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687474).length < 2 ^ (prefixWord ++ tailWord_6687474).sum := by decide
  have hdescent : baseEnd_6687474 < baseStart_6687474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687484 : List Nat := [2, 2, 2, 1, 3, 2, 2, 2, 3, 1, 3]
def baseStart_6687484 : Nat := 118140960795 + 6687484 * 2 ^ 59
def prefixEnd_6687484 : Nat := 4983230072969 + 3 ^ 40 * 6687484 * 2
def baseEnd_6687484 : Nat := 3433893661252218421794827

theorem tailTrace_6687484 : CollatzResearch.WordTrace tailWord_6687484 prefixEnd_6687484 3433893661252218421794827 := by
  unfold tailWord_6687484
  simp only [CollatzResearch.WordTrace]
  refine ⟨121956289852197537091294753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162608386469596716121726337 121956289852197537091294753)
  ·
    refine ⟨91467217389148152818471065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121956289852197537091294753 91467217389148152818471065)
    ·
      refine ⟨68600413041861114613853299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91467217389148152818471065 68600413041861114613853299)
      ·
        refine ⟨102900619562791671920779949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68600413041861114613853299 102900619562791671920779949)
        ·
          refine ⟨38587732336046876970292481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102900619562791671920779949 38587732336046876970292481)
          ·
            refine ⟨28940799252035157727719361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38587732336046876970292481 28940799252035157727719361)
            ·
              refine ⟨21705599439026368295789521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28940799252035157727719361 21705599439026368295789521)
              ·
                refine ⟨16279199579269776221842141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21705599439026368295789521 16279199579269776221842141)
                ·
                  refine ⟨6104699842226166083190803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16279199579269776221842141 6104699842226166083190803)
                  ·
                    refine ⟨9157049763339249124786205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6104699842226166083190803 9157049763339249124786205)
                    ·
                      refine ⟨3433893661252218421794827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9157049763339249124786205 3433893661252218421794827)
                      ·
                        rfl

theorem cell23_6687484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_6687484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687484 prefixEnd_6687484 := by exact prefixLift 6687484
  have htrace : WordTrace (prefixWord ++ tailWord_6687484) baseStart_6687484 baseEnd_6687484 := by
    simpa [prefixWord, tailWord_6687484, baseEnd_6687484] using wordTrace_append hprefix tailTrace_6687484
  have hstable : (prefixWord ++ tailWord_6687484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687484).length < 2 ^ (prefixWord ++ tailWord_6687484).sum := by decide
  have hdescent : baseEnd_6687484 < baseStart_6687484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687500 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 3, 6]
def baseStart_6687500 : Nat := 118140960795 + 6687500 * 2 ^ 59
def prefixEnd_6687500 : Nat := 4983230072969 + 3 ^ 40 * 6687500 * 2
def baseEnd_6687500 : Nat := 1144633958980896786398251

theorem tailTrace_6687500 : CollatzResearch.WordTrace tailWord_6687500 prefixEnd_6687500 1144633958980896786398251 := by
  unfold tailWord_6687500
  simp only [CollatzResearch.WordTrace]
  refine ⟨121956581636168554457585977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162608775514891405943447969 121956581636168554457585977)
  ·
    refine ⟨91467436227126415843189483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121956581636168554457585977 91467436227126415843189483)
    ·
      refine ⟨137201154340689623764784225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91467436227126415843189483 137201154340689623764784225)
      ·
        refine ⟨102900865755517217823588169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137201154340689623764784225 102900865755517217823588169)
        ·
          refine ⟨77175649316637913367691127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102900865755517217823588169 77175649316637913367691127)
          ·
            refine ⟨115763473974956870051536691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77175649316637913367691127 115763473974956870051536691)
            ·
              refine ⟨173645210962435305077305037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115763473974956870051536691 173645210962435305077305037)
              ·
                refine ⟨65116954110913239403989389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173645210962435305077305037 65116954110913239403989389)
                ·
                  refine ⟨24418857791592464776496021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65116954110913239403989389 24418857791592464776496021)
                  ·
                    refine ⟨1144633958980896786398251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24418857791592464776496021 1144633958980896786398251)
                    ·
                      rfl

theorem cell23_6687500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_6687500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687500 prefixEnd_6687500 := by exact prefixLift 6687500
  have htrace : WordTrace (prefixWord ++ tailWord_6687500) baseStart_6687500 baseEnd_6687500 := by
    simpa [prefixWord, tailWord_6687500, baseEnd_6687500] using wordTrace_append hprefix tailTrace_6687500
  have hstable : (prefixWord ++ tailWord_6687500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687500).length < 2 ^ (prefixWord ++ tailWord_6687500).sum := by decide
  have hdescent : baseEnd_6687500 < baseStart_6687500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687507 : List Nat := [1, 1, 1, 2, 1, 3, 3, 5, 1, 1, 4]
def baseStart_6687507 : Nat := 118140960795 + 6687507 * 2 ^ 59
def prefixEnd_6687507 : Nat := 4983230072969 + 3 ^ 40 * 6687507 * 2
def baseEnd_6687507 : Nat := 3433905471307271831807221

theorem tailTrace_6687507 : CollatzResearch.WordTrace tailWord_6687507 prefixEnd_6687507 3433905471307271831807221 := by
  unfold tailWord_6687507
  simp only [CollatzResearch.WordTrace]
  refine ⟨243913418583311749110676775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162608945722207832740451183 243913418583311749110676775)
  ·
    refine ⟨365870127874967623666015163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243913418583311749110676775 365870127874967623666015163)
    ·
      refine ⟨548805191812451435499022745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365870127874967623666015163 548805191812451435499022745)
      ·
        refine ⟨411603893859338576624267059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 548805191812451435499022745 411603893859338576624267059)
        ·
          refine ⟨617405840789007864936400589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411603893859338576624267059 617405840789007864936400589)
          ·
            refine ⟨231527190295877949351150221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 617405840789007864936400589 231527190295877949351150221)
            ·
              refine ⟨86822696360954231006681333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231527190295877949351150221 86822696360954231006681333)
              ·
                refine ⟨8139627783839459156876375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86822696360954231006681333 8139627783839459156876375)
                ·
                  refine ⟨12209441675759188735314563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8139627783839459156876375 12209441675759188735314563)
                  ·
                    refine ⟨18314162513638783102971845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12209441675759188735314563 18314162513638783102971845)
                    ·
                      refine ⟨3433905471307271831807221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18314162513638783102971845 3433905471307271831807221)
                      ·
                        rfl

theorem cell23_6687507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 1, 4].length) (baseStart_6687507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687507 prefixEnd_6687507 := by exact prefixLift 6687507
  have htrace : WordTrace (prefixWord ++ tailWord_6687507) baseStart_6687507 baseEnd_6687507 := by
    simpa [prefixWord, tailWord_6687507, baseEnd_6687507] using wordTrace_append hprefix tailTrace_6687507
  have hstable : (prefixWord ++ tailWord_6687507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687507).length < 2 ^ (prefixWord ++ tailWord_6687507).sum := by decide
  have hdescent : baseEnd_6687507 < baseStart_6687507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687511 : List Nat := [1, 1, 3, 4, 3, 1, 1, 2, 2, 3, 2]
def baseStart_6687511 : Nat := 118140960795 + 6687511 * 2 ^ 59
def prefixEnd_6687511 : Nat := 4983230072969 + 3 ^ 40 * 6687511 * 2
def baseEnd_6687511 : Nat := 3433907525229889816157203

theorem tailTrace_6687511 : CollatzResearch.WordTrace tailWord_6687511 prefixEnd_6687511 3433907525229889816157203 := by
  unfold tailWord_6687511
  simp only [CollatzResearch.WordTrace]
  refine ⟨243913564475297257793822387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162609042983531505195881591 243913564475297257793822387)
  ·
    refine ⟨365870346712945886690733581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243913564475297257793822387 365870346712945886690733581)
    ·
      refine ⟨137201380017354707509025093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365870346712945886690733581 137201380017354707509025093)
      ·
        refine ⟨25725258753254007657942205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137201380017354707509025093 25725258753254007657942205)
        ·
          refine ⟨9646972032470252871728327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25725258753254007657942205 9646972032470252871728327)
          ·
            refine ⟨14470458048705379307592491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9646972032470252871728327 14470458048705379307592491)
            ·
              refine ⟨21705687073058068961388737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14470458048705379307592491 21705687073058068961388737)
              ·
                refine ⟨16279265304793551721041553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21705687073058068961388737 16279265304793551721041553)
                ·
                  refine ⟨12209448978595163790781165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16279265304793551721041553 12209448978595163790781165)
                  ·
                    refine ⟨4578543366973186421542937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12209448978595163790781165 4578543366973186421542937)
                    ·
                      refine ⟨3433907525229889816157203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4578543366973186421542937 3433907525229889816157203)
                      ·
                        rfl

theorem cell23_6687511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_6687511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687511 prefixEnd_6687511 := by exact prefixLift 6687511
  have htrace : WordTrace (prefixWord ++ tailWord_6687511) baseStart_6687511 baseEnd_6687511 := by
    simpa [prefixWord, tailWord_6687511, baseEnd_6687511] using wordTrace_append hprefix tailTrace_6687511
  have hstable : (prefixWord ++ tailWord_6687511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687511).length < 2 ^ (prefixWord ++ tailWord_6687511).sum := by decide
  have hdescent : baseEnd_6687511 < baseStart_6687511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687537 : List Nat := [1, 2, 2, 3, 2, 1, 2, 3, 1, 2, 4]
def baseStart_6687537 : Nat := 118140960795 + 6687537 * 2 ^ 59
def prefixEnd_6687537 : Nat := 4983230072969 + 3 ^ 40 * 6687537 * 2
def baseEnd_6687537 : Nat := 3433920875726906714432083

theorem tailTrace_6687537 : CollatzResearch.WordTrace tailWord_6687537 prefixEnd_6687537 3433920875726906714432083 := by
  unfold tailWord_6687537
  simp only [CollatzResearch.WordTrace]
  refine ⟨243914512773203064234268865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162609675182135376156179243 243914512773203064234268865)
  ·
    refine ⟨182935884579902298175701649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243914512773203064234268865 182935884579902298175701649)
    ·
      refine ⟨137201913434926723631776237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182935884579902298175701649 137201913434926723631776237)
      ·
        refine ⟨51450717538097521361916089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137201913434926723631776237 51450717538097521361916089)
        ·
          refine ⟨38588038153573141021437067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51450717538097521361916089 38588038153573141021437067)
          ·
            refine ⟨57882057230359711532155601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38588038153573141021437067 57882057230359711532155601)
            ·
              refine ⟨43411542922769783649116701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57882057230359711532155601 43411542922769783649116701)
              ·
                refine ⟨16279328596038668868418763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43411542922769783649116701 16279328596038668868418763)
                ·
                  refine ⟨24418992894058003302628145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16279328596038668868418763 24418992894058003302628145)
                  ·
                    refine ⟨18314244670543502476971109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24418992894058003302628145 18314244670543502476971109)
                    ·
                      refine ⟨3433920875726906714432083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18314244670543502476971109 3433920875726906714432083)
                      ·
                        rfl

theorem cell23_6687537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_6687537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687537 prefixEnd_6687537 := by exact prefixLift 6687537
  have htrace : WordTrace (prefixWord ++ tailWord_6687537) baseStart_6687537 baseEnd_6687537 := by
    simpa [prefixWord, tailWord_6687537, baseEnd_6687537] using wordTrace_append hprefix tailTrace_6687537
  have hstable : (prefixWord ++ tailWord_6687537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687537).length < 2 ^ (prefixWord ++ tailWord_6687537).sum := by decide
  have hdescent : baseEnd_6687537 < baseStart_6687537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687541 : List Nat := [1, 3, 3, 1, 3, 3, 1, 2, 1, 1, 4]
def baseStart_6687541 : Nat := 118140960795 + 6687541 * 2 ^ 59
def prefixEnd_6687541 : Nat := 4983230072969 + 3 ^ 40 * 6687541 * 2
def baseEnd_6687541 : Nat := 3433922929649524698782065

theorem tailTrace_6687541 : CollatzResearch.WordTrace tailWord_6687541 prefixEnd_6687541 3433922929649524698782065 := by
  unfold tailWord_6687541
  simp only [CollatzResearch.WordTrace]
  refine ⟨243914658665188572917414477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162609772443459048611609651 243914658665188572917414477)
  ·
    refine ⟨91467996999445714844030429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243914658665188572917414477 91467996999445714844030429)
    ·
      refine ⟨34300498874792143066511411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91467996999445714844030429 34300498874792143066511411)
      ·
        refine ⟨51450748312188214599767117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34300498874792143066511411 51450748312188214599767117)
        ·
          refine ⟨19294030617070580474912669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51450748312188214599767117 19294030617070580474912669)
          ·
            refine ⟨7235261481401467678092251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19294030617070580474912669 7235261481401467678092251)
            ·
              refine ⟨10852892222102201517138377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7235261481401467678092251 10852892222102201517138377)
              ·
                refine ⟨8139669166576651137853783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10852892222102201517138377 8139669166576651137853783)
                ·
                  refine ⟨12209503749864976706780675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8139669166576651137853783 12209503749864976706780675)
                  ·
                    refine ⟨18314255624797465060171013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12209503749864976706780675 18314255624797465060171013)
                    ·
                      refine ⟨3433922929649524698782065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18314255624797465060171013 3433922929649524698782065)
                      ·
                        rfl

theorem cell23_6687541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_6687541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687541 prefixEnd_6687541 := by exact prefixLift 6687541
  have htrace : WordTrace (prefixWord ++ tailWord_6687541) baseStart_6687541 baseEnd_6687541 := by
    simpa [prefixWord, tailWord_6687541, baseEnd_6687541] using wordTrace_append hprefix tailTrace_6687541
  have hstable : (prefixWord ++ tailWord_6687541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687541).length < 2 ^ (prefixWord ++ tailWord_6687541).sum := by decide
  have hdescent : baseEnd_6687541 < baseStart_6687541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687561 : List Nat := [1, 2, 1, 1, 2, 6, 3, 1, 1, 2, 3]
def baseStart_6687561 : Nat := 118140960795 + 6687561 * 2 ^ 59
def prefixEnd_6687561 : Nat := 4983230072969 + 3 ^ 40 * 6687561 * 2
def baseEnd_6687561 : Nat := 3433933199262614620531973

theorem tailTrace_6687561 : CollatzResearch.WordTrace tailWord_6687561 prefixEnd_6687561 3433933199262614620531973 := by
  unfold tailWord_6687561
  simp only [CollatzResearch.WordTrace]
  refine ⟨243915388125116116333142537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162610258750077410888761691 243915388125116116333142537)
  ·
    refine ⟨182936541093837087249856903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243915388125116116333142537 182936541093837087249856903)
    ·
      refine ⟨274404811640755630874785355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182936541093837087249856903 274404811640755630874785355)
      ·
        refine ⟨411607217461133446312178033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274404811640755630874785355 411607217461133446312178033)
        ·
          refine ⟨308705413095850084734133525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411607217461133446312178033 308705413095850084734133525)
          ·
            refine ⟨14470566238867972721912509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 308705413095850084734133525 14470566238867972721912509)
            ·
              refine ⟨5426462339575489770717191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14470566238867972721912509 5426462339575489770717191)
              ·
                refine ⟨8139693509363234656075787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5426462339575489770717191 8139693509363234656075787)
                ·
                  refine ⟨12209540264044851984113681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8139693509363234656075787 12209540264044851984113681)
                  ·
                    refine ⟨9157155198033638988085261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12209540264044851984113681 9157155198033638988085261)
                    ·
                      refine ⟨3433933199262614620531973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9157155198033638988085261 3433933199262614620531973)
                      ·
                        rfl

theorem cell23_6687561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 1, 2, 3].length) (baseStart_6687561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687561 prefixEnd_6687561 := by exact prefixLift 6687561
  have htrace : WordTrace (prefixWord ++ tailWord_6687561) baseStart_6687561 baseEnd_6687561 := by
    simpa [prefixWord, tailWord_6687561, baseEnd_6687561] using wordTrace_append hprefix tailTrace_6687561
  have hstable : (prefixWord ++ tailWord_6687561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687561).length < 2 ^ (prefixWord ++ tailWord_6687561).sum := by decide
  have hdescent : baseEnd_6687561 < baseStart_6687561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687575 : List Nat := [1, 1, 3, 2, 4, 1, 4, 2, 1, 2, 2]
def baseStart_6687575 : Nat := 118140960795 + 6687575 * 2 ^ 59
def prefixEnd_6687575 : Nat := 4983230072969 + 3 ^ 40 * 6687575 * 2
def baseEnd_6687575 : Nat := 3433940387991777565756909

theorem tailTrace_6687575 : CollatzResearch.WordTrace tailWord_6687575 prefixEnd_6687575 3433940387991777565756909 := by
  unfold tailWord_6687575
  simp only [CollatzResearch.WordTrace]
  refine ⟨243915898747065396724152179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162610599164710264482768119 243915898747065396724152179)
  ·
    refine ⟨365873848120598095086228269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243915898747065396724152179 365873848120598095086228269)
    ·
      refine ⟨137202693045224285657335601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365873848120598095086228269 137202693045224285657335601)
      ·
        refine ⟨102902019783918214243001701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137202693045224285657335601 102902019783918214243001701)
        ·
          refine ⟨19294128709484665170562819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102902019783918214243001701 19294128709484665170562819)
          ·
            refine ⟨28941193064226997755844229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19294128709484665170562819 28941193064226997755844229)
            ·
              refine ⟨5426473699542562079220793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28941193064226997755844229 5426473699542562079220793)
              ·
                refine ⟨4069855274656921559415595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5426473699542562079220793 4069855274656921559415595)
                ·
                  refine ⟨6104782911985382339123393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4069855274656921559415595 6104782911985382339123393)
                  ·
                    refine ⟨4578587183989036754342545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6104782911985382339123393 4578587183989036754342545)
                    ·
                      refine ⟨3433940387991777565756909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4578587183989036754342545 3433940387991777565756909)
                      ·
                        rfl

theorem cell23_6687575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 1, 2, 2].length) (baseStart_6687575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687575 prefixEnd_6687575 := by exact prefixLift 6687575
  have htrace : WordTrace (prefixWord ++ tailWord_6687575) baseStart_6687575 baseEnd_6687575 := by
    simpa [prefixWord, tailWord_6687575, baseEnd_6687575] using wordTrace_append hprefix tailTrace_6687575
  have hstable : (prefixWord ++ tailWord_6687575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687575).length < 2 ^ (prefixWord ++ tailWord_6687575).sum := by decide
  have hdescent : baseEnd_6687575 < baseStart_6687575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687584 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 5, 3, 2]
def baseStart_6687584 : Nat := 118140960795 + 6687584 * 2 ^ 59
def prefixEnd_6687584 : Nat := 4983230072969 + 3 ^ 40 * 6687584 * 2
def baseEnd_6687584 : Nat := 3433945009317668030544367

theorem tailTrace_6687584 : CollatzResearch.WordTrace tailWord_6687584 prefixEnd_6687584 3433945009317668030544367 := by
  unfold tailWord_6687584
  simp only [CollatzResearch.WordTrace]
  refine ⟨121958113502016395630614903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162610818002688527507486537 121958113502016395630614903)
  ·
    refine ⟨182937170253024593445922355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121958113502016395630614903 182937170253024593445922355)
    ·
      refine ⟨274405755379536890168883533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182937170253024593445922355 274405755379536890168883533)
      ·
        refine ⟨102902158267326333813331325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274405755379536890168883533 102902158267326333813331325)
        ·
          refine ⟨38588309350247375179999247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102902158267326333813331325 38588309350247375179999247)
          ·
            refine ⟨57882464025371062769998871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38588309350247375179999247 57882464025371062769998871)
            ·
              refine ⟨86823696038056594154998307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57882464025371062769998871 86823696038056594154998307)
              ·
                refine ⟨130235544057084891232497461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86823696038056594154998307 130235544057084891232497461)
                ·
                  refine ⟨12209582255351708553046637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130235544057084891232497461 12209582255351708553046637)
                  ·
                    refine ⟨4578593345756890707392489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12209582255351708553046637 4578593345756890707392489)
                    ·
                      refine ⟨3433945009317668030544367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4578593345756890707392489 3433945009317668030544367)
                      ·
                        rfl

theorem cell23_6687584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 5, 3, 2].length) (baseStart_6687584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687584 prefixEnd_6687584 := by exact prefixLift 6687584
  have htrace : WordTrace (prefixWord ++ tailWord_6687584) baseStart_6687584 baseEnd_6687584 := by
    simpa [prefixWord, tailWord_6687584, baseEnd_6687584] using wordTrace_append hprefix tailTrace_6687584
  have hstable : (prefixWord ++ tailWord_6687584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687584).length < 2 ^ (prefixWord ++ tailWord_6687584).sum := by decide
  have hdescent : baseEnd_6687584 < baseStart_6687584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687591 : List Nat := [1, 1, 5, 1, 2, 2, 2, 3, 2, 1, 3]
def baseStart_6687591 : Nat := 118140960795 + 6687591 * 2 ^ 59
def prefixEnd_6687591 : Nat := 4983230072969 + 3 ^ 40 * 6687591 * 2
def baseEnd_6687591 : Nat := 3433948603682249503156835

theorem tailTrace_6687591 : CollatzResearch.WordTrace tailWord_6687591 prefixEnd_6687591 3433948603682249503156835 := by
  unfold tailWord_6687591
  simp only [CollatzResearch.WordTrace]
  refine ⟨243916482315007431456734627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162610988210004954304489751 243916482315007431456734627)
  ·
    refine ⟨365874723472511147185101941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243916482315007431456734627 365874723472511147185101941)
    ·
      refine ⟨34300755325547920048603307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 365874723472511147185101941 34300755325547920048603307)
      ·
        refine ⟨51451132988321880072904961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34300755325547920048603307 51451132988321880072904961)
        ·
          refine ⟨38588349741241410054678721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51451132988321880072904961 38588349741241410054678721)
          ·
            refine ⟨28941262305931057541009041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38588349741241410054678721 28941262305931057541009041)
            ·
              refine ⟨21705946729448293155756781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28941262305931057541009041 21705946729448293155756781)
              ·
                refine ⟨8139730023543109933408793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21705946729448293155756781 8139730023543109933408793)
                ·
                  refine ⟨6104797517657332450056595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8139730023543109933408793 6104797517657332450056595)
                  ·
                    refine ⟨9157196276485998675084893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6104797517657332450056595 9157196276485998675084893)
                    ·
                      refine ⟨3433948603682249503156835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9157196276485998675084893 3433948603682249503156835)
                      ·
                        rfl

theorem cell23_6687591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_6687591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687591 prefixEnd_6687591 := by exact prefixLift 6687591
  have htrace : WordTrace (prefixWord ++ tailWord_6687591) baseStart_6687591 baseEnd_6687591 := by
    simpa [prefixWord, tailWord_6687591, baseEnd_6687591] using wordTrace_append hprefix tailTrace_6687591
  have hstable : (prefixWord ++ tailWord_6687591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687591).length < 2 ^ (prefixWord ++ tailWord_6687591).sum := by decide
  have hdescent : baseEnd_6687591 < baseStart_6687591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687597 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_6687597 : Nat := 118140960795 + 6687597 * 2 ^ 59
def prefixEnd_6687597 : Nat := 4983230072969 + 3 ^ 40 * 6687597 * 2
def baseEnd_6687597 : Nat := 3433951684566176479681807

theorem tailTrace_6687597 : CollatzResearch.WordTrace tailWord_6687597 prefixEnd_6687597 3433951684566176479681807 := by
  unfold tailWord_6687597
  simp only [CollatzResearch.WordTrace]
  refine ⟨243916701152985694481453045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162611134101990462987635363 243916701152985694481453045)
  ·
    refine ⟨22867190733092408857636223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 243916701152985694481453045 22867190733092408857636223)
    ·
      refine ⟨34300786099638613286454335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22867190733092408857636223 34300786099638613286454335)
      ·
        refine ⟨51451179149457919929681503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34300786099638613286454335 51451179149457919929681503)
        ·
          refine ⟨77176768724186879894522255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51451179149457919929681503 77176768724186879894522255)
          ·
            refine ⟨115765153086280319841783383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77176768724186879894522255 115765153086280319841783383)
            ·
              refine ⟨173647729629420479762675075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115765153086280319841783383 173647729629420479762675075)
              ·
                refine ⟨260471594444130719644012613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173647729629420479762675075 260471594444130719644012613)
                ·
                  refine ⟨48838423958274509933252365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 260471594444130719644012613 48838423958274509933252365)
                  ·
                    refine ⟨18314408984352941224969637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48838423958274509933252365 18314408984352941224969637)
                    ·
                      refine ⟨3433951684566176479681807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18314408984352941224969637 3433951684566176479681807)
                      ·
                        rfl

theorem cell23_6687597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_6687597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687597 prefixEnd_6687597 := by exact prefixLift 6687597
  have htrace : WordTrace (prefixWord ++ tailWord_6687597) baseStart_6687597 baseEnd_6687597 := by
    simpa [prefixWord, tailWord_6687597, baseEnd_6687597] using wordTrace_append hprefix tailTrace_6687597
  have hstable : (prefixWord ++ tailWord_6687597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687597).length < 2 ^ (prefixWord ++ tailWord_6687597).sum := by decide
  have hdescent : baseEnd_6687597 < baseStart_6687597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687627 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 4]
def baseStart_6687627 : Nat := 118140960795 + 6687627 * 2 ^ 59
def prefixEnd_6687627 : Nat := 4983230072969 + 3 ^ 40 * 6687627 * 2
def baseEnd_6687627 : Nat := 3433967088985811362306669

theorem tailTrace_6687627 : CollatzResearch.WordTrace tailWord_6687627 prefixEnd_6687627 3433967088985811362306669 := by
  unfold tailWord_6687627
  simp only [CollatzResearch.WordTrace]
  refine ⟨243917795342877009605045135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162611863561918006403363423 243917795342877009605045135)
  ·
    refine ⟨365876693014315514407567703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243917795342877009605045135 365876693014315514407567703)
    ·
      refine ⟨548815039521473271611351555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365876693014315514407567703 548815039521473271611351555)
      ·
        refine ⟨823222559282209907417027333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548815039521473271611351555 823222559282209907417027333)
        ·
          refine ⟨154354229865414357640692625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 823222559282209907417027333 154354229865414357640692625)
          ·
            refine ⟨115765672399060768230519469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154354229865414357640692625 115765672399060768230519469)
            ·
              refine ⟨43412127149647788086444801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115765672399060768230519469 43412127149647788086444801)
              ·
                refine ⟨32559095362235841064833601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43412127149647788086444801 32559095362235841064833601)
                ·
                  refine ⟨24419321521676880798625201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32559095362235841064833601 24419321521676880798625201)
                  ·
                    refine ⟨18314491141257660598968901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24419321521676880798625201 18314491141257660598968901)
                    ·
                      refine ⟨3433967088985811362306669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18314491141257660598968901 3433967088985811362306669)
                      ·
                        rfl

theorem cell23_6687627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 4].length) (baseStart_6687627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687627 prefixEnd_6687627 := by exact prefixLift 6687627
  have htrace : WordTrace (prefixWord ++ tailWord_6687627) baseStart_6687627 baseEnd_6687627 := by
    simpa [prefixWord, tailWord_6687627, baseEnd_6687627] using wordTrace_append hprefix tailTrace_6687627
  have hstable : (prefixWord ++ tailWord_6687627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687627).length < 2 ^ (prefixWord ++ tailWord_6687627).sum := by decide
  have hdescent : baseEnd_6687627 < baseStart_6687627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687637 : List Nat := [1, 3, 2, 1, 1, 4, 1, 3, 7]
def baseStart_6687637 : Nat := 118140960795 + 6687637 * 2 ^ 59
def prefixEnd_6687637 : Nat := 4983230072969 + 3 ^ 40 * 6687637 * 2
def baseEnd_6687637 : Nat := 381552469310261813686847

theorem tailTrace_6687637 : CollatzResearch.WordTrace tailWord_6687637 prefixEnd_6687637 381552469310261813686847 := by
  unfold tailWord_6687637
  simp only [CollatzResearch.WordTrace]
  refine ⟨243918160072840781312909165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162612106715227187541939443 243918160072840781312909165)
  ·
    refine ⟨91469310027315292992340937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243918160072840781312909165 91469310027315292992340937)
    ·
      refine ⟨68601982520486469744255703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91469310027315292992340937 68601982520486469744255703)
      ·
        refine ⟨102902973780729704616383555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68601982520486469744255703 102902973780729704616383555)
        ·
          refine ⟨154354460671094556924575333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102902973780729704616383555 154354460671094556924575333)
          ·
            refine ⟨28941461375830229423357875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154354460671094556924575333 28941461375830229423357875)
            ·
              refine ⟨43412192063745344135036813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28941461375830229423357875 43412192063745344135036813)
              ·
                refine ⟨16279572023904504050638805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43412192063745344135036813 16279572023904504050638805)
                ·
                  refine ⟨381552469310261813686847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16279572023904504050638805 381552469310261813686847)
                  ·
                    rfl

theorem cell23_6687637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 7].length) (baseStart_6687637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687637 prefixEnd_6687637 := by exact prefixLift 6687637
  have htrace : WordTrace (prefixWord ++ tailWord_6687637) baseStart_6687637 baseEnd_6687637 := by
    simpa [prefixWord, tailWord_6687637, baseEnd_6687637] using wordTrace_append hprefix tailTrace_6687637
  have hstable : (prefixWord ++ tailWord_6687637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687637).length < 2 ^ (prefixWord ++ tailWord_6687637).sum := by decide
  have hdescent : baseEnd_6687637 < baseStart_6687637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687688 : List Nat := [2, 1, 3, 1, 5, 1, 3, 2, 5]
def baseStart_6687688 : Nat := 118140960795 + 6687688 * 2 ^ 59
def prefixEnd_6687688 : Nat := 4983230072969 + 3 ^ 40 * 6687688 * 2
def baseEnd_6687688 : Nat := 381555379033970624849321

theorem tailTrace_6687688 : CollatzResearch.WordTrace tailWord_6687688 prefixEnd_6687688 381555379033970624849321 := by
  unfold tailWord_6687688
  simp only [CollatzResearch.WordTrace]
  refine ⟨121960010097828008511507859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162613346797104011348677145 121960010097828008511507859)
  ·
    refine ⟨182940015146742012767261789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121960010097828008511507859 182940015146742012767261789)
    ·
      refine ⟨68602505680028254787723171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182940015146742012767261789 68602505680028254787723171)
      ·
        refine ⟨102903758520042382181584757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68602505680028254787723171 102903758520042382181584757)
        ·
          refine ⟨9647227361253973329523571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102903758520042382181584757 9647227361253973329523571)
          ·
            refine ⟨14470841041880959994285357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9647227361253973329523571 14470841041880959994285357)
            ·
              refine ⟨5426565390705359997857009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14470841041880959994285357 5426565390705359997857009)
              ·
                refine ⟨4069924043029019998392757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5426565390705359997857009 4069924043029019998392757)
                ·
                  refine ⟨381555379033970624849321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4069924043029019998392757 381555379033970624849321)
                  ·
                    rfl

theorem cell23_6687688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 5].length) (baseStart_6687688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687688 prefixEnd_6687688 := by exact prefixLift 6687688
  have htrace : WordTrace (prefixWord ++ tailWord_6687688) baseStart_6687688 baseEnd_6687688 := by
    simpa [prefixWord, tailWord_6687688, baseEnd_6687688] using wordTrace_append hprefix tailTrace_6687688
  have hstable : (prefixWord ++ tailWord_6687688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687688).length < 2 ^ (prefixWord ++ tailWord_6687688).sum := by decide
  have hdescent : baseEnd_6687688 < baseStart_6687688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687694 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5]
def baseStart_6687694 : Nat := 118140960795 + 6687694 * 2 ^ 59
def prefixEnd_6687694 : Nat := 4983230072969 + 3 ^ 40 * 6687694 * 2
def baseEnd_6687694 : Nat := 3434001492189662600168861

theorem tailTrace_6687694 : CollatzResearch.WordTrace tailWord_6687694 prefixEnd_6687694 3434001492189662600168861 := by
  unfold tailWord_6687694
  simp only [CollatzResearch.WordTrace]
  refine ⟨30490029879204285005966767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162613492689089520031822757 30490029879204285005966767)
  ·
    refine ⟨45735044818806427508950151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30490029879204285005966767 45735044818806427508950151)
    ·
      refine ⟨68602567228209641263425227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45735044818806427508950151 68602567228209641263425227)
      ·
        refine ⟨102903850842314461895137841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68602567228209641263425227 102903850842314461895137841)
        ·
          refine ⟨77177888131735846421353381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102903850842314461895137841 77177888131735846421353381)
          ·
            refine ⟨14470854024700471204003759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77177888131735846421353381 14470854024700471204003759)
            ·
              refine ⟨21706281037050706806005639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14470854024700471204003759 21706281037050706806005639)
              ·
                refine ⟨32559421555576060209008459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21706281037050706806005639 32559421555576060209008459)
                ·
                  refine ⟨48839132333364090313512689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32559421555576060209008459 48839132333364090313512689)
                  ·
                    refine ⟨36629349250023067735134517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48839132333364090313512689 36629349250023067735134517)
                    ·
                      refine ⟨3434001492189662600168861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36629349250023067735134517 3434001492189662600168861)
                      ·
                        rfl

theorem cell23_6687694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_6687694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687694 prefixEnd_6687694 := by exact prefixLift 6687694
  have htrace : WordTrace (prefixWord ++ tailWord_6687694) baseStart_6687694 baseEnd_6687694 := by
    simpa [prefixWord, tailWord_6687694, baseEnd_6687694] using wordTrace_append hprefix tailTrace_6687694
  have hstable : (prefixWord ++ tailWord_6687694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687694).length < 2 ^ (prefixWord ++ tailWord_6687694).sum := by decide
  have hdescent : baseEnd_6687694 < baseStart_6687694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687781 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 1, 5, 2]
def baseStart_6687781 : Nat := 118140960795 + 6687781 * 2 ^ 59
def prefixEnd_6687781 : Nat := 4983230072969 + 3 ^ 40 * 6687781 * 2
def baseEnd_6687781 : Nat := 3434046165006603759780961

theorem tailTrace_6687781 : CollatzResearch.WordTrace tailWord_6687781 prefixEnd_6687781 3434046165006603759780961 := by
  unfold tailWord_6687781
  simp only [CollatzResearch.WordTrace]
  refine ⟨243923412184319093906151197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162615608122879395937434131 243923412184319093906151197)
  ·
    refine ⟨91471279569119660214806699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243923412184319093906151197 91471279569119660214806699)
    ·
      refine ⟨137206919353679490322210049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91471279569119660214806699 137206919353679490322210049)
      ·
        refine ⟨102905189515259617741657537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137206919353679490322210049 102905189515259617741657537)
        ·
          refine ⟨77178892136444713306243153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102905189515259617741657537 77178892136444713306243153)
          ·
            refine ⟨57884169102333534979682365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77178892136444713306243153 57884169102333534979682365)
            ·
              refine ⟨21706563413375075617380887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57884169102333534979682365 21706563413375075617380887)
              ·
                refine ⟨32559845120062613426071331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21706563413375075617380887 32559845120062613426071331)
                ·
                  refine ⟨48839767680093920139106997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32559845120062613426071331 48839767680093920139106997)
                  ·
                    refine ⟨4578728220008805013041281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48839767680093920139106997 4578728220008805013041281)
                    ·
                      refine ⟨3434046165006603759780961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4578728220008805013041281 3434046165006603759780961)
                      ·
                        rfl

theorem cell23_6687781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 5, 2].length) (baseStart_6687781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687781 prefixEnd_6687781 := by exact prefixLift 6687781
  have htrace : WordTrace (prefixWord ++ tailWord_6687781) baseStart_6687781 baseEnd_6687781 := by
    simpa [prefixWord, tailWord_6687781, baseEnd_6687781] using wordTrace_append hprefix tailTrace_6687781
  have hstable : (prefixWord ++ tailWord_6687781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687781).length < 2 ^ (prefixWord ++ tailWord_6687781).sum := by decide
  have hdescent : baseEnd_6687781 < baseStart_6687781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687805 : List Nat := [1, 4, 1, 3, 1, 2, 2, 4, 1, 1, 3]
def baseStart_6687805 : Nat := 118140960795 + 6687805 * 2 ^ 59
def prefixEnd_6687805 : Nat := 4983230072969 + 3 ^ 40 * 6687805 * 2
def baseEnd_6687805 : Nat := 3434058488542311665880851

theorem tailTrace_6687805 : CollatzResearch.WordTrace tailWord_6687805 prefixEnd_6687805 3434058488542311665880851 := by
  unfold tailWord_6687805
  simp only [CollatzResearch.WordTrace]
  refine ⟨243924287536232146005024869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162616191690821430670016579 243924287536232146005024869)
  ·
    refine ⟨45735803913043527375942163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243924287536232146005024869 45735803913043527375942163)
    ·
      refine ⟨68603705869565291063913245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45735803913043527375942163 68603705869565291063913245)
      ·
        refine ⟨25726389701086984148967467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68603705869565291063913245 25726389701086984148967467)
        ·
          refine ⟨38589584551630476223451201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25726389701086984148967467 38589584551630476223451201)
          ·
            refine ⟨28942188413722857167588401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38589584551630476223451201 28942188413722857167588401)
            ·
              refine ⟨21706641310292142875691301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28942188413722857167588401 21706641310292142875691301)
              ·
                refine ⟨4069995245679776789192119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21706641310292142875691301 4069995245679776789192119)
                ·
                  refine ⟨6104992868519665183788179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4069995245679776789192119 6104992868519665183788179)
                  ·
                    refine ⟨9157489302779497775682269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6104992868519665183788179 9157489302779497775682269)
                    ·
                      refine ⟨3434058488542311665880851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9157489302779497775682269 3434058488542311665880851)
                      ·
                        rfl

theorem cell23_6687805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_6687805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687805 prefixEnd_6687805 := by exact prefixLift 6687805
  have htrace : WordTrace (prefixWord ++ tailWord_6687805) baseStart_6687805 baseEnd_6687805 := by
    simpa [prefixWord, tailWord_6687805, baseEnd_6687805] using wordTrace_append hprefix tailTrace_6687805
  have hstable : (prefixWord ++ tailWord_6687805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687805).length < 2 ^ (prefixWord ++ tailWord_6687805).sum := by decide
  have hdescent : baseEnd_6687805 < baseStart_6687805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687888 : List Nat := [2, 1, 1, 1, 1, 1, 4, 6, 1, 3, 2]
def baseStart_6687888 : Nat := 118140960795 + 6687888 * 2 ^ 59
def prefixEnd_6687888 : Nat := 4983230072969 + 3 ^ 40 * 6687888 * 2
def baseEnd_6687888 : Nat := 3434101107436634841142969

theorem tailTrace_6687888 : CollatzResearch.WordTrace tailWord_6687888 prefixEnd_6687888 3434101107436634841142969 := by
  unfold tailWord_6687888
  simp only [CollatzResearch.WordTrace]
  refine ⟨121963657397465725590148159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162618209863287634120197545 121963657397465725590148159)
  ·
    refine ⟨182945486096198588385222239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121963657397465725590148159 182945486096198588385222239)
    ·
      refine ⟨274418229144297882577833359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182945486096198588385222239 274418229144297882577833359)
      ·
        refine ⟨411627343716446823866750039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274418229144297882577833359 411627343716446823866750039)
        ·
          refine ⟨617441015574670235800125059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411627343716446823866750039 617441015574670235800125059)
          ·
            refine ⟨926161523362005353700187589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617441015574670235800125059 926161523362005353700187589)
            ·
              refine ⟨173655285630376003818785173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 926161523362005353700187589 173655285630376003818785173)
              ·
                refine ⟨8140091513923875179005555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 173655285630376003818785173 8140091513923875179005555)
                ·
                  refine ⟨12210137270885812768508333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8140091513923875179005555 12210137270885812768508333)
                  ·
                    refine ⟨4578801476582179788190625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12210137270885812768508333 4578801476582179788190625)
                    ·
                      refine ⟨3434101107436634841142969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4578801476582179788190625 3434101107436634841142969)
                      ·
                        rfl

theorem cell23_6687888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 1, 3, 2].length) (baseStart_6687888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687888 prefixEnd_6687888 := by exact prefixLift 6687888
  have htrace : WordTrace (prefixWord ++ tailWord_6687888) baseStart_6687888 baseEnd_6687888 := by
    simpa [prefixWord, tailWord_6687888, baseEnd_6687888] using wordTrace_append hprefix tailTrace_6687888
  have hstable : (prefixWord ++ tailWord_6687888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687888).length < 2 ^ (prefixWord ++ tailWord_6687888).sum := by decide
  have hdescent : baseEnd_6687888 < baseStart_6687888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687935 : List Nat := [1, 1, 2, 2, 2, 2, 4, 3, 2, 2, 2]
def baseStart_6687935 : Nat := 118140960795 + 6687935 * 2 ^ 59
def prefixEnd_6687935 : Nat := 4983230072969 + 3 ^ 40 * 6687935 * 2
def baseEnd_6687935 : Nat := 3434125241027396157255253

theorem tailTrace_6687935 : CollatzResearch.WordTrace tailWord_6687935 prefixEnd_6687935 3434125241027396157255253 := by
  unfold tailWord_6687935
  simp only [CollatzResearch.WordTrace]
  refine ⟨243929029025761178207257259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162619352683840785471504839 243929029025761178207257259)
  ·
    refine ⟨365893543538641767310885889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243929029025761178207257259 365893543538641767310885889)
    ·
      refine ⟨274420157653981325483164417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365893543538641767310885889 274420157653981325483164417)
      ·
        refine ⟨205815118240485994112373313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274420157653981325483164417 205815118240485994112373313)
        ·
          refine ⟨154361338680364495584279985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205815118240485994112373313 154361338680364495584279985)
          ·
            refine ⟨115771004010273371688209989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154361338680364495584279985 115771004010273371688209989)
            ·
              refine ⟨21707063251926257191539373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115771004010273371688209989 21707063251926257191539373)
              ·
                refine ⟨8140148719472346446827265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21707063251926257191539373 8140148719472346446827265)
                ·
                  refine ⟨6105111539604259835120449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8140148719472346446827265 6105111539604259835120449)
                  ·
                    refine ⟨4578833654703194876340337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6105111539604259835120449 4578833654703194876340337)
                    ·
                      refine ⟨3434125241027396157255253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4578833654703194876340337 3434125241027396157255253)
                      ·
                        rfl

theorem cell23_6687935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 2, 2].length) (baseStart_6687935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687935 prefixEnd_6687935 := by exact prefixLift 6687935
  have htrace : WordTrace (prefixWord ++ tailWord_6687935) baseStart_6687935 baseEnd_6687935 := by
    simpa [prefixWord, tailWord_6687935, baseEnd_6687935] using wordTrace_append hprefix tailTrace_6687935
  have hstable : (prefixWord ++ tailWord_6687935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687935).length < 2 ^ (prefixWord ++ tailWord_6687935).sum := by decide
  have hdescent : baseEnd_6687935 < baseStart_6687935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687956 : List Nat := [2, 4, 1, 4, 1, 2, 2, 1, 1, 3, 2]
def baseStart_6687956 : Nat := 118140960795 + 6687956 * 2 ^ 59
def prefixEnd_6687956 : Nat := 4983230072969 + 3 ^ 40 * 6687956 * 2
def baseEnd_6687956 : Nat := 3434136024121140575092657

theorem tailTrace_6687956 : CollatzResearch.WordTrace tailWord_6687956 prefixEnd_6687956 3434136024121140575092657 := by
  unfold tailWord_6687956
  simp only [CollatzResearch.WordTrace]
  refine ⟨121964897479342549396885861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162619863305790065862514481 121964897479342549396885861)
  ·
    refine ⟨22868418277376728011916099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121964897479342549396885861 22868418277376728011916099)
    ·
      refine ⟨34302627416065092017874149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22868418277376728011916099 34302627416065092017874149)
      ·
        refine ⟨6431742640512204753351403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34302627416065092017874149 6431742640512204753351403)
        ·
          refine ⟨9647613960768307130027105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6431742640512204753351403 9647613960768307130027105)
          ·
            refine ⟨7235710470576230347520329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9647613960768307130027105 7235710470576230347520329)
            ·
              refine ⟨5426782852932172760640247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7235710470576230347520329 5426782852932172760640247)
              ·
                refine ⟨8140174279398259140960371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5426782852932172760640247 8140174279398259140960371)
                ·
                  refine ⟨12210261419097388711440557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8140174279398259140960371 12210261419097388711440557)
                  ·
                    refine ⟨4578848032161520766790209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12210261419097388711440557 4578848032161520766790209)
                    ·
                      refine ⟨3434136024121140575092657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4578848032161520766790209 3434136024121140575092657)
                      ·
                        rfl

theorem cell23_6687956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_6687956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687956 prefixEnd_6687956 := by exact prefixLift 6687956
  have htrace : WordTrace (prefixWord ++ tailWord_6687956) baseStart_6687956 baseEnd_6687956 := by
    simpa [prefixWord, tailWord_6687956, baseEnd_6687956] using wordTrace_append hprefix tailTrace_6687956
  have hstable : (prefixWord ++ tailWord_6687956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687956).length < 2 ^ (prefixWord ++ tailWord_6687956).sum := by decide
  have hdescent : baseEnd_6687956 < baseStart_6687956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687991 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 4]
def baseStart_6687991 : Nat := 118140960795 + 6687991 * 2 ^ 59
def prefixEnd_6687991 : Nat := 4983230072969 + 3 ^ 40 * 6687991 * 2
def baseEnd_6687991 : Nat := 3434153995944047938154995

theorem tailTrace_6687991 : CollatzResearch.WordTrace tailWord_6687991 prefixEnd_6687991 3434153995944047938154995 := by
  unfold tailWord_6687991
  simp only [CollatzResearch.WordTrace]
  refine ⟨243931071513558299771295827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162620714342372199847530551 243931071513558299771295827)
  ·
    refine ⟨365896607270337449656943741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243931071513558299771295827 365896607270337449656943741)
    ·
      refine ⟨137211227726376543621353903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365896607270337449656943741 137211227726376543621353903)
      ·
        refine ⟨205816841589564815432030855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137211227726376543621353903 205816841589564815432030855)
        ·
          refine ⟨308725262384347223148046283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205816841589564815432030855 308725262384347223148046283)
          ·
            refine ⟨463087893576520834722069425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308725262384347223148046283 463087893576520834722069425)
            ·
              refine ⟨347315920182390626041552069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463087893576520834722069425 347315920182390626041552069)
              ·
                refine ⟨65121735034198242382791013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 347315920182390626041552069 65121735034198242382791013)
                ·
                  refine ⟨12210325318912170446773315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65121735034198242382791013 12210325318912170446773315)
                  ·
                    refine ⟨18315487978368255670159973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12210325318912170446773315 18315487978368255670159973)
                    ·
                      refine ⟨3434153995944047938154995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18315487978368255670159973 3434153995944047938154995)
                      ·
                        rfl

theorem cell23_6687991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_6687991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687991 prefixEnd_6687991 := by exact prefixLift 6687991
  have htrace : WordTrace (prefixWord ++ tailWord_6687991) baseStart_6687991 baseEnd_6687991 := by
    simpa [prefixWord, tailWord_6687991, baseEnd_6687991] using wordTrace_append hprefix tailTrace_6687991
  have hstable : (prefixWord ++ tailWord_6687991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687991).length < 2 ^ (prefixWord ++ tailWord_6687991).sum := by decide
  have hdescent : baseEnd_6687991 < baseStart_6687991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688028 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 4, 2, 3]
def baseStart_6688028 : Nat := 118140960795 + 6688028 * 2 ^ 59
def prefixEnd_6688028 : Nat := 4983230072969 + 3 ^ 40 * 6688028 * 2
def baseEnd_6688028 : Nat := 3434172994728264293392325

theorem tailTrace_6688028 : CollatzResearch.WordTrace tailWord_6688028 prefixEnd_6688028 3434172994728264293392325 := by
  unfold tailWord_6688028
  simp only [CollatzResearch.WordTrace]
  refine ⟨121966210507212127545196369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162621614009616170060261825 121966210507212127545196369)
  ·
    refine ⟨91474657880409095658897277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121966210507212127545196369 91474657880409095658897277)
    ·
      refine ⟨34302996705153410872086479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91474657880409095658897277 34302996705153410872086479)
      ·
        refine ⟨51454495057730116308129719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34302996705153410872086479 51454495057730116308129719)
        ·
          refine ⟨77181742586595174462194579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51454495057730116308129719 77181742586595174462194579)
          ·
            refine ⟨115772613879892761693291869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77181742586595174462194579 115772613879892761693291869)
            ·
              refine ⟨43414730204959785634984451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115772613879892761693291869 43414730204959785634984451)
              ·
                refine ⟨65122095307439678452476677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43414730204959785634984451 65122095307439678452476677)
                ·
                  refine ⟨12210392870144939709839377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65122095307439678452476677 12210392870144939709839377)
                  ·
                    refine ⟨9157794652608704782379533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12210392870144939709839377 9157794652608704782379533)
                    ·
                      refine ⟨3434172994728264293392325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9157794652608704782379533 3434172994728264293392325)
                      ·
                        rfl

theorem cell23_6688028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_6688028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688028 prefixEnd_6688028 := by exact prefixLift 6688028
  have htrace : WordTrace (prefixWord ++ tailWord_6688028) baseStart_6688028 baseEnd_6688028 := by
    simpa [prefixWord, tailWord_6688028, baseEnd_6688028] using wordTrace_append hprefix tailTrace_6688028
  have hstable : (prefixWord ++ tailWord_6688028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688028).length < 2 ^ (prefixWord ++ tailWord_6688028).sum := by decide
  have hdescent : baseEnd_6688028 < baseStart_6688028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688035 : List Nat := [1, 1, 1, 4, 2, 5, 1, 1, 3, 4]
def baseStart_6688035 : Nat := 118140960795 + 6688035 * 2 ^ 59
def prefixEnd_6688035 : Nat := 4983230072969 + 3 ^ 40 * 6688035 * 2
def baseEnd_6688035 : Nat := 1144725529697615255334931

theorem tailTrace_6688035 : CollatzResearch.WordTrace tailWord_6688035 prefixEnd_6688035 1144725529697615255334931 := by
  unfold tailWord_6688035
  simp only [CollatzResearch.WordTrace]
  refine ⟨243932676325398895285897559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162621784216932596857265039 243932676325398895285897559)
  ·
    refine ⟨365899014488098342928846339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243932676325398895285897559 365899014488098342928846339)
    ·
      refine ⟨548848521732147514393269509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365899014488098342928846339 548848521732147514393269509)
      ·
        refine ⟨102909097824777658948738033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 548848521732147514393269509 102909097824777658948738033)
        ·
          refine ⟨77181823368583244211553525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102909097824777658948738033 77181823368583244211553525)
          ·
            refine ⟨7235795940804679144833143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77181823368583244211553525 7235795940804679144833143)
            ·
              refine ⟨10853693911207018717249715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7235795940804679144833143 10853693911207018717249715)
              ·
                refine ⟨16280540866810528075874573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10853693911207018717249715 16280540866810528075874573)
                ·
                  refine ⟨6105202825053948028452965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16280540866810528075874573 6105202825053948028452965)
                  ·
                    refine ⟨1144725529697615255334931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6105202825053948028452965 1144725529697615255334931)
                    ·
                      rfl

theorem cell23_6688035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 4].length) (baseStart_6688035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688035 prefixEnd_6688035 := by exact prefixLift 6688035
  have htrace : WordTrace (prefixWord ++ tailWord_6688035) baseStart_6688035 baseEnd_6688035 := by
    simpa [prefixWord, tailWord_6688035, baseEnd_6688035] using wordTrace_append hprefix tailTrace_6688035
  have hstable : (prefixWord ++ tailWord_6688035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688035).length < 2 ^ (prefixWord ++ tailWord_6688035).sum := by decide
  have hdescent : baseEnd_6688035 < baseStart_6688035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688041 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 3, 7, 3]
def baseStart_6688041 : Nat := 118140960795 + 6688041 * 2 ^ 59
def prefixEnd_6688041 : Nat := 4983230072969 + 3 ^ 40 * 6688041 * 2
def baseEnd_6688041 : Nat := 3434179669976772742529765

theorem tailTrace_6688041 : CollatzResearch.WordTrace tailWord_6688041 prefixEnd_6688041 3434179669976772742529765 := by
  unfold tailWord_6688041
  simp only [CollatzResearch.WordTrace]
  refine ⟨243932895163377158310615977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162621930108918105540410651 243932895163377158310615977)
  ·
    refine ⟨182949671372532868732961983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243932895163377158310615977 182949671372532868732961983)
    ·
      refine ⟨274424507058799303099442975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182949671372532868732961983 274424507058799303099442975)
      ·
        refine ⟨411636760588198954649164463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274424507058799303099442975 411636760588198954649164463)
        ·
          refine ⟨617455140882298431973746695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411636760588198954649164463 617455140882298431973746695)
          ·
            refine ⟨926182711323447647960620043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617455140882298431973746695 926182711323447647960620043)
            ·
              refine ⟨1389274066985171471940930065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926182711323447647960620043 1389274066985171471940930065)
              ·
                refine ⟨1041955550238878603955697549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1389274066985171471940930065 1041955550238878603955697549)
                ·
                  refine ⟨390733331339579476483386581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1041955550238878603955697549 390733331339579476483386581)
                  ·
                    refine ⟨9157812453271393980079373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 390733331339579476483386581 9157812453271393980079373)
                    ·
                      refine ⟨3434179669976772742529765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9157812453271393980079373 3434179669976772742529765)
                      ·
                        rfl

theorem cell23_6688041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 7, 3].length) (baseStart_6688041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688041 prefixEnd_6688041 := by exact prefixLift 6688041
  have htrace : WordTrace (prefixWord ++ tailWord_6688041) baseStart_6688041 baseEnd_6688041 := by
    simpa [prefixWord, tailWord_6688041, baseEnd_6688041] using wordTrace_append hprefix tailTrace_6688041
  have hstable : (prefixWord ++ tailWord_6688041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688041).length < 2 ^ (prefixWord ++ tailWord_6688041).sum := by decide
  have hdescent : baseEnd_6688041 < baseStart_6688041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688108 : List Nat := [2, 2, 1, 1, 5, 1, 1, 3, 1, 6]
def baseStart_6688108 : Nat := 118140960795 + 6688108 * 2 ^ 59
def prefixEnd_6688108 : Nat := 4983230072969 + 3 ^ 40 * 6688108 * 2
def baseEnd_6688108 : Nat := 1144738024393541326797319

theorem tailTrace_6688108 : CollatzResearch.WordTrace tailWord_6688108 prefixEnd_6688108 1144738024393541326797319 := by
  unfold tailWord_6688108
  simp only [CollatzResearch.WordTrace]
  refine ⟨121967669427067214376652489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162623559236089619168869985 121967669427067214376652489)
  ·
    refine ⟨91475752070300410782489367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121967669427067214376652489 91475752070300410782489367)
    ·
      refine ⟨137213628105450616173734051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91475752070300410782489367 137213628105450616173734051)
      ·
        refine ⟨205820442158175924260601077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137213628105450616173734051 205820442158175924260601077)
        ·
          refine ⟨19295666452328992899431351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205820442158175924260601077 19295666452328992899431351)
          ·
            refine ⟨28943499678493489349147027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19295666452328992899431351 28943499678493489349147027)
            ·
              refine ⟨43415249517740234023720541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28943499678493489349147027 43415249517740234023720541)
              ·
                refine ⟨16280718569152587758895203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43415249517740234023720541 16280718569152587758895203)
                ·
                  refine ⟨24421077853728881638342805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16280718569152587758895203 24421077853728881638342805)
                  ·
                    refine ⟨1144738024393541326797319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24421077853728881638342805 1144738024393541326797319)
                    ·
                      rfl

theorem cell23_6688108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_6688108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688108 prefixEnd_6688108 := by exact prefixLift 6688108
  have htrace : WordTrace (prefixWord ++ tailWord_6688108) baseStart_6688108 baseEnd_6688108 := by
    simpa [prefixWord, tailWord_6688108, baseEnd_6688108] using wordTrace_append hprefix tailTrace_6688108
  have hstable : (prefixWord ++ tailWord_6688108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688108).length < 2 ^ (prefixWord ++ tailWord_6688108).sum := by decide
  have hdescent : baseEnd_6688108 < baseStart_6688108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688121 : List Nat := [1, 2, 1, 3, 2, 1, 2, 11]
def baseStart_6688121 : Nat := 118140960795 + 6688121 * 2 ^ 59
def prefixEnd_6688121 : Nat := 4983230072969 + 3 ^ 40 * 6688121 * 2
def baseEnd_6688121 : Nat := 127193361052930830723311

theorem tailTrace_6688121 : CollatzResearch.WordTrace tailWord_6688121 prefixEnd_6688121 127193361052930830723311 := by
  unfold tailWord_6688121
  simp only [CollatzResearch.WordTrace]
  refine ⟨243935813003087331973528217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162623875335391554649018811 243935813003087331973528217)
  ·
    refine ⟨182951859752315498980146163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243935813003087331973528217 182951859752315498980146163)
    ·
      refine ⟨274427789628473248470219245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182951859752315498980146163 274427789628473248470219245)
      ·
        refine ⟨102910421110677468176332217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274427789628473248470219245 102910421110677468176332217)
        ·
          refine ⟨77182815833008101132249163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102910421110677468176332217 77182815833008101132249163)
          ·
            refine ⟨115774223749512151698373745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77182815833008101132249163 115774223749512151698373745)
            ·
              refine ⟨86830667812134113773780309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115774223749512151698373745 86830667812134113773780309)
              ·
                refine ⟨127193361052930830723311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 86830667812134113773780309 127193361052930830723311)
                ·
                  rfl

theorem cell23_6688121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 11].length) (baseStart_6688121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688121 prefixEnd_6688121 := by exact prefixLift 6688121
  have htrace : WordTrace (prefixWord ++ tailWord_6688121) baseStart_6688121 baseEnd_6688121 := by
    simpa [prefixWord, tailWord_6688121, baseEnd_6688121] using wordTrace_append hprefix tailTrace_6688121
  have hstable : (prefixWord ++ tailWord_6688121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688121).length < 2 ^ (prefixWord ++ tailWord_6688121).sum := by decide
  have hdescent : baseEnd_6688121 < baseStart_6688121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688129 : List Nat := [1, 2, 4, 3, 2, 2, 2, 1, 1, 5]
def baseStart_6688129 : Nat := 118140960795 + 6688129 * 2 ^ 59
def prefixEnd_6688129 : Nat := 4983230072969 + 3 ^ 40 * 6688129 * 2
def baseEnd_6688129 : Nat := 1144741618758122799409787

theorem tailTrace_6688129 : CollatzResearch.WordTrace tailWord_6688129 prefixEnd_6688129 1144741618758122799409787 := by
  unfold tailWord_6688129
  simp only [CollatzResearch.WordTrace]
  refine ⟨243936104787058349339819441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162624069858038899559879627 243936104787058349339819441)
  ·
    refine ⟨182952078590293762004864581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243936104787058349339819441 182952078590293762004864581)
    ·
      refine ⟨34303514735680080375912109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182952078590293762004864581 34303514735680080375912109)
      ·
        refine ⟨12863818025880030140967041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34303514735680080375912109 12863818025880030140967041)
        ·
          refine ⟨9647863519410022605725281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12863818025880030140967041 9647863519410022605725281)
          ·
            refine ⟨7235897639557516954293961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9647863519410022605725281 7235897639557516954293961)
            ·
              refine ⟨5426923229668137715720471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7235897639557516954293961 5426923229668137715720471)
              ·
                refine ⟨8140384844502206573580707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5426923229668137715720471 8140384844502206573580707)
                ·
                  refine ⟨12210577266753309860371061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8140384844502206573580707 12210577266753309860371061)
                  ·
                    refine ⟨1144741618758122799409787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12210577266753309860371061 1144741618758122799409787)
                    ·
                      rfl

theorem cell23_6688129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_6688129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688129 prefixEnd_6688129 := by exact prefixLift 6688129
  have htrace : WordTrace (prefixWord ++ tailWord_6688129) baseStart_6688129 baseEnd_6688129 := by
    simpa [prefixWord, tailWord_6688129, baseEnd_6688129] using wordTrace_append hprefix tailTrace_6688129
  have hstable : (prefixWord ++ tailWord_6688129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688129).length < 2 ^ (prefixWord ++ tailWord_6688129).sum := by decide
  have hdescent : baseEnd_6688129 < baseStart_6688129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688132 : List Nat := [2, 3, 2, 1, 1, 3, 4, 1, 1, 1, 4]
def baseStart_6688132 : Nat := 118140960795 + 6688132 * 2 ^ 59
def prefixEnd_6688132 : Nat := 4983230072969 + 3 ^ 40 * 6688132 * 2
def baseEnd_6688132 : Nat := 3434226396716331886491847

theorem tailTrace_6688132 : CollatzResearch.WordTrace tailWord_6688132 prefixEnd_6688132 3434226396716331886491847 := by
  unfold tailWord_6688132
  simp only [CollatzResearch.WordTrace]
  refine ⟨121968107103023740426089325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162624142804031653901452433 121968107103023740426089325)
  ·
    refine ⟨45738040163633902659783497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121968107103023740426089325 45738040163633902659783497)
    ·
      refine ⟨34303530122725426994837623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45738040163633902659783497 34303530122725426994837623)
      ·
        refine ⟨51455295184088140492256435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34303530122725426994837623 51455295184088140492256435)
        ·
          refine ⟨77182942776132210738384653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51455295184088140492256435 77182942776132210738384653)
          ·
            refine ⟨28943603541049579026894245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77182942776132210738384653 28943603541049579026894245)
            ·
              refine ⟨5426925663946796067542671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28943603541049579026894245 5426925663946796067542671)
              ·
                refine ⟨8140388495920194101314007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5426925663946796067542671 8140388495920194101314007)
                ·
                  refine ⟨12210582743880291151971011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8140388495920194101314007 12210582743880291151971011)
                  ·
                    refine ⟨18315874115820436727956517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12210582743880291151971011 18315874115820436727956517)
                    ·
                      refine ⟨3434226396716331886491847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18315874115820436727956517 3434226396716331886491847)
                      ·
                        rfl

theorem cell23_6688132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_6688132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688132 prefixEnd_6688132 := by exact prefixLift 6688132
  have htrace : WordTrace (prefixWord ++ tailWord_6688132) baseStart_6688132 baseEnd_6688132 := by
    simpa [prefixWord, tailWord_6688132, baseEnd_6688132] using wordTrace_append hprefix tailTrace_6688132
  have hstable : (prefixWord ++ tailWord_6688132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688132).length < 2 ^ (prefixWord ++ tailWord_6688132).sum := by decide
  have hdescent : baseEnd_6688132 < baseStart_6688132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688142 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 4, 4]
def baseStart_6688142 : Nat := 118140960795 + 6688142 * 2 ^ 59
def prefixEnd_6688142 : Nat := 4983230072969 + 3 ^ 40 * 6688142 * 2
def baseEnd_6688142 : Nat := 1144743843840958949122267

theorem tailTrace_6688142 : CollatzResearch.WordTrace tailWord_6688142 prefixEnd_6688142 1144743843840958949122267 := by
  unfold tailWord_6688142
  simp only [CollatzResearch.WordTrace]
  refine ⟨30492072367001406570005335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162624385957340835040028453 30492072367001406570005335)
  ·
    refine ⟨45738108550502109855008003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30492072367001406570005335 45738108550502109855008003)
    ·
      refine ⟨68607162825753164782512005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45738108550502109855008003 68607162825753164782512005)
      ·
        refine ⟨12863843029828718396721001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68607162825753164782512005 12863843029828718396721001)
        ·
          refine ⟨9647882272371538797540751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12863843029828718396721001 9647882272371538797540751)
          ·
            refine ⟨14471823408557308196311127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9647882272371538797540751 14471823408557308196311127)
            ·
              refine ⟨21707735112835962294466691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14471823408557308196311127 21707735112835962294466691)
              ·
                refine ⟨32561602669253943441700037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21707735112835962294466691 32561602669253943441700037)
                ·
                  refine ⟨6105300500485114395318757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32561602669253943441700037 6105300500485114395318757)
                  ·
                    refine ⟨1144743843840958949122267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6105300500485114395318757 1144743843840958949122267)
                    ·
                      rfl

theorem cell23_6688142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_6688142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688142 prefixEnd_6688142 := by exact prefixLift 6688142
  have htrace : WordTrace (prefixWord ++ tailWord_6688142) baseStart_6688142 baseEnd_6688142 := by
    simpa [prefixWord, tailWord_6688142, baseEnd_6688142] using wordTrace_append hprefix tailTrace_6688142
  have hstable : (prefixWord ++ tailWord_6688142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688142).length < 2 ^ (prefixWord ++ tailWord_6688142).sum := by decide
  have hdescent : baseEnd_6688142 < baseStart_6688142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688149 : List Nat := [1, 3, 2, 1, 1, 2, 4, 4, 1, 2, 2]
def baseStart_6688149 : Nat := 118140960795 + 6688149 * 2 ^ 59
def prefixEnd_6688149 : Nat := 4983230072969 + 3 ^ 40 * 6688149 * 2
def baseEnd_6688149 : Nat := 3434235125887458319979269

theorem tailTrace_6688149 : CollatzResearch.WordTrace tailWord_6688149 prefixEnd_6688149 3434235125887458319979269 := by
  unfold tailWord_6688149
  simp only [CollatzResearch.WordTrace]
  refine ⟨243936834246985892755547501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162624556164657261837031667 243936834246985892755547501)
  ·
    refine ⟨91476312842619709783330313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243936834246985892755547501 91476312842619709783330313)
    ·
      refine ⟨68607234631964782337497735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91476312842619709783330313 68607234631964782337497735)
      ·
        refine ⟨102910851947947173506246603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68607234631964782337497735 102910851947947173506246603)
        ·
          refine ⟨154366277921920760259369905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102910851947947173506246603 154366277921920760259369905)
          ·
            refine ⟨115774708441440570194527429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154366277921920760259369905 115774708441440570194527429)
            ·
              refine ⟨21707757832770106911473893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115774708441440570194527429 21707757832770106911473893)
              ·
                refine ⟨4070204593644395045901355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21707757832770106911473893 4070204593644395045901355)
                ·
                  refine ⟨6105306890466592568852033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4070204593644395045901355 6105306890466592568852033)
                  ·
                    refine ⟨4578980167849944426639025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6105306890466592568852033 4578980167849944426639025)
                    ·
                      refine ⟨3434235125887458319979269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4578980167849944426639025 3434235125887458319979269)
                      ·
                        rfl

theorem cell23_6688149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 1, 2, 2].length) (baseStart_6688149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688149 prefixEnd_6688149 := by exact prefixLift 6688149
  have htrace : WordTrace (prefixWord ++ tailWord_6688149) baseStart_6688149 baseEnd_6688149 := by
    simpa [prefixWord, tailWord_6688149, baseEnd_6688149] using wordTrace_append hprefix tailTrace_6688149
  have hstable : (prefixWord ++ tailWord_6688149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688149).length < 2 ^ (prefixWord ++ tailWord_6688149).sum := by decide
  have hdescent : baseEnd_6688149 < baseStart_6688149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688162 : List Nat := [3, 3, 1, 2, 1, 4, 1, 1, 1, 2, 4]
def baseStart_6688162 : Nat := 118140960795 + 6688162 * 2 ^ 59
def prefixEnd_6688162 : Nat := 4983230072969 + 3 ^ 40 * 6688162 * 2
def baseEnd_6688162 : Nat := 3434241801135966769116709

theorem tailTrace_6688162 : CollatzResearch.WordTrace tailWord_6688162 prefixEnd_6688162 3434241801135966769116709 := by
  unfold tailWord_6688162
  simp only [CollatzResearch.WordTrace]
  refine ⟨60984327098984698993942685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162624872263959197317180493 60984327098984698993942685)
  ·
    refine ⟨22869122662119262122728507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60984327098984698993942685 22869122662119262122728507)
    ·
      refine ⟨34303683993178893184092761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22869122662119262122728507 34303683993178893184092761)
      ·
        refine ⟨25727762994884169888069571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34303683993178893184092761 25727762994884169888069571)
        ·
          refine ⟨38591644492326254832104357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25727762994884169888069571 38591644492326254832104357)
          ·
            refine ⟨7235933342311172781019567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38591644492326254832104357 7235933342311172781019567)
            ·
              refine ⟨10853900013466759171529351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7235933342311172781019567 10853900013466759171529351)
              ·
                refine ⟨16280850020200138757294027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10853900013466759171529351 16280850020200138757294027)
                ·
                  refine ⟨24421275030300208135941041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16280850020200138757294027 24421275030300208135941041)
                  ·
                    refine ⟨18315956272725156101955781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24421275030300208135941041 18315956272725156101955781)
                    ·
                      refine ⟨3434241801135966769116709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18315956272725156101955781 3434241801135966769116709)
                      ·
                        rfl

theorem cell23_6688162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_6688162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688162 prefixEnd_6688162 := by exact prefixLift 6688162
  have htrace : WordTrace (prefixWord ++ tailWord_6688162) baseStart_6688162 baseEnd_6688162 := by
    simpa [prefixWord, tailWord_6688162, baseEnd_6688162] using wordTrace_append hprefix tailTrace_6688162
  have hstable : (prefixWord ++ tailWord_6688162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688162).length < 2 ^ (prefixWord ++ tailWord_6688162).sum := by decide
  have hdescent : baseEnd_6688162 < baseStart_6688162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688175 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 3, 3, 2]
def baseStart_6688175 : Nat := 118140960795 + 6688175 * 2 ^ 59
def prefixEnd_6688175 : Nat := 4983230072969 + 3 ^ 40 * 6688175 * 2
def baseEnd_6688175 : Nat := 3434248476384475218254149

theorem tailTrace_6688175 : CollatzResearch.WordTrace tailWord_6688175 prefixEnd_6688175 3434248476384475218254149 := by
  unfold tailWord_6688175
  simp only [CollatzResearch.WordTrace]
  refine ⟨243937782544891699195993979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162625188363261132797329319 243937782544891699195993979)
  ·
    refine ⟨365906673817337548793990969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243937782544891699195993979 365906673817337548793990969)
    ·
      refine ⟨274430005363003161595493227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365906673817337548793990969 274430005363003161595493227)
      ·
        refine ⟨411645008044504742393239841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274430005363003161595493227 411645008044504742393239841)
        ·
          refine ⟨308733756033378556794929881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411645008044504742393239841 308733756033378556794929881)
          ·
            refine ⟨231550317025033917596197411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308733756033378556794929881 231550317025033917596197411)
            ·
              refine ⟨347325475537550876394296117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231550317025033917596197411 347325475537550876394296117)
              ·
                refine ⟨32561763331645394661965261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 347325475537550876394296117 32561763331645394661965261)
                ·
                  refine ⟨12210661249367022998236973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32561763331645394661965261 12210661249367022998236973)
                  ·
                    refine ⟨4578997968512633624338865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12210661249367022998236973 4578997968512633624338865)
                    ·
                      refine ⟨3434248476384475218254149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4578997968512633624338865 3434248476384475218254149)
                      ·
                        rfl

theorem cell23_6688175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 3, 2].length) (baseStart_6688175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688175 prefixEnd_6688175 := by exact prefixLift 6688175
  have htrace : WordTrace (prefixWord ++ tailWord_6688175) baseStart_6688175 baseEnd_6688175 := by
    simpa [prefixWord, tailWord_6688175, baseEnd_6688175] using wordTrace_append hprefix tailTrace_6688175
  have hstable : (prefixWord ++ tailWord_6688175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688175).length < 2 ^ (prefixWord ++ tailWord_6688175).sum := by decide
  have hdescent : baseEnd_6688175 < baseStart_6688175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688192 : List Nat := [2, 1, 1, 2, 3, 1, 4, 3, 1, 3, 2]
def baseStart_6688192 : Nat := 118140960795 + 6688192 * 2 ^ 59
def prefixEnd_6688192 : Nat := 4983230072969 + 3 ^ 40 * 6688192 * 2
def baseEnd_6688192 : Nat := 3434257205555601651741571

theorem tailTrace_6688192 : CollatzResearch.WordTrace tailWord_6688192 prefixEnd_6688192 3434257205555601651741571 := by
  unfold tailWord_6688192
  simp only [CollatzResearch.WordTrace]
  refine ⟨121969201292915055549681415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162625601723886740732908553 121969201292915055549681415)
  ·
    refine ⟨182953801939372583324522123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121969201292915055549681415 182953801939372583324522123)
    ·
      refine ⟨274430702909058874986783185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182953801939372583324522123 274430702909058874986783185)
      ·
        refine ⟨205823027181794156240087389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274430702909058874986783185 205823027181794156240087389)
        ·
          refine ⟨77183635193172808590032771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205823027181794156240087389 77183635193172808590032771)
          ·
            refine ⟨115775452789759212885049157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77183635193172808590032771 115775452789759212885049157)
            ·
              refine ⟨21707897398079852415946717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115775452789759212885049157 21707897398079852415946717)
              ·
                refine ⟨8140461524279944655980019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21707897398079852415946717 8140461524279944655980019)
                ·
                  refine ⟨12210692286419916983970029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8140461524279944655980019 12210692286419916983970029)
                  ·
                    refine ⟨4579009607407468868988761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12210692286419916983970029 4579009607407468868988761)
                    ·
                      refine ⟨3434257205555601651741571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4579009607407468868988761 3434257205555601651741571)
                      ·
                        rfl

theorem cell23_6688192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 1, 3, 2].length) (baseStart_6688192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688192 prefixEnd_6688192 := by exact prefixLift 6688192
  have htrace : WordTrace (prefixWord ++ tailWord_6688192) baseStart_6688192 baseEnd_6688192 := by
    simpa [prefixWord, tailWord_6688192, baseEnd_6688192] using wordTrace_append hprefix tailTrace_6688192
  have hstable : (prefixWord ++ tailWord_6688192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688192).length < 2 ^ (prefixWord ++ tailWord_6688192).sum := by decide
  have hdescent : baseEnd_6688192 < baseStart_6688192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688208 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 3]
def baseStart_6688208 : Nat := 118140960795 + 6688208 * 2 ^ 59
def prefixEnd_6688208 : Nat := 4983230072969 + 3 ^ 40 * 6688208 * 2
def baseEnd_6688208 : Nat := 3434265421246073589141497

theorem tailTrace_6688208 : CollatzResearch.WordTrace tailWord_6688208 prefixEnd_6688208 3434265421246073589141497 := by
  unfold tailWord_6688208
  simp only [CollatzResearch.WordTrace]
  refine ⟨121969493076886072915972639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162625990769181430554630185 121969493076886072915972639)
  ·
    refine ⟨182954239615329109373958959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121969493076886072915972639 182954239615329109373958959)
    ·
      refine ⟨274431359422993664060938439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182954239615329109373958959 274431359422993664060938439)
      ·
        refine ⟨411647039134490496091407659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274431359422993664060938439 411647039134490496091407659)
        ·
          refine ⟨617470558701735744137111489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411647039134490496091407659 617470558701735744137111489)
          ·
            refine ⟨463102919026301808102833617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 617470558701735744137111489 463102919026301808102833617)
            ·
              refine ⟨347327189269726356077125213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463102919026301808102833617 347327189269726356077125213)
              ·
                refine ⟨130247695976147383528921955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347327189269726356077125213 130247695976147383528921955)
                ·
                  refine ⟨195371543964221075293382933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130247695976147383528921955 195371543964221075293382933)
                  ·
                    refine ⟨9158041123322862904377325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 195371543964221075293382933 9158041123322862904377325)
                    ·
                      refine ⟨3434265421246073589141497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9158041123322862904377325 3434265421246073589141497)
                      ·
                        rfl

theorem cell23_6688208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 3].length) (baseStart_6688208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688208 prefixEnd_6688208 := by exact prefixLift 6688208
  have htrace : WordTrace (prefixWord ++ tailWord_6688208) baseStart_6688208 baseEnd_6688208 := by
    simpa [prefixWord, tailWord_6688208, baseEnd_6688208] using wordTrace_append hprefix tailTrace_6688208
  have hstable : (prefixWord ++ tailWord_6688208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688208).length < 2 ^ (prefixWord ++ tailWord_6688208).sum := by decide
  have hdescent : baseEnd_6688208 < baseStart_6688208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688228 : List Nat := [2, 3, 1, 1, 1, 1, 1, 6, 7]
def baseStart_6688228 : Nat := 118140960795 + 6688228 * 2 ^ 59
def prefixEnd_6688228 : Nat := 4983230072969 + 3 ^ 40 * 6688228 * 2
def baseEnd_6688228 : Nat := 381586187873240390099045

theorem tailTrace_6688228 : CollatzResearch.WordTrace tailWord_6688228 prefixEnd_6688228 381586187873240390099045 := by
  unfold tailWord_6688228
  simp only [CollatzResearch.WordTrace]
  refine ⟨121969857806849844623836669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162626477075799792831782225 121969857806849844623836669)
  ·
    refine ⟨45738696677568691733938751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121969857806849844623836669 45738696677568691733938751)
    ·
      refine ⟨68608045016353037600908127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45738696677568691733938751 68608045016353037600908127)
      ·
        refine ⟨102912067524529556401362191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68608045016353037600908127 102912067524529556401362191)
        ·
          refine ⟨154368101286794334602043287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102912067524529556401362191 154368101286794334602043287)
          ·
            refine ⟨231552151930191501903064931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154368101286794334602043287 231552151930191501903064931)
            ·
              refine ⟨347328227895287252854597397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231552151930191501903064931 347328227895287252854597397)
              ·
                refine ⟨16281010682591589977559253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 347328227895287252854597397 16281010682591589977559253)
                ·
                  refine ⟨381586187873240390099045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16281010682591589977559253 381586187873240390099045)
                  ·
                    rfl

theorem cell23_6688228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_6688228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688228 prefixEnd_6688228 := by exact prefixLift 6688228
  have htrace : WordTrace (prefixWord ++ tailWord_6688228) baseStart_6688228 baseEnd_6688228 := by
    simpa [prefixWord, tailWord_6688228, baseEnd_6688228] using wordTrace_append hprefix tailTrace_6688228
  have hstable : (prefixWord ++ tailWord_6688228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688228).length < 2 ^ (prefixWord ++ tailWord_6688228).sum := by decide
  have hdescent : baseEnd_6688228 < baseStart_6688228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688265 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 1, 7, 2]
def baseStart_6688265 : Nat := 118140960795 + 6688265 * 2 ^ 59
def prefixEnd_6688265 : Nat := 4983230072969 + 3 ^ 40 * 6688265 * 2
def baseEnd_6688265 : Nat := 3434294689643379866128735

theorem tailTrace_6688265 : CollatzResearch.WordTrace tailWord_6688265 prefixEnd_6688265 3434294689643379866128735 := by
  unfold tailWord_6688265
  simp only [CollatzResearch.WordTrace]
  refine ⟨243941065114565644566770249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162627376743043763044513499 243941065114565644566770249)
  ·
    refine ⟨182955798835924233425077687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243941065114565644566770249 182955798835924233425077687)
    ·
      refine ⟨274433698253886350137616531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182955798835924233425077687 274433698253886350137616531)
      ·
        refine ⟨411650547380829525206424797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274433698253886350137616531 411650547380829525206424797)
        ·
          refine ⟨154368955267811071952409299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 411650547380829525206424797 154368955267811071952409299)
          ·
            refine ⟨231553432901716607928613949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154368955267811071952409299 231553432901716607928613949)
            ·
              refine ⟨86832537338143727973230231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231553432901716607928613949 86832537338143727973230231)
              ·
                refine ⟨130248806007215591959845347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86832537338143727973230231 130248806007215591959845347)
                ·
                  refine ⟨195373209010823387939768021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130248806007215591959845347 195373209010823387939768021)
                  ·
                    refine ⟨4579059586191173154838313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 195373209010823387939768021 4579059586191173154838313)
                    ·
                      refine ⟨3434294689643379866128735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4579059586191173154838313 3434294689643379866128735)
                      ·
                        rfl

theorem cell23_6688265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 7, 2].length) (baseStart_6688265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688265 prefixEnd_6688265 := by exact prefixLift 6688265
  have htrace : WordTrace (prefixWord ++ tailWord_6688265) baseStart_6688265 baseEnd_6688265 := by
    simpa [prefixWord, tailWord_6688265, baseEnd_6688265] using wordTrace_append hprefix tailTrace_6688265
  have hstable : (prefixWord ++ tailWord_6688265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688265).length < 2 ^ (prefixWord ++ tailWord_6688265).sum := by decide
  have hdescent : baseEnd_6688265 < baseStart_6688265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688305 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 7, 4]
def baseStart_6688305 : Nat := 118140960795 + 6688305 * 2 ^ 59
def prefixEnd_6688305 : Nat := 4983230072969 + 3 ^ 40 * 6688305 * 2
def baseEnd_6688305 : Nat := 1144771742956519903209517

theorem tailTrace_6688305 : CollatzResearch.WordTrace tailWord_6688305 prefixEnd_6688305 1144771742956519903209517 := by
  unfold tailWord_6688305
  simp only [CollatzResearch.WordTrace]
  refine ⟨243942524034420731398226369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162628349356280487598817579 243942524034420731398226369)
  ·
    refine ⟨182956893025815548548669777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243942524034420731398226369 182956893025815548548669777)
    ·
      refine ⟨137217669769361661411502333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182956893025815548548669777 137217669769361661411502333)
      ·
        refine ⟨51456626163510623029313375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137217669769361661411502333 51456626163510623029313375)
        ·
          refine ⟨77184939245265934543970063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51456626163510623029313375 77184939245265934543970063)
          ·
            refine ⟨115777408867898901815955095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77184939245265934543970063 115777408867898901815955095)
            ·
              refine ⟨173666113301848352723932643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115777408867898901815955095 173666113301848352723932643)
              ·
                refine ⟨260499169952772529085898965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173666113301848352723932643 260499169952772529085898965)
                ·
                  refine ⟨6105449295768106150450757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 260499169952772529085898965 6105449295768106150450757)
                  ·
                    refine ⟨1144771742956519903209517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6105449295768106150450757 1144771742956519903209517)
                    ·
                      rfl

theorem cell23_6688305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 4].length) (baseStart_6688305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688305 prefixEnd_6688305 := by exact prefixLift 6688305
  have htrace : WordTrace (prefixWord ++ tailWord_6688305) baseStart_6688305 baseEnd_6688305 := by
    simpa [prefixWord, tailWord_6688305, baseEnd_6688305] using wordTrace_append hprefix tailTrace_6688305
  have hstable : (prefixWord ++ tailWord_6688305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688305).length < 2 ^ (prefixWord ++ tailWord_6688305).sum := by decide
  have hdescent : baseEnd_6688305 < baseStart_6688305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688312 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 2, 4, 2]
def baseStart_6688312 : Nat := 118140960795 + 6688312 * 2 ^ 59
def prefixEnd_6688312 : Nat := 4983230072969 + 3 ^ 40 * 6688312 * 2
def baseEnd_6688312 : Nat := 3434318823234141182241019

theorem tailTrace_6688312 : CollatzResearch.WordTrace tailWord_6688312 prefixEnd_6688312 3434318823234141182241019 := by
  unfold tailWord_6688312
  simp only [CollatzResearch.WordTrace]
  refine ⟨121971389672697685796865595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162628519563596914395820793 121971389672697685796865595)
  ·
    refine ⟨182957084509046528695298393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121971389672697685796865595 182957084509046528695298393)
    ·
      refine ⟨137217813381784896521473795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182957084509046528695298393 137217813381784896521473795)
      ·
        refine ⟨205826720072677344782210693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137217813381784896521473795 205826720072677344782210693)
        ·
          refine ⟨38592510013627002146664505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205826720072677344782210693 38592510013627002146664505)
          ·
            refine ⟨28944382510220251609998379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38592510013627002146664505 28944382510220251609998379)
            ·
              refine ⟨43416573765330377414997569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28944382510220251609998379 43416573765330377414997569)
              ·
                refine ⟨32562430323997783061248177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43416573765330377414997569 32562430323997783061248177)
                ·
                  refine ⟨24421822742998337295936133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32562430323997783061248177 24421822742998337295936133)
                  ·
                    refine ⟨4579091764312188242988025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24421822742998337295936133 4579091764312188242988025)
                    ·
                      refine ⟨3434318823234141182241019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4579091764312188242988025 3434318823234141182241019)
                      ·
                        rfl

theorem cell23_6688312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 2, 4, 2].length) (baseStart_6688312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688312 prefixEnd_6688312 := by exact prefixLift 6688312
  have htrace : WordTrace (prefixWord ++ tailWord_6688312) baseStart_6688312 baseEnd_6688312 := by
    simpa [prefixWord, tailWord_6688312, baseEnd_6688312] using wordTrace_append hprefix tailTrace_6688312
  have hstable : (prefixWord ++ tailWord_6688312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688312).length < 2 ^ (prefixWord ++ tailWord_6688312).sum := by decide
  have hdescent : baseEnd_6688312 < baseStart_6688312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688356 : List Nat := [2, 3, 1, 1, 2, 5, 1, 3, 1, 4]
def baseStart_6688356 : Nat := 118140960795 + 6688356 * 2 ^ 59
def prefixEnd_6688356 : Nat := 4983230072969 + 3 ^ 40 * 6688356 * 2
def baseEnd_6688356 : Nat := 1144780472127646336696939

theorem tailTrace_6688356 : CollatzResearch.WordTrace tailWord_6688356 prefixEnd_6688356 1144780472127646336696939 := by
  unfold tailWord_6688356
  simp only [CollatzResearch.WordTrace]
  refine ⟨121972192078617983554166461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162629589438157311405555281 121972192078617983554166461)
  ·
    refine ⟨45739572029481743832812423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121972192078617983554166461 45739572029481743832812423)
    ·
      refine ⟨68609358044222615749218635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45739572029481743832812423 68609358044222615749218635)
      ·
        refine ⟨102914037066333923623827953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68609358044222615749218635 102914037066333923623827953)
        ·
          refine ⟨77185527799750442717870965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102914037066333923623827953 77185527799750442717870965)
          ·
            refine ⟨7236143231226604004800403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77185527799750442717870965 7236143231226604004800403)
            ·
              refine ⟨10854214846839906007200605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7236143231226604004800403 10854214846839906007200605)
              ·
                refine ⟨4070330567564964752700227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10854214846839906007200605 4070330567564964752700227)
                ·
                  refine ⟨6105495851347447129050341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4070330567564964752700227 6105495851347447129050341)
                  ·
                    refine ⟨1144780472127646336696939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6105495851347447129050341 1144780472127646336696939)
                    ·
                      rfl

theorem cell23_6688356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_6688356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688356 prefixEnd_6688356 := by exact prefixLift 6688356
  have htrace : WordTrace (prefixWord ++ tailWord_6688356) baseStart_6688356 baseEnd_6688356 := by
    simpa [prefixWord, tailWord_6688356, baseEnd_6688356] using wordTrace_append hprefix tailTrace_6688356
  have hstable : (prefixWord ++ tailWord_6688356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688356).length < 2 ^ (prefixWord ++ tailWord_6688356).sum := by decide
  have hdescent : baseEnd_6688356 < baseStart_6688356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688373 : List Nat := [1, 3, 4, 2, 1, 2, 3, 2, 1, 4]
def baseStart_6688373 : Nat := 118140960795 + 6688373 * 2 ^ 59
def prefixEnd_6688373 : Nat := 4983230072969 + 3 ^ 40 * 6688373 * 2
def baseEnd_6688373 : Nat := 1144783381851355147859413

theorem tailTrace_6688373 : CollatzResearch.WordTrace tailWord_6688373 prefixEnd_6688373 1144783381851355147859413 := by
  unfold tailWord_6688373
  simp only [CollatzResearch.WordTrace]
  refine ⟨243945004198174379011701773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162630002798782919341134515 243945004198174379011701773)
  ·
    refine ⟨91479376574315392129388165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243945004198174379011701773 91479376574315392129388165)
    ·
      refine ⟨17152383107684136024260281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91479376574315392129388165 17152383107684136024260281)
      ·
        refine ⟨12864287330763102018195211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17152383107684136024260281 12864287330763102018195211)
        ·
          refine ⟨19296430996144653027292817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12864287330763102018195211 19296430996144653027292817)
          ·
            refine ⟨14472323247108489770469613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19296430996144653027292817 14472323247108489770469613)
            ·
              refine ⟨5427121217665683663926105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14472323247108489770469613 5427121217665683663926105)
              ·
                refine ⟨4070340913249262747944579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5427121217665683663926105 4070340913249262747944579)
                ·
                  refine ⟨6105511369873894121916869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4070340913249262747944579 6105511369873894121916869)
                  ·
                    refine ⟨1144783381851355147859413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6105511369873894121916869 1144783381851355147859413)
                    ·
                      rfl

theorem cell23_6688373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_6688373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688373 prefixEnd_6688373 := by exact prefixLift 6688373
  have htrace : WordTrace (prefixWord ++ tailWord_6688373) baseStart_6688373 baseEnd_6688373 := by
    simpa [prefixWord, tailWord_6688373, baseEnd_6688373] using wordTrace_append hprefix tailTrace_6688373
  have hstable : (prefixWord ++ tailWord_6688373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688373).length < 2 ^ (prefixWord ++ tailWord_6688373).sum := by decide
  have hdescent : baseEnd_6688373 < baseStart_6688373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688395 : List Nat := [1, 1, 1, 1, 4, 1, 4, 3, 1, 6]
def baseStart_6688395 : Nat := 118140960795 + 6688395 * 2 ^ 59
def prefixEnd_6688395 : Nat := 4983230072969 + 3 ^ 40 * 6688395 * 2
def baseEnd_6688395 : Nat := 1144787147376154785834379

theorem tailTrace_6688395 : CollatzResearch.WordTrace tailWord_6688395 prefixEnd_6688395 1144787147376154785834379 := by
  unfold tailWord_6688395
  simp only [CollatzResearch.WordTrace]
  refine ⟨243945806604094676769002639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162630537736063117846001759 243945806604094676769002639)
  ·
    refine ⟨365918709906142015153503959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243945806604094676769002639 365918709906142015153503959)
    ·
      refine ⟨548878064859213022730255939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365918709906142015153503959 548878064859213022730255939)
      ·
        refine ⟨823317097288819534095383909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548878064859213022730255939 823317097288819534095383909)
        ·
          refine ⟨154371955741653662642884483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 823317097288819534095383909 154371955741653662642884483)
          ·
            refine ⟨231557933612480493964326725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154371955741653662642884483 231557933612480493964326725)
            ·
              refine ⟨43417112552340092618311261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231557933612480493964326725 43417112552340092618311261)
              ·
                refine ⟨16281417207127534731866723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43417112552340092618311261 16281417207127534731866723)
                ·
                  refine ⟨24422125810691302097800085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16281417207127534731866723 24422125810691302097800085)
                  ·
                    refine ⟨1144787147376154785834379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24422125810691302097800085 1144787147376154785834379)
                    ·
                      rfl

theorem cell23_6688395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 6].length) (baseStart_6688395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688395 prefixEnd_6688395 := by exact prefixLift 6688395
  have htrace : WordTrace (prefixWord ++ tailWord_6688395) baseStart_6688395 baseEnd_6688395 := by
    simpa [prefixWord, tailWord_6688395, baseEnd_6688395] using wordTrace_append hprefix tailTrace_6688395
  have hstable : (prefixWord ++ tailWord_6688395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688395).length < 2 ^ (prefixWord ++ tailWord_6688395).sum := by decide
  have hdescent : baseEnd_6688395 < baseStart_6688395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688405 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 3, 1, 5]
def baseStart_6688405 : Nat := 118140960795 + 6688405 * 2 ^ 59
def prefixEnd_6688405 : Nat := 4983230072969 + 3 ^ 40 * 6688405 * 2
def baseEnd_6688405 : Nat := 3434366576935009318378091

theorem tailTrace_6688405 : CollatzResearch.WordTrace tailWord_6688405 prefixEnd_6688405 3434366576935009318378091 := by
  unfold tailWord_6688405
  simp only [CollatzResearch.WordTrace]
  refine ⟨243946171334058448476866669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162630780889372298984577779 243946171334058448476866669)
  ·
    refine ⟨91479814250271918178825001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243946171334058448476866669 91479814250271918178825001)
    ·
      refine ⟨68609860687703938634118751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91479814250271918178825001 68609860687703938634118751)
      ·
        refine ⟨102914791031555907951178127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68609860687703938634118751 102914791031555907951178127)
        ·
          refine ⟨154372186547333861926767191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102914791031555907951178127 154372186547333861926767191)
          ·
            refine ⟨231558279821000792890150787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154372186547333861926767191 231558279821000792890150787)
            ·
              refine ⟨347337419731501189335226181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231558279821000792890150787 347337419731501189335226181)
              ·
                refine ⟨65125766199656473000354909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 347337419731501189335226181 65125766199656473000354909)
                ·
                  refine ⟨24422162324871177375133091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65125766199656473000354909 24422162324871177375133091)
                  ·
                    refine ⟨36633243487306766062699637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24422162324871177375133091 36633243487306766062699637)
                    ·
                      refine ⟨3434366576935009318378091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36633243487306766062699637 3434366576935009318378091)
                      ·
                        rfl

theorem cell23_6688405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_6688405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688405 prefixEnd_6688405 := by exact prefixLift 6688405
  have htrace : WordTrace (prefixWord ++ tailWord_6688405) baseStart_6688405 baseEnd_6688405 := by
    simpa [prefixWord, tailWord_6688405, baseEnd_6688405] using wordTrace_append hprefix tailTrace_6688405
  have hstable : (prefixWord ++ tailWord_6688405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688405).length < 2 ^ (prefixWord ++ tailWord_6688405).sum := by decide
  have hdescent : baseEnd_6688405 < baseStart_6688405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688419 : List Nat := [1, 1, 1, 4, 1, 1, 7, 1, 1, 1, 4]
def baseStart_6688419 : Nat := 118140960795 + 6688419 * 2 ^ 59
def prefixEnd_6688419 : Nat := 4983230072969 + 3 ^ 40 * 6688419 * 2
def baseEnd_6688419 : Nat := 3434373765664172263603027

theorem tailTrace_6688419 : CollatzResearch.WordTrace tailWord_6688419 prefixEnd_6688419 3434373765664172263603027 := by
  unfold tailWord_6688419
  simp only [CollatzResearch.WordTrace]
  refine ⟨243946681956007728867876311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162631121304005152578584207 243946681956007728867876311)
  ·
    refine ⟨365920022934011593301814467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243946681956007728867876311 365920022934011593301814467)
    ·
      refine ⟨548880034401017389952721701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365920022934011593301814467 548880034401017389952721701)
      ·
        refine ⟨102915006450190760616135319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 548880034401017389952721701 102915006450190760616135319)
        ·
          refine ⟨154372509675286140924202979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102915006450190760616135319 154372509675286140924202979)
          ·
            refine ⟨231558764512929211386304469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154372509675286140924202979 231558764512929211386304469)
            ·
              refine ⟨5427158543271778391866511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 231558764512929211386304469 5427158543271778391866511)
              ·
                refine ⟨8140737814907667587799767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5427158543271778391866511 8140737814907667587799767)
                ·
                  refine ⟨12211106722361501381699651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8140737814907667587799767 12211106722361501381699651)
                  ·
                    refine ⟨18316660083542252072549477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12211106722361501381699651 18316660083542252072549477)
                    ·
                      refine ⟨3434373765664172263603027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18316660083542252072549477 3434373765664172263603027)
                      ·
                        rfl

theorem cell23_6688419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 1, 1, 4].length) (baseStart_6688419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688419 prefixEnd_6688419 := by exact prefixLift 6688419
  have htrace : WordTrace (prefixWord ++ tailWord_6688419) baseStart_6688419 baseEnd_6688419 := by
    simpa [prefixWord, tailWord_6688419, baseEnd_6688419] using wordTrace_append hprefix tailTrace_6688419
  have hstable : (prefixWord ++ tailWord_6688419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688419).length < 2 ^ (prefixWord ++ tailWord_6688419).sum := by decide
  have hdescent : baseEnd_6688419 < baseStart_6688419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688424 : List Nat := [2, 1, 7, 1, 2, 1, 2, 2, 1, 4]
def baseStart_6688424 : Nat := 118140960795 + 6688424 * 2 ^ 59
def prefixEnd_6688424 : Nat := 4983230072969 + 3 ^ 40 * 6688424 * 2
def baseEnd_6688424 : Nat := 1144792111022481581346835

theorem tailTrace_6688424 : CollatzResearch.WordTrace tailWord_6688424 prefixEnd_6688424 1144792111022481581346835 := by
  unfold tailWord_6688424
  simp only [CollatzResearch.WordTrace]
  refine ⟨121973432160494807360904163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162631242880659743147872217 121973432160494807360904163)
  ·
    refine ⟨182960148240742211041356245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121973432160494807360904163 182960148240742211041356245)
    ·
      refine ⟨4288128474392395571281787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 182960148240742211041356245 4288128474392395571281787)
      ·
        refine ⟨6432192711588593356922681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4288128474392395571281787 6432192711588593356922681)
        ·
          refine ⟨4824144533691445017692011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6432192711588593356922681 4824144533691445017692011)
          ·
            refine ⟨7236216800537167526538017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4824144533691445017692011 7236216800537167526538017)
            ·
              refine ⟨5427162600402875644903513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7236216800537167526538017 5427162600402875644903513)
              ·
                refine ⟨4070371950302156733677635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5427162600402875644903513 4070371950302156733677635)
                ·
                  refine ⟨6105557925453235100516453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4070371950302156733677635 6105557925453235100516453)
                  ·
                    refine ⟨1144792111022481581346835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6105557925453235100516453 1144792111022481581346835)
                    ·
                      rfl

theorem cell23_6688424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_6688424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688424 prefixEnd_6688424 := by exact prefixLift 6688424
  have htrace : WordTrace (prefixWord ++ tailWord_6688424) baseStart_6688424 baseEnd_6688424 := by
    simpa [prefixWord, tailWord_6688424, baseEnd_6688424] using wordTrace_append hprefix tailTrace_6688424
  have hstable : (prefixWord ++ tailWord_6688424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688424).length < 2 ^ (prefixWord ++ tailWord_6688424).sum := by decide
  have hdescent : baseEnd_6688424 < baseStart_6688424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688430 : List Nat := [4, 1, 4, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_6688430 : Nat := 118140960795 + 6688430 * 2 ^ 59
def prefixEnd_6688430 : Nat := 4983230072969 + 3 ^ 40 * 6688430 * 2
def baseEnd_6688430 : Nat := 3434379413951371720565477

theorem tailTrace_6688430 : CollatzResearch.WordTrace tailWord_6688430 prefixEnd_6688430 3434379413951371720565477 := by
  unfold tailWord_6688430
  simp only [CollatzResearch.WordTrace]
  refine ⟨30493385394870984718315843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162631388772645251831017829 30493385394870984718315843)
  ·
    refine ⟨45740078092306477077473765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30493385394870984718315843 45740078092306477077473765)
    ·
      refine ⟨8576264642307464452026331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45740078092306477077473765 8576264642307464452026331)
      ·
        refine ⟨12864396963461196678039497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8576264642307464452026331 12864396963461196678039497)
        ·
          refine ⟨9648297722595897508529623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12864396963461196678039497 9648297722595897508529623)
          ·
            refine ⟨14472446583893846262794435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9648297722595897508529623 14472446583893846262794435)
            ·
              refine ⟨21708669875840769394191653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14472446583893846262794435 21708669875840769394191653)
              ·
                refine ⟨4070375601720144261410935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21708669875840769394191653 4070375601720144261410935)
                ·
                  refine ⟨6105563402580216392116403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4070375601720144261410935 6105563402580216392116403)
                  ·
                    refine ⟨9158345103870324588174605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6105563402580216392116403 9158345103870324588174605)
                    ·
                      refine ⟨3434379413951371720565477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9158345103870324588174605 3434379413951371720565477)
                      ·
                        rfl

theorem cell23_6688430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_6688430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688430 prefixEnd_6688430 := by exact prefixLift 6688430
  have htrace : WordTrace (prefixWord ++ tailWord_6688430) baseStart_6688430 baseEnd_6688430 := by
    simpa [prefixWord, tailWord_6688430, baseEnd_6688430] using wordTrace_append hprefix tailTrace_6688430
  have hstable : (prefixWord ++ tailWord_6688430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688430).length < 2 ^ (prefixWord ++ tailWord_6688430).sum := by decide
  have hdescent : baseEnd_6688430 < baseStart_6688430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688442 : List Nat := [3, 1, 1, 1, 2, 6, 1, 8]
def baseStart_6688442 : Nat := 118140960795 + 6688442 * 2 ^ 59
def prefixEnd_6688442 : Nat := 4983230072969 + 3 ^ 40 * 6688442 * 2
def baseEnd_6688442 : Nat := 127199465767378728652423

theorem tailTrace_6688442 : CollatzResearch.WordTrace tailWord_6688442 prefixEnd_6688442 127199465767378728652423 := by
  unfold tailWord_6688442
  simp only [CollatzResearch.WordTrace]
  refine ⟨60986880208731100948990895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162631680556616269197309053 60986880208731100948990895)
  ·
    refine ⟨91480320313096651423486343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60986880208731100948990895 91480320313096651423486343)
    ·
      refine ⟨137220480469644977135229515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91480320313096651423486343 137220480469644977135229515)
      ·
        refine ⟨205830720704467465702844273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137220480469644977135229515 205830720704467465702844273)
        ·
          refine ⟨154373040528350599277133205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205830720704467465702844273 154373040528350599277133205)
          ·
            refine ⟨7236236274766434341115619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 154373040528350599277133205 7236236274766434341115619)
            ·
              refine ⟨10854354412149651511673429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7236236274766434341115619 10854354412149651511673429)
              ·
                refine ⟨127199465767378728652423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10854354412149651511673429 127199465767378728652423)
                ·
                  rfl

theorem cell23_6688442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 8].length) (baseStart_6688442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688442 prefixEnd_6688442 := by exact prefixLift 6688442
  have htrace : WordTrace (prefixWord ++ tailWord_6688442) baseStart_6688442 baseEnd_6688442 := by
    simpa [prefixWord, tailWord_6688442, baseEnd_6688442] using wordTrace_append hprefix tailTrace_6688442
  have hstable : (prefixWord ++ tailWord_6688442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688442).length < 2 ^ (prefixWord ++ tailWord_6688442).sum := by decide
  have hdescent : baseEnd_6688442 < baseStart_6688442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688455 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 2, 7]
def baseStart_6688455 : Nat := 118140960795 + 6688455 * 2 ^ 59
def prefixEnd_6688455 : Nat := 4983230072969 + 3 ^ 40 * 6688455 * 2
def baseEnd_6688455 : Nat := 1144797416989244707584287

theorem tailTrace_6688455 : CollatzResearch.WordTrace tailWord_6688455 prefixEnd_6688455 1144797416989244707584287 := by
  unfold tailWord_6688455
  simp only [CollatzResearch.WordTrace]
  refine ⟨243947994983877307016186819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162631996655918204677457879 243947994983877307016186819)
  ·
    refine ⟨365921992475815960524280229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243947994983877307016186819 365921992475815960524280229)
    ·
      refine ⟨68610373589215492598302543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 365921992475815960524280229 68610373589215492598302543)
      ·
        refine ⟨102915560383823238897453815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68610373589215492598302543 102915560383823238897453815)
        ·
          refine ⟨154373340575734858346180723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102915560383823238897453815 154373340575734858346180723)
          ·
            refine ⟨231560010863602287519271085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154373340575734858346180723 231560010863602287519271085)
            ·
              refine ⟨86835004073850857819726657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231560010863602287519271085 86835004073850857819726657)
              ·
                refine ⟨65126253055388143364794993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86835004073850857819726657 65126253055388143364794993)
                ·
                  refine ⟨48844689791541107523596245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65126253055388143364794993 48844689791541107523596245)
                  ·
                    refine ⟨1144797416989244707584287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48844689791541107523596245 1144797416989244707584287)
                    ·
                      rfl

theorem cell23_6688455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_6688455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688455 prefixEnd_6688455 := by exact prefixLift 6688455
  have htrace : WordTrace (prefixWord ++ tailWord_6688455) baseStart_6688455 baseEnd_6688455 := by
    simpa [prefixWord, tailWord_6688455, baseEnd_6688455] using wordTrace_append hprefix tailTrace_6688455
  have hstable : (prefixWord ++ tailWord_6688455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688455).length < 2 ^ (prefixWord ++ tailWord_6688455).sum := by decide
  have hdescent : baseEnd_6688455 < baseStart_6688455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688509 : List Nat := [1, 4, 1, 1, 1, 1, 2, 5, 1, 4, 2]
def baseStart_6688509 : Nat := 118140960795 + 6688509 * 2 ^ 59
def prefixEnd_6688509 : Nat := 4983230072969 + 3 ^ 40 * 6688509 * 2
def baseEnd_6688509 : Nat := 3434419978923076911477613

theorem tailTrace_6688509 : CollatzResearch.WordTrace tailWord_6688509 prefixEnd_6688509 3434419978923076911477613 := by
  unfold tailWord_6688509
  simp only [CollatzResearch.WordTrace]
  refine ⟨243949964525681674238652581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162633309683787782825768387 243949964525681674238652581)
  ·
    refine ⟨45740618348565313919747359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243949964525681674238652581 45740618348565313919747359)
    ·
      refine ⟨68610927522847970879621039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45740618348565313919747359 68610927522847970879621039)
      ·
        refine ⟨102916391284271956319431559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68610927522847970879621039 102916391284271956319431559)
        ·
          refine ⟨154374586926407934479147339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102916391284271956319431559 154374586926407934479147339)
          ·
            refine ⟨231561880389611901718721009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154374586926407934479147339 231561880389611901718721009)
            ·
              refine ⟨173671410292208926289040757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231561880389611901718721009 173671410292208926289040757)
              ·
                refine ⟨16281694714894586839597571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173671410292208926289040757 16281694714894586839597571)
                ·
                  refine ⟨24422542072341880259396357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16281694714894586839597571 24422542072341880259396357)
                  ·
                    refine ⟨4579226638564102548636817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24422542072341880259396357 4579226638564102548636817)
                    ·
                      refine ⟨3434419978923076911477613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4579226638564102548636817 3434419978923076911477613)
                      ·
                        rfl

theorem cell23_6688509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 4, 2].length) (baseStart_6688509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688509 prefixEnd_6688509 := by exact prefixLift 6688509
  have htrace : WordTrace (prefixWord ++ tailWord_6688509) baseStart_6688509 baseEnd_6688509 := by
    simpa [prefixWord, tailWord_6688509, baseEnd_6688509] using wordTrace_append hprefix tailTrace_6688509
  have hstable : (prefixWord ++ tailWord_6688509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688509).length < 2 ^ (prefixWord ++ tailWord_6688509).sum := by decide
  have hdescent : baseEnd_6688509 < baseStart_6688509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688526 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2]
def baseStart_6688526 : Nat := 118140960795 + 6688526 * 2 ^ 59
def prefixEnd_6688526 : Nat := 4983230072969 + 3 ^ 40 * 6688526 * 2
def baseEnd_6688526 : Nat := 3434428708094203344965035

theorem tailTrace_6688526 : CollatzResearch.WordTrace tailWord_6688526 prefixEnd_6688526 3434428708094203344965035 := by
  unfold tailWord_6688526
  simp only [CollatzResearch.WordTrace]
  refine ⟨30493823070827510767752679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162633723044413390761347621 30493823070827510767752679)
  ·
    refine ⟨45740734606241266151629019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30493823070827510767752679 45740734606241266151629019)
    ·
      refine ⟨68611101909361899227443529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45740734606241266151629019 68611101909361899227443529)
      ·
        refine ⟨51458326432021424420582647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68611101909361899227443529 51458326432021424420582647)
        ·
          refine ⟨77187489648032136630873971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51458326432021424420582647 77187489648032136630873971)
          ·
            refine ⟨115781234472048204946310957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77187489648032136630873971 115781234472048204946310957)
            ·
              refine ⟨43417962927018076854866609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115781234472048204946310957 43417962927018076854866609)
              ·
                refine ⟨32563472195263557641149957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43417962927018076854866609 32563472195263557641149957)
                ·
                  refine ⟨6105651036611917057715617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32563472195263557641149957 6105651036611917057715617)
                  ·
                    refine ⟨4579238277458937793286713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6105651036611917057715617 4579238277458937793286713)
                    ·
                      refine ⟨3434428708094203344965035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4579238277458937793286713 3434428708094203344965035)
                      ·
                        rfl

theorem cell23_6688526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_6688526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688526 prefixEnd_6688526 := by exact prefixLift 6688526
  have htrace : WordTrace (prefixWord ++ tailWord_6688526) baseStart_6688526 baseEnd_6688526 := by
    simpa [prefixWord, tailWord_6688526, baseEnd_6688526] using wordTrace_append hprefix tailTrace_6688526
  have hstable : (prefixWord ++ tailWord_6688526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688526).length < 2 ^ (prefixWord ++ tailWord_6688526).sum := by decide
  have hdescent : baseEnd_6688526 < baseStart_6688526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688549 : List Nat := [1, 3, 1, 2, 3, 4, 1, 1, 7]
def baseStart_6688549 : Nat := 118140960795 + 6688549 * 2 ^ 59
def prefixEnd_6688549 : Nat := 4983230072969 + 3 ^ 40 * 6688549 * 2
def baseEnd_6688549 : Nat := 381604502016584083886381

theorem tailTrace_6688549 : CollatzResearch.WordTrace tailWord_6688549 prefixEnd_6688549 381604502016584083886381 := by
  unfold tailWord_6688549
  simp only [CollatzResearch.WordTrace]
  refine ⟨243951423445536761070108701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162634282297024507380072467 243951423445536761070108701)
  ·
    refine ⟨91481783792076285401290763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243951423445536761070108701 91481783792076285401290763)
    ·
      refine ⟨137222675688114428101936145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91481783792076285401290763 137222675688114428101936145)
      ·
        refine ⟨102917006766085821076452109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137222675688114428101936145 102917006766085821076452109)
        ·
          refine ⟨38593877537282182903669541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102917006766085821076452109 38593877537282182903669541)
          ·
            refine ⟨7236352038240409294438039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38593877537282182903669541 7236352038240409294438039)
            ·
              refine ⟨10854528057360613941657059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7236352038240409294438039 10854528057360613941657059)
              ·
                refine ⟨16281792086040920912485589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10854528057360613941657059 16281792086040920912485589)
                ·
                  refine ⟨381604502016584083886381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16281792086040920912485589 381604502016584083886381)
                  ·
                    rfl

theorem cell23_6688549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 7].length) (baseStart_6688549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688549 prefixEnd_6688549 := by exact prefixLift 6688549
  have htrace : WordTrace (prefixWord ++ tailWord_6688549) baseStart_6688549 baseEnd_6688549 := by
    simpa [prefixWord, tailWord_6688549, baseEnd_6688549] using wordTrace_append hprefix tailTrace_6688549
  have hstable : (prefixWord ++ tailWord_6688549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688549).length < 2 ^ (prefixWord ++ tailWord_6688549).sum := by decide
  have hdescent : baseEnd_6688549 < baseStart_6688549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688579 : List Nat := [1, 1, 1, 3, 1, 6, 2, 1, 2, 5]
def baseStart_6688579 : Nat := 118140960795 + 6688579 * 2 ^ 59
def prefixEnd_6688579 : Nat := 4983230072969 + 3 ^ 40 * 6688579 * 2
def baseEnd_6688579 : Nat := 1144818640856297212534097

theorem tailTrace_6688579 : CollatzResearch.WordTrace tailWord_6688579 prefixEnd_6688579 1144818640856297212534097 := by
  unfold tailWord_6688579
  simp only [CollatzResearch.WordTrace]
  refine ⟨243952517635428076193700791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162635011756952050795800527 243952517635428076193700791)
  ·
    refine ⟨365928776453142114290551187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243952517635428076193700791 365928776453142114290551187)
    ·
      refine ⟨548893164679713171435826781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365928776453142114290551187 548893164679713171435826781)
      ·
        refine ⟨205834936754892439288435043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 548893164679713171435826781 205834936754892439288435043)
        ·
          refine ⟨308752405132338658932652565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205834936754892439288435043 308752405132338658932652565)
          ·
            refine ⟨14472768990578374637468089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 308752405132338658932652565 14472768990578374637468089)
            ·
              refine ⟨10854576742933780978101067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14472768990578374637468089 10854576742933780978101067)
              ·
                refine ⟨16281865114400671467151601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10854576742933780978101067 16281865114400671467151601)
                ·
                  refine ⟨12211398835800503600363701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16281865114400671467151601 12211398835800503600363701)
                  ·
                    refine ⟨1144818640856297212534097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12211398835800503600363701 1144818640856297212534097)
                    ·
                      rfl

theorem cell23_6688579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 5].length) (baseStart_6688579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688579 prefixEnd_6688579 := by exact prefixLift 6688579
  have htrace : WordTrace (prefixWord ++ tailWord_6688579) baseStart_6688579 baseEnd_6688579 := by
    simpa [prefixWord, tailWord_6688579, baseEnd_6688579] using wordTrace_append hprefix tailTrace_6688579
  have hstable : (prefixWord ++ tailWord_6688579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688579).length < 2 ^ (prefixWord ++ tailWord_6688579).sum := by decide
  have hdescent : baseEnd_6688579 < baseStart_6688579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688602 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5]
def baseStart_6688602 : Nat := 118140960795 + 6688602 * 2 ^ 59
def prefixEnd_6688602 : Nat := 4983230072969 + 3 ^ 40 * 6688602 * 2
def baseEnd_6688602 : Nat := 3434467732623945047614685

theorem tailTrace_6688602 : CollatzResearch.WordTrace tailWord_6688602 prefixEnd_6688602 3434467732623945047614685 := by
  unfold tailWord_6688602
  simp only [CollatzResearch.WordTrace]
  refine ⟨60988339128586187780447015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162635571009563167414525373 60988339128586187780447015)
  ·
    refine ⟨91482508692879281670670523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60988339128586187780447015 91482508692879281670670523)
    ·
      refine ⟨137223763039318922506005785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91482508692879281670670523 137223763039318922506005785)
      ·
        refine ⟨102917822279489191879504339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137223763039318922506005785 102917822279489191879504339)
        ·
          refine ⟨154376733419233787819256509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102917822279489191879504339 154376733419233787819256509)
          ·
            refine ⟨57891275032212670432221191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154376733419233787819256509 57891275032212670432221191)
            ·
              refine ⟨86836912548319005648331787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57891275032212670432221191 86836912548319005648331787)
              ·
                refine ⟨130255368822478508472497681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86836912548319005648331787 130255368822478508472497681)
                ·
                  refine ⟨97691526616858881354373261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130255368822478508472497681 97691526616858881354373261)
                  ·
                    refine ⟨36634322481322080507889973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97691526616858881354373261 36634322481322080507889973)
                    ·
                      refine ⟨3434467732623945047614685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36634322481322080507889973 3434467732623945047614685)
                      ·
                        rfl

theorem cell23_6688602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_6688602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688602 prefixEnd_6688602 := by exact prefixLift 6688602
  have htrace : WordTrace (prefixWord ++ tailWord_6688602) baseStart_6688602 baseEnd_6688602 := by
    simpa [prefixWord, tailWord_6688602, baseEnd_6688602] using wordTrace_append hprefix tailTrace_6688602
  have hstable : (prefixWord ++ tailWord_6688602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688602).length < 2 ^ (prefixWord ++ tailWord_6688602).sum := by decide
  have hdescent : baseEnd_6688602 < baseStart_6688602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688609 : List Nat := [1, 2, 3, 1, 1, 1, 4, 3, 3, 4]
def baseStart_6688609 : Nat := 118140960795 + 6688609 * 2 ^ 59
def prefixEnd_6688609 : Nat := 4983230072969 + 3 ^ 40 * 6688609 * 2
def baseEnd_6688609 : Nat := 1144823775662842173409051

theorem tailTrace_6688609 : CollatzResearch.WordTrace tailWord_6688609 prefixEnd_6688609 1144823775662842173409051 := by
  unfold tailWord_6688609
  simp only [CollatzResearch.WordTrace]
  refine ⟨243953611825319391317292881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162635741216879594211528587 243953611825319391317292881)
  ·
    refine ⟨182965208868989543487969661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243953611825319391317292881 182965208868989543487969661)
    ·
      refine ⟨68611953325871078807988623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182965208868989543487969661 68611953325871078807988623)
      ·
        refine ⟨102917929988806618211982935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68611953325871078807988623 102917929988806618211982935)
        ·
          refine ⟨154376894983209927317974403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102917929988806618211982935 154376894983209927317974403)
          ·
            refine ⟨231565342474814890976961605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154376894983209927317974403 231565342474814890976961605)
            ·
              refine ⟨43418501714027792058180301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231565342474814890976961605 43418501714027792058180301)
              ·
                refine ⟨16281938142760422021817613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43418501714027792058180301 16281938142760422021817613)
                ·
                  refine ⟨6105726803535158258181605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16281938142760422021817613 6105726803535158258181605)
                  ·
                    refine ⟨1144823775662842173409051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6105726803535158258181605 1144823775662842173409051)
                    ·
                      rfl

theorem cell23_6688609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_6688609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688609 prefixEnd_6688609 := by exact prefixLift 6688609
  have htrace : WordTrace (prefixWord ++ tailWord_6688609) baseStart_6688609 baseEnd_6688609 := by
    simpa [prefixWord, tailWord_6688609, baseEnd_6688609] using wordTrace_append hprefix tailTrace_6688609
  have hstable : (prefixWord ++ tailWord_6688609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688609).length < 2 ^ (prefixWord ++ tailWord_6688609).sum := by decide
  have hdescent : baseEnd_6688609 < baseStart_6688609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688616 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 2, 4, 2]
def baseStart_6688616 : Nat := 118140960795 + 6688616 * 2 ^ 59
def prefixEnd_6688616 : Nat := 4983230072969 + 3 ^ 40 * 6688616 * 2
def baseEnd_6688616 : Nat := 3434474921353107992839621

theorem tailTrace_6688616 : CollatzResearch.WordTrace tailWord_6688616 prefixEnd_6688616 3434474921353107992839621 := by
  unfold tailWord_6688616
  simp only [CollatzResearch.WordTrace]
  refine ⟨121976933568147015756398851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162635911424196021008531801 121976933568147015756398851)
  ·
    refine ⟨182965400352220523634598277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121976933568147015756398851 182965400352220523634598277)
    ·
      refine ⟨34306012566041348181487177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182965400352220523634598277 34306012566041348181487177)
      ·
        refine ⟨25729509424531011136115383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34306012566041348181487177 25729509424531011136115383)
        ·
          refine ⟨38594264136796516704173075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25729509424531011136115383 38594264136796516704173075)
          ·
            refine ⟨57891396205194775056259613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38594264136796516704173075 57891396205194775056259613)
            ·
              refine ⟨21709273576948040646097355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57891396205194775056259613 21709273576948040646097355)
              ·
                refine ⟨32563910365422060969146033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21709273576948040646097355 32563910365422060969146033)
                ·
                  refine ⟨24422932774066545726859525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32563910365422060969146033 24422932774066545726859525)
                  ·
                    refine ⟨4579299895137477323786161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24422932774066545726859525 4579299895137477323786161)
                    ·
                      refine ⟨3434474921353107992839621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4579299895137477323786161 3434474921353107992839621)
                      ·
                        rfl

theorem cell23_6688616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_6688616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688616 prefixEnd_6688616 := by exact prefixLift 6688616
  have htrace : WordTrace (prefixWord ++ tailWord_6688616) baseStart_6688616 baseEnd_6688616 := by
    simpa [prefixWord, tailWord_6688616, baseEnd_6688616] using wordTrace_append hprefix tailTrace_6688616
  have hstable : (prefixWord ++ tailWord_6688616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688616).length < 2 ^ (prefixWord ++ tailWord_6688616).sum := by decide
  have hdescent : baseEnd_6688616 < baseStart_6688616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688630 : List Nat := [5, 1, 1, 3, 3, 1, 1, 1, 2, 5]
def baseStart_6688630 : Nat := 118140960795 + 6688630 * 2 ^ 59
def prefixEnd_6688630 : Nat := 4983230072969 + 3 ^ 40 * 6688630 * 2
def baseEnd_6688630 : Nat := 1144827370027423646021519

theorem tailTrace_6688630 : CollatzResearch.WordTrace tailWord_6688630 prefixEnd_6688630 1144827370027423646021519 := by
  unfold tailWord_6688630
  simp only [CollatzResearch.WordTrace]
  refine ⟨15247148609890206993987959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162636251838828874602538229 15247148609890206993987959)
  ·
    refine ⟨22870722914835310490981939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15247148609890206993987959 22870722914835310490981939)
    ·
      refine ⟨34306084372252965736472909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22870722914835310490981939 34306084372252965736472909)
      ·
        refine ⟨12864781639594862151177341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34306084372252965736472909 12864781639594862151177341)
        ·
          refine ⟨4824293114848073306691503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12864781639594862151177341 4824293114848073306691503)
          ·
            refine ⟨7236439672272109960037255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4824293114848073306691503 7236439672272109960037255)
            ·
              refine ⟨10854659508408164940055883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7236439672272109960037255 10854659508408164940055883)
              ·
                refine ⟨16281989262612247410083825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10854659508408164940055883 16281989262612247410083825)
                ·
                  refine ⟨12211491946959185557562869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16281989262612247410083825 12211491946959185557562869)
                  ·
                    refine ⟨1144827370027423646021519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12211491946959185557562869 1144827370027423646021519)
                    ·
                      rfl

theorem cell23_6688630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_6688630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688630 prefixEnd_6688630 := by exact prefixLift 6688630
  have htrace : WordTrace (prefixWord ++ tailWord_6688630) baseStart_6688630 baseEnd_6688630 := by
    simpa [prefixWord, tailWord_6688630, baseEnd_6688630] using wordTrace_append hprefix tailTrace_6688630
  have hstable : (prefixWord ++ tailWord_6688630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688630).length < 2 ^ (prefixWord ++ tailWord_6688630).sum := by decide
  have hdescent : baseEnd_6688630 < baseStart_6688630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688643 : List Nat := [1, 1, 1, 3, 4, 3, 2, 3, 1, 4]
def baseStart_6688643 : Nat := 118140960795 + 6688643 * 2 ^ 59
def prefixEnd_6688643 : Nat := 4983230072969 + 3 ^ 40 * 6688643 * 2
def baseEnd_6688643 : Nat := 1144829595110259795733999

theorem tailTrace_6688643 : CollatzResearch.WordTrace tailWord_6688643 prefixEnd_6688643 1144829595110259795733999 := by
  unfold tailWord_6688643
  simp only [CollatzResearch.WordTrace]
  refine ⟨243954851907196215124030583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162636567938130810082687055 243954851907196215124030583)
  ·
    refine ⟨365932277860794322686045875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243954851907196215124030583 365932277860794322686045875)
    ·
      refine ⟨548898416791191484029068813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365932277860794322686045875 548898416791191484029068813)
      ·
        refine ⟨205836906296696806510900805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 548898416791191484029068813 205836906296696806510900805)
        ·
          refine ⟨38594419930630651220793901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205836906296696806510900805 38594419930630651220793901)
          ·
            refine ⟨14472907473986494207797713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38594419930630651220793901 14472907473986494207797713)
            ·
              refine ⟨10854680605489870655848285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14472907473986494207797713 10854680605489870655848285)
              ·
                refine ⟨4070505227058701495943107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10854680605489870655848285 4070505227058701495943107)
                ·
                  refine ⟨6105757840588052243914661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4070505227058701495943107 6105757840588052243914661)
                  ·
                    refine ⟨1144829595110259795733999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6105757840588052243914661 1144829595110259795733999)
                    ·
                      rfl

theorem cell23_6688643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 1, 4].length) (baseStart_6688643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688643 prefixEnd_6688643 := by exact prefixLift 6688643
  have htrace : WordTrace (prefixWord ++ tailWord_6688643) baseStart_6688643 baseEnd_6688643 := by
    simpa [prefixWord, tailWord_6688643, baseEnd_6688643] using wordTrace_append hprefix tailTrace_6688643
  have hstable : (prefixWord ++ tailWord_6688643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688643).length < 2 ^ (prefixWord ++ tailWord_6688643).sum := by decide
  have hdescent : baseEnd_6688643 < baseStart_6688643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688673 : List Nat := [1, 2, 3, 4, 2, 1, 3, 1, 6]
def baseStart_6688673 : Nat := 118140960795 + 6688673 * 2 ^ 59
def prefixEnd_6688673 : Nat := 4983230072969 + 3 ^ 40 * 6688673 * 2
def baseEnd_6688673 : Nat := 381611576638934918869651

theorem tailTrace_6688673 : CollatzResearch.WordTrace tailWord_6688673 prefixEnd_6688673 381611576638934918869651 := by
  unfold tailWord_6688673
  simp only [CollatzResearch.WordTrace]
  refine ⟨243955946097087530247622673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162637297398058353498415115 243955946097087530247622673)
  ·
    refine ⟨182966959572815647685717005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243955946097087530247622673 182966959572815647685717005)
    ·
      refine ⟨68612609839805867882143877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182966959572815647685717005 68612609839805867882143877)
      ·
        refine ⟨12864864344963600227901977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68612609839805867882143877 12864864344963600227901977)
        ·
          refine ⟨9648648258722700170926483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12864864344963600227901977 9648648258722700170926483)
          ·
            refine ⟨14472972388084050256389725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9648648258722700170926483 14472972388084050256389725)
            ·
              refine ⟨5427364645531518846146147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14472972388084050256389725 5427364645531518846146147)
              ·
                refine ⟨8141046968297278269219221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5427364645531518846146147 8141046968297278269219221)
                ·
                  refine ⟨381611576638934918869651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8141046968297278269219221 381611576638934918869651)
                  ·
                    rfl

theorem cell23_6688673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 6].length) (baseStart_6688673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688673 prefixEnd_6688673 := by exact prefixLift 6688673
  have htrace : WordTrace (prefixWord ++ tailWord_6688673) baseStart_6688673 baseEnd_6688673 := by
    simpa [prefixWord, tailWord_6688673, baseEnd_6688673] using wordTrace_append hprefix tailTrace_6688673
  have hstable : (prefixWord ++ tailWord_6688673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688673).length < 2 ^ (prefixWord ++ tailWord_6688673).sum := by decide
  have hdescent : baseEnd_6688673 < baseStart_6688673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688676 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 1, 5, 2]
def baseStart_6688676 : Nat := 118140960795 + 6688676 * 2 ^ 59
def prefixEnd_6688676 : Nat := 4983230072969 + 3 ^ 40 * 6688676 * 2
def baseEnd_6688676 : Nat := 3434505730192377758089345

theorem tailTrace_6688676 : CollatzResearch.WordTrace tailWord_6688676 prefixEnd_6688676 3434505730192377758089345 := by
  unfold tailWord_6688676
  simp only [CollatzResearch.WordTrace]
  refine ⟨121978027758038330879990941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162637370344051107839987921 121978027758038330879990941)
  ·
    refine ⟨45741760409264374079996603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121978027758038330879990941 45741760409264374079996603)
    ·
      refine ⟨68612640613896561119994905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45741760409264374079996603 68612640613896561119994905)
      ·
        refine ⟨51459480460422420839996179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68612640613896561119994905 51459480460422420839996179)
        ·
          refine ⟨77189220690633631259994269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51459480460422420839996179 77189220690633631259994269)
          ·
            refine ⟨28945957758987611722497851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77189220690633631259994269 28945957758987611722497851)
            ·
              refine ⟨43418936638481417583746777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28945957758987611722497851 43418936638481417583746777)
              ·
                refine ⟨32564202478861063187810083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43418936638481417583746777 32564202478861063187810083)
                ·
                  refine ⟨48846303718291594781715125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32564202478861063187810083 48846303718291594781715125)
                  ·
                    refine ⟨4579340973589837010785793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48846303718291594781715125 4579340973589837010785793)
                    ·
                      refine ⟨3434505730192377758089345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4579340973589837010785793 3434505730192377758089345)
                      ·
                        rfl

theorem cell23_6688676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_6688676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688676 prefixEnd_6688676 := by exact prefixLift 6688676
  have htrace : WordTrace (prefixWord ++ tailWord_6688676) baseStart_6688676 baseEnd_6688676 := by
    simpa [prefixWord, tailWord_6688676, baseEnd_6688676] using wordTrace_append hprefix tailTrace_6688676
  have hstable : (prefixWord ++ tailWord_6688676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688676).length < 2 ^ (prefixWord ++ tailWord_6688676).sum := by decide
  have hdescent : baseEnd_6688676 < baseStart_6688676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688699 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 4, 4]
def baseStart_6688699 : Nat := 118140960795 + 6688699 * 2 ^ 59
def prefixEnd_6688699 : Nat := 4983230072969 + 3 ^ 40 * 6688699 * 2
def baseEnd_6688699 : Nat := 1144839180082477056033913

theorem tailTrace_6688699 : CollatzResearch.WordTrace tailWord_6688699 prefixEnd_6688699 1144839180082477056033913 := by
  unfold tailWord_6688699
  simp only [CollatzResearch.WordTrace]
  refine ⟨243956894394993336688069151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162637929596662224458712767 243956894394993336688069151)
  ·
    refine ⟨365935341592490005032103727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243956894394993336688069151 365935341592490005032103727)
    ·
      refine ⟨548903012388735007548155591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365935341592490005032103727 548903012388735007548155591)
      ·
        refine ⟨823354518583102511322233387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548903012388735007548155591 823354518583102511322233387)
        ·
          refine ⟨1235031777874653766983350081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 823354518583102511322233387 1235031777874653766983350081)
          ·
            refine ⟨926273833405990325237512561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1235031777874653766983350081 926273833405990325237512561)
            ·
              refine ⟨694705375054492743928134421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 926273833405990325237512561 694705375054492743928134421)
              ·
                refine ⟨32564314455679347371631301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 694705375054492743928134421 32564314455679347371631301)
                ·
                  refine ⟨6105808960439877632180869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32564314455679347371631301 6105808960439877632180869)
                  ·
                    refine ⟨1144839180082477056033913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6105808960439877632180869 1144839180082477056033913)
                    ·
                      rfl

theorem cell23_6688699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 4].length) (baseStart_6688699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688699 prefixEnd_6688699 := by exact prefixLift 6688699
  have htrace : WordTrace (prefixWord ++ tailWord_6688699) baseStart_6688699 baseEnd_6688699 := by
    simpa [prefixWord, tailWord_6688699, baseEnd_6688699] using wordTrace_append hprefix tailTrace_6688699
  have hstable : (prefixWord ++ tailWord_6688699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688699).length < 2 ^ (prefixWord ++ tailWord_6688699).sum := by decide
  have hdescent : baseEnd_6688699 < baseStart_6688699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688716 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 4, 4]
def baseStart_6688716 : Nat := 118140960795 + 6688716 * 2 ^ 59
def prefixEnd_6688716 : Nat := 4983230072969 + 3 ^ 40 * 6688716 * 2
def baseEnd_6688716 : Nat := 1144842089806185867196387

theorem tailTrace_6688716 : CollatzResearch.WordTrace tailWord_6688716 prefixEnd_6688716 1144842089806185867196387 := by
  unfold tailWord_6688716
  simp only [CollatzResearch.WordTrace]
  refine ⟨121978757217965874295719001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162638342957287832394292001 121978757217965874295719001)
  ·
    refine ⟨91484067913474405721789251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121978757217965874295719001 91484067913474405721789251)
    ·
      refine ⟨137226101870211608582683877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91484067913474405721789251 137226101870211608582683877)
      ·
        refine ⟨25729894100664676609253227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137226101870211608582683877 25729894100664676609253227)
        ·
          refine ⟨38594841150997014913879841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25729894100664676609253227 38594841150997014913879841)
          ·
            refine ⟨28946130863247761185409881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38594841150997014913879841 28946130863247761185409881)
            ·
              refine ⟨21709598147435820889057411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28946130863247761185409881 21709598147435820889057411)
              ·
                refine ⟨32564397221153731333586117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21709598147435820889057411 32564397221153731333586117)
                ·
                  refine ⟨6105824478966324625047397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32564397221153731333586117 6105824478966324625047397)
                  ·
                    refine ⟨1144842089806185867196387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6105824478966324625047397 1144842089806185867196387)
                    ·
                      rfl

theorem cell23_6688716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 4, 4].length) (baseStart_6688716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688716 prefixEnd_6688716 := by exact prefixLift 6688716
  have htrace : WordTrace (prefixWord ++ tailWord_6688716) baseStart_6688716 baseEnd_6688716 := by
    simpa [prefixWord, tailWord_6688716, baseEnd_6688716] using wordTrace_append hprefix tailTrace_6688716
  have hstable : (prefixWord ++ tailWord_6688716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688716).length < 2 ^ (prefixWord ++ tailWord_6688716).sum := by decide
  have hdescent : baseEnd_6688716 < baseStart_6688716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688743 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 3]
def baseStart_6688743 : Nat := 118140960795 + 6688743 * 2 ^ 59
def prefixEnd_6688743 : Nat := 4983230072969 + 3 ^ 40 * 6688743 * 2
def baseEnd_6688743 : Nat := 3434540133396228995951537

theorem tailTrace_6688743 : CollatzResearch.WordTrace tailWord_6688743 prefixEnd_6688743 3434540133396228995951537 := by
  unfold tailWord_6688743
  simp only [CollatzResearch.WordTrace]
  refine ⟨243958499206833932202670883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162638999471222621468447255 243958499206833932202670883)
  ·
    refine ⟨365937748810250898304006325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243958499206833932202670883 365937748810250898304006325)
    ·
      refine ⟨34306663950961021716000593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 365937748810250898304006325 34306663950961021716000593)
      ·
        refine ⟨25729997963220766287000445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34306663950961021716000593 25729997963220766287000445)
        ·
          refine ⟨9648749236207787357625167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25729997963220766287000445 9648749236207787357625167)
          ·
            refine ⟨14473123854311681036437751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9648749236207787357625167 14473123854311681036437751)
            ·
              refine ⟨21709685781467521554656627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14473123854311681036437751 21709685781467521554656627)
              ·
                refine ⟨32564528672201282331984941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21709685781467521554656627 32564528672201282331984941)
                ·
                  refine ⟨12211698252075480874494353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32564528672201282331984941 12211698252075480874494353)
                  ·
                    refine ⟨9158773689056610655870765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12211698252075480874494353 9158773689056610655870765)
                    ·
                      refine ⟨3434540133396228995951537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9158773689056610655870765 3434540133396228995951537)
                      ·
                        rfl

theorem cell23_6688743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_6688743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688743 prefixEnd_6688743 := by exact prefixLift 6688743
  have htrace : WordTrace (prefixWord ++ tailWord_6688743) baseStart_6688743 baseEnd_6688743 := by
    simpa [prefixWord, tailWord_6688743, baseEnd_6688743] using wordTrace_append hprefix tailTrace_6688743
  have hstable : (prefixWord ++ tailWord_6688743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688743).length < 2 ^ (prefixWord ++ tailWord_6688743).sum := by decide
  have hdescent : baseEnd_6688743 < baseStart_6688743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688773 : List Nat := [1, 3, 1, 1, 2, 4, 1, 4, 2, 1, 3]
def baseStart_6688773 : Nat := 118140960795 + 6688773 * 2 ^ 59
def prefixEnd_6688773 : Nat := 4983230072969 + 3 ^ 40 * 6688773 * 2
def baseEnd_6688773 : Nat := 3434555537815863878576399

theorem tailTrace_6688773 : CollatzResearch.WordTrace tailWord_6688773 prefixEnd_6688773 3434555537815863878576399 := by
  unfold tailWord_6688773
  simp only [CollatzResearch.WordTrace]
  refine ⟨243959593396725247326262973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162639728931150164884175315 243959593396725247326262973)
  ·
    refine ⟨91484847523771967747348615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243959593396725247326262973 91484847523771967747348615)
    ·
      refine ⟨137227271285657951621022923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91484847523771967747348615 137227271285657951621022923)
      ·
        refine ⟨205840906928486927431534385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137227271285657951621022923 205840906928486927431534385)
        ·
          refine ⟨154380680196365195573650789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205840906928486927431534385 154380680196365195573650789)
          ·
            refine ⟨28946377536818474170059523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154380680196365195573650789 28946377536818474170059523)
            ·
              refine ⟨43419566305227711255089285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28946377536818474170059523 43419566305227711255089285)
              ·
                refine ⟨8141168682230195860329241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43419566305227711255089285 8141168682230195860329241)
                ·
                  refine ⟨6105876511672646895246931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8141168682230195860329241 6105876511672646895246931)
                  ·
                    refine ⟨9158814767508970342870397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6105876511672646895246931 9158814767508970342870397)
                    ·
                      refine ⟨3434555537815863878576399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9158814767508970342870397 3434555537815863878576399)
                      ·
                        rfl

theorem cell23_6688773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 1, 3].length) (baseStart_6688773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688773 prefixEnd_6688773 := by exact prefixLift 6688773
  have htrace : WordTrace (prefixWord ++ tailWord_6688773) baseStart_6688773 baseEnd_6688773 := by
    simpa [prefixWord, tailWord_6688773, baseEnd_6688773] using wordTrace_append hprefix tailTrace_6688773
  have hstable : (prefixWord ++ tailWord_6688773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688773).length < 2 ^ (prefixWord ++ tailWord_6688773).sum := by decide
  have hdescent : baseEnd_6688773 < baseStart_6688773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688779 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 4]
def baseStart_6688779 : Nat := 118140960795 + 6688779 * 2 ^ 59
def prefixEnd_6688779 : Nat := 4983230072969 + 3 ^ 40 * 6688779 * 2
def baseEnd_6688779 : Nat := 3434558618699790855101371

theorem tailTrace_6688779 : CollatzResearch.WordTrace tailWord_6688779 prefixEnd_6688779 3434558618699790855101371 := by
  unfold tailWord_6688779
  simp only [CollatzResearch.WordTrace]
  refine ⟨243959812234703510350981391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162639874823135673567320927 243959812234703510350981391)
  ·
    refine ⟨365939718352055265526472087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243959812234703510350981391 365939718352055265526472087)
    ·
      refine ⟨548909577528082898289708131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365939718352055265526472087 548909577528082898289708131)
      ·
        refine ⟨823364366292124347434562197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548909577528082898289708131 823364366292124347434562197)
        ·
          refine ⟨38595204669943328785995103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 823364366292124347434562197 38595204669943328785995103)
          ·
            refine ⟨57892807004914993178992655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38595204669943328785995103 57892807004914993178992655)
            ·
              refine ⟨86839210507372489768488983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57892807004914993178992655 86839210507372489768488983)
              ·
                refine ⟨130258815761058734652733475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86839210507372489768488983 130258815761058734652733475)
                ·
                  refine ⟨195388223641588101979100213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130258815761058734652733475 195388223641588101979100213)
                  ·
                    refine ⟨18317645966398884560540645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 195388223641588101979100213 18317645966398884560540645)
                    ·
                      refine ⟨3434558618699790855101371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18317645966398884560540645 3434558618699790855101371)
                      ·
                        rfl

theorem cell23_6688779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 4].length) (baseStart_6688779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688779 prefixEnd_6688779 := by exact prefixLift 6688779
  have htrace : WordTrace (prefixWord ++ tailWord_6688779) baseStart_6688779 baseEnd_6688779 := by
    simpa [prefixWord, tailWord_6688779, baseEnd_6688779] using wordTrace_append hprefix tailTrace_6688779
  have hstable : (prefixWord ++ tailWord_6688779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688779).length < 2 ^ (prefixWord ++ tailWord_6688779).sum := by decide
  have hdescent : baseEnd_6688779 < baseStart_6688779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688817 : List Nat := [1, 2, 2, 3, 1, 5, 2, 1, 1, 3, 2]
def baseStart_6688817 : Nat := 118140960795 + 6688817 * 2 ^ 59
def prefixEnd_6688817 : Nat := 4983230072969 + 3 ^ 40 * 6688817 * 2
def baseEnd_6688817 : Nat := 3434578130964661706426197

theorem tailTrace_6688817 : CollatzResearch.WordTrace tailWord_6688817 prefixEnd_6688817 3434578130964661706426197 := by
  unfold tailWord_6688817
  simp only [CollatzResearch.WordTrace]
  refine ⟨243961198208565842840864705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162640798805710561893909803 243961198208565842840864705)
  ·
    refine ⟨182970898656424382130648529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243961198208565842840864705 182970898656424382130648529)
    ·
      refine ⟨137228173992318286597986397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182970898656424382130648529 137228173992318286597986397)
      ·
        refine ⟨51460565247119357474244899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137228173992318286597986397 51460565247119357474244899)
        ·
          refine ⟨77190847870679036211367349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51460565247119357474244899 77190847870679036211367349)
          ·
            refine ⟨7236641987876159644815689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77190847870679036211367349 7236641987876159644815689)
            ·
              refine ⟨5427481490907119733611767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7236641987876159644815689 5427481490907119733611767)
              ·
                refine ⟨8141222236360679600417651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5427481490907119733611767 8141222236360679600417651)
                ·
                  refine ⟨12211833354541019400626477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8141222236360679600417651 12211833354541019400626477)
                  ·
                    refine ⟨4579437507952882275234929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12211833354541019400626477 4579437507952882275234929)
                    ·
                      refine ⟨3434578130964661706426197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4579437507952882275234929 3434578130964661706426197)
                      ·
                        rfl

theorem cell23_6688817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_6688817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688817 prefixEnd_6688817 := by exact prefixLift 6688817
  have htrace : WordTrace (prefixWord ++ tailWord_6688817) baseStart_6688817 baseEnd_6688817 := by
    simpa [prefixWord, tailWord_6688817, baseEnd_6688817] using wordTrace_append hprefix tailTrace_6688817
  have hstable : (prefixWord ++ tailWord_6688817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688817).length < 2 ^ (prefixWord ++ tailWord_6688817).sum := by decide
  have hdescent : baseEnd_6688817 < baseStart_6688817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688903 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 2, 4, 2]
def baseStart_6688903 : Nat := 118140960795 + 6688903 * 2 ^ 59
def prefixEnd_6688903 : Nat := 4983230072969 + 3 ^ 40 * 6688903 * 2
def baseEnd_6688903 : Nat := 3434622290300948369950801

theorem tailTrace_6688903 : CollatzResearch.WordTrace tailWord_6688903 prefixEnd_6688903 3434622290300948369950801 := by
  unfold tailWord_6688903
  simp only [CollatzResearch.WordTrace]
  refine ⟨243964334886254279528495363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162642889924169519685663575 243964334886254279528495363)
  ·
    refine ⟨365946502329381419292743045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243964334886254279528495363 365946502329381419292743045)
    ·
      refine ⟨68614969186759016117389321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 365946502329381419292743045 68614969186759016117389321)
      ·
        refine ⟨51461226890069262088041991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68614969186759016117389321 51461226890069262088041991)
        ·
          refine ⟨77191840335103893132062987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51461226890069262088041991 77191840335103893132062987)
          ·
            refine ⟨115787760502655839698094481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77191840335103893132062987 115787760502655839698094481)
            ·
              refine ⟨86840820376991879773570861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115787760502655839698094481 86840820376991879773570861)
              ·
                refine ⟨32565307641371954915089073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86840820376991879773570861 32565307641371954915089073)
                ·
                  refine ⟨24423980731028966186316805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32565307641371954915089073 24423980731028966186316805)
                  ·
                    refine ⟨4579496387067931159934401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24423980731028966186316805 4579496387067931159934401)
                    ·
                      refine ⟨3434622290300948369950801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4579496387067931159934401 3434622290300948369950801)
                      ·
                        rfl

theorem cell23_6688903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_6688903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688903 prefixEnd_6688903 := by exact prefixLift 6688903
  have htrace : WordTrace (prefixWord ++ tailWord_6688903) baseStart_6688903 baseEnd_6688903 := by
    simpa [prefixWord, tailWord_6688903, baseEnd_6688903] using wordTrace_append hprefix tailTrace_6688903
  have hstable : (prefixWord ++ tailWord_6688903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688903).length < 2 ^ (prefixWord ++ tailWord_6688903).sum := by decide
  have hdescent : baseEnd_6688903 < baseStart_6688903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688920 : List Nat := [2, 1, 2, 4, 3, 1, 2, 1, 2, 1, 4]
def baseStart_6688920 : Nat := 118140960795 + 6688920 * 2 ^ 59
def prefixEnd_6688920 : Nat := 4983230072969 + 3 ^ 40 * 6688920 * 2
def baseEnd_6688920 : Nat := 3434631019472074803438223

theorem tailTrace_6688920 : CollatzResearch.WordTrace tailWord_6688920 prefixEnd_6688920 3434631019472074803438223 := by
  unfold tailWord_6688920
  simp only [CollatzResearch.WordTrace]
  refine ⟨121982477463596345715932107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162643303284795127621242809 121982477463596345715932107)
  ·
    refine ⟨182973716195394518573898161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121982477463596345715932107 182973716195394518573898161)
    ·
      refine ⟨137230287146545888930423621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182973716195394518573898161 137230287146545888930423621)
      ·
        refine ⟨25730678839977354174454429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137230287146545888930423621 25730678839977354174454429)
        ·
          refine ⟨9649004564991507815420411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25730678839977354174454429 9649004564991507815420411)
          ·
            refine ⟨14473506847487261723130617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9649004564991507815420411 14473506847487261723130617)
            ·
              refine ⟨10855130135615446292347963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14473506847487261723130617 10855130135615446292347963)
              ·
                refine ⟨16282695203423169438521945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10855130135615446292347963 16282695203423169438521945)
                ·
                  refine ⟨12212021402567377078891459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16282695203423169438521945 12212021402567377078891459)
                  ·
                    refine ⟨18318032103851065618337189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12212021402567377078891459 18318032103851065618337189)
                    ·
                      refine ⟨3434631019472074803438223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18318032103851065618337189 3434631019472074803438223)
                      ·
                        rfl

theorem cell23_6688920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_6688920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688920 prefixEnd_6688920 := by exact prefixLift 6688920
  have htrace : WordTrace (prefixWord ++ tailWord_6688920) baseStart_6688920 baseEnd_6688920 := by
    simpa [prefixWord, tailWord_6688920, baseEnd_6688920] using wordTrace_append hprefix tailTrace_6688920
  have hstable : (prefixWord ++ tailWord_6688920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688920).length < 2 ^ (prefixWord ++ tailWord_6688920).sum := by decide
  have hdescent : baseEnd_6688920 < baseStart_6688920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688946 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6]
def baseStart_6688946 : Nat := 118140960795 + 6688946 * 2 ^ 59
def prefixEnd_6688946 : Nat := 4983230072969 + 3 ^ 40 * 6688946 * 2
def baseEnd_6688946 : Nat := 3434644369969091701713103

theorem tailTrace_6688946 : CollatzResearch.WordTrace tailWord_6688946 prefixEnd_6688946 3434644369969091701713103 := by
  unfold tailWord_6688946
  simp only [CollatzResearch.WordTrace]
  refine ⟨60991475806274624468077673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162643935483398998581540461 60991475806274624468077673)
  ·
    refine ⟨45743606854705968351058255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60991475806274624468077673 45743606854705968351058255)
    ·
      refine ⟨68615410282058952526587383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45743606854705968351058255 68615410282058952526587383)
      ·
        refine ⟨102923115423088428789881075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68615410282058952526587383 102923115423088428789881075)
        ·
          refine ⟨154384673134632643184821613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102923115423088428789881075 154384673134632643184821613)
          ·
            refine ⟨57894252425487241194308105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154384673134632643184821613 57894252425487241194308105)
            ·
              refine ⟨43420689319115430895731079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57894252425487241194308105 43420689319115430895731079)
              ·
                refine ⟨65131033978673146343596619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43420689319115430895731079 65131033978673146343596619)
                ·
                  refine ⟨97696550968009719515394929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65131033978673146343596619 97696550968009719515394929)
                  ·
                    refine ⟨73272413226007289636546197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97696550968009719515394929 73272413226007289636546197)
                    ·
                      refine ⟨3434644369969091701713103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73272413226007289636546197 3434644369969091701713103)
                      ·
                        rfl

theorem cell23_6688946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_6688946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688946 prefixEnd_6688946 := by exact prefixLift 6688946
  have htrace : WordTrace (prefixWord ++ tailWord_6688946) baseStart_6688946 baseEnd_6688946 := by
    simpa [prefixWord, tailWord_6688946, baseEnd_6688946] using wordTrace_append hprefix tailTrace_6688946
  have hstable : (prefixWord ++ tailWord_6688946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688946).length < 2 ^ (prefixWord ++ tailWord_6688946).sum := by decide
  have hdescent : baseEnd_6688946 < baseStart_6688946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6688970 : List Nat := [3, 1, 2, 1, 3, 1, 3, 2, 3, 1, 3]
def baseStart_6688970 : Nat := 118140960795 + 6688970 * 2 ^ 59
def prefixEnd_6688970 : Nat := 4983230072969 + 3 ^ 40 * 6688970 * 2
def baseEnd_6688970 : Nat := 3434656693504799607812993

theorem tailTrace_6688970 : CollatzResearch.WordTrace tailWord_6688970 prefixEnd_6688970 3434656693504799607812993 := by
  unfold tailWord_6688970
  simp only [CollatzResearch.WordTrace]
  refine ⟨60991694644252887492796091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162644519051341033314122909 60991694644252887492796091)
  ·
    refine ⟨91487541966379331239194137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60991694644252887492796091 91487541966379331239194137)
    ·
      refine ⟨68615656474784498429395603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91487541966379331239194137 68615656474784498429395603)
      ·
        refine ⟨102923484712176747644093405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68615656474784498429395603 102923484712176747644093405)
        ·
          refine ⟨38596306767066280366535027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102923484712176747644093405 38596306767066280366535027)
          ·
            refine ⟨57894460150599420549802541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38596306767066280366535027 57894460150599420549802541)
            ·
              refine ⟨21710422556474782706175953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57894460150599420549802541 21710422556474782706175953)
              ·
                refine ⟨16282816917356087029631965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21710422556474782706175953 16282816917356087029631965)
                ·
                  refine ⟨6106056344008532636111987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16282816917356087029631965 6106056344008532636111987)
                  ·
                    refine ⟨9159084516012798954167981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6106056344008532636111987 9159084516012798954167981)
                    ·
                      refine ⟨3434656693504799607812993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9159084516012798954167981 3434656693504799607812993)
                      ·
                        rfl

theorem cell23_6688970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_6688970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6688970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6688970 prefixEnd_6688970 := by exact prefixLift 6688970
  have htrace : WordTrace (prefixWord ++ tailWord_6688970) baseStart_6688970 baseEnd_6688970 := by
    simpa [prefixWord, tailWord_6688970, baseEnd_6688970] using wordTrace_append hprefix tailTrace_6688970
  have hstable : (prefixWord ++ tailWord_6688970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6688970).length < 2 ^ (prefixWord ++ tailWord_6688970).sum := by decide
  have hdescent : baseEnd_6688970 < baseStart_6688970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6688970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689003 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 4, 4]
def baseStart_6689003 : Nat := 118140960795 + 6689003 * 2 ^ 59
def prefixEnd_6689003 : Nat := 4983230072969 + 3 ^ 40 * 6689003 * 2
def baseEnd_6689003 : Nat := 1144891212788799326233447

theorem tailTrace_6689003 : CollatzResearch.WordTrace tailWord_6689003 prefixEnd_6689003 1144891212788799326233447 := by
  unfold tailWord_6689003
  simp only [CollatzResearch.WordTrace]
  refine ⟨243967982185891996607135663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162645321457261331071423775 243967982185891996607135663)
  ·
    refine ⟨365951973278837994910703495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243967982185891996607135663 365951973278837994910703495)
    ·
      refine ⟨548927959918256992366055243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365951973278837994910703495 548927959918256992366055243)
      ·
        refine ⟨823391939877385488549082865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548927959918256992366055243 823391939877385488549082865)
        ·
          refine ⟨617543954908039116411812149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 823391939877385488549082865 617543954908039116411812149)
          ·
            refine ⟨57894745772628667163607389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 617543954908039116411812149 57894745772628667163607389)
            ·
              refine ⟨21710529664735750186352771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57894745772628667163607389 21710529664735750186352771)
              ·
                refine ⟨32565794497103625279529157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21710529664735750186352771 32565794497103625279529157)
                ·
                  refine ⟨6106086468206929739911717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32565794497103625279529157 6106086468206929739911717)
                  ·
                    refine ⟨1144891212788799326233447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6106086468206929739911717 1144891212788799326233447)
                    ·
                      rfl

theorem cell23_6689003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 4].length) (baseStart_6689003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689003 prefixEnd_6689003 := by exact prefixLift 6689003
  have htrace : WordTrace (prefixWord ++ tailWord_6689003) baseStart_6689003 baseEnd_6689003 := by
    simpa [prefixWord, tailWord_6689003, baseEnd_6689003] using wordTrace_append hprefix tailTrace_6689003
  have hstable : (prefixWord ++ tailWord_6689003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689003).length < 2 ^ (prefixWord ++ tailWord_6689003).sum := by decide
  have hdescent : baseEnd_6689003 < baseStart_6689003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689020 : List Nat := [2, 2, 2, 1, 4, 3, 1, 1, 1, 6]
def baseStart_6689020 : Nat := 118140960795 + 6689020 * 2 ^ 59
def prefixEnd_6689020 : Nat := 4983230072969 + 3 ^ 40 * 6689020 * 2
def baseEnd_6689020 : Nat := 1144894122512508137395921

theorem tailTrace_6689020 : CollatzResearch.WordTrace tailWord_6689020 prefixEnd_6689020 1144894122512508137395921 := by
  unfold tailWord_6689020
  simp only [CollatzResearch.WordTrace]
  refine ⟨121984301113415204255252257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162645734817886939007003009 121984301113415204255252257)
  ·
    refine ⟨91488225835061403191439193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121984301113415204255252257 91488225835061403191439193)
    ·
      refine ⟨68616169376296052393579395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91488225835061403191439193 68616169376296052393579395)
      ·
        refine ⟨102924254064444078590369093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68616169376296052393579395 102924254064444078590369093)
        ·
          refine ⟨19298297637083264735694205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102924254064444078590369093 19298297637083264735694205)
          ·
            refine ⟨7236861613906224275885327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19298297637083264735694205 7236861613906224275885327)
            ·
              refine ⟨10855292420859336413827991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7236861613906224275885327 10855292420859336413827991)
              ·
                refine ⟨16282938631289004620741987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10855292420859336413827991 16282938631289004620741987)
                ·
                  refine ⟨24424407946933506931112981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16282938631289004620741987 24424407946933506931112981)
                  ·
                    refine ⟨1144894122512508137395921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24424407946933506931112981 1144894122512508137395921)
                    ·
                      rfl

theorem cell23_6689020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_6689020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689020 prefixEnd_6689020 := by exact prefixLift 6689020
  have htrace : WordTrace (prefixWord ++ tailWord_6689020) baseStart_6689020 baseEnd_6689020 := by
    simpa [prefixWord, tailWord_6689020, baseEnd_6689020] using wordTrace_append hprefix tailTrace_6689020
  have hstable : (prefixWord ++ tailWord_6689020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689020).length < 2 ^ (prefixWord ++ tailWord_6689020).sum := by decide
  have hdescent : baseEnd_6689020 < baseStart_6689020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689033 : List Nat := [1, 2, 1, 1, 3, 4, 4, 7]
def baseStart_6689033 : Nat := 118140960795 + 6689033 * 2 ^ 59
def prefixEnd_6689033 : Nat := 4983230072969 + 3 ^ 40 * 6689033 * 2
def baseEnd_6689033 : Nat := 127210705288371587456489

theorem tailTrace_6689033 : CollatzResearch.WordTrace tailWord_6689033 prefixEnd_6689033 127210705288371587456489 := by
  unfold tailWord_6689033
  simp only [CollatzResearch.WordTrace]
  refine ⟨243969076375783311730727753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162646050917188874487151835 243969076375783311730727753)
  ·
    refine ⟨182976807281837483798045815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243969076375783311730727753 182976807281837483798045815)
    ·
      refine ⟨274465210922756225697068723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182976807281837483798045815 274465210922756225697068723)
      ·
        refine ⟨411697816384134338545603085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274465210922756225697068723 411697816384134338545603085)
        ·
          refine ⟨154386681144050376954601157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 411697816384134338545603085 154386681144050376954601157)
          ·
            refine ⟨28947502714509445678987717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154386681144050376954601157 28947502714509445678987717)
            ·
              refine ⟨5427656758970521064810197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28947502714509445678987717 5427656758970521064810197)
              ·
                refine ⟨127210705288371587456489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5427656758970521064810197 127210705288371587456489)
                ·
                  rfl

theorem cell23_6689033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 7].length) (baseStart_6689033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689033 prefixEnd_6689033 := by exact prefixLift 6689033
  have htrace : WordTrace (prefixWord ++ tailWord_6689033) baseStart_6689033 baseEnd_6689033 := by
    simpa [prefixWord, tailWord_6689033, baseEnd_6689033] using wordTrace_append hprefix tailTrace_6689033
  have hstable : (prefixWord ++ tailWord_6689033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689033).length < 2 ^ (prefixWord ++ tailWord_6689033).sum := by decide
  have hdescent : baseEnd_6689033 < baseStart_6689033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689043 : List Nat := [1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 3]
def baseStart_6689043 : Nat := 118140960795 + 6689043 * 2 ^ 59
def prefixEnd_6689043 : Nat := 4983230072969 + 3 ^ 40 * 6689043 * 2
def baseEnd_6689043 : Nat := 3434694177592577822200157

theorem tailTrace_6689043 : CollatzResearch.WordTrace tailWord_6689043 prefixEnd_6689043 3434694177592577822200157 := by
  unfold tailWord_6689043
  simp only [CollatzResearch.WordTrace]
  refine ⟨243969441105747083438591783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162646294070498055625727855 243969441105747083438591783)
  ·
    refine ⟨365954161658620625157887675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243969441105747083438591783 365954161658620625157887675)
    ·
      refine ⟨548931242487930937736831513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365954161658620625157887675 548931242487930937736831513)
      ·
        refine ⟨411698431865948203302623635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 548931242487930937736831513 411698431865948203302623635)
        ·
          refine ⟨617547647798922304953935453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411698431865948203302623635 617547647798922304953935453)
          ·
            refine ⟨231580367924595864357725795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 617547647798922304953935453 231580367924595864357725795)
            ·
              refine ⟨347370551886893796536588693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231580367924595864357725795 347370551886893796536588693)
              ·
                refine ⟨16282994619698146712652595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 347370551886893796536588693 16282994619698146712652595)
                ·
                  refine ⟨24424491929547220068978893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16282994619698146712652595 24424491929547220068978893)
                  ·
                    refine ⟨9159184473580207525867085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24424491929547220068978893 9159184473580207525867085)
                    ·
                      refine ⟨3434694177592577822200157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9159184473580207525867085 3434694177592577822200157)
                      ·
                        rfl

theorem cell23_6689043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 3].length) (baseStart_6689043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689043 prefixEnd_6689043 := by exact prefixLift 6689043
  have htrace : WordTrace (prefixWord ++ tailWord_6689043) baseStart_6689043 baseEnd_6689043 := by
    simpa [prefixWord, tailWord_6689043, baseEnd_6689043] using wordTrace_append hprefix tailTrace_6689043
  have hstable : (prefixWord ++ tailWord_6689043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689043).length < 2 ^ (prefixWord ++ tailWord_6689043).sum := by decide
  have hdescent : baseEnd_6689043 < baseStart_6689043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689050 : List Nat := [3, 1, 1, 3, 5, 1, 9]
def baseStart_6689050 : Nat := 118140960795 + 6689050 * 2 ^ 59
def prefixEnd_6689050 : Nat := 4983230072969 + 3 ^ 40 * 6689050 * 2
def baseEnd_6689050 : Nat := 42403676197001966602625

theorem tailTrace_6689050 : CollatzResearch.WordTrace tailWord_6689050 prefixEnd_6689050 42403676197001966602625 := by
  unfold tailWord_6689050
  simp only [CollatzResearch.WordTrace]
  refine ⟨60992424104180430908524151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162646464277814482422731069 60992424104180430908524151)
  ·
    refine ⟨91488636156270646362786227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60992424104180430908524151 91488636156270646362786227)
    ·
      refine ⟨137232954234405969544179341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91488636156270646362786227 137232954234405969544179341)
      ·
        refine ⟨51462357837902238579067253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137232954234405969544179341 51462357837902238579067253)
        ·
          refine ⟨4824596047303334866787555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51462357837902238579067253 4824596047303334866787555)
          ·
            refine ⟨7236894070955002300181333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4824596047303334866787555 7236894070955002300181333)
            ·
              refine ⟨42403676197001966602625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7236894070955002300181333 42403676197001966602625)
              ·
                rfl

theorem cell23_6689050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 9].length) (baseStart_6689050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689050 prefixEnd_6689050 := by exact prefixLift 6689050
  have htrace : WordTrace (prefixWord ++ tailWord_6689050) baseStart_6689050 baseEnd_6689050 := by
    simpa [prefixWord, tailWord_6689050, baseEnd_6689050] using wordTrace_append hprefix tailTrace_6689050
  have hstable : (prefixWord ++ tailWord_6689050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689050).length < 2 ^ (prefixWord ++ tailWord_6689050).sum := by decide
  have hdescent : baseEnd_6689050 < baseStart_6689050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689061 : List Nat := [1, 3, 1, 2, 6, 1, 1, 1, 3, 2, 2]
def baseStart_6689061 : Nat := 118140960795 + 6689061 * 2 ^ 59
def prefixEnd_6689061 : Nat := 4983230072969 + 3 ^ 40 * 6689061 * 2
def baseEnd_6689061 : Nat := 3434703420244358751775075

theorem tailTrace_6689061 : CollatzResearch.WordTrace tailWord_6689061 prefixEnd_6689061 3434703420244358751775075 := by
  unfold tailWord_6689061
  simp only [CollatzResearch.WordTrace]
  refine ⟨243970097619681872512747037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162646731746454581675164691 243970097619681872512747037)
  ·
    refine ⟨91488786607380702192280139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243970097619681872512747037 91488786607380702192280139)
    ·
      refine ⟨137233179911071053288420209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91488786607380702192280139 137233179911071053288420209)
      ·
        refine ⟨102924884933303289966315157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137233179911071053288420209 102924884933303289966315157)
        ·
          refine ⟨4824603981248591717171023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 102924884933303289966315157 4824603981248591717171023)
          ·
            refine ⟨7236905971872887575756535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4824603981248591717171023 7236905971872887575756535)
            ·
              refine ⟨10855358957809331363634803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7236905971872887575756535 10855358957809331363634803)
              ·
                refine ⟨16283038436713997045452205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10855358957809331363634803 16283038436713997045452205)
                ·
                  refine ⟨6106139413767748892044577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16283038436713997045452205 6106139413767748892044577)
                  ·
                    refine ⟨4579604560325811669033433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6106139413767748892044577 4579604560325811669033433)
                    ·
                      refine ⟨3434703420244358751775075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4579604560325811669033433 3434703420244358751775075)
                      ·
                        rfl

theorem cell23_6689061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 3, 2, 2].length) (baseStart_6689061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689061 prefixEnd_6689061 := by exact prefixLift 6689061
  have htrace : WordTrace (prefixWord ++ tailWord_6689061) baseStart_6689061 baseEnd_6689061 := by
    simpa [prefixWord, tailWord_6689061, baseEnd_6689061] using wordTrace_append hprefix tailTrace_6689061
  have hstable : (prefixWord ++ tailWord_6689061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689061).length < 2 ^ (prefixWord ++ tailWord_6689061).sum := by decide
  have hdescent : baseEnd_6689061 < baseStart_6689061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689077 : List Nat := [1, 3, 3, 1, 2, 1, 3, 3, 2, 1, 3]
def baseStart_6689077 : Nat := 118140960795 + 6689077 * 2 ^ 59
def prefixEnd_6689077 : Nat := 4983230072969 + 3 ^ 40 * 6689077 * 2
def baseEnd_6689077 : Nat := 3434711635934830689175001

theorem tailTrace_6689077 : CollatzResearch.WordTrace tailWord_6689077 prefixEnd_6689077 3434711635934830689175001 := by
  unfold tailWord_6689077
  simp only [CollatzResearch.WordTrace]
  refine ⟨243970681187623907245329485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162647120791749271496886323 243970681187623907245329485)
  ·
    refine ⟨91489005445358965216998557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243970681187623907245329485 91489005445358965216998557)
    ·
      refine ⟨34308377042009611956374459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91489005445358965216998557 34308377042009611956374459)
      ·
        refine ⟨51462565563014417934561689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34308377042009611956374459 51462565563014417934561689)
        ·
          refine ⟨38596924172260813450921267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51462565563014417934561689 38596924172260813450921267)
          ·
            refine ⟨57895386258391220176381901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38596924172260813450921267 57895386258391220176381901)
            ·
              refine ⟨21710769846896707566143213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57895386258391220176381901 21710769846896707566143213)
              ·
                refine ⟨8141538692586265337303705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21710769846896707566143213 8141538692586265337303705)
                ·
                  refine ⟨6106154019439699002977779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8141538692586265337303705 6106154019439699002977779)
                  ·
                    refine ⟨9159231029159548504466669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6106154019439699002977779 9159231029159548504466669)
                    ·
                      refine ⟨3434711635934830689175001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9159231029159548504466669 3434711635934830689175001)
                      ·
                        rfl

theorem cell23_6689077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_6689077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689077 prefixEnd_6689077 := by exact prefixLift 6689077
  have htrace : WordTrace (prefixWord ++ tailWord_6689077) baseStart_6689077 baseEnd_6689077 := by
    simpa [prefixWord, tailWord_6689077, baseEnd_6689077] using wordTrace_append hprefix tailTrace_6689077
  have hstable : (prefixWord ++ tailWord_6689077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689077).length < 2 ^ (prefixWord ++ tailWord_6689077).sum := by decide
  have hdescent : baseEnd_6689077 < baseStart_6689077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689104 : List Nat := [2, 1, 1, 1, 1, 7, 3, 1, 1, 3, 2]
def baseStart_6689104 : Nat := 118140960795 + 6689104 * 2 ^ 59
def prefixEnd_6689104 : Nat := 4983230072969 + 3 ^ 40 * 6689104 * 2
def baseEnd_6689104 : Nat := 3434725499912502083537377

theorem tailTrace_6689104 : CollatzResearch.WordTrace tailWord_6689104 prefixEnd_6689104 3434725499912502083537377 := by
  unfold tailWord_6689104
  simp only [CollatzResearch.WordTrace]
  refine ⟨121985832979263045428281183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162647777305684060571041577 121985832979263045428281183)
  ·
    refine ⟨182978749468894568142421775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121985832979263045428281183 182978749468894568142421775)
    ·
      refine ⟨274468124203341852213632663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182978749468894568142421775 274468124203341852213632663)
      ·
        refine ⟨411702186305012778320448995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274468124203341852213632663 411702186305012778320448995)
        ·
          refine ⟨617553279457519167480673493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411702186305012778320448995 617553279457519167480673493)
          ·
            refine ⟨14473904987285605487828285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 617553279457519167480673493 14473904987285605487828285)
            ·
              refine ⟨5427714370232102057935607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14473904987285605487828285 5427714370232102057935607)
              ·
                refine ⟨8141571555348153086903411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5427714370232102057935607 8141571555348153086903411)
                ·
                  refine ⟨12212357333022229630355117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8141571555348153086903411 12212357333022229630355117)
                  ·
                    refine ⟨4579633999883336111383169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12212357333022229630355117 4579633999883336111383169)
                    ·
                      refine ⟨3434725499912502083537377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4579633999883336111383169 3434725499912502083537377)
                      ·
                        rfl

theorem cell23_6689104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 1, 3, 2].length) (baseStart_6689104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689104 prefixEnd_6689104 := by exact prefixLift 6689104
  have htrace : WordTrace (prefixWord ++ tailWord_6689104) baseStart_6689104 baseEnd_6689104 := by
    simpa [prefixWord, tailWord_6689104, baseEnd_6689104] using wordTrace_append hprefix tailTrace_6689104
  have hstable : (prefixWord ++ tailWord_6689104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689104).length < 2 ^ (prefixWord ++ tailWord_6689104).sum := by decide
  have hdescent : baseEnd_6689104 < baseStart_6689104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689113 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 2, 2, 4]
def baseStart_6689113 : Nat := 118140960795 + 6689113 * 2 ^ 59
def prefixEnd_6689113 : Nat := 4983230072969 + 3 ^ 40 * 6689113 * 2
def baseEnd_6689113 : Nat := 3434730121238392548324835

theorem tailTrace_6689113 : CollatzResearch.WordTrace tailWord_6689113 prefixEnd_6689113 3434730121238392548324835 := by
  unfold tailWord_6689113
  simp only [CollatzResearch.WordTrace]
  refine ⟨243971994215493485393639993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162647996143662323595759995 243971994215493485393639993)
  ·
    refine ⟨182978995661620114045229995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243971994215493485393639993 182978995661620114045229995)
    ·
      refine ⟨274468493492430171067844993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182978995661620114045229995 274468493492430171067844993)
      ·
        refine ⟨205851370119322628300883745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274468493492430171067844993 205851370119322628300883745)
        ·
          refine ⟨154388527589491971225662809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205851370119322628300883745 154388527589491971225662809)
          ·
            refine ⟨115791395692118978419247107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154388527589491971225662809 115791395692118978419247107)
            ·
              refine ⟨173687093538178467628870661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115791395692118978419247107 173687093538178467628870661)
              ·
                refine ⟨32566330038408462680413249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173687093538178467628870661 32566330038408462680413249)
                ·
                  refine ⟨24424747528806347010309937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32566330038408462680413249 24424747528806347010309937)
                  ·
                    refine ⟨18318560646604760257732453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24424747528806347010309937 18318560646604760257732453)
                    ·
                      refine ⟨3434730121238392548324835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18318560646604760257732453 3434730121238392548324835)
                      ·
                        rfl

theorem cell23_6689113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_6689113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689113 prefixEnd_6689113 := by exact prefixLift 6689113
  have htrace : WordTrace (prefixWord ++ tailWord_6689113) baseStart_6689113 baseEnd_6689113 := by
    simpa [prefixWord, tailWord_6689113, baseEnd_6689113] using wordTrace_append hprefix tailTrace_6689113
  have hstable : (prefixWord ++ tailWord_6689113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689113).length < 2 ^ (prefixWord ++ tailWord_6689113).sum := by decide
  have hdescent : baseEnd_6689113 < baseStart_6689113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689118 : List Nat := [4, 4, 2, 1, 2, 1, 1, 8]
def baseStart_6689118 : Nat := 118140960795 + 6689118 * 2 ^ 59
def prefixEnd_6689118 : Nat := 4983230072969 + 3 ^ 40 * 6689118 * 2
def baseEnd_6689118 : Nat := 127212321801543149213419

theorem tailTrace_6689118 : CollatzResearch.WordTrace tailWord_6689118 prefixEnd_6689118 127212321801543149213419 := by
  unfold tailWord_6689118
  simp only [CollatzResearch.WordTrace]
  refine ⟨30496522072559421405946501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162648117720316914165048005 30496522072559421405946501)
  ·
    refine ⟨5718097888604891513614969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30496522072559421405946501 5718097888604891513614969)
    ·
      refine ⟨4288573416453668635211227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5718097888604891513614969 4288573416453668635211227)
      ·
        refine ⟨6432860124680502952816841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4288573416453668635211227 6432860124680502952816841)
        ·
          refine ⟨4824645093510377214612631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6432860124680502952816841 4824645093510377214612631)
          ·
            refine ⟨7236967640265565821918947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4824645093510377214612631 7236967640265565821918947)
            ·
              refine ⟨10855451460398348732878421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7236967640265565821918947 10855451460398348732878421)
              ·
                refine ⟨127212321801543149213419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10855451460398348732878421 127212321801543149213419)
                ·
                  rfl

theorem cell23_6689118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 8].length) (baseStart_6689118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689118 prefixEnd_6689118 := by exact prefixLift 6689118
  have htrace : WordTrace (prefixWord ++ tailWord_6689118) baseStart_6689118 baseEnd_6689118 := by
    simpa [prefixWord, tailWord_6689118, baseEnd_6689118] using wordTrace_append hprefix tailTrace_6689118
  have hstable : (prefixWord ++ tailWord_6689118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689118).length < 2 ^ (prefixWord ++ tailWord_6689118).sum := by decide
  have hdescent : baseEnd_6689118 < baseStart_6689118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689123 : List Nat := [1, 1, 1, 5, 2, 1, 2, 3, 7]
def baseStart_6689123 : Nat := 118140960795 + 6689123 * 2 ^ 59
def prefixEnd_6689123 : Nat := 4983230072969 + 3 ^ 40 * 6689123 * 2
def baseEnd_6689123 : Nat := 381637250671659723244421

theorem tailTrace_6689123 : CollatzResearch.WordTrace tailWord_6689123 prefixEnd_6689123 381637250671659723244421 := by
  unfold tailWord_6689123
  simp only [CollatzResearch.WordTrace]
  refine ⟨243972358945457257101504023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162648239296971504734336015 243972358945457257101504023)
  ·
    refine ⟨365958538418185885652256035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243972358945457257101504023 365958538418185885652256035)
    ·
      refine ⟨548937807627278828478384053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365958538418185885652256035 548937807627278828478384053)
      ·
        refine ⟨51462919465057390169848505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 548937807627278828478384053 51462919465057390169848505)
        ·
          refine ⟨38597189598793042627386379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51462919465057390169848505 38597189598793042627386379)
          ·
            refine ⟨57895784398189563941079569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38597189598793042627386379 57895784398189563941079569)
            ·
              refine ⟨43421838298642172955809677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57895784398189563941079569 43421838298642172955809677)
              ·
                refine ⟨16283189361990814858428629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43421838298642172955809677 16283189361990814858428629)
                ·
                  refine ⟨381637250671659723244421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16283189361990814858428629 381637250671659723244421)
                  ·
                    rfl

theorem cell23_6689123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 7].length) (baseStart_6689123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689123 prefixEnd_6689123 := by exact prefixLift 6689123
  have htrace : WordTrace (prefixWord ++ tailWord_6689123) baseStart_6689123 baseEnd_6689123 := by
    simpa [prefixWord, tailWord_6689123, baseEnd_6689123] using wordTrace_append hprefix tailTrace_6689123
  have hstable : (prefixWord ++ tailWord_6689123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689123).length < 2 ^ (prefixWord ++ tailWord_6689123).sum := by decide
  have hdescent : baseEnd_6689123 < baseStart_6689123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689130 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_6689130 : Nat := 118140960795 + 6689130 * 2 ^ 59
def prefixEnd_6689130 : Nat := 4983230072969 + 3 ^ 40 * 6689130 * 2
def baseEnd_6689130 : Nat := 3434738850409518981812257

theorem tailTrace_6689130 : CollatzResearch.WordTrace tailWord_6689130 prefixEnd_6689130 3434738850409518981812257 := by
  unfold tailWord_6689130
  simp only [CollatzResearch.WordTrace]
  refine ⟨60993153564107974324252211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162648409504287931531339229 60993153564107974324252211)
  ·
    refine ⟨91489730346161961486378317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60993153564107974324252211 91489730346161961486378317)
    ·
      refine ⟨34308648879810735557391869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91489730346161961486378317 34308648879810735557391869)
      ·
        refine ⟨12865743329929025834021951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34308648879810735557391869 12865743329929025834021951)
        ·
          refine ⟨19298614994893538751032927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12865743329929025834021951 19298614994893538751032927)
          ·
            refine ⟨28947922492340308126549391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19298614994893538751032927 28947922492340308126549391)
            ·
              refine ⟨43421883738510462189824087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28947922492340308126549391 43421883738510462189824087)
              ·
                refine ⟨65132825607765693284736131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43421883738510462189824087 65132825607765693284736131)
                ·
                  refine ⟨97699238411648539927104197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65132825607765693284736131 97699238411648539927104197)
                  ·
                    refine ⟨18318607202184101236332037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97699238411648539927104197 18318607202184101236332037)
                    ·
                      refine ⟨3434738850409518981812257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18318607202184101236332037 3434738850409518981812257)
                      ·
                        rfl

theorem cell23_6689130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_6689130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689130 prefixEnd_6689130 := by exact prefixLift 6689130
  have htrace : WordTrace (prefixWord ++ tailWord_6689130) baseStart_6689130 baseEnd_6689130 := by
    simpa [prefixWord, tailWord_6689130, baseEnd_6689130] using wordTrace_append hprefix tailTrace_6689130
  have hstable : (prefixWord ++ tailWord_6689130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689130).length < 2 ^ (prefixWord ++ tailWord_6689130).sum := by decide
  have hdescent : baseEnd_6689130 < baseStart_6689130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689210 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3]
def baseStart_6689210 : Nat := 118140960795 + 6689210 * 2 ^ 59
def prefixEnd_6689210 : Nat := 4983230072969 + 3 ^ 40 * 6689210 * 2
def baseEnd_6689210 : Nat := 3434779928861878668811889

theorem tailTrace_6689210 : CollatzResearch.WordTrace tailWord_6689210 prefixEnd_6689210 3434779928861878668811889 := by
  unfold tailWord_6689210
  simp only [CollatzResearch.WordTrace]
  refine ⟨60993883024035517739980271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162650354730761380639947389 60993883024035517739980271)
  ·
    refine ⟨91490824536053276609970407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60993883024035517739980271 91490824536053276609970407)
    ·
      refine ⟨137236236804079914914955611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91490824536053276609970407 137236236804079914914955611)
      ·
        refine ⟨205854355206119872372433417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137236236804079914914955611 205854355206119872372433417)
        ·
          refine ⟨154390766404589904279325063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205854355206119872372433417 154390766404589904279325063)
          ·
            refine ⟨231586149606884856418987595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154390766404589904279325063 231586149606884856418987595)
            ·
              refine ⟨347379224410327284628481393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231586149606884856418987595 347379224410327284628481393)
              ·
                refine ⟨260534418307745463471361045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347379224410327284628481393 260534418307745463471361045)
                ·
                  refine ⟨12212550858175568600220049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 260534418307745463471361045 12212550858175568600220049)
                  ·
                    refine ⟨9159413143631676450165037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12212550858175568600220049 9159413143631676450165037)
                    ·
                      refine ⟨3434779928861878668811889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9159413143631676450165037 3434779928861878668811889)
                      ·
                        rfl

theorem cell23_6689210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3].length) (baseStart_6689210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689210 prefixEnd_6689210 := by exact prefixLift 6689210
  have htrace : WordTrace (prefixWord ++ tailWord_6689210) baseStart_6689210 baseEnd_6689210 := by
    simpa [prefixWord, tailWord_6689210, baseEnd_6689210] using wordTrace_append hprefix tailTrace_6689210
  have hstable : (prefixWord ++ tailWord_6689210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689210).length < 2 ^ (prefixWord ++ tailWord_6689210).sum := by decide
  have hdescent : baseEnd_6689210 < baseStart_6689210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689230 : List Nat := [4, 1, 1, 1, 2, 1, 1, 6, 6]
def baseStart_6689230 : Nat := 118140960795 + 6689230 * 2 ^ 59
def prefixEnd_6689230 : Nat := 4983230072969 + 3 ^ 40 * 6689230 * 2
def baseEnd_6689230 : Nat := 381643355386107621173533

theorem tailTrace_6689230 : CollatzResearch.WordTrace tailWord_6689230 prefixEnd_6689230 381643355386107621173533 := by
  unfold tailWord_6689230
  simp only [CollatzResearch.WordTrace]
  refine ⟨30497032694508701796956143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162650841037379742917099429 30497032694508701796956143)
  ·
    refine ⟨45745549041763052695434215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30497032694508701796956143 45745549041763052695434215)
    ·
      refine ⟨68618323562644579043151323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45745549041763052695434215 68618323562644579043151323)
      ·
        refine ⟨102927485343966868564726985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68618323562644579043151323 102927485343966868564726985)
        ·
          refine ⟨77195614007975151423545239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102927485343966868564726985 77195614007975151423545239)
          ·
            refine ⟨115793421011962727135317859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77195614007975151423545239 115793421011962727135317859)
            ·
              refine ⟨173690131517944090702976789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115793421011962727135317859 173690131517944090702976789)
              ·
                refine ⟨8141724914903629251702037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 173690131517944090702976789 8141724914903629251702037)
                ·
                  refine ⟨381643355386107621173533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8141724914903629251702037 381643355386107621173533)
                  ·
                    rfl

theorem cell23_6689230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_6689230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689230 prefixEnd_6689230 := by exact prefixLift 6689230
  have htrace : WordTrace (prefixWord ++ tailWord_6689230) baseStart_6689230 baseEnd_6689230 := by
    simpa [prefixWord, tailWord_6689230, baseEnd_6689230] using wordTrace_append hprefix tailTrace_6689230
  have hstable : (prefixWord ++ tailWord_6689230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689230).length < 2 ^ (prefixWord ++ tailWord_6689230).sum := by decide
  have hdescent : baseEnd_6689230 < baseStart_6689230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689233 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 8]
def baseStart_6689233 : Nat := 118140960795 + 6689233 * 2 ^ 59
def prefixEnd_6689233 : Nat := 4983230072969 + 3 ^ 40 * 6689233 * 2
def baseEnd_6689233 : Nat := 3434791738916932078824283

theorem tailTrace_6689233 : CollatzResearch.WordTrace tailWord_6689233 prefixEnd_6689233 3434791738916932078824283 := by
  unfold tailWord_6689233
  simp only [CollatzResearch.WordTrace]
  refine ⟨243976370975058745888008353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162650913983372497258672235 243976370975058745888008353)
  ·
    refine ⟨182982278231294059416006265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243976370975058745888008353 182982278231294059416006265)
    ·
      refine ⟨137236708673470544562004699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182982278231294059416006265 137236708673470544562004699)
      ·
        refine ⟨205855063010205816843007049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137236708673470544562004699 205855063010205816843007049)
        ·
          refine ⟨154391297257654362632255287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205855063010205816843007049 154391297257654362632255287)
          ·
            refine ⟨231586945886481543948382931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154391297257654362632255287 231586945886481543948382931)
            ·
              refine ⟨347380418829722315922574397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231586945886481543948382931 347380418829722315922574397)
              ·
                refine ⟨130267657061145868470965399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347380418829722315922574397 130267657061145868470965399)
                ·
                  refine ⟨195401485591718802706448099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130267657061145868470965399 195401485591718802706448099)
                  ·
                    refine ⟨293102228387578204059672149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 195401485591718802706448099 293102228387578204059672149)
                    ·
                      refine ⟨3434791738916932078824283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 293102228387578204059672149 3434791738916932078824283)
                      ·
                        rfl

theorem cell23_6689233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_6689233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689233 prefixEnd_6689233 := by exact prefixLift 6689233
  have htrace : WordTrace (prefixWord ++ tailWord_6689233) baseStart_6689233 baseEnd_6689233 := by
    simpa [prefixWord, tailWord_6689233, baseEnd_6689233] using wordTrace_append hprefix tailTrace_6689233
  have hstable : (prefixWord ++ tailWord_6689233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689233).length < 2 ^ (prefixWord ++ tailWord_6689233).sum := by decide
  have hdescent : baseEnd_6689233 < baseStart_6689233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689247 : List Nat := [1, 1, 2, 3, 3, 2, 4, 1, 6]
def baseStart_6689247 : Nat := 118140960795 + 6689247 * 2 ^ 59
def prefixEnd_6689247 : Nat := 4983230072969 + 3 ^ 40 * 6689247 * 2
def baseEnd_6689247 : Nat := 381644325294010558227691

theorem tailTrace_6689247 : CollatzResearch.WordTrace tailWord_6689247 prefixEnd_6689247 381644325294010558227691 := by
  unfold tailWord_6689247
  simp only [CollatzResearch.WordTrace]
  refine ⟨243976881597008026279017995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162651254398005350852678663 243976881597008026279017995)
  ·
    refine ⟨365965322395512039418526993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243976881597008026279017995 365965322395512039418526993)
    ·
      refine ⟨274473991796634029563895245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365965322395512039418526993 274473991796634029563895245)
      ·
        refine ⟨102927746923737761086460717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274473991796634029563895245 102927746923737761086460717)
        ·
          refine ⟨38597905096401660407422769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102927746923737761086460717 38597905096401660407422769)
          ·
            refine ⟨28948428822301245305567077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38597905096401660407422769 28948428822301245305567077)
            ·
              refine ⟨5427830404181483494793827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28948428822301245305567077 5427830404181483494793827)
              ·
                refine ⟨8141745606272225242190741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5427830404181483494793827 8141745606272225242190741)
                ·
                  refine ⟨381644325294010558227691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8141745606272225242190741 381644325294010558227691)
                  ·
                    rfl

theorem cell23_6689247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 6].length) (baseStart_6689247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689247 prefixEnd_6689247 := by exact prefixLift 6689247
  have htrace : WordTrace (prefixWord ++ tailWord_6689247) baseStart_6689247 baseEnd_6689247 := by
    simpa [prefixWord, tailWord_6689247, baseEnd_6689247] using wordTrace_append hprefix tailTrace_6689247
  have hstable : (prefixWord ++ tailWord_6689247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689247).length < 2 ^ (prefixWord ++ tailWord_6689247).sum := by decide
  have hdescent : baseEnd_6689247 < baseStart_6689247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689260 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 3, 5]
def baseStart_6689260 : Nat := 118140960795 + 6689260 * 2 ^ 59
def prefixEnd_6689260 : Nat := 4983230072969 + 3 ^ 40 * 6689260 * 2
def baseEnd_6689260 : Nat := 1144935200964867824395553

theorem tailTrace_6689260 : CollatzResearch.WordTrace tailWord_6689260 prefixEnd_6689260 1144935200964867824395553 := by
  unfold tailWord_6689260
  simp only [CollatzResearch.WordTrace]
  refine ⟨121988677872980464749620617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162651570497307286332827489 121988677872980464749620617)
  ·
    refine ⟨91491508404735348562215463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121988677872980464749620617 91491508404735348562215463)
    ·
      refine ⟨137237262607103022843323195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91491508404735348562215463 137237262607103022843323195)
      ·
        refine ⟨205855893910654534264984793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137237262607103022843323195 205855893910654534264984793)
        ·
          refine ⟨154391920432990900698738595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205855893910654534264984793 154391920432990900698738595)
          ·
            refine ⟨231587880649486351048107893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154391920432990900698738595 231587880649486351048107893)
            ·
              refine ⟨21711363810889345410760115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 231587880649486351048107893 21711363810889345410760115)
              ·
                refine ⟨32567045716334018116140173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21711363810889345410760115 32567045716334018116140173)
                ·
                  refine ⟨12212642143625256793552565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32567045716334018116140173 12212642143625256793552565)
                  ·
                    refine ⟨1144935200964867824395553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12212642143625256793552565 1144935200964867824395553)
                    ·
                      rfl

theorem cell23_6689260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_6689260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689260 prefixEnd_6689260 := by exact prefixLift 6689260
  have htrace : WordTrace (prefixWord ++ tailWord_6689260) baseStart_6689260 baseEnd_6689260 := by
    simpa [prefixWord, tailWord_6689260, baseEnd_6689260] using wordTrace_append hprefix tailTrace_6689260
  have hstable : (prefixWord ++ tailWord_6689260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689260).length < 2 ^ (prefixWord ++ tailWord_6689260).sum := by decide
  have hdescent : baseEnd_6689260 < baseStart_6689260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689290 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 3, 6]
def baseStart_6689290 : Nat := 118140960795 + 6689290 * 2 ^ 59
def prefixEnd_6689290 : Nat := 4983230072969 + 3 ^ 40 * 6689290 * 2
def baseEnd_6689290 : Nat := 1144940335771412785270507

theorem tailTrace_6689290 : CollatzResearch.WordTrace tailWord_6689290 prefixEnd_6689290 1144940335771412785270507 := by
  unfold tailWord_6689290
  simp only [CollatzResearch.WordTrace]
  refine ⟨60994612483963061155708331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162652299957234829748555549 60994612483963061155708331)
  ·
    refine ⟨91491918725944591733562497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60994612483963061155708331 91491918725944591733562497)
    ·
      refine ⟨68618939044458443800171873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91491918725944591733562497 68618939044458443800171873)
      ·
        refine ⟨51464204283343832850128905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68618939044458443800171873 51464204283343832850128905)
        ·
          refine ⟨38598153212507874637596679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51464204283343832850128905 38598153212507874637596679)
          ·
            refine ⟨57897229818761811956395019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38598153212507874637596679 57897229818761811956395019)
            ·
              refine ⟨86845844728142717934592529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57897229818761811956395019 86845844728142717934592529)
              ·
                refine ⟨65134383546107038450944397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86845844728142717934592529 65134383546107038450944397)
                ·
                  refine ⟨24425393829790139419104149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65134383546107038450944397 24425393829790139419104149)
                  ·
                    refine ⟨1144940335771412785270507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24425393829790139419104149 1144940335771412785270507)
                    ·
                      rfl

theorem cell23_6689290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_6689290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689290 prefixEnd_6689290 := by exact prefixLift 6689290
  have htrace : WordTrace (prefixWord ++ tailWord_6689290) baseStart_6689290 baseEnd_6689290 := by
    simpa [prefixWord, tailWord_6689290, baseEnd_6689290] using wordTrace_append hprefix tailTrace_6689290
  have hstable : (prefixWord ++ tailWord_6689290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689290).length < 2 ^ (prefixWord ++ tailWord_6689290).sum := by decide
  have hdescent : baseEnd_6689290 < baseStart_6689290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689291 : List Nat := [1, 1, 1, 1, 7, 2, 1, 4, 1, 1, 3]
def baseStart_6689291 : Nat := 118140960795 + 6689291 * 2 ^ 59
def prefixEnd_6689291 : Nat := 4983230072969 + 3 ^ 40 * 6689291 * 2
def baseEnd_6689291 : Nat := 3434821520794892851899017

theorem tailTrace_6689291 : CollatzResearch.WordTrace tailWord_6689291 prefixEnd_6689291 3434821520794892851899017 := by
  unfold tailWord_6689291
  simp only [CollatzResearch.WordTrace]
  refine ⟨243978486408848621793619727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162652324272565747862413151 243978486408848621793619727)
  ·
    refine ⟨365967729613272932690429591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243978486408848621793619727 365967729613272932690429591)
    ·
      refine ⟨548951594419909399035644387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365967729613272932690429591 548951594419909399035644387)
      ·
        refine ⟨823427391629864098553466581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548951594419909399035644387 823427391629864098553466581)
        ·
          refine ⟨19299079491324939809846873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 823427391629864098553466581 19299079491324939809846873)
          ·
            refine ⟨14474309618493704857385155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19299079491324939809846873 14474309618493704857385155)
            ·
              refine ⟨21711464427740557286077733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14474309618493704857385155 21711464427740557286077733)
              ·
                refine ⟨4070899580201354491139575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21711464427740557286077733 4070899580201354491139575)
                ·
                  refine ⟨6106349370302031736709363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4070899580201354491139575 6106349370302031736709363)
                  ·
                    refine ⟨9159524055453047605064045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6106349370302031736709363 9159524055453047605064045)
                    ·
                      refine ⟨3434821520794892851899017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9159524055453047605064045 3434821520794892851899017)
                      ·
                        rfl

theorem cell23_6689291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 1, 1, 3].length) (baseStart_6689291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689291 prefixEnd_6689291 := by exact prefixLift 6689291
  have htrace : WordTrace (prefixWord ++ tailWord_6689291) baseStart_6689291 baseEnd_6689291 := by
    simpa [prefixWord, tailWord_6689291, baseEnd_6689291] using wordTrace_append hprefix tailTrace_6689291
  have hstable : (prefixWord ++ tailWord_6689291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689291).length < 2 ^ (prefixWord ++ tailWord_6689291).sum := by decide
  have hdescent : baseEnd_6689291 < baseStart_6689291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689317 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 3, 2, 3]
def baseStart_6689317 : Nat := 118140960795 + 6689317 * 2 ^ 59
def prefixEnd_6689317 : Nat := 4983230072969 + 3 ^ 40 * 6689317 * 2
def baseEnd_6689317 : Nat := 3434834871291909750173897

theorem tailTrace_6689317 : CollatzResearch.WordTrace tailWord_6689317 prefixEnd_6689317 3434834871291909750173897 := by
  unfold tailWord_6689317
  simp only [CollatzResearch.WordTrace]
  refine ⟨243979434706754428234066205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162652956471169618822710803 243979434706754428234066205)
  ·
    refine ⟨91492288015032910587774827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243979434706754428234066205 91492288015032910587774827)
    ·
      refine ⟨137238432022549365881662241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91492288015032910587774827 137238432022549365881662241)
      ·
        refine ⟨102928824016912024411246681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137238432022549365881662241 102928824016912024411246681)
        ·
          refine ⟨77196618012684018308435011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102928824016912024411246681 77196618012684018308435011)
          ·
            refine ⟨115794927019026027462652517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77196618012684018308435011 115794927019026027462652517)
            ·
              refine ⟨21711548816067380149247347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115794927019026027462652517 21711548816067380149247347)
              ·
                refine ⟨32567323224101070223871021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21711548816067380149247347 32567323224101070223871021)
                ·
                  refine ⟨12212746209037901333951633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32567323224101070223871021 12212746209037901333951633)
                  ·
                    refine ⟨9159559656778426000463725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12212746209037901333951633 9159559656778426000463725)
                    ·
                      refine ⟨3434834871291909750173897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9159559656778426000463725 3434834871291909750173897)
                      ·
                        rfl

theorem cell23_6689317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_6689317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689317 prefixEnd_6689317 := by exact prefixLift 6689317
  have htrace : WordTrace (prefixWord ++ tailWord_6689317) baseStart_6689317 baseEnd_6689317 := by
    simpa [prefixWord, tailWord_6689317, baseEnd_6689317] using wordTrace_append hprefix tailTrace_6689317
  have hstable : (prefixWord ++ tailWord_6689317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689317).length < 2 ^ (prefixWord ++ tailWord_6689317).sum := by decide
  have hdescent : baseEnd_6689317 < baseStart_6689317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689341 : List Nat := [1, 4, 1, 3, 2, 3, 1, 2, 2, 4]
def baseStart_6689341 : Nat := 118140960795 + 6689341 * 2 ^ 59
def prefixEnd_6689341 : Nat := 4983230072969 + 3 ^ 40 * 6689341 * 2
def baseEnd_6689341 : Nat := 1144949064942539218757929

theorem tailTrace_6689341 : CollatzResearch.WordTrace tailWord_6689341 prefixEnd_6689341 1144949064942539218757929 := by
  unfold tailWord_6689341
  simp only [CollatzResearch.WordTrace]
  refine ⟨243980310058667480332939877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162653540039111653555293251 243980310058667480332939877)
  ·
    refine ⟨45746308136000152562426227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243980310058667480332939877 45746308136000152562426227)
    ·
      refine ⟨68619462204000228843639341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45746308136000152562426227 68619462204000228843639341)
      ·
        refine ⟨25732298326500085816364753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68619462204000228843639341 25732298326500085816364753)
        ·
          refine ⟨19299223744875064362273565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25732298326500085816364753 19299223744875064362273565)
          ·
            refine ⟨7237208904328149135852587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19299223744875064362273565 7237208904328149135852587)
            ·
              refine ⟨10855813356492223703778881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7237208904328149135852587 10855813356492223703778881)
              ·
                refine ⟨8141860017369167777834161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10855813356492223703778881 8141860017369167777834161)
                ·
                  refine ⟨6106395013026875833375621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8141860017369167777834161 6106395013026875833375621)
                  ·
                    refine ⟨1144949064942539218757929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6106395013026875833375621 1144949064942539218757929)
                    ·
                      rfl

theorem cell23_6689341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_6689341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689341 prefixEnd_6689341 := by exact prefixLift 6689341
  have htrace : WordTrace (prefixWord ++ tailWord_6689341) baseStart_6689341 baseEnd_6689341 := by
    simpa [prefixWord, tailWord_6689341, baseEnd_6689341] using wordTrace_append hprefix tailTrace_6689341
  have hstable : (prefixWord ++ tailWord_6689341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689341).length < 2 ^ (prefixWord ++ tailWord_6689341).sum := by decide
  have hdescent : baseEnd_6689341 < baseStart_6689341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689364 : List Nat := [2, 4, 1, 1, 1, 3, 3, 1, 1, 3, 3]
def baseStart_6689364 : Nat := 118140960795 + 6689364 * 2 ^ 59
def prefixEnd_6689364 : Nat := 4983230072969 + 3 ^ 40 * 6689364 * 2
def baseEnd_6689364 : Nat := 3434859004882671066286181

theorem tailTrace_6689364 : CollatzResearch.WordTrace tailWord_6689364 prefixEnd_6689364 3434859004882671066286181 := by
  unfold tailWord_6689364
  simp only [CollatzResearch.WordTrace]
  refine ⟨121990574468792077630513573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162654099291722770174018097 121990574468792077630513573)
  ·
    refine ⟨22873232712898514555721295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121990574468792077630513573 22873232712898514555721295)
    ·
      refine ⟨34309849069347771833581943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22873232712898514555721295 34309849069347771833581943)
      ·
        refine ⟨51464773604021657750372915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34309849069347771833581943 51464773604021657750372915)
        ·
          refine ⟨77197160406032486625559373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51464773604021657750372915 77197160406032486625559373)
          ·
            refine ⟨28948935152262182484584765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77197160406032486625559373 28948935152262182484584765)
            ·
              refine ⟨10855850682098318431719287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28948935152262182484584765 10855850682098318431719287)
              ·
                refine ⟨16283776023147477647578931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10855850682098318431719287 16283776023147477647578931)
                ·
                  refine ⟨24425664034721216471368397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16283776023147477647578931 24425664034721216471368397)
                  ·
                    refine ⟨9159624013020456176763149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24425664034721216471368397 9159624013020456176763149)
                    ·
                      refine ⟨3434859004882671066286181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9159624013020456176763149 3434859004882671066286181)
                      ·
                        rfl

theorem cell23_6689364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_6689364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689364 prefixEnd_6689364 := by exact prefixLift 6689364
  have htrace : WordTrace (prefixWord ++ tailWord_6689364) baseStart_6689364 baseEnd_6689364 := by
    simpa [prefixWord, tailWord_6689364, baseEnd_6689364] using wordTrace_append hprefix tailTrace_6689364
  have hstable : (prefixWord ++ tailWord_6689364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689364).length < 2 ^ (prefixWord ++ tailWord_6689364).sum := by decide
  have hdescent : baseEnd_6689364 < baseStart_6689364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689444 : List Nat := [2, 3, 1, 2, 2, 1, 2, 5, 5]
def baseStart_6689444 : Nat := 118140960795 + 6689444 * 2 ^ 59
def prefixEnd_6689444 : Nat := 4983230072969 + 3 ^ 40 * 6689444 * 2
def baseEnd_6689444 : Nat := 381655564815003417031757

theorem tailTrace_6689444 : CollatzResearch.WordTrace tailWord_6689444 prefixEnd_6689444 381655564815003417031757 := by
  unfold tailWord_6689444
  simp only [CollatzResearch.WordTrace]
  refine ⟨121992033388647164461969693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162656044518196219282626257 121992033388647164461969693)
  ·
    refine ⟨45747012520742686673238635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121992033388647164461969693 45747012520742686673238635)
    ·
      refine ⟨68620518781114030009857953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45747012520742686673238635 68620518781114030009857953)
      ·
        refine ⟨51465389085835522507393465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68620518781114030009857953 51465389085835522507393465)
        ·
          refine ⟨38599041814376641880545099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51465389085835522507393465 38599041814376641880545099)
          ·
            refine ⟨57898562721564962820817649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38599041814376641880545099 57898562721564962820817649)
            ·
              refine ⟨43423922041173722115613237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57898562721564962820817649 43423922041173722115613237)
              ·
                refine ⟨4070992691360036448338741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43423922041173722115613237 4070992691360036448338741)
                ·
                  refine ⟨381655564815003417031757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4070992691360036448338741 381655564815003417031757)
                  ·
                    rfl

theorem cell23_6689444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_6689444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689444 prefixEnd_6689444 := by exact prefixLift 6689444
  have htrace : WordTrace (prefixWord ++ tailWord_6689444) baseStart_6689444 baseEnd_6689444 := by
    simpa [prefixWord, tailWord_6689444, baseEnd_6689444] using wordTrace_append hprefix tailTrace_6689444
  have hstable : (prefixWord ++ tailWord_6689444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689444).length < 2 ^ (prefixWord ++ tailWord_6689444).sum := by decide
  have hdescent : baseEnd_6689444 < baseStart_6689444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689461 : List Nat := [1, 3, 3, 3, 1, 2, 1, 4, 5]
def baseStart_6689461 : Nat := 118140960795 + 6689461 * 2 ^ 59
def prefixEnd_6689461 : Nat := 4983230072969 + 3 ^ 40 * 6689461 * 2
def baseEnd_6689461 : Nat := 381656534722906354085915

theorem tailTrace_6689461 : CollatzResearch.WordTrace tailWord_6689461 prefixEnd_6689461 381656534722906354085915 := by
  unfold tailWord_6689461
  simp only [CollatzResearch.WordTrace]
  refine ⟨243984686818232740827308237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162656457878821827218205491 243984686818232740827308237)
  ·
    refine ⟨91494257556837277810240589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243984686818232740827308237 91494257556837277810240589)
    ·
      refine ⟨34310346583813979178840221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91494257556837277810240589 34310346583813979178840221)
      ·
        refine ⟨12866379968930242192065083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34310346583813979178840221 12866379968930242192065083)
        ·
          refine ⟨19299569953395363288097625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12866379968930242192065083 19299569953395363288097625)
          ·
            refine ⟨14474677465046522466073219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19299569953395363288097625 14474677465046522466073219)
            ·
              refine ⟨21712016197569783699109829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14474677465046522466073219 21712016197569783699109829)
              ·
                refine ⟨4071003037044334443583093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21712016197569783699109829 4071003037044334443583093)
                ·
                  refine ⟨381656534722906354085915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4071003037044334443583093 381656534722906354085915)
                  ·
                    rfl

theorem cell23_6689461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 5].length) (baseStart_6689461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689461 prefixEnd_6689461 := by exact prefixLift 6689461
  have htrace : WordTrace (prefixWord ++ tailWord_6689461) baseStart_6689461 baseEnd_6689461 := by
    simpa [prefixWord, tailWord_6689461, baseEnd_6689461] using wordTrace_append hprefix tailTrace_6689461
  have hstable : (prefixWord ++ tailWord_6689461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689461).length < 2 ^ (prefixWord ++ tailWord_6689461).sum := by decide
  have hdescent : baseEnd_6689461 < baseStart_6689461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689478 : List Nat := [6, 1, 2, 1, 2, 1, 1, 2, 7]
def baseStart_6689478 : Nat := 118140960795 + 6689478 * 2 ^ 59
def prefixEnd_6689478 : Nat := 4983230072969 + 3 ^ 40 * 6689478 * 2
def baseEnd_6689478 : Nat := 381657504630809291140073

theorem tailTrace_6689478 : CollatzResearch.WordTrace tailWord_6689478 prefixEnd_6689478 381657504630809291140073 := by
  unfold tailWord_6689478
  simp only [CollatzResearch.WordTrace]
  refine ⟨7624540839349098522833659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 162656871239447435153784725 7624540839349098522833659)
  ·
    refine ⟨11436811259023647784250489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7624540839349098522833659 11436811259023647784250489)
    ·
      refine ⟨8577608444267735838187867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11436811259023647784250489 8577608444267735838187867)
      ·
        refine ⟨12866412666401603757281801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8577608444267735838187867 12866412666401603757281801)
        ·
          refine ⟨9649809499801202817961351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12866412666401603757281801 9649809499801202817961351)
          ·
            refine ⟨14474714249701804226942027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9649809499801202817961351 14474714249701804226942027)
            ·
              refine ⟨21712071374552706340413041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14474714249701804226942027 21712071374552706340413041)
              ·
                refine ⟨16284053530914529755309781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21712071374552706340413041 16284053530914529755309781)
                ·
                  refine ⟨381657504630809291140073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16284053530914529755309781 381657504630809291140073)
                  ·
                    rfl

theorem cell23_6689478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_6689478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689478 prefixEnd_6689478 := by exact prefixLift 6689478
  have htrace : WordTrace (prefixWord ++ tailWord_6689478) baseStart_6689478 baseEnd_6689478 := by
    simpa [prefixWord, tailWord_6689478, baseEnd_6689478] using wordTrace_append hprefix tailTrace_6689478
  have hstable : (prefixWord ++ tailWord_6689478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689478).length < 2 ^ (prefixWord ++ tailWord_6689478).sum := by decide
  have hdescent : baseEnd_6689478 < baseStart_6689478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689514 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 4, 2, 3]
def baseStart_6689514 : Nat := 118140960795 + 6689514 * 2 ^ 59
def prefixEnd_6689514 : Nat := 4983230072969 + 3 ^ 40 * 6689514 * 2
def baseEnd_6689514 : Nat := 3434936026980845479410491

theorem tailTrace_6689514 : CollatzResearch.WordTrace tailWord_6689514 prefixEnd_6689514 3434936026980845479410491 := by
  unfold tailWord_6689514
  simp only [CollatzResearch.WordTrace]
  refine ⟨60996654971760182719746899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162657746591360487252658397 60996654971760182719746899)
  ·
    refine ⟨91494982457640274079620349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60996654971760182719746899 91494982457640274079620349)
    ·
      refine ⟨34310618421615102779857631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91494982457640274079620349 34310618421615102779857631)
      ·
        refine ⟨51465927632422654169786447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34310618421615102779857631 51465927632422654169786447)
        ·
          refine ⟨77198891448633981254679671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51465927632422654169786447 77198891448633981254679671)
          ·
            refine ⟨115798337172950971882019507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77198891448633981254679671 115798337172950971882019507)
            ·
              refine ⟨173697505759426457823029261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115798337172950971882019507 173697505759426457823029261)
              ·
                refine ⟨65136564659784921683635973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173697505759426457823029261 65136564659784921683635973)
                ·
                  refine ⟨12213105873709672815681745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65136564659784921683635973 12213105873709672815681745)
                  ·
                    refine ⟨9159829405282254611761309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12213105873709672815681745 9159829405282254611761309)
                    ·
                      refine ⟨3434936026980845479410491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9159829405282254611761309 3434936026980845479410491)
                      ·
                        rfl

theorem cell23_6689514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_6689514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689514 prefixEnd_6689514 := by exact prefixLift 6689514
  have htrace : WordTrace (prefixWord ++ tailWord_6689514) baseStart_6689514 baseEnd_6689514 := by
    simpa [prefixWord, tailWord_6689514, baseEnd_6689514] using wordTrace_append hprefix tailTrace_6689514
  have hstable : (prefixWord ++ tailWord_6689514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689514).length < 2 ^ (prefixWord ++ tailWord_6689514).sum := by decide
  have hdescent : baseEnd_6689514 < baseStart_6689514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689521 : List Nat := [1, 2, 2, 2, 2, 2, 1, 6, 1, 4]
def baseStart_6689521 : Nat := 118140960795 + 6689521 * 2 ^ 59
def prefixEnd_6689521 : Nat := 4983230072969 + 3 ^ 40 * 6689521 * 2
def baseEnd_6689521 : Nat := 1144979873781808984007653

theorem tailTrace_6689521 : CollatzResearch.WordTrace tailWord_6689521 prefixEnd_6689521 1144979873781808984007653 := by
  unfold tailWord_6689521
  simp only [CollatzResearch.WordTrace]
  refine ⟨243986875198015371074492417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162657916798676914049661611 243986875198015371074492417)
  ·
    refine ⟨182990156398511528305869313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243986875198015371074492417 182990156398511528305869313)
    ·
      refine ⟨137242617298883646229401985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182990156398511528305869313 137242617298883646229401985)
      ·
        refine ⟨102931962974162734672051489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137242617298883646229401985 102931962974162734672051489)
        ·
          refine ⟨77198972230622051004038617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102931962974162734672051489 77198972230622051004038617)
          ·
            refine ⟨57899229172966538253028963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77198972230622051004038617 57899229172966538253028963)
            ·
              refine ⟨86848843759449807379543445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57899229172966538253028963 86848843759449807379543445)
              ·
                refine ⟨4071039551224209720916099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86848843759449807379543445 4071039551224209720916099)
                ·
                  refine ⟨6106559326836314581374149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4071039551224209720916099 6106559326836314581374149)
                  ·
                    refine ⟨1144979873781808984007653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6106559326836314581374149 1144979873781808984007653)
                    ·
                      rfl

theorem cell23_6689521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 1, 4].length) (baseStart_6689521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689521 prefixEnd_6689521 := by exact prefixLift 6689521
  have htrace : WordTrace (prefixWord ++ tailWord_6689521) baseStart_6689521 baseEnd_6689521 := by
    simpa [prefixWord, tailWord_6689521, baseEnd_6689521] using wordTrace_append hprefix tailTrace_6689521
  have hstable : (prefixWord ++ tailWord_6689521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689521).length < 2 ^ (prefixWord ++ tailWord_6689521).sum := by decide
  have hdescent : baseEnd_6689521 < baseStart_6689521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689537 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_6689537 : Nat := 118140960795 + 6689537 * 2 ^ 59
def prefixEnd_6689537 : Nat := 4983230072969 + 3 ^ 40 * 6689537 * 2
def baseEnd_6689537 : Nat := 3434947837035898889422885

theorem tailTrace_6689537 : CollatzResearch.WordTrace tailWord_6689537 prefixEnd_6689537 3434947837035898889422885 := by
  unfold tailWord_6689537
  simp only [CollatzResearch.WordTrace]
  refine ⟨243987458765957405807074865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162658305843971603871383243 243987458765957405807074865)
  ·
    refine ⟨182990594074468054355306149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243987458765957405807074865 182990594074468054355306149)
    ·
      refine ⟨34310736388962760191619903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182990594074468054355306149 34310736388962760191619903)
      ·
        refine ⟨51466104583444140287429855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34310736388962760191619903 51466104583444140287429855)
        ·
          refine ⟨77199156875166210431144783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51466104583444140287429855 77199156875166210431144783)
          ·
            refine ⟨115798735312749315646717175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77199156875166210431144783 115798735312749315646717175)
            ·
              refine ⟨173698102969123973470075763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115798735312749315646717175 173698102969123973470075763)
              ·
                refine ⟨260547154453685960205113645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173698102969123973470075763 260547154453685960205113645)
                ·
                  refine ⟨97705182920132235076917617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260547154453685960205113645 97705182920132235076917617)
                  ·
                    refine ⟨73278887190099176307688213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97705182920132235076917617 73278887190099176307688213)
                    ·
                      refine ⟨3434947837035898889422885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73278887190099176307688213 3434947837035898889422885)
                      ·
                        rfl

theorem cell23_6689537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_6689537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689537 prefixEnd_6689537 := by exact prefixLift 6689537
  have htrace : WordTrace (prefixWord ++ tailWord_6689537) baseStart_6689537 baseEnd_6689537 := by
    simpa [prefixWord, tailWord_6689537, baseEnd_6689537] using wordTrace_append hprefix tailTrace_6689537
  have hstable : (prefixWord ++ tailWord_6689537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689537).length < 2 ^ (prefixWord ++ tailWord_6689537).sum := by decide
  have hdescent : baseEnd_6689537 < baseStart_6689537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689577 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 3, 6]
def baseStart_6689577 : Nat := 118140960795 + 6689577 * 2 ^ 59
def prefixEnd_6689577 : Nat := 4983230072969 + 3 ^ 40 * 6689577 * 2
def baseEnd_6689577 : Nat := 1144989458754026244307567

theorem tailTrace_6689577 : CollatzResearch.WordTrace tailWord_6689577 prefixEnd_6689577 1144989458754026244307567 := by
  unfold tailWord_6689577
  simp only [CollatzResearch.WordTrace]
  refine ⟨243988917685812492638530985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162659278457208328425687323 243988917685812492638530985)
  ·
    refine ⟨182991688264359369478898239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243988917685812492638530985 182991688264359369478898239)
    ·
      refine ⟨274487532396539054218347359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182991688264359369478898239 274487532396539054218347359)
      ·
        refine ⟨411731298594808581327521039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274487532396539054218347359 411731298594808581327521039)
        ·
          refine ⟨617596947892212871991281559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411731298594808581327521039 617596947892212871991281559)
          ·
            refine ⟨926395421838319307986922339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617596947892212871991281559 926395421838319307986922339)
            ·
              refine ⟨1389593132757478961980383509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926395421838319307986922339 1389593132757478961980383509)
              ·
                refine ⟨65137178098006826342830477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1389593132757478961980383509 65137178098006826342830477)
                ·
                  refine ⟨24426441786752559878561429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65137178098006826342830477 24426441786752559878561429)
                  ·
                    refine ⟨1144989458754026244307567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24426441786752559878561429 1144989458754026244307567)
                    ·
                      rfl

theorem cell23_6689577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 6].length) (baseStart_6689577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689577 prefixEnd_6689577 := by exact prefixLift 6689577
  have htrace : WordTrace (prefixWord ++ tailWord_6689577) baseStart_6689577 baseEnd_6689577 := by
    simpa [prefixWord, tailWord_6689577, baseEnd_6689577] using wordTrace_append hprefix tailTrace_6689577
  have hstable : (prefixWord ++ tailWord_6689577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689577).length < 2 ^ (prefixWord ++ tailWord_6689577).sum := by decide
  have hdescent : baseEnd_6689577 < baseStart_6689577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689618 : List Nat := [3, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4]
def baseStart_6689618 : Nat := 118140960795 + 6689618 * 2 ^ 59
def prefixEnd_6689618 : Nat := 4983230072969 + 3 ^ 40 * 6689618 * 2
def baseEnd_6689618 : Nat := 3434989428968913072510013

theorem tailTrace_6689618 : CollatzResearch.WordTrace tailWord_6689618 prefixEnd_6689618 3434989428968913072510013 := by
  unfold tailWord_6689618
  simp only [CollatzResearch.WordTrace]
  refine ⟨60997603269665989160193377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162660275385775971093849005 60997603269665989160193377)
  ·
    refine ⟨45748202452249491870145033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60997603269665989160193377 45748202452249491870145033)
    ·
      refine ⟨34311151839187118902608775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45748202452249491870145033 34311151839187118902608775)
      ·
        refine ⟨51466727758780678353913163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34311151839187118902608775 51466727758780678353913163)
        ·
          refine ⟨77200091638171017530869745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51466727758780678353913163 77200091638171017530869745)
          ·
            refine ⟨57900068728628263148152309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77200091638171017530869745 57900068728628263148152309)
            ·
              refine ⟨5428131443308899670139279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57900068728628263148152309 5428131443308899670139279)
              ·
                refine ⟨8142197164963349505208919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5428131443308899670139279 8142197164963349505208919)
                ·
                  refine ⟨12213295747445024257813379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8142197164963349505208919 12213295747445024257813379)
                  ·
                    refine ⟨18319943621167536386720069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12213295747445024257813379 18319943621167536386720069)
                    ·
                      refine ⟨3434989428968913072510013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18319943621167536386720069 3434989428968913072510013)
                      ·
                        rfl

theorem cell23_6689618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_6689618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689618 prefixEnd_6689618 := by exact prefixLift 6689618
  have htrace : WordTrace (prefixWord ++ tailWord_6689618) baseStart_6689618 baseEnd_6689618 := by
    simpa [prefixWord, tailWord_6689618, baseEnd_6689618] using wordTrace_append hprefix tailTrace_6689618
  have hstable : (prefixWord ++ tailWord_6689618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689618).length < 2 ^ (prefixWord ++ tailWord_6689618).sum := by decide
  have hdescent : baseEnd_6689618 < baseStart_6689618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689627 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 6]
def baseStart_6689627 : Nat := 118140960795 + 6689627 * 2 ^ 59
def prefixEnd_6689627 : Nat := 4983230072969 + 3 ^ 40 * 6689627 * 2
def baseEnd_6689627 : Nat := 3434994050294803537297471

theorem tailTrace_6689627 : CollatzResearch.WordTrace tailWord_6689627 prefixEnd_6689627 3434994050294803537297471 := by
  unfold tailWord_6689627
  simp only [CollatzResearch.WordTrace]
  refine ⟨243990741335631351177851135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162660494223754234118567423 243990741335631351177851135)
  ·
    refine ⟨365986112003447026766776703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243990741335631351177851135 365986112003447026766776703)
    ·
      refine ⟨548979168005170540150165055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365986112003447026766776703 548979168005170540150165055)
      ·
        refine ⟨823468752007755810225247583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548979168005170540150165055 823468752007755810225247583)
        ·
          refine ⟨1235203128011633715337871375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 823468752007755810225247583 1235203128011633715337871375)
          ·
            refine ⟨1852804692017450573006807063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1235203128011633715337871375 1852804692017450573006807063)
            ·
              refine ⟨2779207038026175859510210595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1852804692017450573006807063 2779207038026175859510210595)
              ·
                refine ⟨4168810557039263789265315893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2779207038026175859510210595 4168810557039263789265315893)
                ·
                  refine ⟨390825989722430980243623365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4168810557039263789265315893 390825989722430980243623365)
                  ·
                    refine ⟨73279873072955808795679381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 390825989722430980243623365 73279873072955808795679381)
                    ·
                      refine ⟨3434994050294803537297471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73279873072955808795679381 3434994050294803537297471)
                      ·
                        rfl

theorem cell23_6689627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 6].length) (baseStart_6689627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689627 prefixEnd_6689627 := by exact prefixLift 6689627
  have htrace : WordTrace (prefixWord ++ tailWord_6689627) baseStart_6689627 baseEnd_6689627 := by
    simpa [prefixWord, tailWord_6689627, baseEnd_6689627] using wordTrace_append hprefix tailTrace_6689627
  have hstable : (prefixWord ++ tailWord_6689627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689627).length < 2 ^ (prefixWord ++ tailWord_6689627).sum := by decide
  have hdescent : baseEnd_6689627 < baseStart_6689627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689628 : List Nat := [2, 2, 4, 2, 1, 1, 1, 4, 2, 4]
def baseStart_6689628 : Nat := 118140960795 + 6689628 * 2 ^ 59
def prefixEnd_6689628 : Nat := 4983230072969 + 3 ^ 40 * 6689628 * 2
def baseEnd_6689628 : Nat := 1144998187925152677794989

theorem tailTrace_6689628 : CollatzResearch.WordTrace tailWord_6689628 prefixEnd_6689628 1144998187925152677794989 := by
  unfold tailWord_6689628
  simp only [CollatzResearch.WordTrace]
  refine ⟨121995388904313864174318769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162660518539085152232425025 121995388904313864174318769)
  ·
    refine ⟨91496541678235398130739077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121995388904313864174318769 91496541678235398130739077)
    ·
      refine ⟨17155601564669137149513577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91496541678235398130739077 17155601564669137149513577)
      ·
        refine ⟨12866701173501852862135183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17155601564669137149513577 12866701173501852862135183)
        ·
          refine ⟨19300051760252779293202775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12866701173501852862135183 19300051760252779293202775)
          ·
            refine ⟨28950077640379168939804163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19300051760252779293202775 28950077640379168939804163)
            ·
              refine ⟨43425116460568753409706245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28950077640379168939804163 43425116460568753409706245)
              ·
                refine ⟨8142209336356641264319921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43425116460568753409706245 8142209336356641264319921)
                ·
                  refine ⟨6106657002267480948239941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8142209336356641264319921 6106657002267480948239941)
                  ·
                    refine ⟨1144998187925152677794989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6106657002267480948239941 1144998187925152677794989)
                    ·
                      rfl

theorem cell23_6689628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_6689628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689628 prefixEnd_6689628 := by exact prefixLift 6689628
  have htrace : WordTrace (prefixWord ++ tailWord_6689628) baseStart_6689628 baseEnd_6689628 := by
    simpa [prefixWord, tailWord_6689628, baseEnd_6689628] using wordTrace_append hprefix tailTrace_6689628
  have hstable : (prefixWord ++ tailWord_6689628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689628).length < 2 ^ (prefixWord ++ tailWord_6689628).sum := by decide
  have hdescent : baseEnd_6689628 < baseStart_6689628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689685 : List Nat := [1, 3, 2, 1, 1, 6, 1, 2, 2, 1, 3]
def baseStart_6689685 : Nat := 118140960795 + 6689685 * 2 ^ 59
def prefixEnd_6689685 : Nat := 4983230072969 + 3 ^ 40 * 6689685 * 2
def baseEnd_6689685 : Nat := 3435023832172764310372205

theorem tailTrace_6689685 : CollatzResearch.WordTrace tailWord_6689685 prefixEnd_6689685 3435023832172764310372205 := by
  unfold tailWord_6689685
  simp only [CollatzResearch.WordTrace]
  refine ⟨243992856769421227083462509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162661904512947484722308339 243992856769421227083462509)
  ·
    refine ⟨91497321288532960156298441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243992856769421227083462509 91497321288532960156298441)
    ·
      refine ⟨68622990966399720117223831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91497321288532960156298441 68622990966399720117223831)
      ·
        refine ⟨102934486449599580175835747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68622990966399720117223831 102934486449599580175835747)
        ·
          refine ⟨154401729674399370263753621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102934486449599580175835747 154401729674399370263753621)
          ·
            refine ⟨7237581078487470481113451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 154401729674399370263753621 7237581078487470481113451)
            ·
              refine ⟨10856371617731205721670177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7237581078487470481113451 10856371617731205721670177)
              ·
                refine ⟨8142278713298404291252633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10856371617731205721670177 8142278713298404291252633)
                ·
                  refine ⟨6106709034973803218439475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8142278713298404291252633 6106709034973803218439475)
                  ·
                    refine ⟨9160063552460704827659213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6106709034973803218439475 9160063552460704827659213)
                    ·
                      refine ⟨3435023832172764310372205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9160063552460704827659213 3435023832172764310372205)
                      ·
                        rfl

theorem cell23_6689685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_6689685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689685 prefixEnd_6689685 := by exact prefixLift 6689685
  have htrace : WordTrace (prefixWord ++ tailWord_6689685) baseStart_6689685 baseEnd_6689685 := by
    simpa [prefixWord, tailWord_6689685, baseEnd_6689685] using wordTrace_append hprefix tailTrace_6689685
  have hstable : (prefixWord ++ tailWord_6689685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689685).length < 2 ^ (prefixWord ++ tailWord_6689685).sum := by decide
  have hdescent : baseEnd_6689685 < baseStart_6689685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689686 : List Nat := [5, 3, 1, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_6689686 : Nat := 118140960795 + 6689686 * 2 ^ 59
def prefixEnd_6689686 : Nat := 4983230072969 + 3 ^ 40 * 6689686 * 2
def baseEnd_6689686 : Nat := 3435024345653418806459701

theorem tailTrace_6689686 : CollatzResearch.WordTrace tailWord_6689686 prefixEnd_6689686 3435024345653418806459701 := by
  unfold tailWord_6689686
  simp only [CollatzResearch.WordTrace]
  refine ⟨15249555827651100265890557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162661928828278402836165941 15249555827651100265890557)
  ·
    refine ⟨5718583435369162599708959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15249555827651100265890557 5718583435369162599708959)
    ·
      refine ⟨8577875153053743899563439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5718583435369162599708959 8577875153053743899563439)
      ·
        refine ⟨12866812729580615849345159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8577875153053743899563439 12866812729580615849345159)
        ·
          refine ⟨19300219094370923774017739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12866812729580615849345159 19300219094370923774017739)
          ·
            refine ⟨28950328641556385661026609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19300219094370923774017739 28950328641556385661026609)
            ·
              refine ⟨21712746481167289245769957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28950328641556385661026609 21712746481167289245769957)
              ·
                refine ⟨4071139965218866733581867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21712746481167289245769957 4071139965218866733581867)
                ·
                  refine ⟨6106709947828300100372801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4071139965218866733581867 6106709947828300100372801)
                  ·
                    refine ⟨4580032460871225075279601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6106709947828300100372801 4580032460871225075279601)
                    ·
                      refine ⟨3435024345653418806459701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4580032460871225075279601 3435024345653418806459701)
                      ·
                        rfl

theorem cell23_6689686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_6689686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689686 prefixEnd_6689686 := by exact prefixLift 6689686
  have htrace : WordTrace (prefixWord ++ tailWord_6689686) baseStart_6689686 baseEnd_6689686 := by
    simpa [prefixWord, tailWord_6689686, baseEnd_6689686] using wordTrace_append hprefix tailTrace_6689686
  have hstable : (prefixWord ++ tailWord_6689686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689686).length < 2 ^ (prefixWord ++ tailWord_6689686).sum := by decide
  have hdescent : baseEnd_6689686 < baseStart_6689686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689748 : List Nat := [2, 4, 1, 2, 1, 4, 1, 1, 7]
def baseStart_6689748 : Nat := 118140960795 + 6689748 * 2 ^ 59
def prefixEnd_6689748 : Nat := 4983230072969 + 3 ^ 40 * 6689748 * 2
def baseEnd_6689748 : Nat := 381672909050444173764935

theorem tailTrace_6689748 : CollatzResearch.WordTrace tailWord_6689748 prefixEnd_6689748 381672909050444173764935 := by
  unfold tailWord_6689748
  simp only [CollatzResearch.WordTrace]
  refine ⟨121997577284096494421502949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162663436378795325895337265 121997577284096494421502949)
  ·
    refine ⟨22874545740768092704031803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121997577284096494421502949 22874545740768092704031803)
    ·
      refine ⟨34311818611152139056047705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22874545740768092704031803 34311818611152139056047705)
      ·
        refine ⟨25733863958364104292035779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34311818611152139056047705 25733863958364104292035779)
        ·
          refine ⟨38600795937546156438053669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25733863958364104292035779 38600795937546156438053669)
          ·
            refine ⟨7237649238289904332135063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38600795937546156438053669 7237649238289904332135063)
            ·
              refine ⟨10856473857434856498202595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7237649238289904332135063 10856473857434856498202595)
              ·
                refine ⟨16284710786152284747303893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10856473857434856498202595 16284710786152284747303893)
                ·
                  refine ⟨381672909050444173764935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16284710786152284747303893 381672909050444173764935)
                  ·
                    rfl

theorem cell23_6689748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_6689748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689748 prefixEnd_6689748 := by exact prefixLift 6689748
  have htrace : WordTrace (prefixWord ++ tailWord_6689748) baseStart_6689748 baseEnd_6689748 := by
    simpa [prefixWord, tailWord_6689748, baseEnd_6689748] using wordTrace_append hprefix tailTrace_6689748
  have hstable : (prefixWord ++ tailWord_6689748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689748).length < 2 ^ (prefixWord ++ tailWord_6689748).sum := by decide
  have hdescent : baseEnd_6689748 < baseStart_6689748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689759 : List Nat := [1, 1, 2, 3, 5, 2, 2, 1, 2, 2, 2]
def baseStart_6689759 : Nat := 118140960795 + 6689759 * 2 ^ 59
def prefixEnd_6689759 : Nat := 4983230072969 + 3 ^ 40 * 6689759 * 2
def baseEnd_6689759 : Nat := 3435061829741197020846865

theorem tailTrace_6689759 : CollatzResearch.WordTrace tailWord_6689759 prefixEnd_6689759 3435061829741197020846865 := by
  unfold tailWord_6689759
  simp only [CollatzResearch.WordTrace]
  refine ⟨243995555771153137721656331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162663703847435425147770887 243995555771153137721656331)
  ·
    refine ⟨365993333656729706582484497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243995555771153137721656331 365993333656729706582484497)
    ·
      refine ⟨274495000242547279936863373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365993333656729706582484497 274495000242547279936863373)
      ·
        refine ⟨102935625090955229976323765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274495000242547279936863373 102935625090955229976323765)
        ·
          refine ⟨9650214852277052810280353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102935625090955229976323765 9650214852277052810280353)
          ·
            refine ⟨7237661139207789607710265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9650214852277052810280353 7237661139207789607710265)
            ·
              refine ⟨5428245854405842205782699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7237661139207789607710265 5428245854405842205782699)
              ·
                refine ⟨8142368781608763308674049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5428245854405842205782699 8142368781608763308674049)
                ·
                  refine ⟨6106776586206572481505537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8142368781608763308674049 6106776586206572481505537)
                  ·
                    refine ⟨4580082439654929361129153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6106776586206572481505537 4580082439654929361129153)
                    ·
                      refine ⟨3435061829741197020846865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4580082439654929361129153 3435061829741197020846865)
                      ·
                        rfl

theorem cell23_6689759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 2, 2, 2].length) (baseStart_6689759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689759 prefixEnd_6689759 := by exact prefixLift 6689759
  have htrace : WordTrace (prefixWord ++ tailWord_6689759) baseStart_6689759 baseEnd_6689759 := by
    simpa [prefixWord, tailWord_6689759, baseEnd_6689759] using wordTrace_append hprefix tailTrace_6689759
  have hstable : (prefixWord ++ tailWord_6689759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689759).length < 2 ^ (prefixWord ++ tailWord_6689759).sum := by decide
  have hdescent : baseEnd_6689759 < baseStart_6689759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689815 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 2, 4, 2]
def baseStart_6689815 : Nat := 118140960795 + 6689815 * 2 ^ 59
def prefixEnd_6689815 : Nat := 4983230072969 + 3 ^ 40 * 6689815 * 2
def baseEnd_6689815 : Nat := 3435090584657848801746607

theorem tailTrace_6689815 : CollatzResearch.WordTrace tailWord_6689815 prefixEnd_6689815 3435090584657848801746607 := by
  unfold tailWord_6689815
  simp only [CollatzResearch.WordTrace]
  refine ⟨243997598258950259285694899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162665065505966839523796599 243997598258950259285694899)
  ·
    refine ⟨365996397388425388928542349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243997598258950259285694899 365996397388425388928542349)
    ·
      refine ⟨137248649020659520848203381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365996397388425388928542349 137248649020659520848203381)
      ·
        refine ⟨12867060845686830079519067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137248649020659520848203381 12867060845686830079519067)
        ·
          refine ⟨19300591268530245119278601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12867060845686830079519067 19300591268530245119278601)
          ·
            refine ⟨14475443451397683839458951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19300591268530245119278601 14475443451397683839458951)
            ·
              refine ⟨21713165177096525759188427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14475443451397683839458951 21713165177096525759188427)
              ·
                refine ⟨32569747765644788638782641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21713165177096525759188427 32569747765644788638782641)
                ·
                  refine ⟨24427310824233591479086981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32569747765644788638782641 24427310824233591479086981)
                  ·
                    refine ⟨4580120779543798402328809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24427310824233591479086981 4580120779543798402328809)
                    ·
                      refine ⟨3435090584657848801746607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4580120779543798402328809 3435090584657848801746607)
                      ·
                        rfl

theorem cell23_6689815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_6689815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689815 prefixEnd_6689815 := by exact prefixLift 6689815
  have htrace : WordTrace (prefixWord ++ tailWord_6689815) baseStart_6689815 baseEnd_6689815 := by
    simpa [prefixWord, tailWord_6689815, baseEnd_6689815] using wordTrace_append hprefix tailTrace_6689815
  have hstable : (prefixWord ++ tailWord_6689815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689815).length < 2 ^ (prefixWord ++ tailWord_6689815).sum := by decide
  have hdescent : baseEnd_6689815 < baseStart_6689815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689881 : List Nat := [1, 2, 1, 2, 2, 1, 2, 5, 1, 6]
def baseStart_6689881 : Nat := 118140960795 + 6689881 * 2 ^ 59
def prefixEnd_6689881 : Nat := 4983230072969 + 3 ^ 40 * 6689881 * 2
def baseEnd_6689881 : Nat := 1145041491460348514507101

theorem tailTrace_6689881 : CollatzResearch.WordTrace tailWord_6689881 prefixEnd_6689881 1145041491460348514507101 := by
  unfold tailWord_6689881
  simp only [CollatzResearch.WordTrace]
  refine ⟨244000005476711152557597497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162666670317807435038398331 244000005476711152557597497)
  ·
    refine ⟨183000004107533364418198123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244000005476711152557597497 183000004107533364418198123)
    ·
      refine ⟨274500006161300046627297185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183000004107533364418198123 274500006161300046627297185)
      ·
        refine ⟨205875004620975034970472889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274500006161300046627297185 205875004620975034970472889)
        ·
          refine ⟨154406253465731276227854667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205875004620975034970472889 154406253465731276227854667)
          ·
            refine ⟨231609380198596914341782001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154406253465731276227854667 231609380198596914341782001)
            ·
              refine ⟨173707035148947685756336501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231609380198596914341782001 173707035148947685756336501)
              ·
                refine ⟨16285034545213845539656547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173707035148947685756336501 16285034545213845539656547)
                ·
                  refine ⟨24427551817820768309484821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16285034545213845539656547 24427551817820768309484821)
                  ·
                    refine ⟨1145041491460348514507101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24427551817820768309484821 1145041491460348514507101)
                    ·
                      rfl

theorem cell23_6689881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 6].length) (baseStart_6689881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689881 prefixEnd_6689881 := by exact prefixLift 6689881
  have htrace : WordTrace (prefixWord ++ tailWord_6689881) baseStart_6689881 baseEnd_6689881 := by
    simpa [prefixWord, tailWord_6689881, baseEnd_6689881] using wordTrace_append hprefix tailTrace_6689881
  have hstable : (prefixWord ++ tailWord_6689881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689881).length < 2 ^ (prefixWord ++ tailWord_6689881).sum := by decide
  have hdescent : baseEnd_6689881 < baseStart_6689881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689888 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 2, 6, 2]
def baseStart_6689888 : Nat := 118140960795 + 6689888 * 2 ^ 59
def prefixEnd_6689888 : Nat := 4983230072969 + 3 ^ 40 * 6689888 * 2
def baseEnd_6689888 : Nat := 3435128068745627016133771

theorem tailTrace_6689888 : CollatzResearch.WordTrace tailWord_6689888 prefixEnd_6689888 3435128068745627016133771 := by
  unfold tailWord_6689888
  simp only [CollatzResearch.WordTrace]
  refine ⟨122000130393842896376551159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162666840525123861835401545 122000130393842896376551159)
  ·
    refine ⟨183000195590764344564826739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122000130393842896376551159 183000195590764344564826739)
    ·
      refine ⟨274500293386146516847240109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183000195590764344564826739 274500293386146516847240109)
      ·
        refine ⟨102937610019804943817715041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274500293386146516847240109 102937610019804943817715041)
        ·
          refine ⟨77203207514853707863286281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102937610019804943817715041 77203207514853707863286281)
          ·
            refine ⟨57902405636140280897464711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77203207514853707863286281 57902405636140280897464711)
            ·
              refine ⟨86853608454210421346197067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57902405636140280897464711 86853608454210421346197067)
              ·
                refine ⟨130280412681315632019295601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86853608454210421346197067 130280412681315632019295601)
                ·
                  refine ⟨97710309510986724014471701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130280412681315632019295601 97710309510986724014471701)
                  ·
                    refine ⟨4580170758327502688178361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97710309510986724014471701 4580170758327502688178361)
                    ·
                      refine ⟨3435128068745627016133771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4580170758327502688178361 3435128068745627016133771)
                      ·
                        rfl

theorem cell23_6689888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 2, 6, 2].length) (baseStart_6689888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689888 prefixEnd_6689888 := by exact prefixLift 6689888
  have htrace : WordTrace (prefixWord ++ tailWord_6689888) baseStart_6689888 baseEnd_6689888 := by
    simpa [prefixWord, tailWord_6689888, baseEnd_6689888] using wordTrace_append hprefix tailTrace_6689888
  have hstable : (prefixWord ++ tailWord_6689888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689888).length < 2 ^ (prefixWord ++ tailWord_6689888).sum := by decide
  have hdescent : baseEnd_6689888 < baseStart_6689888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689891 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 5]
def baseStart_6689891 : Nat := 118140960795 + 6689891 * 2 ^ 59
def prefixEnd_6689891 : Nat := 4983230072969 + 3 ^ 40 * 6689891 * 2
def baseEnd_6689891 : Nat := 3435129609187590504396257

theorem tailTrace_6689891 : CollatzResearch.WordTrace tailWord_6689891 prefixEnd_6689891 3435129609187590504396257 := by
  unfold tailWord_6689891
  simp only [CollatzResearch.WordTrace]
  refine ⟨244000370206674924265461527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162666913471116616176974351 244000370206674924265461527)
  ·
    refine ⟨366000555310012386398192291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244000370206674924265461527 366000555310012386398192291)
    ·
      refine ⟨549000832965018579597288437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366000555310012386398192291 549000832965018579597288437)
      ·
        refine ⟨51468828090470491837245791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 549000832965018579597288437 51468828090470491837245791)
        ·
          refine ⟨77203242135705737755868687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51468828090470491837245791 77203242135705737755868687)
          ·
            refine ⟨115804863203558606633803031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77203242135705737755868687 115804863203558606633803031)
            ·
              refine ⟨173707294805337909950704547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115804863203558606633803031 173707294805337909950704547)
              ·
                refine ⟨260560942208006864926056821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173707294805337909950704547 260560942208006864926056821)
                ·
                  refine ⟨24427588332000643586817827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 260560942208006864926056821 24427588332000643586817827)
                  ·
                    refine ⟨36641382498000965380226741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24427588332000643586817827 36641382498000965380226741)
                    ·
                      refine ⟨3435129609187590504396257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36641382498000965380226741 3435129609187590504396257)
                      ·
                        rfl

theorem cell23_6689891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_6689891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689891 prefixEnd_6689891 := by exact prefixLift 6689891
  have htrace : WordTrace (prefixWord ++ tailWord_6689891) baseStart_6689891 baseEnd_6689891 := by
    simpa [prefixWord, tailWord_6689891, baseEnd_6689891] using wordTrace_append hprefix tailTrace_6689891
  have hstable : (prefixWord ++ tailWord_6689891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689891).length < 2 ^ (prefixWord ++ tailWord_6689891).sum := by decide
  have hdescent : baseEnd_6689891 < baseStart_6689891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689909 : List Nat := [1, 3, 4, 3, 1, 1, 1, 2, 2, 3, 2]
def baseStart_6689909 : Nat := 118140960795 + 6689909 * 2 ^ 59
def prefixEnd_6689909 : Nat := 4983230072969 + 3 ^ 40 * 6689909 * 2
def baseEnd_6689909 : Nat := 3435138851839371433971175

theorem tailTrace_6689909 : CollatzResearch.WordTrace tailWord_6689909 prefixEnd_6689909 3435138851839371433971175 := by
  unfold tailWord_6689909
  simp only [CollatzResearch.WordTrace]
  refine ⟨244001026720609713339616781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162667351147073142226411187 244001026720609713339616781)
  ·
    refine ⟨91500385020228642502356293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244001026720609713339616781 91500385020228642502356293)
    ·
      refine ⟨17156322191292870469191805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91500385020228642502356293 17156322191292870469191805)
      ·
        refine ⟨6433620821734826425946927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17156322191292870469191805 6433620821734826425946927)
        ·
          refine ⟨9650431232602239638920391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6433620821734826425946927 9650431232602239638920391)
          ·
            refine ⟨14475646848903359458380587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9650431232602239638920391 14475646848903359458380587)
            ·
              refine ⟨21713470273355039187570881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14475646848903359458380587 21713470273355039187570881)
              ·
                refine ⟨16285102705016279390678161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21713470273355039187570881 16285102705016279390678161)
                ·
                  refine ⟨12213827028762209543008621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16285102705016279390678161 12213827028762209543008621)
                  ·
                    refine ⟨4580185135785828578628233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12213827028762209543008621 4580185135785828578628233)
                    ·
                      refine ⟨3435138851839371433971175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4580185135785828578628233 3435138851839371433971175)
                      ·
                        rfl

theorem cell23_6689909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_6689909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689909 prefixEnd_6689909 := by exact prefixLift 6689909
  have htrace : WordTrace (prefixWord ++ tailWord_6689909) baseStart_6689909 baseEnd_6689909 := by
    simpa [prefixWord, tailWord_6689909, baseEnd_6689909] using wordTrace_append hprefix tailTrace_6689909
  have hstable : (prefixWord ++ tailWord_6689909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689909).length < 2 ^ (prefixWord ++ tailWord_6689909).sum := by decide
  have hdescent : baseEnd_6689909 < baseStart_6689909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689941 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 4, 7]
def baseStart_6689941 : Nat := 118140960795 + 6689941 * 2 ^ 59
def prefixEnd_6689941 : Nat := 4983230072969 + 3 ^ 40 * 6689941 * 2
def baseEnd_6689941 : Nat := 1145051761073438436257009

theorem tailTrace_6689941 : CollatzResearch.WordTrace tailWord_6689941 prefixEnd_6689941 1145051761073438436257009 := by
  unfold tailWord_6689941
  simp only [CollatzResearch.WordTrace]
  refine ⟨244002193856493782804781677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162668129237662521869854451 244002193856493782804781677)
  ·
    refine ⟨91500822696185168551793129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244002193856493782804781677 91500822696185168551793129)
    ·
      refine ⟨68625617022138876413844847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91500822696185168551793129 68625617022138876413844847)
      ·
        refine ⟨102938425533208314620767271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68625617022138876413844847 102938425533208314620767271)
        ·
          refine ⟨154407638299812471931150907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102938425533208314620767271 154407638299812471931150907)
          ·
            refine ⟨231611457449718707896726361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154407638299812471931150907 231611457449718707896726361)
            ·
              refine ⟨173708593087289030922544771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231611457449718707896726361 173708593087289030922544771)
              ·
                refine ⟨260562889630933546383817157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173708593087289030922544771 260562889630933546383817157)
                ·
                  refine ⟨48855541805800039946965717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 260562889630933546383817157 48855541805800039946965717)
                  ·
                    refine ⟨1145051761073438436257009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48855541805800039946965717 1145051761073438436257009)
                    ·
                      rfl

theorem cell23_6689941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_6689941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689941 prefixEnd_6689941 := by exact prefixLift 6689941
  have htrace : WordTrace (prefixWord ++ tailWord_6689941) baseStart_6689941 baseEnd_6689941 := by
    simpa [prefixWord, tailWord_6689941, baseEnd_6689941] using wordTrace_append hprefix tailTrace_6689941
  have hstable : (prefixWord ++ tailWord_6689941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689941).length < 2 ^ (prefixWord ++ tailWord_6689941).sum := by decide
  have hdescent : baseEnd_6689941 < baseStart_6689941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689959 : List Nat := [1, 1, 6, 2, 1, 2, 3, 1, 1, 2, 3]
def baseStart_6689959 : Nat := 118140960795 + 6689959 * 2 ^ 59
def prefixEnd_6689959 : Nat := 4983230072969 + 3 ^ 40 * 6689959 * 2
def baseEnd_6689959 : Nat := 3435164525872096238345945

theorem tailTrace_6689959 : CollatzResearch.WordTrace tailWord_6689959 prefixEnd_6689959 3435164525872096238345945 := by
  unfold tailWord_6689959
  simp only [CollatzResearch.WordTrace]
  refine ⟨244002850370428571878936931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162668566913619047919291287 244002850370428571878936931)
  ·
    refine ⟨366004275555642857818405397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244002850370428571878936931 366004275555642857818405397)
    ·
      refine ⟨17156450416670758960237753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 366004275555642857818405397 17156450416670758960237753)
      ·
        refine ⟨12867337812503069220178315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17156450416670758960237753 12867337812503069220178315)
        ·
          refine ⟨19301006718754603830267473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12867337812503069220178315 19301006718754603830267473)
          ·
            refine ⟨14475755039065952872700605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19301006718754603830267473 14475755039065952872700605)
            ·
              refine ⟨5428408139649732327262727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14475755039065952872700605 5428408139649732327262727)
              ·
                refine ⟨8142612209474598490894091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5428408139649732327262727 8142612209474598490894091)
                ·
                  refine ⟨12213918314211897736341137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8142612209474598490894091 12213918314211897736341137)
                  ·
                    refine ⟨9160438735658923302255853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12213918314211897736341137 9160438735658923302255853)
                    ·
                      refine ⟨3435164525872096238345945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9160438735658923302255853 3435164525872096238345945)
                      ·
                        rfl

theorem cell23_6689959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_6689959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689959 prefixEnd_6689959 := by exact prefixLift 6689959
  have htrace : WordTrace (prefixWord ++ tailWord_6689959) baseStart_6689959 baseEnd_6689959 := by
    simpa [prefixWord, tailWord_6689959, baseEnd_6689959] using wordTrace_append hprefix tailTrace_6689959
  have hstable : (prefixWord ++ tailWord_6689959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689959).length < 2 ^ (prefixWord ++ tailWord_6689959).sum := by decide
  have hdescent : baseEnd_6689959 < baseStart_6689959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6689982 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2]
def baseStart_6689982 : Nat := 118140960795 + 6689982 * 2 ^ 59
def prefixEnd_6689982 : Nat := 4983230072969 + 3 ^ 40 * 6689982 * 2
def baseEnd_6689982 : Nat := 3435176335927149648358339

theorem tailTrace_6689982 : CollatzResearch.WordTrace tailWord_6689982 prefixEnd_6689982 3435176335927149648358339 := by
  unfold tailWord_6689982
  simp only [CollatzResearch.WordTrace]
  refine ⟨30500461156168155850878025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162669126166230164538016133 30500461156168155850878025)
  ·
    refine ⟨22875345867126116888158519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30500461156168155850878025 22875345867126116888158519)
    ·
      refine ⟨34313018800689175332237779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22875345867126116888158519 34313018800689175332237779)
      ·
        refine ⟨51469528201033762998356669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34313018800689175332237779 51469528201033762998356669)
        ·
          refine ⟨19301073075387661124383751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51469528201033762998356669 19301073075387661124383751)
          ·
            refine ⟨28951609613081491686575627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19301073075387661124383751 28951609613081491686575627)
            ·
              refine ⟨43427414419622237529863441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28951609613081491686575627 43427414419622237529863441)
              ·
                refine ⟨32570560814716678147397581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43427414419622237529863441 32570560814716678147397581)
                ·
                  refine ⟨12213960305518754305274093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32570560814716678147397581 12213960305518754305274093)
                  ·
                    refine ⟨4580235114569532864477785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12213960305518754305274093 4580235114569532864477785)
                    ·
                      refine ⟨3435176335927149648358339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4580235114569532864477785 3435176335927149648358339)
                      ·
                        rfl

theorem cell23_6689982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_6689982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6689982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6689982 prefixEnd_6689982 := by exact prefixLift 6689982
  have htrace : WordTrace (prefixWord ++ tailWord_6689982) baseStart_6689982 baseEnd_6689982 := by
    simpa [prefixWord, tailWord_6689982, baseEnd_6689982] using wordTrace_append hprefix tailTrace_6689982
  have hstable : (prefixWord ++ tailWord_6689982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6689982).length < 2 ^ (prefixWord ++ tailWord_6689982).sum := by decide
  have hdescent : baseEnd_6689982 < baseStart_6689982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6689982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690029 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 4, 2, 2]
def baseStart_6690029 : Nat := 118140960795 + 6690029 * 2 ^ 59
def prefixEnd_6690029 : Nat := 4983230072969 + 3 ^ 40 * 6690029 * 2
def baseEnd_6690029 : Nat := 3435200469517910964470623

theorem tailTrace_6690029 : CollatzResearch.WordTrace tailWord_6690029 prefixEnd_6690029 3435200469517910964470623 := by
  unfold tailWord_6690029
  simp only [CollatzResearch.WordTrace]
  refine ⟨244005403480174973833985141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162670268986783315889323427 244005403480174973833985141)
  ·
    refine ⟨22875506576266403796936107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244005403480174973833985141 22875506576266403796936107)
    ·
      refine ⟨34313259864399605695404161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22875506576266403796936107 34313259864399605695404161)
      ·
        refine ⟨25734944898299704271553121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34313259864399605695404161 25734944898299704271553121)
        ·
          refine ⟨19301208673724778203664841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25734944898299704271553121 19301208673724778203664841)
          ·
            refine ⟨14475906505293583652748631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19301208673724778203664841 14475906505293583652748631)
            ·
              refine ⟨21713859757940375479122947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14475906505293583652748631 21713859757940375479122947)
              ·
                refine ⟨32570789636910563218684421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21713859757940375479122947 32570789636910563218684421)
                ·
                  refine ⟨6107023056920730603503329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32570789636910563218684421 6107023056920730603503329)
                  ·
                    refine ⟨4580267292690547952627497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6107023056920730603503329 4580267292690547952627497)
                    ·
                      refine ⟨3435200469517910964470623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4580267292690547952627497 3435200469517910964470623)
                      ·
                        rfl

theorem cell23_6690029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_6690029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690029 prefixEnd_6690029 := by exact prefixLift 6690029
  have htrace : WordTrace (prefixWord ++ tailWord_6690029) baseStart_6690029 baseEnd_6690029 := by
    simpa [prefixWord, tailWord_6690029, baseEnd_6690029] using wordTrace_append hprefix tailTrace_6690029
  have hstable : (prefixWord ++ tailWord_6690029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690029).length < 2 ^ (prefixWord ++ tailWord_6690029).sum := by decide
  have hdescent : baseEnd_6690029 < baseStart_6690029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690035 : List Nat := [1, 1, 1, 2, 2, 5, 2, 4, 5]
def baseStart_6690035 : Nat := 118140960795 + 6690035 * 2 ^ 59
def prefixEnd_6690035 : Nat := 4983230072969 + 3 ^ 40 * 6690035 * 2
def baseEnd_6690035 : Nat := 381689283377981993443955

theorem tailTrace_6690035 : CollatzResearch.WordTrace tailWord_6690035 prefixEnd_6690035 381689283377981993443955 := by
  unfold tailWord_6690035
  simp only [CollatzResearch.WordTrace]
  refine ⟨244005622318153236858703559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162670414878768824572469039 244005622318153236858703559)
  ·
    refine ⟨366008433477229855288055339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244005622318153236858703559 366008433477229855288055339)
    ·
      refine ⟨549012650215844782932083009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366008433477229855288055339 549012650215844782932083009)
      ·
        refine ⟨411759487661883587199062257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 549012650215844782932083009 411759487661883587199062257)
        ·
          refine ⟨308819615746412690399296693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411759487661883587199062257 308819615746412690399296693)
          ·
            refine ⟨28951838976226189724934065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 308819615746412690399296693 28951838976226189724934065)
            ·
              refine ⟨21713879232169642293700549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28951838976226189724934065 21713879232169642293700549)
              ·
                refine ⟨4071352356031807930068853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21713879232169642293700549 4071352356031807930068853)
                ·
                  refine ⟨381689283377981993443955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4071352356031807930068853 381689283377981993443955)
                  ·
                    rfl

theorem cell23_6690035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 5].length) (baseStart_6690035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690035 prefixEnd_6690035 := by exact prefixLift 6690035
  have htrace : WordTrace (prefixWord ++ tailWord_6690035) baseStart_6690035 baseEnd_6690035 := by
    simpa [prefixWord, tailWord_6690035, baseEnd_6690035] using wordTrace_append hprefix tailTrace_6690035
  have hstable : (prefixWord ++ tailWord_6690035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690035).length < 2 ^ (prefixWord ++ tailWord_6690035).sum := by decide
  have hdescent : baseEnd_6690035 < baseStart_6690035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690058 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5]
def baseStart_6690058 : Nat := 118140960795 + 6690058 * 2 ^ 59
def prefixEnd_6690058 : Nat := 4983230072969 + 3 ^ 40 * 6690058 * 2
def baseEnd_6690058 : Nat := 3435215360456891351007989

theorem tailTrace_6690058 : CollatzResearch.WordTrace tailWord_6690058 prefixEnd_6690058 3435215360456891351007989 := by
  unfold tailWord_6690058
  simp only [CollatzResearch.WordTrace]
  refine ⟨61001615299267477946697707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162670974131379941191193885 61001615299267477946697707)
  ·
    refine ⟨91502422948901216920046561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61001615299267477946697707 91502422948901216920046561)
    ·
      refine ⟨68626817211675912690034921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91502422948901216920046561 68626817211675912690034921)
      ·
        refine ⟨51470112908756934517526191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68626817211675912690034921 51470112908756934517526191)
        ·
          refine ⟨77205169363135401776289287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51470112908756934517526191 77205169363135401776289287)
          ·
            refine ⟨115807754044703102664433931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77205169363135401776289287 115807754044703102664433931)
            ·
              refine ⟨173711631067054653996650897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115807754044703102664433931 173711631067054653996650897)
              ·
                refine ⟨130283723300290990497488173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173711631067054653996650897 130283723300290990497488173)
                ·
                  refine ⟨48856396237609121436558065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130283723300290990497488173 48856396237609121436558065)
                  ·
                    refine ⟨36642297178206841077418549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48856396237609121436558065 36642297178206841077418549)
                    ·
                      refine ⟨3435215360456891351007989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36642297178206841077418549 3435215360456891351007989)
                      ·
                        rfl

theorem cell23_6690058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_6690058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690058 prefixEnd_6690058 := by exact prefixLift 6690058
  have htrace : WordTrace (prefixWord ++ tailWord_6690058) baseStart_6690058 baseEnd_6690058 := by
    simpa [prefixWord, tailWord_6690058, baseEnd_6690058] using wordTrace_append hprefix tailTrace_6690058
  have hstable : (prefixWord ++ tailWord_6690058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690058).length < 2 ^ (prefixWord ++ tailWord_6690058).sum := by decide
  have hdescent : baseEnd_6690058 < baseStart_6690058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690082 : List Nat := [3, 3, 1, 1, 4, 1, 1, 2, 2, 5]
def baseStart_6690082 : Nat := 118140960795 + 6690082 * 2 ^ 59
def prefixEnd_6690082 : Nat := 4983230072969 + 3 ^ 40 * 6690082 * 2
def baseEnd_6690082 : Nat := 1145075894664199752369293

theorem tailTrace_6690082 : CollatzResearch.WordTrace tailWord_6690082 prefixEnd_6690082 1145075894664199752369293 := by
  unfold tailWord_6690082
  simp only [CollatzResearch.WordTrace]
  refine ⟨61001834137245740971416125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162671557699321975923776333 61001834137245740971416125)
  ·
    refine ⟨22875687801467152864281047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61001834137245740971416125 22875687801467152864281047)
    ·
      refine ⟨34313531702200729296421571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22875687801467152864281047 34313531702200729296421571)
      ·
        refine ⟨51470297553301093944632357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34313531702200729296421571 51470297553301093944632357)
        ·
          refine ⟨9650680791243955114618567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51470297553301093944632357 9650680791243955114618567)
          ·
            refine ⟨14476021186865932671927851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9650680791243955114618567 14476021186865932671927851)
            ·
              refine ⟨21714031780298899007891777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14476021186865932671927851 21714031780298899007891777)
              ·
                refine ⟨16285523835224174255918833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21714031780298899007891777 16285523835224174255918833)
                ·
                  refine ⟨12214142876418130691939125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16285523835224174255918833 12214142876418130691939125)
                  ·
                    refine ⟨1145075894664199752369293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12214142876418130691939125 1145075894664199752369293)
                    ·
                      rfl

theorem cell23_6690082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_6690082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690082 prefixEnd_6690082 := by exact prefixLift 6690082
  have htrace : WordTrace (prefixWord ++ tailWord_6690082) baseStart_6690082 baseEnd_6690082 := by
    simpa [prefixWord, tailWord_6690082, baseEnd_6690082] using wordTrace_append hprefix tailTrace_6690082
  have hstable : (prefixWord ++ tailWord_6690082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690082).length < 2 ^ (prefixWord ++ tailWord_6690082).sum := by decide
  have hdescent : baseEnd_6690082 < baseStart_6690082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690085 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 4, 1, 4]
def baseStart_6690085 : Nat := 118140960795 + 6690085 * 2 ^ 59
def prefixEnd_6690085 : Nat := 4983230072969 + 3 ^ 40 * 6690085 * 2
def baseEnd_6690085 : Nat := 3435229224434562745370365

theorem tailTrace_6690085 : CollatzResearch.WordTrace tailWord_6690085 prefixEnd_6690085 3435229224434562745370365 := by
  unfold tailWord_6690085
  simp only [CollatzResearch.WordTrace]
  refine ⟨244007445967972095398023709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162671630645314730265349139 244007445967972095398023709)
  ·
    refine ⟨91502792237989535774258891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244007445967972095398023709 91502792237989535774258891)
    ·
      refine ⟨137254188356984303661388337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91502792237989535774258891 137254188356984303661388337)
      ·
        refine ⟨102940641267738227746041253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137254188356984303661388337 102940641267738227746041253)
        ·
          refine ⟨19301370237700917702382735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102940641267738227746041253 19301370237700917702382735)
          ·
            refine ⟨28952055356551376553574103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19301370237700917702382735 28952055356551376553574103)
            ·
              refine ⟨43428083034827064830361155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28952055356551376553574103 43428083034827064830361155)
              ·
                refine ⟨65142124552240597245541733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43428083034827064830361155 65142124552240597245541733)
                ·
                  refine ⟨12214148353545111983539075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65142124552240597245541733 12214148353545111983539075)
                  ·
                    refine ⟨18321222530317667975308613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12214148353545111983539075 18321222530317667975308613)
                    ·
                      refine ⟨3435229224434562745370365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18321222530317667975308613 3435229224434562745370365)
                      ·
                        rfl

theorem cell23_6690085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_6690085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690085 prefixEnd_6690085 := by exact prefixLift 6690085
  have htrace : WordTrace (prefixWord ++ tailWord_6690085) baseStart_6690085 baseEnd_6690085 := by
    simpa [prefixWord, tailWord_6690085, baseEnd_6690085] using wordTrace_append hprefix tailTrace_6690085
  have hstable : (prefixWord ++ tailWord_6690085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690085).length < 2 ^ (prefixWord ++ tailWord_6690085).sum := by decide
  have hdescent : baseEnd_6690085 < baseStart_6690085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690162 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 1, 5, 2]
def baseStart_6690162 : Nat := 118140960795 + 6690162 * 2 ^ 59
def prefixEnd_6690162 : Nat := 4983230072969 + 3 ^ 40 * 6690162 * 2
def baseEnd_6690162 : Nat := 3435268762444958944107511

theorem tailTrace_6690162 : CollatzResearch.WordTrace tailWord_6690162 prefixEnd_6690162 3435268762444958944107511 := by
  unfold tailWord_6690162
  simp only [CollatzResearch.WordTrace]
  refine ⟨61002563597173284387144185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162673502925795425032384493 61002563597173284387144185)
  ·
    refine ⟨45751922697879963290358139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61002563597173284387144185 45751922697879963290358139)
    ·
      refine ⟨68627884046819944935537209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45751922697879963290358139 68627884046819944935537209)
      ·
        refine ⟨51470913035114958701652907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68627884046819944935537209 51470913035114958701652907)
        ·
          refine ⟨77206369552672438052479361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51470913035114958701652907 77206369552672438052479361)
          ·
            refine ⟨57904777164504328539359521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77206369552672438052479361 57904777164504328539359521)
            ·
              refine ⟨43428582873378246404519641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57904777164504328539359521 43428582873378246404519641)
              ·
                refine ⟨32571437155033684803389731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43428582873378246404519641 32571437155033684803389731)
                ·
                  refine ⟨48857155732550527205084597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32571437155033684803389731 48857155732550527205084597)
                  ·
                    refine ⟨4580358349926611925476681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48857155732550527205084597 4580358349926611925476681)
                    ·
                      refine ⟨3435268762444958944107511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4580358349926611925476681 3435268762444958944107511)
                      ·
                        rfl

theorem cell23_6690162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_6690162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690162 prefixEnd_6690162 := by exact prefixLift 6690162
  have htrace : WordTrace (prefixWord ++ tailWord_6690162) baseStart_6690162 baseEnd_6690162 := by
    simpa [prefixWord, tailWord_6690162, baseEnd_6690162] using wordTrace_append hprefix tailTrace_6690162
  have hstable : (prefixWord ++ tailWord_6690162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690162).length < 2 ^ (prefixWord ++ tailWord_6690162).sum := by decide
  have hdescent : baseEnd_6690162 < baseStart_6690162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690179 : List Nat := [1, 1, 1, 3, 5, 1, 3, 1, 2, 3, 2]
def baseStart_6690179 : Nat := 118140960795 + 6690179 * 2 ^ 59
def prefixEnd_6690179 : Nat := 4983230072969 + 3 ^ 40 * 6690179 * 2
def baseEnd_6690179 : Nat := 3435277491616085377594933

theorem tailTrace_6690179 : CollatzResearch.WordTrace tailWord_6690179 prefixEnd_6690179 3435277491616085377594933 := by
  unfold tailWord_6690179
  simp only [CollatzResearch.WordTrace]
  refine ⟨244010874429631549451945591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162673916286421032967963727 244010874429631549451945591)
  ·
    refine ⟨366016311644447324177918387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244010874429631549451945591 366016311644447324177918387)
    ·
      refine ⟨549024467466670986266877581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366016311644447324177918387 549024467466670986266877581)
      ·
        refine ⟨205884175300001619850079093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 549024467466670986266877581 205884175300001619850079093)
        ·
          refine ⟨19301641434375151860944915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205884175300001619850079093 19301641434375151860944915)
          ·
            refine ⟨28952462151562727791417373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19301641434375151860944915 28952462151562727791417373)
            ·
              refine ⟨10857173306836022921781515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28952462151562727791417373 10857173306836022921781515)
              ·
                refine ⟨16285759960254034382672273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10857173306836022921781515 16285759960254034382672273)
                ·
                  refine ⟨12214319970190525787004205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16285759960254034382672273 12214319970190525787004205)
                  ·
                    refine ⟨4580369988821447170126577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12214319970190525787004205 4580369988821447170126577)
                    ·
                      refine ⟨3435277491616085377594933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4580369988821447170126577 3435277491616085377594933)
                      ·
                        rfl

theorem cell23_6690179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 3, 2].length) (baseStart_6690179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690179 prefixEnd_6690179 := by exact prefixLift 6690179
  have htrace : WordTrace (prefixWord ++ tailWord_6690179) baseStart_6690179 baseEnd_6690179 := by
    simpa [prefixWord, tailWord_6690179, baseEnd_6690179] using wordTrace_append hprefix tailTrace_6690179
  have hstable : (prefixWord ++ tailWord_6690179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690179).length < 2 ^ (prefixWord ++ tailWord_6690179).sum := by decide
  have hdescent : baseEnd_6690179 < baseStart_6690179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690202 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 4, 4]
def baseStart_6690202 : Nat := 118140960795 + 6690202 * 2 ^ 59
def prefixEnd_6690202 : Nat := 4983230072969 + 3 ^ 40 * 6690202 * 2
def baseEnd_6690202 : Nat := 1145096433890379595869109

theorem tailTrace_6690202 : CollatzResearch.WordTrace tailWord_6690202 prefixEnd_6690202 1145096433890379595869109 := by
  unfold tailWord_6690202
  simp only [CollatzResearch.WordTrace]
  refine ⟨61002928327137056095008215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162674475539032149586688573 61002928327137056095008215)
  ·
    refine ⟨91504392490705584142512323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61002928327137056095008215 91504392490705584142512323)
    ·
      refine ⟨137256588736058376213768485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91504392490705584142512323 137256588736058376213768485)
      ·
        refine ⟨25735610388010945540081591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137256588736058376213768485 25735610388010945540081591)
        ·
          refine ⟨38603415582016418310122387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25735610388010945540081591 38603415582016418310122387)
          ·
            refine ⟨57905123373024627465183581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38603415582016418310122387 57905123373024627465183581)
            ·
              refine ⟨21714421264884235299443843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57905123373024627465183581 21714421264884235299443843)
              ·
                refine ⟨32571631897326352949165765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21714421264884235299443843 32571631897326352949165765)
                ·
                  refine ⟨6107180980748691177968581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32571631897326352949165765 6107180980748691177968581)
                  ·
                    refine ⟨1145096433890379595869109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6107180980748691177968581 1145096433890379595869109)
                    ·
                      rfl

theorem cell23_6690202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 4, 4].length) (baseStart_6690202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690202 prefixEnd_6690202 := by exact prefixLift 6690202
  have htrace : WordTrace (prefixWord ++ tailWord_6690202) baseStart_6690202 baseEnd_6690202 := by
    simpa [prefixWord, tailWord_6690202, baseEnd_6690202] using wordTrace_append hprefix tailTrace_6690202
  have hstable : (prefixWord ++ tailWord_6690202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690202).length < 2 ^ (prefixWord ++ tailWord_6690202).sum := by decide
  have hdescent : baseEnd_6690202 < baseStart_6690202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690215 : List Nat := [1, 1, 6, 1, 1, 1, 2, 10]
def baseStart_6690215 : Nat := 118140960795 + 6690215 * 2 ^ 59
def prefixEnd_6690215 : Nat := 4983230072969 + 3 ^ 40 * 6690215 * 2
def baseEnd_6690215 : Nat := 127233184330357305064621

theorem tailTrace_6690215 : CollatzResearch.WordTrace tailWord_6690215 prefixEnd_6690215 127233184330357305064621 := by
  unfold tailWord_6690215
  simp only [CollatzResearch.WordTrace]
  refine ⟨244012187457501127600256099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162674791638334085066837399 244012187457501127600256099)
  ·
    refine ⟨366018281186251691400384149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244012187457501127600256099 366018281186251691400384149)
    ·
      refine ⟨17157106930605548034393007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 366018281186251691400384149 17157106930605548034393007)
      ·
        refine ⟨25735660395908322051589511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17157106930605548034393007 25735660395908322051589511)
        ·
          refine ⟨38603490593862483077384267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25735660395908322051589511 38603490593862483077384267)
          ·
            refine ⟨57905235890793724616076401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38603490593862483077384267 57905235890793724616076401)
            ·
              refine ⟨43428926918095293462057301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57905235890793724616076401 43428926918095293462057301)
              ·
                refine ⟨127233184330357305064621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 43428926918095293462057301 127233184330357305064621)
                ·
                  rfl

theorem cell23_6690215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 10].length) (baseStart_6690215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690215 prefixEnd_6690215 := by exact prefixLift 6690215
  have htrace : WordTrace (prefixWord ++ tailWord_6690215) baseStart_6690215 baseEnd_6690215 := by
    simpa [prefixWord, tailWord_6690215, baseEnd_6690215] using wordTrace_append hprefix tailTrace_6690215
  have hstable : (prefixWord ++ tailWord_6690215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690215).length < 2 ^ (prefixWord ++ tailWord_6690215).sum := by decide
  have hdescent : baseEnd_6690215 < baseStart_6690215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690229 : List Nat := [1, 3, 3, 2, 2, 1, 1, 4, 1, 2, 3]
def baseStart_6690229 : Nat := 118140960795 + 6690229 * 2 ^ 59
def prefixEnd_6690229 : Nat := 4983230072969 + 3 ^ 40 * 6690229 * 2
def baseEnd_6690229 : Nat := 3435303165648810181969703

theorem tailTrace_6690229 : CollatzResearch.WordTrace tailWord_6690229 prefixEnd_6690229 3435303165648810181969703 := by
  unfold tailWord_6690229
  simp only [CollatzResearch.WordTrace]
  refine ⟨244012698079450407991265741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162675132052966938660843827 244012698079450407991265741)
  ·
    refine ⟨91504761779793902996724653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244012698079450407991265741 91504761779793902996724653)
    ·
      refine ⟨34314285667422713623771745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91504761779793902996724653 34314285667422713623771745)
      ·
        refine ⟨25735714250567035217828809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34314285667422713623771745 25735714250567035217828809)
        ·
          refine ⟨19301785687925276413371607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25735714250567035217828809 19301785687925276413371607)
          ·
            refine ⟨28952678531887914620057411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19301785687925276413371607 28952678531887914620057411)
            ·
              refine ⟨43429017797831871930086117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28952678531887914620057411 43429017797831871930086117)
              ·
                refine ⟨8142940837093475986891147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43429017797831871930086117 8142940837093475986891147)
                ·
                  refine ⟨12214411255640213980336721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8142940837093475986891147 12214411255640213980336721)
                  ·
                    refine ⟨9160808441730160485252541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12214411255640213980336721 9160808441730160485252541)
                    ·
                      refine ⟨3435303165648810181969703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9160808441730160485252541 3435303165648810181969703)
                      ·
                        rfl

theorem cell23_6690229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_6690229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690229 prefixEnd_6690229 := by exact prefixLift 6690229
  have htrace : WordTrace (prefixWord ++ tailWord_6690229) baseStart_6690229 baseEnd_6690229 := by
    simpa [prefixWord, tailWord_6690229, baseEnd_6690229] using wordTrace_append hprefix tailTrace_6690229
  have hstable : (prefixWord ++ tailWord_6690229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690229).length < 2 ^ (prefixWord ++ tailWord_6690229).sum := by decide
  have hdescent : baseEnd_6690229 < baseStart_6690229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690260 : List Nat := [2, 4, 1, 2, 4, 1, 1, 1, 3, 2, 2]
def baseStart_6690260 : Nat := 118140960795 + 6690260 * 2 ^ 59
def prefixEnd_6690260 : Nat := 4983230072969 + 3 ^ 40 * 6690260 * 2
def baseEnd_6690260 : Nat := 3435319083549099560682061

theorem tailTrace_6690260 : CollatzResearch.WordTrace tailWord_6690260 prefixEnd_6690260 3435319083549099560682061 := by
  unfold tailWord_6690260
  simp only [CollatzResearch.WordTrace]
  refine ⟨122006914371169050142822117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162675885828225400190429489 122006914371169050142822117)
  ·
    refine ⟨22876296444594196901779147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122006914371169050142822117 22876296444594196901779147)
    ·
      refine ⟨34314444666891295352668721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22876296444594196901779147 34314444666891295352668721)
      ·
        refine ⟨25735833500168471514501541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34314444666891295352668721 25735833500168471514501541)
        ·
          refine ⟨4825468781281588408969039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25735833500168471514501541 4825468781281588408969039)
          ·
            refine ⟨7238203171922382613453559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4825468781281588408969039 7238203171922382613453559)
            ·
              refine ⟨10857304757883573920180339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7238203171922382613453559 10857304757883573920180339)
              ·
                refine ⟨16285957136825360880270509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10857304757883573920180339 16285957136825360880270509)
                ·
                  refine ⟨6107233926309510330101441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16285957136825360880270509 6107233926309510330101441)
                  ·
                    refine ⟨4580425444732132747576081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6107233926309510330101441 4580425444732132747576081)
                    ·
                      refine ⟨3435319083549099560682061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4580425444732132747576081 3435319083549099560682061)
                      ·
                        rfl

theorem cell23_6690260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_6690260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690260 prefixEnd_6690260 := by exact prefixLift 6690260
  have htrace : WordTrace (prefixWord ++ tailWord_6690260) baseStart_6690260 baseEnd_6690260 := by
    simpa [prefixWord, tailWord_6690260, baseEnd_6690260] using wordTrace_append hprefix tailTrace_6690260
  have hstable : (prefixWord ++ tailWord_6690260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690260).length < 2 ^ (prefixWord ++ tailWord_6690260).sum := by decide
  have hdescent : baseEnd_6690260 < baseStart_6690260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690295 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 4]
def baseStart_6690295 : Nat := 118140960795 + 6690295 * 2 ^ 59
def prefixEnd_6690295 : Nat := 4983230072969 + 3 ^ 40 * 6690295 * 2
def baseEnd_6690295 : Nat := 3435337055372006923744399

theorem tailTrace_6690295 : CollatzResearch.WordTrace tailWord_6690295 prefixEnd_6690295 3435337055372006923744399 := by
  unfold tailWord_6690295
  simp only [CollatzResearch.WordTrace]
  refine ⟨244015105297211301263168339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162676736864807534175445559 244015105297211301263168339)
  ·
    refine ⟨366022657945816951894752509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244015105297211301263168339 366022657945816951894752509)
    ·
      refine ⟨137258496729681356960532191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366022657945816951894752509 137258496729681356960532191)
      ·
        refine ⟨205887745094522035440798287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137258496729681356960532191 205887745094522035440798287)
        ·
          refine ⟨308831617641783053161197431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205887745094522035440798287 308831617641783053161197431)
          ·
            refine ⟨463247426462674579741796147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308831617641783053161197431 463247426462674579741796147)
            ·
              refine ⟨694871139694011869612694221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463247426462674579741796147 694871139694011869612694221)
              ·
                refine ⟨260576677385254451104760333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 694871139694011869612694221 260576677385254451104760333)
                ·
                  refine ⟨97716254019470419164285125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260576677385254451104760333 97716254019470419164285125)
                  ·
                    refine ⟨18321797628650703593303461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97716254019470419164285125 18321797628650703593303461)
                    ·
                      refine ⟨3435337055372006923744399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18321797628650703593303461 3435337055372006923744399)
                      ·
                        rfl

theorem cell23_6690295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_6690295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690295 prefixEnd_6690295 := by exact prefixLift 6690295
  have htrace : WordTrace (prefixWord ++ tailWord_6690295) baseStart_6690295 baseEnd_6690295 := by
    simpa [prefixWord, tailWord_6690295, baseEnd_6690295] using wordTrace_append hprefix tailTrace_6690295
  have hstable : (prefixWord ++ tailWord_6690295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690295).length < 2 ^ (prefixWord ++ tailWord_6690295).sum := by decide
  have hdescent : baseEnd_6690295 < baseStart_6690295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690345 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 1, 8, 5]
def baseStart_6690345 : Nat := 118140960795 + 6690345 * 2 ^ 59
def prefixEnd_6690345 : Nat := 4983230072969 + 3 ^ 40 * 6690345 * 2
def baseEnd_6690345 : Nat := 3435362729404731728119169

theorem tailTrace_6690345 : CollatzResearch.WordTrace tailWord_6690345 prefixEnd_6690345 3435362729404731728119169 := by
  unfold tailWord_6690345
  simp only [CollatzResearch.WordTrace]
  refine ⟨244016928947030159802488489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162677952631353439868325659 244016928947030159802488489)
  ·
    refine ⟨183012696710272619851866367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244016928947030159802488489 183012696710272619851866367)
    ·
      refine ⟨274519045065408929777799551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183012696710272619851866367 274519045065408929777799551)
      ·
        refine ⟨411778567598113394666699327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274519045065408929777799551 411778567598113394666699327)
        ·
          refine ⟨617667851397170092000048991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411778567598113394666699327 617667851397170092000048991)
          ·
            refine ⟨926501777095755138000073487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617667851397170092000048991 926501777095755138000073487)
            ·
              refine ⟨1389752665643632707000110231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926501777095755138000073487 1389752665643632707000110231)
              ·
                refine ⟨2084628998465449060500165347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1389752665643632707000110231 2084628998465449060500165347)
                ·
                  refine ⟨3126943497698173590750248021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2084628998465449060500165347 3126943497698173590750248021)
                  ·
                    refine ⟨36643869113650471766604469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3126943497698173590750248021 36643869113650471766604469)
                    ·
                      refine ⟨3435362729404731728119169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36643869113650471766604469 3435362729404731728119169)
                      ·
                        rfl

theorem cell23_6690345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_6690345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690345 prefixEnd_6690345 := by exact prefixLift 6690345
  have htrace : WordTrace (prefixWord ++ tailWord_6690345) baseStart_6690345 baseEnd_6690345 := by
    simpa [prefixWord, tailWord_6690345, baseEnd_6690345] using wordTrace_append hprefix tailTrace_6690345
  have hstable : (prefixWord ++ tailWord_6690345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690345).length < 2 ^ (prefixWord ++ tailWord_6690345).sum := by decide
  have hdescent : baseEnd_6690345 < baseStart_6690345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690446 : List Nat := [4, 1, 1, 3, 1, 2, 4, 1, 6]
def baseStart_6690446 : Nat := 118140960795 + 6690446 * 2 ^ 59
def prefixEnd_6690446 : Nat := 4983230072969 + 3 ^ 40 * 6690446 * 2
def baseEnd_6690446 : Nat := 381712732327870648106245

theorem tailTrace_6690446 : CollatzResearch.WordTrace tailWord_6690446 prefixEnd_6690446 381712732327870648106245 := by
  unfold tailWord_6690446
  simp only [CollatzResearch.WordTrace]
  refine ⟨30502576589958031756489399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162680408479776169367943461 30502576589958031756489399)
  ·
    refine ⟨45753864884937047634734099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30502576589958031756489399 45753864884937047634734099)
    ·
      refine ⟨68630797327405571452101149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45753864884937047634734099 68630797327405571452101149)
      ·
        refine ⟨25736548997777089294537931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68630797327405571452101149 25736548997777089294537931)
        ·
          refine ⟨38604823496665633941806897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25736548997777089294537931 38604823496665633941806897)
          ·
            refine ⟨28953617622499225456355173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38604823496665633941806897 28953617622499225456355173)
            ·
              refine ⟨5428803304218604773066595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28953617622499225456355173 5428803304218604773066595)
              ·
                refine ⟨8143204956327907159599893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5428803304218604773066595 8143204956327907159599893)
                ·
                  refine ⟨381712732327870648106245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8143204956327907159599893 381712732327870648106245)
                  ·
                    rfl

theorem cell23_6690446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_6690446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690446 prefixEnd_6690446 := by exact prefixLift 6690446
  have htrace : WordTrace (prefixWord ++ tailWord_6690446) baseStart_6690446 baseEnd_6690446 := by
    simpa [prefixWord, tailWord_6690446, baseEnd_6690446] using wordTrace_append hprefix tailTrace_6690446
  have hstable : (prefixWord ++ tailWord_6690446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690446).length < 2 ^ (prefixWord ++ tailWord_6690446).sum := by decide
  have hdescent : baseEnd_6690446 < baseStart_6690446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690449 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 1, 5, 2]
def baseStart_6690449 : Nat := 118140960795 + 6690449 * 2 ^ 59
def prefixEnd_6690449 : Nat := 4983230072969 + 3 ^ 40 * 6690449 * 2
def baseEnd_6690449 : Nat := 3435416131392799321218691

theorem tailTrace_6690449 : CollatzResearch.WordTrace tailWord_6690449 prefixEnd_6690449 3435416131392799321218691 := by
  unfold tailWord_6690449
  simp only [CollatzResearch.WordTrace]
  refine ⟨244020722138653385564274401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162680481425768923709516267 244020722138653385564274401)
  ·
    refine ⟨183015541603990039173205801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244020722138653385564274401 183015541603990039173205801)
    ·
      refine ⟨137261656202992529379904351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183015541603990039173205801 137261656202992529379904351)
      ·
        refine ⟨205892484304488794069856527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137261656202992529379904351 205892484304488794069856527)
        ·
          refine ⟨308838726456733191104784791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205892484304488794069856527 308838726456733191104784791)
          ·
            refine ⟨463258089685099786657177187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308838726456733191104784791 463258089685099786657177187)
            ·
              refine ⟨694887134527649679985765781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463258089685099786657177187 694887134527649679985765781)
              ·
                refine ⟨32572834430983578749332771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 694887134527649679985765781 32572834430983578749332771)
                ·
                  refine ⟨48859251646475368123999157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32572834430983578749332771 48859251646475368123999157)
                  ·
                    refine ⟨4580554841857065761624921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48859251646475368123999157 4580554841857065761624921)
                    ·
                      refine ⟨3435416131392799321218691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4580554841857065761624921 3435416131392799321218691)
                      ·
                        rfl

theorem cell23_6690449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 5, 2].length) (baseStart_6690449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690449 prefixEnd_6690449 := by exact prefixLift 6690449
  have htrace : WordTrace (prefixWord ++ tailWord_6690449) baseStart_6690449 baseEnd_6690449 := by
    simpa [prefixWord, tailWord_6690449, baseEnd_6690449] using wordTrace_append hprefix tailTrace_6690449
  have hstable : (prefixWord ++ tailWord_6690449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690449).length < 2 ^ (prefixWord ++ tailWord_6690449).sum := by decide
  have hdescent : baseEnd_6690449 < baseStart_6690449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690489 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 4, 4]
def baseStart_6690489 : Nat := 118140960795 + 6690489 * 2 ^ 59
def prefixEnd_6690489 : Nat := 4983230072969 + 3 ^ 40 * 6690489 * 2
def baseEnd_6690489 : Nat := 1145145556872993054906169

theorem tailTrace_6690489 : CollatzResearch.WordTrace tailWord_6690489 prefixEnd_6690489 1145145556872993054906169 := by
  unfold tailWord_6690489
  simp only [CollatzResearch.WordTrace]
  refine ⟨244022181058508472395730521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162681454039005648263820347 244022181058508472395730521)
  ·
    refine ⟨183016635793881354296797891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244022181058508472395730521 183016635793881354296797891)
    ·
      refine ⟨274524953690822031445196837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183016635793881354296797891 274524953690822031445196837)
      ·
        refine ⟨51473428817029130895974407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274524953690822031445196837 51473428817029130895974407)
        ·
          refine ⟨77210143225543696343961611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51473428817029130895974407 77210143225543696343961611)
          ·
            refine ⟨115815214838315544515942417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77210143225543696343961611 115815214838315544515942417)
            ·
              refine ⟨86861411128736658386956813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115815214838315544515942417 86861411128736658386956813)
              ·
                refine ⟨32573029173276246895108805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86861411128736658386956813 32573029173276246895108805)
                ·
                  refine ⟨6107442969989296292832901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32573029173276246895108805 6107442969989296292832901)
                  ·
                    refine ⟨1145145556872993054906169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6107442969989296292832901 1145145556872993054906169)
                    ·
                      rfl

theorem cell23_6690489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 4].length) (baseStart_6690489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690489 prefixEnd_6690489 := by exact prefixLift 6690489
  have htrace : WordTrace (prefixWord ++ tailWord_6690489) baseStart_6690489 baseEnd_6690489 := by
    simpa [prefixWord, tailWord_6690489, baseEnd_6690489] using wordTrace_append hprefix tailTrace_6690489
  have hstable : (prefixWord ++ tailWord_6690489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690489).length < 2 ^ (prefixWord ++ tailWord_6690489).sum := by decide
  have hdescent : baseEnd_6690489 < baseStart_6690489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690490 : List Nat := [3, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3]
def baseStart_6690490 : Nat := 118140960795 + 6690490 * 2 ^ 59
def prefixEnd_6690490 : Nat := 4983230072969 + 3 ^ 40 * 6690490 * 2
def baseEnd_6690490 : Nat := 3435437184099633660806003

theorem tailTrace_6690490 : CollatzResearch.WordTrace tailWord_6690490 prefixEnd_6690490 3435437184099633660806003 := by
  unfold tailWord_6690490
  simp only [CollatzResearch.WordTrace]
  refine ⟨61005554382876212391629231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162681478354336566377677949 61005554382876212391629231)
  ·
    refine ⟨91508331574314318587443847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61005554382876212391629231 91508331574314318587443847)
    ·
      refine ⟨137262497361471477881165771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91508331574314318587443847 137262497361471477881165771)
      ·
        refine ⟨205893746042207216821748657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137262497361471477881165771 205893746042207216821748657)
        ·
          refine ⟨154420309531655412616311493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205893746042207216821748657 154420309531655412616311493)
          ·
            refine ⟨28953808037185389865558405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154420309531655412616311493 28953808037185389865558405)
            ·
              refine ⟨5428839006972260599792201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28953808037185389865558405 5428839006972260599792201)
              ·
                refine ⟨4071629255229195449844151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5428839006972260599792201 4071629255229195449844151)
                ·
                  refine ⟨6107443882843793174766227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4071629255229195449844151 6107443882843793174766227)
                  ·
                    refine ⟨9161165824265689762149341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6107443882843793174766227 9161165824265689762149341)
                    ·
                      refine ⟨3435437184099633660806003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9161165824265689762149341 3435437184099633660806003)
                      ·
                        rfl

theorem cell23_6690490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3].length) (baseStart_6690490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690490 prefixEnd_6690490 := by exact prefixLift 6690490
  have htrace : WordTrace (prefixWord ++ tailWord_6690490) baseStart_6690490 baseEnd_6690490 := by
    simpa [prefixWord, tailWord_6690490, baseEnd_6690490] using wordTrace_append hprefix tailTrace_6690490
  have hstable : (prefixWord ++ tailWord_6690490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690490).length < 2 ^ (prefixWord ++ tailWord_6690490).sum := by decide
  have hdescent : baseEnd_6690490 < baseStart_6690490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690506 : List Nat := [3, 1, 2, 1, 5, 1, 2, 1, 1, 6]
def baseStart_6690506 : Nat := 118140960795 + 6690506 * 2 ^ 59
def prefixEnd_6690506 : Nat := 4983230072969 + 3 ^ 40 * 6690506 * 2
def baseEnd_6690506 : Nat := 1145148466596701866068643

theorem tailTrace_6690506 : CollatzResearch.WordTrace tailWord_6690506 prefixEnd_6690506 1145148466596701866068643 := by
  unfold tailWord_6690506
  simp only [CollatzResearch.WordTrace]
  refine ⟨61005700274861721074774843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162681867399631256199399581 61005700274861721074774843)
  ·
    refine ⟨91508550412292581612162265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61005700274861721074774843 91508550412292581612162265)
    ·
      refine ⟨68631412809219436209121699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91508550412292581612162265 68631412809219436209121699)
      ·
        refine ⟨102947119213829154313682549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68631412809219436209121699 102947119213829154313682549)
        ·
          refine ⟨9651292426296483216907739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102947119213829154313682549 9651292426296483216907739)
          ·
            refine ⟨14476938639444724825361609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9651292426296483216907739 14476938639444724825361609)
            ·
              refine ⟨10857703979583543619021207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14476938639444724825361609 10857703979583543619021207)
              ·
                refine ⟨16286555969375315428531811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10857703979583543619021207 16286555969375315428531811)
                ·
                  refine ⟨24429833954062973142797717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16286555969375315428531811 24429833954062973142797717)
                  ·
                    refine ⟨1145148466596701866068643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24429833954062973142797717 1145148466596701866068643)
                    ·
                      rfl

theorem cell23_6690506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_6690506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690506 prefixEnd_6690506 := by exact prefixLift 6690506
  have htrace : WordTrace (prefixWord ++ tailWord_6690506) baseStart_6690506 baseEnd_6690506 := by
    simpa [prefixWord, tailWord_6690506, baseEnd_6690506] using wordTrace_append hprefix tailTrace_6690506
  have hstable : (prefixWord ++ tailWord_6690506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690506).length < 2 ^ (prefixWord ++ tailWord_6690506).sum := by decide
  have hdescent : baseEnd_6690506 < baseStart_6690506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690513 : List Nat := [1, 2, 2, 1, 2, 5, 1, 2, 3, 2, 2]
def baseStart_6690513 : Nat := 118140960795 + 6690513 * 2 ^ 59
def prefixEnd_6690513 : Nat := 4983230072969 + 3 ^ 40 * 6690513 * 2
def baseEnd_6690513 : Nat := 3435448994154687070818397

theorem tailTrace_6690513 : CollatzResearch.WordTrace tailWord_6690513 prefixEnd_6690513 3435448994154687070818397 := by
  unfold tailWord_6690513
  simp only [CollatzResearch.WordTrace]
  refine ⟨244023056410421524494604193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162682037606947682996402795 244023056410421524494604193)
  ·
    refine ⟨183017292307816143370953145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244023056410421524494604193 183017292307816143370953145)
    ·
      refine ⟨137262969230862107528214859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183017292307816143370953145 137262969230862107528214859)
      ·
        refine ⟨205894453846293161292322289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137262969230862107528214859 205894453846293161292322289)
        ·
          refine ⟨154420840384719870969241717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205894453846293161292322289 154420840384719870969241717)
          ·
            refine ⟨14476953786067487903366411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 154420840384719870969241717 14476953786067487903366411)
            ·
              refine ⟨21715430679101231855049617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14476953786067487903366411 21715430679101231855049617)
              ·
                refine ⟨16286573009325923891287213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21715430679101231855049617 16286573009325923891287213)
                ·
                  refine ⟨6107464878497221459232705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16286573009325923891287213 6107464878497221459232705)
                  ·
                    refine ⟨4580598658872916094424529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6107464878497221459232705 4580598658872916094424529)
                    ·
                      refine ⟨3435448994154687070818397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4580598658872916094424529 3435448994154687070818397)
                      ·
                        rfl

theorem cell23_6690513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 2, 2].length) (baseStart_6690513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690513 prefixEnd_6690513 := by exact prefixLift 6690513
  have htrace : WordTrace (prefixWord ++ tailWord_6690513) baseStart_6690513 baseEnd_6690513 := by
    simpa [prefixWord, tailWord_6690513, baseEnd_6690513] using wordTrace_append hprefix tailTrace_6690513
  have hstable : (prefixWord ++ tailWord_6690513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690513).length < 2 ^ (prefixWord ++ tailWord_6690513).sum := by decide
  have hdescent : baseEnd_6690513 < baseStart_6690513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690519 : List Nat := [1, 1, 3, 2, 1, 3, 5, 7]
def baseStart_6690519 : Nat := 118140960795 + 6690519 * 2 ^ 59
def prefixEnd_6690519 : Nat := 4983230072969 + 3 ^ 40 * 6690519 * 2
def baseEnd_6690519 : Nat := 127238965742170890642347

theorem tailTrace_6690519 : CollatzResearch.WordTrace tailWord_6690519 prefixEnd_6690519 127238965742170890642347 := by
  unfold tailWord_6690519
  simp only [CollatzResearch.WordTrace]
  refine ⟨244023275248399787519322611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162682183498933191679548407 244023275248399787519322611)
  ·
    refine ⟨366034912872599681278983917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244023275248399787519322611 366034912872599681278983917)
    ·
      refine ⟨137263092327224880479618969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366034912872599681278983917 137263092327224880479618969)
      ·
        refine ⟨102947319245418660359714227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137263092327224880479618969 102947319245418660359714227)
        ·
          refine ⟨154420978868127990539571341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102947319245418660359714227 154420978868127990539571341)
          ·
            refine ⟨57907867075547996452339253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154420978868127990539571341 57907867075547996452339253)
            ·
              refine ⟨5428862538332624667406805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57907867075547996452339253 5428862538332624667406805)
              ·
                refine ⟨127238965742170890642347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5428862538332624667406805 127238965742170890642347)
                ·
                  rfl

theorem cell23_6690519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 7].length) (baseStart_6690519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690519 prefixEnd_6690519 := by exact prefixLift 6690519
  have htrace : WordTrace (prefixWord ++ tailWord_6690519) baseStart_6690519 baseEnd_6690519 := by
    simpa [prefixWord, tailWord_6690519, baseEnd_6690519] using wordTrace_append hprefix tailTrace_6690519
  have hstable : (prefixWord ++ tailWord_6690519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690519).length < 2 ^ (prefixWord ++ tailWord_6690519).sum := by decide
  have hdescent : baseEnd_6690519 < baseStart_6690519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690614 : List Nat := [5, 1, 2, 2, 1, 3, 2, 1, 2, 1, 3]
def baseStart_6690614 : Nat := 118140960795 + 6690614 * 2 ^ 59
def prefixEnd_6690614 : Nat := 4983230072969 + 3 ^ 40 * 6690614 * 2
def baseEnd_6690614 : Nat := 3435500855700791175655433

theorem tailTrace_6690614 : CollatzResearch.WordTrace tailWord_6690614 prefixEnd_6690614 3435500855700791175655433 := by
  unfold tailWord_6690614
  simp only [CollatzResearch.WordTrace]
  refine ⟨15251671261440976171501931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162684493455370412496020597 15251671261440976171501931)
  ·
    refine ⟨22877506892161464257252897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15251671261440976171501931 22877506892161464257252897)
    ·
      refine ⟨17158130169121098192939673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22877506892161464257252897 17158130169121098192939673)
      ·
        refine ⟨12868597626840823644704755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17158130169121098192939673 12868597626840823644704755)
        ·
          refine ⟨19302896440261235467057133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12868597626840823644704755 19302896440261235467057133)
          ·
            refine ⟨7238586165097963300146425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19302896440261235467057133 7238586165097963300146425)
            ·
              refine ⟨5428939623823472475109819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7238586165097963300146425 5428939623823472475109819)
              ·
                refine ⟨8143409435735208712664729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5428939623823472475109819 8143409435735208712664729)
                ·
                  refine ⟨6107557076801406534498547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8143409435735208712664729 6107557076801406534498547)
                  ·
                    refine ⟨9161335615202109801747821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6107557076801406534498547 9161335615202109801747821)
                    ·
                      refine ⟨3435500855700791175655433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9161335615202109801747821 3435500855700791175655433)
                      ·
                        rfl

theorem cell23_6690614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_6690614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690614 prefixEnd_6690614 := by exact prefixLift 6690614
  have htrace : WordTrace (prefixWord ++ tailWord_6690614) baseStart_6690614 baseEnd_6690614 := by
    simpa [prefixWord, tailWord_6690614, baseEnd_6690614] using wordTrace_append hprefix tailTrace_6690614
  have hstable : (prefixWord ++ tailWord_6690614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690614).length < 2 ^ (prefixWord ++ tailWord_6690614).sum := by decide
  have hdescent : baseEnd_6690614 < baseStart_6690614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690649 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 3, 2, 5]
def baseStart_6690649 : Nat := 118140960795 + 6690649 * 2 ^ 59
def prefixEnd_6690649 : Nat := 4983230072969 + 3 ^ 40 * 6690649 * 2
def baseEnd_6690649 : Nat := 3435518827523698538717771

theorem tailTrace_6690649 : CollatzResearch.WordTrace tailWord_6690649 prefixEnd_6690649 3435518827523698538717771 := by
  unfold tailWord_6690649
  simp only [CollatzResearch.WordTrace]
  refine ⟨244028016737928819721555001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162685344491952546481036667 244028016737928819721555001)
  ·
    refine ⟨183021012553446614791166251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244028016737928819721555001 183021012553446614791166251)
    ·
      refine ⟨274531518830169922186749377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183021012553446614791166251 274531518830169922186749377)
      ·
        refine ⟨205898639122627441640062033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274531518830169922186749377 205898639122627441640062033)
        ·
          refine ⟨154423979341970581230046525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205898639122627441640062033 154423979341970581230046525)
          ·
            refine ⟨57908992253238967961267447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154423979341970581230046525 57908992253238967961267447)
            ·
              refine ⟨86863488379858451941901171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57908992253238967961267447 86863488379858451941901171)
              ·
                refine ⟨130295232569787677912851757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86863488379858451941901171 130295232569787677912851757)
                ·
                  refine ⟨48860712213670379217319409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130295232569787677912851757 48860712213670379217319409)
                  ·
                    refine ⟨36645534160252784412989557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48860712213670379217319409 36645534160252784412989557)
                    ·
                      refine ⟨3435518827523698538717771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36645534160252784412989557 3435518827523698538717771)
                      ·
                        rfl

theorem cell23_6690649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_6690649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690649 prefixEnd_6690649 := by exact prefixLift 6690649
  have htrace : WordTrace (prefixWord ++ tailWord_6690649) baseStart_6690649 baseEnd_6690649 := by
    simpa [prefixWord, tailWord_6690649, baseEnd_6690649] using wordTrace_append hprefix tailTrace_6690649
  have hstable : (prefixWord ++ tailWord_6690649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690649).length < 2 ^ (prefixWord ++ tailWord_6690649).sum := by decide
  have hdescent : baseEnd_6690649 < baseStart_6690649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690656 : List Nat := [2, 1, 1, 3, 3, 2, 2, 2, 2, 5]
def baseStart_6690656 : Nat := 118140960795 + 6690656 * 2 ^ 59
def prefixEnd_6690656 : Nat := 4983230072969 + 3 ^ 40 * 6690656 * 2
def baseEnd_6690656 : Nat := 1145174140629426670443413

theorem tailTrace_6690656 : CollatzResearch.WordTrace tailWord_6690656 prefixEnd_6690656 1145174140629426670443413 := by
  unfold tailWord_6690656
  simp only [CollatzResearch.WordTrace]
  refine ⟨122014136024451729958529911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162685514699268973278039881 122014136024451729958529911)
  ·
    refine ⟨183021204036677594937794867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122014136024451729958529911 183021204036677594937794867)
    ·
      refine ⟨274531806055016392406692301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183021204036677594937794867 274531806055016392406692301)
      ·
        refine ⟨102949427270631147152509613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274531806055016392406692301 102949427270631147152509613)
        ·
          refine ⟨38606035226486680182191105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102949427270631147152509613 38606035226486680182191105)
          ·
            refine ⟨28954526419865010136643329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38606035226486680182191105 28954526419865010136643329)
            ·
              refine ⟨21715894814898757602482497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28954526419865010136643329 21715894814898757602482497)
              ·
                refine ⟨16286921111174068201861873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21715894814898757602482497 16286921111174068201861873)
                ·
                  refine ⟨12215190833380551151396405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16286921111174068201861873 12215190833380551151396405)
                  ·
                    refine ⟨1145174140629426670443413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12215190833380551151396405 1145174140629426670443413)
                    ·
                      rfl

theorem cell23_6690656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 2, 5].length) (baseStart_6690656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690656 prefixEnd_6690656 := by exact prefixLift 6690656
  have htrace : WordTrace (prefixWord ++ tailWord_6690656) baseStart_6690656 baseEnd_6690656 := by
    simpa [prefixWord, tailWord_6690656, baseEnd_6690656] using wordTrace_append hprefix tailTrace_6690656
  have hstable : (prefixWord ++ tailWord_6690656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690656).length < 2 ^ (prefixWord ++ tailWord_6690656).sum := by decide
  have hdescent : baseEnd_6690656 < baseStart_6690656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690699 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 8]
def baseStart_6690699 : Nat := 118140960795 + 6690699 * 2 ^ 59
def prefixEnd_6690699 : Nat := 4983230072969 + 3 ^ 40 * 6690699 * 2
def baseEnd_6690699 : Nat := 381727166839602593676949

theorem tailTrace_6690699 : CollatzResearch.WordTrace tailWord_6690699 prefixEnd_6690699 381727166839602593676949 := by
  unfold tailWord_6690699
  simp only [CollatzResearch.WordTrace]
  refine ⟨244029840387747678260875151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162686560258498452173916767 244029840387747678260875151)
  ·
    refine ⟨366044760581621517391312727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244029840387747678260875151 366044760581621517391312727)
    ·
      refine ⟨549067140872432276086969091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366044760581621517391312727 549067140872432276086969091)
      ·
        refine ⟨823600711308648414130453637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549067140872432276086969091 823600711308648414130453637)
        ·
          refine ⟨154425133370371577649460057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 823600711308648414130453637 154425133370371577649460057)
          ·
            refine ⟨115818850027778683237095043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154425133370371577649460057 115818850027778683237095043)
            ·
              refine ⟨173728275041668024855642565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115818850027778683237095043 173728275041668024855642565)
              ·
                refine ⟨32574051570312754660432981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173728275041668024855642565 32574051570312754660432981)
                ·
                  refine ⟨381727166839602593676949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32574051570312754660432981 381727166839602593676949)
                  ·
                    rfl

theorem cell23_6690699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 8].length) (baseStart_6690699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690699 prefixEnd_6690699 := by exact prefixLift 6690699
  have htrace : WordTrace (prefixWord ++ tailWord_6690699) baseStart_6690699 baseEnd_6690699 := by
    simpa [prefixWord, tailWord_6690699, baseEnd_6690699] using wordTrace_append hprefix tailTrace_6690699
  have hstable : (prefixWord ++ tailWord_6690699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690699).length < 2 ^ (prefixWord ++ tailWord_6690699).sum := by decide
  have hdescent : baseEnd_6690699 < baseStart_6690699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690729 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 2, 9]
def baseStart_6690729 : Nat := 118140960795 + 6690729 * 2 ^ 59
def prefixEnd_6690729 : Nat := 4983230072969 + 3 ^ 40 * 6690729 * 2
def baseEnd_6690729 : Nat := 1145186635325352741905801

theorem tailTrace_6690729 : CollatzResearch.WordTrace tailWord_6690729 prefixEnd_6690729 1145186635325352741905801 := by
  unfold tailWord_6690729
  simp only [CollatzResearch.WordTrace]
  refine ⟨244030934577638993384467241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162687289718425995589644827 244030934577638993384467241)
  ·
    refine ⟨183023200933229245038350431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244030934577638993384467241 183023200933229245038350431)
    ·
      refine ⟨274534801399843867557525647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183023200933229245038350431 274534801399843867557525647)
      ·
        refine ⟨411802202099765801336288471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274534801399843867557525647 411802202099765801336288471)
        ·
          refine ⟨617703303149648702004432707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411802202099765801336288471 617703303149648702004432707)
          ·
            refine ⟨926554954724473053006649061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617703303149648702004432707 926554954724473053006649061)
            ·
              refine ⟨173729054010838697438746699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 926554954724473053006649061 173729054010838697438746699)
              ·
                refine ⟨260593581016258046158120049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173729054010838697438746699 260593581016258046158120049)
                ·
                  refine ⟨195445185762193534618590037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260593581016258046158120049 195445185762193534618590037)
                  ·
                    refine ⟨1145186635325352741905801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 195445185762193534618590037 1145186635325352741905801)
                    ·
                      rfl

theorem cell23_6690729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 9].length) (baseStart_6690729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690729 prefixEnd_6690729 := by exact prefixLift 6690729
  have htrace : WordTrace (prefixWord ++ tailWord_6690729) baseStart_6690729 baseEnd_6690729 := by
    simpa [prefixWord, tailWord_6690729, baseEnd_6690729] using wordTrace_append hprefix tailTrace_6690729
  have hstable : (prefixWord ++ tailWord_6690729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690729).length < 2 ^ (prefixWord ++ tailWord_6690729).sum := by decide
  have hdescent : baseEnd_6690729 < baseStart_6690729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690777 : List Nat := [1, 2, 1, 2, 6, 2, 1, 1, 3, 1, 3]
def baseStart_6690777 : Nat := 118140960795 + 6690777 * 2 ^ 59
def prefixEnd_6690777 : Nat := 4983230072969 + 3 ^ 40 * 6690777 * 2
def baseEnd_6690777 : Nat := 3435584553047474037917183

theorem tailTrace_6690777 : CollatzResearch.WordTrace tailWord_6690777 prefixEnd_6690777 3435584553047474037917183 := by
  unfold tailWord_6690777
  simp only [CollatzResearch.WordTrace]
  refine ⟨244032685281465097582214585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162688456854310065054809723 244032685281465097582214585)
  ·
    refine ⟨183024513961098823186660939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244032685281465097582214585 183024513961098823186660939)
    ·
      refine ⟨274536770941648234779991409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183024513961098823186660939 274536770941648234779991409)
      ·
        refine ⟨205902578206236176084993557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274536770941648234779991409 205902578206236176084993557)
        ·
          refine ⟨9651683353417320753984073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 205902578206236176084993557 9651683353417320753984073)
          ·
            refine ⟨7238762515062990565488055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9651683353417320753984073 7238762515062990565488055)
            ·
              refine ⟨10858143772594485848232083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7238762515062990565488055 10858143772594485848232083)
              ·
                refine ⟨16287215658891728772348125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10858143772594485848232083 16287215658891728772348125)
                ·
                  refine ⟨6107705872084398289630547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16287215658891728772348125 6107705872084398289630547)
                  ·
                    refine ⟨9161558808126597434445821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6107705872084398289630547 9161558808126597434445821)
                    ·
                      refine ⟨3435584553047474037917183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9161558808126597434445821 3435584553047474037917183)
                      ·
                        rfl

theorem cell23_6690777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 1, 3].length) (baseStart_6690777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690777 prefixEnd_6690777 := by exact prefixLift 6690777
  have htrace : WordTrace (prefixWord ++ tailWord_6690777) baseStart_6690777 baseEnd_6690777 := by
    simpa [prefixWord, tailWord_6690777, baseEnd_6690777] using wordTrace_append hprefix tailTrace_6690777
  have hstable : (prefixWord ++ tailWord_6690777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690777).length < 2 ^ (prefixWord ++ tailWord_6690777).sum := by decide
  have hdescent : baseEnd_6690777 < baseStart_6690777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690796 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 4]
def baseStart_6690796 : Nat := 118140960795 + 6690796 * 2 ^ 59
def prefixEnd_6690796 : Nat := 4983230072969 + 3 ^ 40 * 6690796 * 2
def baseEnd_6690796 : Nat := 3435594309179909463579595

theorem tailTrace_6690796 : CollatzResearch.WordTrace tailWord_6690796 prefixEnd_6690796 3435594309179909463579595 := by
  unfold tailWord_6690796
  simp only [CollatzResearch.WordTrace]
  refine ⟨122016689134198131913578121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162688918845597509218104161 122016689134198131913578121)
  ·
    refine ⟨91512516850648598935183591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122016689134198131913578121 91512516850648598935183591)
    ·
      refine ⟨137268775275972898402775387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91512516850648598935183591 137268775275972898402775387)
      ·
        refine ⟨205903162913959347604163081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137268775275972898402775387 205903162913959347604163081)
        ·
          refine ⟨154427372185469510703122311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205903162913959347604163081 154427372185469510703122311)
          ·
            refine ⟨231641058278204266054683467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154427372185469510703122311 231641058278204266054683467)
            ·
              refine ⟨347461587417306399082025201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231641058278204266054683467 347461587417306399082025201)
              ·
                refine ⟨260596190562979799311518901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347461587417306399082025201 260596190562979799311518901)
                ·
                  refine ⟨24430892865279356185454897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 260596190562979799311518901 24430892865279356185454897)
                  ·
                    refine ⟨18323169648959517139091173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24430892865279356185454897 18323169648959517139091173)
                    ·
                      refine ⟨3435594309179909463579595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18323169648959517139091173 3435594309179909463579595)
                      ·
                        rfl

theorem cell23_6690796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_6690796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690796 prefixEnd_6690796 := by exact prefixLift 6690796
  have htrace : WordTrace (prefixWord ++ tailWord_6690796) baseStart_6690796 baseEnd_6690796 := by
    simpa [prefixWord, tailWord_6690796, baseEnd_6690796] using wordTrace_append hprefix tailTrace_6690796
  have hstable : (prefixWord ++ tailWord_6690796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690796).length < 2 ^ (prefixWord ++ tailWord_6690796).sum := by decide
  have hdescent : baseEnd_6690796 < baseStart_6690796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690800 : List Nat := [2, 1, 1, 1, 3, 2, 2, 4, 3, 2, 2]
def baseStart_6690800 : Nat := 118140960795 + 6690800 * 2 ^ 59
def prefixEnd_6690800 : Nat := 4983230072969 + 3 ^ 40 * 6690800 * 2
def baseEnd_6690800 : Nat := 3435596363102527447929577

theorem tailTrace_6690800 : CollatzResearch.WordTrace tailWord_6690800 prefixEnd_6690800 3435596363102527447929577 := by
  unfold tailWord_6690800
  simp only [CollatzResearch.WordTrace]
  refine ⟨122016762080190886255150927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162689016106921181673534569 122016762080190886255150927)
  ·
    refine ⟨183025143120286329382726391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122016762080190886255150927 183025143120286329382726391)
    ·
      refine ⟨274537714680429494074089587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183025143120286329382726391 274537714680429494074089587)
      ·
        refine ⟨411806572020644241111134381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274537714680429494074089587 411806572020644241111134381)
        ·
          refine ⟨154427464507741590416675393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 411806572020644241111134381 154427464507741590416675393)
          ·
            refine ⟨115820598380806192812506545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154427464507741590416675393 115820598380806192812506545)
            ·
              refine ⟨86865448785604644609379909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115820598380806192812506545 86865448785604644609379909)
              ·
                refine ⟨16287271647300870864258733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86865448785604644609379909 16287271647300870864258733)
                ·
                  refine ⟨6107726867737826574097025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16287271647300870864258733 6107726867737826574097025)
                  ·
                    refine ⟨4580795150803369930572769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6107726867737826574097025 4580795150803369930572769)
                    ·
                      refine ⟨3435596363102527447929577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4580795150803369930572769 3435596363102527447929577)
                      ·
                        rfl

theorem cell23_6690800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 3, 2, 2].length) (baseStart_6690800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690800 prefixEnd_6690800 := by exact prefixLift 6690800
  have htrace : WordTrace (prefixWord ++ tailWord_6690800) baseStart_6690800 baseEnd_6690800 := by
    simpa [prefixWord, tailWord_6690800, baseEnd_6690800] using wordTrace_append hprefix tailTrace_6690800
  have hstable : (prefixWord ++ tailWord_6690800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690800).length < 2 ^ (prefixWord ++ tailWord_6690800).sum := by decide
  have hdescent : baseEnd_6690800 < baseStart_6690800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690822 : List Nat := [6, 2, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_6690822 : Nat := 118140960795 + 6690822 * 2 ^ 59
def prefixEnd_6690822 : Nat := 4983230072969 + 3 ^ 40 * 6690822 * 2
def baseEnd_6690822 : Nat := 1145202553225642120618159

theorem tailTrace_6690822 : CollatzResearch.WordTrace tailWord_6690822 prefixEnd_6690822 1145202553225642120618159 := by
  unfold tailWord_6690822
  simp only [CollatzResearch.WordTrace]
  refine ⟨7626072705196939695862585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 162689551044201380178401813 7626072705196939695862585)
  ·
    refine ⟨5719554528897704771896939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7626072705196939695862585 5719554528897704771896939)
    ·
      refine ⟨8579331793346557157845409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5719554528897704771896939 8579331793346557157845409)
      ·
        refine ⟨6434498845009917868384057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8579331793346557157845409 6434498845009917868384057)
        ·
          refine ⟨4825874133757438401288043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6434498845009917868384057 4825874133757438401288043)
          ·
            refine ⟨7238811200636157601932065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4825874133757438401288043 7238811200636157601932065)
            ·
              refine ⟨5429108400477118201449049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7238811200636157601932065 5429108400477118201449049)
              ·
                refine ⟨4071831300357838651086787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5429108400477118201449049 4071831300357838651086787)
                ·
                  refine ⟨6107746950536757976630181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4071831300357838651086787 6107746950536757976630181)
                  ·
                    refine ⟨1145202553225642120618159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6107746950536757976630181 1145202553225642120618159)
                    ·
                      rfl

theorem cell23_6690822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_6690822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690822 prefixEnd_6690822 := by exact prefixLift 6690822
  have htrace : WordTrace (prefixWord ++ tailWord_6690822) baseStart_6690822 baseEnd_6690822 := by
    simpa [prefixWord, tailWord_6690822, baseEnd_6690822] using wordTrace_append hprefix tailTrace_6690822
  have hstable : (prefixWord ++ tailWord_6690822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690822).length < 2 ^ (prefixWord ++ tailWord_6690822).sum := by decide
  have hdescent : baseEnd_6690822 < baseStart_6690822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690850 : List Nat := [3, 3, 1, 1, 1, 2, 4, 1, 1, 3, 3]
def baseStart_6690850 : Nat := 118140960795 + 6690850 * 2 ^ 59
def prefixEnd_6690850 : Nat := 4983230072969 + 3 ^ 40 * 6690850 * 2
def baseEnd_6690850 : Nat := 3435622037135252252304347

theorem tailTrace_6690850 : CollatzResearch.WordTrace tailWord_6690850 prefixEnd_6690850 3435622037135252252304347 := by
  unfold tailWord_6690850
  simp only [CollatzResearch.WordTrace]
  refine ⟨61008836952550157762405501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162690231873467087366414669 61008836952550157762405501)
  ·
    refine ⟨22878313857206309160902063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61008836952550157762405501 22878313857206309160902063)
    ·
      refine ⟨34317470785809463741353095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22878313857206309160902063 34317470785809463741353095)
      ·
        refine ⟨51476206178714195612029643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34317470785809463741353095 51476206178714195612029643)
        ·
          refine ⟨77214309268071293418044465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51476206178714195612029643 77214309268071293418044465)
          ·
            refine ⟨57910731951053470063533349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77214309268071293418044465 57910731951053470063533349)
            ·
              refine ⟨10858262240822525636912503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57910731951053470063533349 10858262240822525636912503)
              ·
                refine ⟨16287393361233788455368755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10858262240822525636912503 16287393361233788455368755)
                ·
                  refine ⟨24431090041850682683053133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16287393361233788455368755 24431090041850682683053133)
                  ·
                    refine ⟨9161658765694006006144925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24431090041850682683053133 9161658765694006006144925)
                    ·
                      refine ⟨3435622037135252252304347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9161658765694006006144925 3435622037135252252304347)
                      ·
                        rfl

theorem cell23_6690850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_6690850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690850 prefixEnd_6690850 := by exact prefixLift 6690850
  have htrace : WordTrace (prefixWord ++ tailWord_6690850) baseStart_6690850 baseEnd_6690850 := by
    simpa [prefixWord, tailWord_6690850, baseEnd_6690850] using wordTrace_append hprefix tailTrace_6690850
  have hstable : (prefixWord ++ tailWord_6690850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690850).length < 2 ^ (prefixWord ++ tailWord_6690850).sum := by decide
  have hdescent : baseEnd_6690850 < baseStart_6690850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690868 : List Nat := [2, 5, 1, 2, 2, 1, 2, 3, 1, 2, 2]
def baseStart_6690868 : Nat := 118140960795 + 6690868 * 2 ^ 59
def prefixEnd_6690868 : Nat := 4983230072969 + 3 ^ 40 * 6690868 * 2
def baseEnd_6690868 : Nat := 3435631279787033181879265

theorem tailTrace_6690868 : CollatzResearch.WordTrace tailWord_6690868 prefixEnd_6690868 3435631279787033181879265 := by
  unfold tailWord_6690868
  simp only [CollatzResearch.WordTrace]
  refine ⟨122018002162067710061888629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162690669549423613415851505 122018002162067710061888629)
  ·
    refine ⟨11439187702693847818302059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122018002162067710061888629 11439187702693847818302059)
    ·
      refine ⟨17158781554040771727453089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11439187702693847818302059 17158781554040771727453089)
      ·
        refine ⟨12869086165530578795589817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17158781554040771727453089 12869086165530578795589817)
        ·
          refine ⟨9651814624147934096692363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12869086165530578795589817 9651814624147934096692363)
          ·
            refine ⟨14477721936221901145038545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9651814624147934096692363 14477721936221901145038545)
            ·
              refine ⟨10858291452166425858778909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14477721936221901145038545 10858291452166425858778909)
              ·
                refine ⟨4071859294562409697042091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10858291452166425858778909 4071859294562409697042091)
                ·
                  refine ⟨6107788941843614545563137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4071859294562409697042091 6107788941843614545563137)
                  ·
                    refine ⟨4580841706382710909172353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6107788941843614545563137 4580841706382710909172353)
                    ·
                      refine ⟨3435631279787033181879265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4580841706382710909172353 3435631279787033181879265)
                      ·
                        rfl

theorem cell23_6690868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_6690868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690868 prefixEnd_6690868 := by exact prefixLift 6690868
  have htrace : WordTrace (prefixWord ++ tailWord_6690868) baseStart_6690868 baseEnd_6690868 := by
    simpa [prefixWord, tailWord_6690868, baseEnd_6690868] using wordTrace_append hprefix tailTrace_6690868
  have hstable : (prefixWord ++ tailWord_6690868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690868).length < 2 ^ (prefixWord ++ tailWord_6690868).sum := by decide
  have hdescent : baseEnd_6690868 < baseStart_6690868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690877 : List Nat := [1, 4, 1, 3, 1, 1, 3, 3, 1, 3, 2]
def baseStart_6690877 : Nat := 118140960795 + 6690877 * 2 ^ 59
def prefixEnd_6690877 : Nat := 4983230072969 + 3 ^ 40 * 6690877 * 2
def baseEnd_6690877 : Nat := 3435635901112923646666723

theorem tailTrace_6690877 : CollatzResearch.WordTrace tailWord_6690877 prefixEnd_6690877 3435635901112923646666723 := by
  unfold tailWord_6690877
  simp only [CollatzResearch.WordTrace]
  refine ⟨244036332581102814660854885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162690888387401876440569923 244036332581102814660854885)
  ·
    refine ⟨45756812358956777748910291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244036332581102814660854885 45756812358956777748910291)
    ·
      refine ⟨68635218538435166623365437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45756812358956777748910291 68635218538435166623365437)
      ·
        refine ⟨25738206951913187483762039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68635218538435166623365437 25738206951913187483762039)
        ·
          refine ⟨38607310427869781225643059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25738206951913187483762039 38607310427869781225643059)
          ·
            refine ⟨57910965641804671838464589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38607310427869781225643059 57910965641804671838464589)
            ·
              refine ⟨21716612115676751939424221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57910965641804671838464589 21716612115676751939424221)
              ·
                refine ⟨8143729543378781977284083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21716612115676751939424221 8143729543378781977284083)
                ·
                  refine ⟨12215594315068172965926125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8143729543378781977284083 12215594315068172965926125)
                  ·
                    refine ⟨4580847868150564862222297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12215594315068172965926125 4580847868150564862222297)
                    ·
                      refine ⟨3435635901112923646666723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4580847868150564862222297 3435635901112923646666723)
                      ·
                        rfl

theorem cell23_6690877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_6690877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690877 prefixEnd_6690877 := by exact prefixLift 6690877
  have htrace : WordTrace (prefixWord ++ tailWord_6690877) baseStart_6690877 baseEnd_6690877 := by
    simpa [prefixWord, tailWord_6690877, baseEnd_6690877] using wordTrace_append hprefix tailTrace_6690877
  have hstable : (prefixWord ++ tailWord_6690877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690877).length < 2 ^ (prefixWord ++ tailWord_6690877).sum := by decide
  have hdescent : baseEnd_6690877 < baseStart_6690877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690903 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 4]
def baseStart_6690903 : Nat := 118140960795 + 6690903 * 2 ^ 59
def prefixEnd_6690903 : Nat := 4983230072969 + 3 ^ 40 * 6690903 * 2
def baseEnd_6690903 : Nat := 3435649251609940544941603

theorem tailTrace_6690903 : CollatzResearch.WordTrace tailWord_6690903 prefixEnd_6690903 3435649251609940544941603 := by
  unfold tailWord_6690903
  simp only [CollatzResearch.WordTrace]
  refine ⟨244037280879008621101301363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162691520586005747400867575 244037280879008621101301363)
  ·
    refine ⟨366055921318512931651952045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244037280879008621101301363 366055921318512931651952045)
    ·
      refine ⟨137270970494442349369482017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366055921318512931651952045 137270970494442349369482017)
      ·
        refine ⟨102953227870831762027111513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137270970494442349369482017 102953227870831762027111513)
        ·
          refine ⟨77214920903123821520333635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102953227870831762027111513 77214920903123821520333635)
          ·
            refine ⟨115822381354685732280500453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77214920903123821520333635 115822381354685732280500453)
            ·
              refine ⟨21716696504003574802593835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115822381354685732280500453 21716696504003574802593835)
              ·
                refine ⟨32575044756005362203890753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21716696504003574802593835 32575044756005362203890753)
                ·
                  refine ⟨24431283567004021652918065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32575044756005362203890753 24431283567004021652918065)
                  ·
                    refine ⟨18323462675253016239688549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24431283567004021652918065 18323462675253016239688549)
                    ·
                      refine ⟨3435649251609940544941603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18323462675253016239688549 3435649251609940544941603)
                      ·
                        rfl

theorem cell23_6690903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_6690903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690903 prefixEnd_6690903 := by exact prefixLift 6690903
  have htrace : WordTrace (prefixWord ++ tailWord_6690903) baseStart_6690903 baseEnd_6690903 := by
    simpa [prefixWord, tailWord_6690903, baseEnd_6690903] using wordTrace_append hprefix tailTrace_6690903
  have hstable : (prefixWord ++ tailWord_6690903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690903).length < 2 ^ (prefixWord ++ tailWord_6690903).sum := by decide
  have hdescent : baseEnd_6690903 < baseStart_6690903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690947 : List Nat := [1, 1, 1, 3, 3, 4, 3, 2, 5]
def baseStart_6690947 : Nat := 118140960795 + 6690947 * 2 ^ 59
def prefixEnd_6690947 : Nat := 4983230072969 + 3 ^ 40 * 6690947 * 2
def baseEnd_6690947 : Nat := 381741316084304263643489

theorem tailTrace_6690947 : CollatzResearch.WordTrace tailWord_6690947 prefixEnd_6690947 381741316084304263643489 := by
  unfold tailWord_6690947
  simp only [CollatzResearch.WordTrace]
  refine ⟨244038885690849216615903095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162692590460566144410602063 244038885690849216615903095)
  ·
    refine ⟨366058328536273824923854643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244038885690849216615903095 366058328536273824923854643)
    ·
      refine ⟨549087492804410737385781965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366058328536273824923854643 549087492804410737385781965)
      ·
        refine ⟨205907809801654026519668237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 549087492804410737385781965 205907809801654026519668237)
        ·
          refine ⟨77215428675620259944875589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205907809801654026519668237 77215428675620259944875589)
          ·
            refine ⟨14477892876678798739664173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77215428675620259944875589 14477892876678798739664173)
            ·
              refine ⟨5429209828754549527374065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14477892876678798739664173 5429209828754549527374065)
              ·
                refine ⟨4071907371565912145530549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5429209828754549527374065 4071907371565912145530549)
                ·
                  refine ⟨381741316084304263643489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4071907371565912145530549 381741316084304263643489)
                  ·
                    rfl

theorem cell23_6690947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 5].length) (baseStart_6690947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690947 prefixEnd_6690947 := by exact prefixLift 6690947
  have htrace : WordTrace (prefixWord ++ tailWord_6690947) baseStart_6690947 baseEnd_6690947 := by
    simpa [prefixWord, tailWord_6690947, baseEnd_6690947] using wordTrace_append hprefix tailTrace_6690947
  have hstable : (prefixWord ++ tailWord_6690947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690947).length < 2 ^ (prefixWord ++ tailWord_6690947).sum := by decide
  have hdescent : baseEnd_6690947 < baseStart_6690947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690953 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 1, 2, 5]
def baseStart_6690953 : Nat := 118140960795 + 6690953 * 2 ^ 59
def prefixEnd_6690953 : Nat := 4983230072969 + 3 ^ 40 * 6690953 * 2
def baseEnd_6690953 : Nat := 3435674925642665349316373

theorem tailTrace_6690953 : CollatzResearch.WordTrace tailWord_6690953 prefixEnd_6690953 3435674925642665349316373 := by
  unfold tailWord_6690953
  simp only [CollatzResearch.WordTrace]
  refine ⟨244039104528827479640621513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162692736352551653093747675 244039104528827479640621513)
  ·
    refine ⟨183029328396620609730466135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244039104528827479640621513 183029328396620609730466135)
    ·
      refine ⟨274543992594930914595699203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183029328396620609730466135 274543992594930914595699203)
      ·
        refine ⟨411815988892396371893548805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274543992594930914595699203 411815988892396371893548805)
        ·
          refine ⟨77215497917324319730040401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 411815988892396371893548805 77215497917324319730040401)
          ·
            refine ⟨57911623437993239797530301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77215497917324319730040401 57911623437993239797530301)
            ·
              refine ⟨21716858789247464924073863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57911623437993239797530301 21716858789247464924073863)
              ·
                refine ⟨32575288183871197386110795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21716858789247464924073863 32575288183871197386110795)
                ·
                  refine ⟨48862932275806796079166193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32575288183871197386110795 48862932275806796079166193)
                  ·
                    refine ⟨36647199206855097059374645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48862932275806796079166193 36647199206855097059374645)
                    ·
                      refine ⟨3435674925642665349316373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36647199206855097059374645 3435674925642665349316373)
                      ·
                        rfl

theorem cell23_6690953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 2, 5].length) (baseStart_6690953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690953 prefixEnd_6690953 := by exact prefixLift 6690953
  have htrace : WordTrace (prefixWord ++ tailWord_6690953) baseStart_6690953 baseEnd_6690953 := by
    simpa [prefixWord, tailWord_6690953, baseEnd_6690953] using wordTrace_append hprefix tailTrace_6690953
  have hstable : (prefixWord ++ tailWord_6690953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690953).length < 2 ^ (prefixWord ++ tailWord_6690953).sum := by decide
  have hdescent : baseEnd_6690953 < baseStart_6690953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690958 : List Nat := [4, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2]
def baseStart_6690958 : Nat := 118140960795 + 6690958 * 2 ^ 59
def prefixEnd_6690958 : Nat := 4983230072969 + 3 ^ 40 * 6690958 * 2
def baseEnd_6690958 : Nat := 3435677493045937829753851

theorem tailTrace_6690958 : CollatzResearch.WordTrace tailWord_6690958 prefixEnd_6690958 3435677493045937829753851 := by
  unfold tailWord_6690958
  simp only [CollatzResearch.WordTrace]
  refine ⟨30504910861726170686819191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162692857929206243663035685 30504910861726170686819191)
  ·
    refine ⟨45757366292589256030228787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30504910861726170686819191 45757366292589256030228787)
    ·
      refine ⟨68636049438883884045343181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45757366292589256030228787 68636049438883884045343181)
      ·
        refine ⟨25738518539581456517003693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68636049438883884045343181 25738518539581456517003693)
        ·
          refine ⟨9651944452343046193876385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25738518539581456517003693 9651944452343046193876385)
          ·
            refine ⟨7238958339257284645407289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9651944452343046193876385 7238958339257284645407289)
            ·
              refine ⟨5429218754442963484055467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7238958339257284645407289 5429218754442963484055467)
              ·
                refine ⟨8143828131664445226083201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5429218754442963484055467 8143828131664445226083201)
                ·
                  refine ⟨6107871098748333919562401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8143828131664445226083201 6107871098748333919562401)
                  ·
                    refine ⟨4580903324061250439671801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6107871098748333919562401 4580903324061250439671801)
                    ·
                      refine ⟨3435677493045937829753851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4580903324061250439671801 3435677493045937829753851)
                      ·
                        rfl

theorem cell23_6690958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_6690958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690958 prefixEnd_6690958 := by exact prefixLift 6690958
  have htrace : WordTrace (prefixWord ++ tailWord_6690958) baseStart_6690958 baseEnd_6690958 := by
    simpa [prefixWord, tailWord_6690958, baseEnd_6690958] using wordTrace_append hprefix tailTrace_6690958
  have hstable : (prefixWord ++ tailWord_6690958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690958).length < 2 ^ (prefixWord ++ tailWord_6690958).sum := by decide
  have hdescent : baseEnd_6690958 < baseStart_6690958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6690963 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 4]
def baseStart_6690963 : Nat := 118140960795 + 6690963 * 2 ^ 59
def prefixEnd_6690963 : Nat := 4983230072969 + 3 ^ 40 * 6690963 * 2
def baseEnd_6690963 : Nat := 3435680060449210310191327

theorem tailTrace_6690963 : CollatzResearch.WordTrace tailWord_6690963 prefixEnd_6690963 3435680060449210310191327 := by
  unfold tailWord_6690963
  simp only [CollatzResearch.WordTrace]
  refine ⟨244039469258791251348485543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162692979505860834232323695 244039469258791251348485543)
  ·
    refine ⟨366059203888186877022728315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244039469258791251348485543 366059203888186877022728315)
    ·
      refine ⟨549088805832280315534092473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366059203888186877022728315 549088805832280315534092473)
      ·
        refine ⟨411816604374210236650569355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 549088805832280315534092473 411816604374210236650569355)
        ·
          refine ⟨617724906561315354975854033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411816604374210236650569355 617724906561315354975854033)
          ·
            refine ⟨463293679920986516231890525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 617724906561315354975854033 463293679920986516231890525)
            ·
              refine ⟨173735129970369943586958947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 463293679920986516231890525 173735129970369943586958947)
              ·
                refine ⟨260602694955554915380438421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173735129970369943586958947 260602694955554915380438421)
                ·
                  refine ⟨12215751326041636658458051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 260602694955554915380438421 12215751326041636658458051)
                  ·
                    refine ⟨18323626989062454987687077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12215751326041636658458051 18323626989062454987687077)
                    ·
                      refine ⟨3435680060449210310191327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18323626989062454987687077 3435680060449210310191327)
                      ·
                        rfl

theorem cell23_6690963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 4].length) (baseStart_6690963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6690963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6690963 prefixEnd_6690963 := by exact prefixLift 6690963
  have htrace : WordTrace (prefixWord ++ tailWord_6690963) baseStart_6690963 baseEnd_6690963 := by
    simpa [prefixWord, tailWord_6690963, baseEnd_6690963] using wordTrace_append hprefix tailTrace_6690963
  have hstable : (prefixWord ++ tailWord_6690963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6690963).length < 2 ^ (prefixWord ++ tailWord_6690963).sum := by decide
  have hdescent : baseEnd_6690963 < baseStart_6690963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6690963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691000 : List Nat := [2, 1, 2, 1, 2, 1, 3, 4, 2, 2, 3]
def baseStart_6691000 : Nat := 118140960795 + 6691000 * 2 ^ 59
def prefixEnd_6691000 : Nat := 4983230072969 + 3 ^ 40 * 6691000 * 2
def baseEnd_6691000 : Nat := 3435699059233426665428657

theorem tailTrace_6691000 : CollatzResearch.WordTrace tailWord_6691000 prefixEnd_6691000 3435699059233426665428657 := by
  unfold tailWord_6691000
  simp only [CollatzResearch.WordTrace]
  refine ⟨122020409379828603333791227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162693879173104804445054969 122020409379828603333791227)
  ·
    refine ⟨183030614069742905000686841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122020409379828603333791227 183030614069742905000686841)
    ·
      refine ⟨137272960552307178750515131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183030614069742905000686841 137272960552307178750515131)
      ·
        refine ⟨205909440828460768125772697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137272960552307178750515131 205909440828460768125772697)
        ·
          refine ⟨154432080621345576094329523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205909440828460768125772697 154432080621345576094329523)
          ·
            refine ⟨231648120932018364141494285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154432080621345576094329523 231648120932018364141494285)
            ·
              refine ⟨86868045349506886553060357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231648120932018364141494285 86868045349506886553060357)
              ·
                refine ⟨16287758503032541228698817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86868045349506886553060357 16287758503032541228698817)
                ·
                  refine ⟨12215818877274405921524113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16287758503032541228698817 12215818877274405921524113)
                  ·
                    refine ⟨9161864157955804441143085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12215818877274405921524113 9161864157955804441143085)
                    ·
                      refine ⟨3435699059233426665428657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9161864157955804441143085 3435699059233426665428657)
                      ·
                        rfl

theorem cell23_6691000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 2, 2, 3].length) (baseStart_6691000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691000 prefixEnd_6691000 := by exact prefixLift 6691000
  have htrace : WordTrace (prefixWord ++ tailWord_6691000) baseStart_6691000 baseEnd_6691000 := by
    simpa [prefixWord, tailWord_6691000, baseEnd_6691000] using wordTrace_append hprefix tailTrace_6691000
  have hstable : (prefixWord ++ tailWord_6691000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691000).length < 2 ^ (prefixWord ++ tailWord_6691000).sum := by decide
  have hdescent : baseEnd_6691000 < baseStart_6691000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691057 : List Nat := [1, 2, 2, 2, 2, 1, 2, 4, 2, 3, 2]
def baseStart_6691057 : Nat := 118140960795 + 6691057 * 2 ^ 59
def prefixEnd_6691057 : Nat := 4983230072969 + 3 ^ 40 * 6691057 * 2
def baseEnd_6691057 : Nat := 3435728327630732942415895

theorem tailTrace_6691057 : CollatzResearch.WordTrace tailWord_6691057 prefixEnd_6691057 3435728327630732942415895 := by
  unfold tailWord_6691057
  simp only [CollatzResearch.WordTrace]
  refine ⟨244042897720450705402407425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162695265146967136934938283 244042897720450705402407425)
  ·
    refine ⟨183032173290338029051805569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244042897720450705402407425 183032173290338029051805569)
    ·
      refine ⟨137274129967753521788854177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183032173290338029051805569 137274129967753521788854177)
      ·
        refine ⟨102955597475815141341640633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137274129967753521788854177 102955597475815141341640633)
        ·
          refine ⟨77216698106861356006230475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102955597475815141341640633 77216698106861356006230475)
          ·
            refine ⟨115825047160292034009345713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77216698106861356006230475 115825047160292034009345713)
            ·
              refine ⟨86868785370219025507009285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115825047160292034009345713 86868785370219025507009285)
              ·
                refine ⟨16287897256916067282564241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86868785370219025507009285 16287897256916067282564241)
                ·
                  refine ⟨12215922942687050461923181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16287897256916067282564241 12215922942687050461923181)
                  ·
                    refine ⟨4580971103507643923221193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12215922942687050461923181 4580971103507643923221193)
                    ·
                      refine ⟨3435728327630732942415895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4580971103507643923221193 3435728327630732942415895)
                      ·
                        rfl

theorem cell23_6691057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 3, 2].length) (baseStart_6691057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691057 prefixEnd_6691057 := by exact prefixLift 6691057
  have htrace : WordTrace (prefixWord ++ tailWord_6691057) baseStart_6691057 baseEnd_6691057 := by
    simpa [prefixWord, tailWord_6691057, baseEnd_6691057] using wordTrace_append hprefix tailTrace_6691057
  have hstable : (prefixWord ++ tailWord_6691057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691057).length < 2 ^ (prefixWord ++ tailWord_6691057).sum := by decide
  have hdescent : baseEnd_6691057 < baseStart_6691057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691074 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 1, 5, 2]
def baseStart_6691074 : Nat := 118140960795 + 6691074 * 2 ^ 59
def prefixEnd_6691074 : Nat := 4983230072969 + 3 ^ 40 * 6691074 * 2
def baseEnd_6691074 : Nat := 3435737056801859375903317

theorem tailTrace_6691074 : CollatzResearch.WordTrace tailWord_6691074 prefixEnd_6691074 3435737056801859375903317 := by
  unfold tailWord_6691074
  simp only [CollatzResearch.WordTrace]
  refine ⟨61010879440347279326444069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162695678507592744870517517 61010879440347279326444069)
  ·
    refine ⟨11439539895065114873708263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61010879440347279326444069 11439539895065114873708263)
    ·
      refine ⟨17159309842597672310562395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11439539895065114873708263 17159309842597672310562395)
      ·
        refine ⟨25738964763896508465843593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17159309842597672310562395 25738964763896508465843593)
        ·
          refine ⟨19304223572922381349382695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25738964763896508465843593 19304223572922381349382695)
          ·
            refine ⟨28956335359383572024074043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19304223572922381349382695 28956335359383572024074043)
            ·
              refine ⟨43434503039075358036111065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28956335359383572024074043 43434503039075358036111065)
              ·
                refine ⟨32575877279306518527083299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43434503039075358036111065 32575877279306518527083299)
                ·
                  refine ⟨48863815918959777790624949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32575877279306518527083299 48863815918959777790624949)
                  ·
                    refine ⟨4580982742402479167871089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48863815918959777790624949 4580982742402479167871089)
                    ·
                      refine ⟨3435737056801859375903317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4580982742402479167871089 3435737056801859375903317)
                      ·
                        rfl

theorem cell23_6691074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_6691074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691074 prefixEnd_6691074 := by exact prefixLift 6691074
  have htrace : WordTrace (prefixWord ++ tailWord_6691074) baseStart_6691074 baseEnd_6691074 := by
    simpa [prefixWord, tailWord_6691074, baseEnd_6691074] using wordTrace_append hprefix tailTrace_6691074
  have hstable : (prefixWord ++ tailWord_6691074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691074).length < 2 ^ (prefixWord ++ tailWord_6691074).sum := by decide
  have hdescent : baseEnd_6691074 < baseStart_6691074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691098 : List Nat := [3, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3]
def baseStart_6691098 : Nat := 118140960795 + 6691098 * 2 ^ 59
def prefixEnd_6691098 : Nat := 4983230072969 + 3 ^ 40 * 6691098 * 2
def baseEnd_6691098 : Nat := 3435749380337567282003207

theorem tailTrace_6691098 : CollatzResearch.WordTrace tailWord_6691098 prefixEnd_6691098 3435749380337567282003207 := by
  unfold tailWord_6691098
  simp only [CollatzResearch.WordTrace]
  refine ⟨61011098278325542351162487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162696262075534779603099965 61011098278325542351162487)
  ·
    refine ⟨91516647417488313526743731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61011098278325542351162487 91516647417488313526743731)
    ·
      refine ⟨137274971126232470290115597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91516647417488313526743731 137274971126232470290115597)
      ·
        refine ⟨51478114172337176358793349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137274971126232470290115597 51478114172337176358793349)
        ·
          refine ⟨9652146407313220567273753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51478114172337176358793349 9652146407313220567273753)
          ·
            refine ⟨7239109805484915425455315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9652146407313220567273753 7239109805484915425455315)
            ·
              refine ⟨10858664708227373138182973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7239109805484915425455315 10858664708227373138182973)
              ·
                refine ⟨4071999265585264926818615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10858664708227373138182973 4071999265585264926818615)
                ·
                  refine ⟨6107998898377897390227923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4071999265585264926818615 6107998898377897390227923)
                  ·
                    refine ⟨9161998347566846085341885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6107998898377897390227923 9161998347566846085341885)
                    ·
                      refine ⟨3435749380337567282003207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9161998347566846085341885 3435749380337567282003207)
                      ·
                        rfl

theorem cell23_6691098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_6691098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691098 prefixEnd_6691098 := by exact prefixLift 6691098
  have htrace : WordTrace (prefixWord ++ tailWord_6691098) baseStart_6691098 baseEnd_6691098 := by
    simpa [prefixWord, tailWord_6691098, baseEnd_6691098] using wordTrace_append hprefix tailTrace_6691098
  have hstable : (prefixWord ++ tailWord_6691098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691098).length < 2 ^ (prefixWord ++ tailWord_6691098).sum := by decide
  have hdescent : baseEnd_6691098 < baseStart_6691098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691100 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_6691100 : Nat := 118140960795 + 6691100 * 2 ^ 59
def prefixEnd_6691100 : Nat := 4983230072969 + 3 ^ 40 * 6691100 * 2
def baseEnd_6691100 : Nat := 3435750407298876274178197

theorem tailTrace_6691100 : CollatzResearch.WordTrace tailWord_6691100 prefixEnd_6691100 3435750407298876274178197 := by
  unfold tailWord_6691100
  simp only [CollatzResearch.WordTrace]
  refine ⟨122022233029647461873111377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162696310706196615830815169 122022233029647461873111377)
  ·
    refine ⟨91516674772235596404833533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122022233029647461873111377 91516674772235596404833533)
    ·
      refine ⟨34318753039588348651812575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91516674772235596404833533 34318753039588348651812575)
      ·
        refine ⟨51478129559382522977718863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34318753039588348651812575 51478129559382522977718863)
        ·
          refine ⟨77217194339073784466578295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51478129559382522977718863 77217194339073784466578295)
          ·
            refine ⟨115825791508610676699867443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77217194339073784466578295 115825791508610676699867443)
            ·
              refine ⟨173738687262916015049801165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115825791508610676699867443 173738687262916015049801165)
              ·
                refine ⟨65152007723593505643675437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173738687262916015049801165 65152007723593505643675437)
                ·
                  refine ⟨24432002896347564616378289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65152007723593505643675437 24432002896347564616378289)
                  ·
                    refine ⟨18324002172260673462283717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24432002896347564616378289 18324002172260673462283717)
                    ·
                      refine ⟨3435750407298876274178197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18324002172260673462283717 3435750407298876274178197)
                      ·
                        rfl

theorem cell23_6691100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_6691100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691100 prefixEnd_6691100 := by exact prefixLift 6691100
  have htrace : WordTrace (prefixWord ++ tailWord_6691100) baseStart_6691100 baseEnd_6691100 := by
    simpa [prefixWord, tailWord_6691100, baseEnd_6691100] using wordTrace_append hprefix tailTrace_6691100
  have hstable : (prefixWord ++ tailWord_6691100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691100).length < 2 ^ (prefixWord ++ tailWord_6691100).sum := by decide
  have hdescent : baseEnd_6691100 < baseStart_6691100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691107 : List Nat := [1, 1, 1, 4, 2, 2, 1, 5, 1, 2, 3]
def baseStart_6691107 : Nat := 118140960795 + 6691107 * 2 ^ 59
def prefixEnd_6691107 : Nat := 4983230072969 + 3 ^ 40 * 6691107 * 2
def baseEnd_6691107 : Nat := 3435754001663457746790665

theorem tailTrace_6691107 : CollatzResearch.WordTrace tailWord_6691107 prefixEnd_6691107 3435754001663457746790665 := by
  unfold tailWord_6691107
  simp only [CollatzResearch.WordTrace]
  refine ⟨244044721370269563941727575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162696480913513042627818383 244044721370269563941727575)
  ·
    refine ⟨366067082055404345912591363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244044721370269563941727575 366067082055404345912591363)
    ·
      refine ⟨549100623083106518868887045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366067082055404345912591363 549100623083106518868887045)
      ·
        refine ⟨102956366828082472287916321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 549100623083106518868887045 102956366828082472287916321)
        ·
          refine ⟨77217275121061854215937241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102956366828082472287916321 77217275121061854215937241)
          ·
            refine ⟨57912956340796390661952931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77217275121061854215937241 57912956340796390661952931)
            ·
              refine ⟨86869434511194585992929397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57912956340796390661952931 86869434511194585992929397)
              ·
                refine ⟨8144009485424492436837131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86869434511194585992929397 8144009485424492436837131)
                ·
                  refine ⟨12216014228136738655255697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8144009485424492436837131 12216014228136738655255697)
                  ·
                    refine ⟨9162010671102553991441773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12216014228136738655255697 9162010671102553991441773)
                    ·
                      refine ⟨3435754001663457746790665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9162010671102553991441773 3435754001663457746790665)
                      ·
                        rfl

theorem cell23_6691107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_6691107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691107 prefixEnd_6691107 := by exact prefixLift 6691107
  have htrace : WordTrace (prefixWord ++ tailWord_6691107) baseStart_6691107 baseEnd_6691107 := by
    simpa [prefixWord, tailWord_6691107, baseEnd_6691107] using wordTrace_append hprefix tailTrace_6691107
  have hstable : (prefixWord ++ tailWord_6691107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691107).length < 2 ^ (prefixWord ++ tailWord_6691107).sum := by decide
  have hdescent : baseEnd_6691107 < baseStart_6691107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691120 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 3]
def baseStart_6691120 : Nat := 118140960795 + 6691120 * 2 ^ 59
def prefixEnd_6691120 : Nat := 4983230072969 + 3 ^ 40 * 6691120 * 2
def baseEnd_6691120 : Nat := 3435760676911966195928105

theorem tailTrace_6691120 : CollatzResearch.WordTrace tailWord_6691120 prefixEnd_6691120 3435760676911966195928105 := by
  unfold tailWord_6691120
  simp only [CollatzResearch.WordTrace]
  refine ⟨122022597759611233580975407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162696797012814978107967209 122022597759611233580975407)
  ·
    refine ⟨183033896639416850371463111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122022597759611233580975407 183033896639416850371463111)
    ·
      refine ⟨274550844959125275557194667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183033896639416850371463111 274550844959125275557194667)
      ·
        refine ⟨411826267438687913335792001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274550844959125275557194667 411826267438687913335792001)
        ·
          refine ⟨308869700579015935001844001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411826267438687913335792001 308869700579015935001844001)
          ·
            refine ⟨231652275434261951251383001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308869700579015935001844001 231652275434261951251383001)
            ·
              refine ⟨173739206575696463438537251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231652275434261951251383001 173739206575696463438537251)
              ·
                refine ⟨260608809863544695157805877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173739206575696463438537251 260608809863544695157805877)
                ·
                  refine ⟨24432075924707315171044301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 260608809863544695157805877 24432075924707315171044301)
                  ·
                    refine ⟨9162028471765243189141613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24432075924707315171044301 9162028471765243189141613)
                    ·
                      refine ⟨3435760676911966195928105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9162028471765243189141613 3435760676911966195928105)
                      ·
                        rfl

theorem cell23_6691120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 3].length) (baseStart_6691120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691120 prefixEnd_6691120 := by exact prefixLift 6691120
  have htrace : WordTrace (prefixWord ++ tailWord_6691120) baseStart_6691120 baseEnd_6691120 := by
    simpa [prefixWord, tailWord_6691120, baseEnd_6691120] using wordTrace_append hprefix tailTrace_6691120
  have hstable : (prefixWord ++ tailWord_6691120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691120).length < 2 ^ (prefixWord ++ tailWord_6691120).sum := by decide
  have hdescent : baseEnd_6691120 < baseStart_6691120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691150 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5]
def baseStart_6691150 : Nat := 118140960795 + 6691150 * 2 ^ 59
def prefixEnd_6691150 : Nat := 4983230072969 + 3 ^ 40 * 6691150 * 2
def baseEnd_6691150 : Nat := 3435776081331601078552967

theorem tailTrace_6691150 : CollatzResearch.WordTrace tailWord_6691150 prefixEnd_6691150 3435776081331601078552967 := by
  unfold tailWord_6691150
  simp only [CollatzResearch.WordTrace]
  refine ⟨30505786213639222785692863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162697526472742521523695269 30505786213639222785692863)
  ·
    refine ⟨45758679320458834178539295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30505786213639222785692863 45758679320458834178539295)
    ·
      refine ⟨68638018980688251267808943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45758679320458834178539295 68638018980688251267808943)
      ·
        refine ⟨102957028471032376901713415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68638018980688251267808943 102957028471032376901713415)
        ·
          refine ⟨154435542706548565352570123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102957028471032376901713415 154435542706548565352570123)
          ·
            refine ⟨231653314059822848028855185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154435542706548565352570123 231653314059822848028855185)
            ·
              refine ⟨173739985544867136021641389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231653314059822848028855185 173739985544867136021641389)
              ·
                refine ⟨65152494579325176008115521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173739985544867136021641389 65152494579325176008115521)
                ·
                  refine ⟨48864370934493882006086641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65152494579325176008115521 48864370934493882006086641)
                  ·
                    refine ⟨36648278200870411504564981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48864370934493882006086641 36648278200870411504564981)
                    ·
                      refine ⟨3435776081331601078552967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36648278200870411504564981 3435776081331601078552967)
                      ·
                        rfl

theorem cell23_6691150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_6691150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691150 prefixEnd_6691150 := by exact prefixLift 6691150
  have htrace : WordTrace (prefixWord ++ tailWord_6691150) baseStart_6691150 baseEnd_6691150 := by
    simpa [prefixWord, tailWord_6691150, baseEnd_6691150] using wordTrace_append hprefix tailTrace_6691150
  have hstable : (prefixWord ++ tailWord_6691150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691150).length < 2 ^ (prefixWord ++ tailWord_6691150).sum := by decide
  have hdescent : baseEnd_6691150 < baseStart_6691150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691166 : List Nat := [4, 4, 2, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_6691166 : Nat := 118140960795 + 6691166 * 2 ^ 59
def prefixEnd_6691166 : Nat := 4983230072969 + 3 ^ 40 * 6691166 * 2
def baseEnd_6691166 : Nat := 3435784297022073015952895

theorem tailTrace_6691166 : CollatzResearch.WordTrace tailWord_6691166 prefixEnd_6691166 3435784297022073015952895 := by
  unfold tailWord_6691166
  simp only [CollatzResearch.WordTrace]
  refine ⟨30505859159631977127265669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162697915518037211345416901 30505859159631977127265669)
  ·
    refine ⟨5719848592430995711362313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30505859159631977127265669 5719848592430995711362313)
    ·
      refine ⟨4289886444323246783521735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5719848592430995711362313 4289886444323246783521735)
      ·
        refine ⟨6434829666484870175282603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4289886444323246783521735 6434829666484870175282603)
        ·
          refine ⟨9652244499727305262923905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6434829666484870175282603 9652244499727305262923905)
          ·
            refine ⟨7239183374795478947192929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9652244499727305262923905 7239183374795478947192929)
            ·
              refine ⟨5429387531096609210394697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7239183374795478947192929 5429387531096609210394697)
              ·
                refine ⟨4072040648322456907796023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5429387531096609210394697 4072040648322456907796023)
                ·
                  refine ⟨6108060972483685361694035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4072040648322456907796023 6108060972483685361694035)
                  ·
                    refine ⟨9162091458725528042541053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6108060972483685361694035 9162091458725528042541053)
                    ·
                      refine ⟨3435784297022073015952895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9162091458725528042541053 3435784297022073015952895)
                      ·
                        rfl

theorem cell23_6691166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_6691166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691166 prefixEnd_6691166 := by exact prefixLift 6691166
  have htrace : WordTrace (prefixWord ++ tailWord_6691166) baseStart_6691166 baseEnd_6691166 := by
    simpa [prefixWord, tailWord_6691166, baseEnd_6691166] using wordTrace_append hprefix tailTrace_6691166
  have hstable : (prefixWord ++ tailWord_6691166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691166).length < 2 ^ (prefixWord ++ tailWord_6691166).sum := by decide
  have hdescent : baseEnd_6691166 < baseStart_6691166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691177 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 3, 4, 2]
def baseStart_6691177 : Nat := 118140960795 + 6691177 * 2 ^ 59
def prefixEnd_6691177 : Nat := 4983230072969 + 3 ^ 40 * 6691177 * 2
def baseEnd_6691177 : Nat := 3435789945309272472915343

theorem tailTrace_6691177 : CollatzResearch.WordTrace tailWord_6691177 prefixEnd_6691177 3435789945309272472915343 := by
  unfold tailWord_6691177
  simp only [CollatzResearch.WordTrace]
  refine ⟨244047274480015965896775785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162698182986677310597850523 244047274480015965896775785)
  ·
    refine ⟨183035455860011974422581839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244047274480015965896775785 183035455860011974422581839)
    ·
      refine ⟨274553183790017961633872759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183035455860011974422581839 274553183790017961633872759)
      ·
        refine ⟨411829775685026942450809139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274553183790017961633872759 411829775685026942450809139)
        ·
          refine ⟨617744663527540413676213709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411829775685026942450809139 617744663527540413676213709)
          ·
            refine ⟨231654248822827655128580141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 617744663527540413676213709 231654248822827655128580141)
            ·
              refine ⟨86870343308560370673217553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231654248822827655128580141 86870343308560370673217553)
              ·
                refine ⟨65152757481420278004913165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86870343308560370673217553 65152757481420278004913165)
                ·
                  refine ⟨24432284055532604251842437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65152757481420278004913165 24432284055532604251842437)
                  ·
                    refine ⟨4581053260412363297220457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24432284055532604251842437 4581053260412363297220457)
                    ·
                      refine ⟨3435789945309272472915343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4581053260412363297220457 3435789945309272472915343)
                      ·
                        rfl

theorem cell23_6691177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 4, 2].length) (baseStart_6691177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691177 prefixEnd_6691177 := by exact prefixLift 6691177
  have htrace : WordTrace (prefixWord ++ tailWord_6691177) baseStart_6691177 baseEnd_6691177 := by
    simpa [prefixWord, tailWord_6691177, baseEnd_6691177] using wordTrace_append hprefix tailTrace_6691177
  have hstable : (prefixWord ++ tailWord_6691177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691177).length < 2 ^ (prefixWord ++ tailWord_6691177).sum := by decide
  have hdescent : baseEnd_6691177 < baseStart_6691177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691234 : List Nat := [3, 3, 1, 2, 1, 1, 1, 6, 5]
def baseStart_6691234 : Nat := 118140960795 + 6691234 * 2 ^ 59
def prefixEnd_6691234 : Nat := 4983230072969 + 3 ^ 40 * 6691234 * 2
def baseEnd_6691234 : Nat := 381757690411842083322509

theorem tailTrace_6691234 : CollatzResearch.WordTrace tailWord_6691234 prefixEnd_6691234 381757690411842083322509 := by
  unfold tailWord_6691234
  simp only [CollatzResearch.WordTrace]
  refine ⟨61012338360202366157900189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162699568960539643087733837 61012338360202366157900189)
  ·
    refine ⟨22879626885075887309212571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61012338360202366157900189 22879626885075887309212571)
    ·
      refine ⟨34319440327613830963818857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22879626885075887309212571 34319440327613830963818857)
      ·
        refine ⟨25739580245710373222864143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34319440327613830963818857 25739580245710373222864143)
        ·
          refine ⟨38609370368565559834296215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25739580245710373222864143 38609370368565559834296215)
          ·
            refine ⟨57914055552848339751444323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38609370368565559834296215 57914055552848339751444323)
            ·
              refine ⟨86871083329272509627166485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57914055552848339751444323 86871083329272509627166485)
              ·
                refine ⟨4072082031059648888773429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86871083329272509627166485 4072082031059648888773429)
                ·
                  refine ⟨381757690411842083322509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4072082031059648888773429 381757690411842083322509)
                  ·
                    rfl

theorem cell23_6691234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_6691234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691234 prefixEnd_6691234 := by exact prefixLift 6691234
  have htrace : WordTrace (prefixWord ++ tailWord_6691234) baseStart_6691234 baseEnd_6691234 := by
    simpa [prefixWord, tailWord_6691234, baseEnd_6691234] using wordTrace_append hprefix tailTrace_6691234
  have hstable : (prefixWord ++ tailWord_6691234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691234).length < 2 ^ (prefixWord ++ tailWord_6691234).sum := by decide
  have hdescent : baseEnd_6691234 < baseStart_6691234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691245 : List Nat := [1, 5, 2, 2, 3, 1, 1, 1, 1, 4, 2]
def baseStart_6691245 : Nat := 118140960795 + 6691245 * 2 ^ 59
def prefixEnd_6691245 : Nat := 4983230072969 + 3 ^ 40 * 6691245 * 2
def baseEnd_6691245 : Nat := 3435824861993778206865031

theorem tailTrace_6691245 : CollatzResearch.WordTrace tailWord_6691245 prefixEnd_6691245 3435824861993778206865031 := by
  unfold tailWord_6691245
  simp only [CollatzResearch.WordTrace]
  refine ⟨244049754643769613510251189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162699836429179742340167459 244049754643769613510251189)
  ·
    refine ⟨22879664497853401266586049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244049754643769613510251189 22879664497853401266586049)
    ·
      refine ⟨17159748373390050949939537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22879664497853401266586049 17159748373390050949939537)
      ·
        refine ⟨12869811280042538212454653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17159748373390050949939537 12869811280042538212454653)
        ·
          refine ⟨4826179230015951829670495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12869811280042538212454653 4826179230015951829670495)
          ·
            refine ⟨7239268845023927744505743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4826179230015951829670495 7239268845023927744505743)
            ·
              refine ⟨10858903267535891616758615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7239268845023927744505743 10858903267535891616758615)
              ·
                refine ⟨16288354901303837425137923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10858903267535891616758615 16288354901303837425137923)
                ·
                  refine ⟨24432532351955756137706885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16288354901303837425137923 24432532351955756137706885)
                  ·
                    refine ⟨4581099815991704275820041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24432532351955756137706885 4581099815991704275820041)
                    ·
                      refine ⟨3435824861993778206865031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4581099815991704275820041 3435824861993778206865031)
                      ·
                        rfl

theorem cell23_6691245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_6691245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691245 prefixEnd_6691245 := by exact prefixLift 6691245
  have htrace : WordTrace (prefixWord ++ tailWord_6691245) baseStart_6691245 baseEnd_6691245 := by
    simpa [prefixWord, tailWord_6691245, baseEnd_6691245] using wordTrace_append hprefix tailTrace_6691245
  have hstable : (prefixWord ++ tailWord_6691245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691245).length < 2 ^ (prefixWord ++ tailWord_6691245).sum := by decide
  have hdescent : baseEnd_6691245 < baseStart_6691245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691267 : List Nat := [1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 4]
def baseStart_6691267 : Nat := 118140960795 + 6691267 * 2 ^ 59
def prefixEnd_6691267 : Nat := 4983230072969 + 3 ^ 40 * 6691267 * 2
def baseEnd_6691267 : Nat := 3435836158568177120789929

theorem tailTrace_6691267 : CollatzResearch.WordTrace tailWord_6691267 prefixEnd_6691267 3435836158568177120789929 := by
  unfold tailWord_6691267
  simp only [CollatzResearch.WordTrace]
  refine ⟨244050557049689911267552055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162700371366459940845034703 244050557049689911267552055)
  ·
    refine ⟨366075835574534866901328083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244050557049689911267552055 366075835574534866901328083)
    ·
      refine ⟨549113753361802300351992125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366075835574534866901328083 549113753361802300351992125)
      ·
        refine ⟨205917657510675862631997047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 549113753361802300351992125 205917657510675862631997047)
        ·
          refine ⟨308876486266013793947995571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205917657510675862631997047 308876486266013793947995571)
          ·
            refine ⟨463314729399020690921993357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308876486266013793947995571 463314729399020690921993357)
            ·
              refine ⟨173743023524632759095747509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 463314729399020690921993357 173743023524632759095747509)
              ·
                refine ⟨16288408455434321165226329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173743023524632759095747509 16288408455434321165226329)
                ·
                  refine ⟨12216306341575740873919747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16288408455434321165226329 12216306341575740873919747)
                  ·
                    refine ⟨18324459512363611310879621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12216306341575740873919747 18324459512363611310879621)
                    ·
                      refine ⟨3435836158568177120789929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18324459512363611310879621 3435836158568177120789929)
                      ·
                        rfl

theorem cell23_6691267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_6691267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691267 prefixEnd_6691267 := by exact prefixLift 6691267
  have htrace : WordTrace (prefixWord ++ tailWord_6691267) baseStart_6691267 baseEnd_6691267 := by
    simpa [prefixWord, tailWord_6691267, baseEnd_6691267] using wordTrace_append hprefix tailTrace_6691267
  have hstable : (prefixWord ++ tailWord_6691267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691267).length < 2 ^ (prefixWord ++ tailWord_6691267).sum := by decide
  have hdescent : baseEnd_6691267 < baseStart_6691267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691268 : List Nat := [2, 3, 3, 2, 2, 2, 1, 3, 5]
def baseStart_6691268 : Nat := 118140960795 + 6691268 * 2 ^ 59
def prefixEnd_6691268 : Nat := 4983230072969 + 3 ^ 40 * 6691268 * 2
def baseEnd_6691268 : Nat := 381759630227647957430825

theorem tailTrace_6691268 : CollatzResearch.WordTrace tailWord_6691268 prefixEnd_6691268 381759630227647957430825 := by
  unfold tailWord_6691268
  simp only [CollatzResearch.WordTrace]
  refine ⟨122025296761343144219169229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162700395681790858958892305 122025296761343144219169229)
  ·
    refine ⟨45759486285503679082188461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122025296761343144219169229 45759486285503679082188461)
    ·
      refine ⟨17159807357063879655820673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45759486285503679082188461 17159807357063879655820673)
      ·
        refine ⟨12869855517797909741865505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17159807357063879655820673 12869855517797909741865505)
        ·
          refine ⟨9652391638348432306399129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12869855517797909741865505 9652391638348432306399129)
          ·
            refine ⟨7239293728761324229799347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9652391638348432306399129 7239293728761324229799347)
            ·
              refine ⟨10858940593141986344699021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7239293728761324229799347 10858940593141986344699021)
              ·
                refine ⟨4072102722428244879262133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10858940593141986344699021 4072102722428244879262133)
                ·
                  refine ⟨381759630227647957430825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4072102722428244879262133 381759630227647957430825)
                  ·
                    rfl

theorem cell23_6691268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_6691268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691268 prefixEnd_6691268 := by exact prefixLift 6691268
  have htrace : WordTrace (prefixWord ++ tailWord_6691268) baseStart_6691268 baseEnd_6691268 := by
    simpa [prefixWord, tailWord_6691268, baseEnd_6691268] using wordTrace_append hprefix tailTrace_6691268
  have hstable : (prefixWord ++ tailWord_6691268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691268).length < 2 ^ (prefixWord ++ tailWord_6691268).sum := by decide
  have hdescent : baseEnd_6691268 < baseStart_6691268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691284 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_6691284 : Nat := 118140960795 + 6691284 * 2 ^ 59
def prefixEnd_6691284 : Nat := 4983230072969 + 3 ^ 40 * 6691284 * 2
def baseEnd_6691284 : Nat := 3435844887739303554277351

theorem tailTrace_6691284 : CollatzResearch.WordTrace tailWord_6691284 prefixEnd_6691284 3435844887739303554277351 := by
  unfold tailWord_6691284
  simp only [CollatzResearch.WordTrace]
  refine ⟨122025588545314161585460453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162700784727085548780613937 122025588545314161585460453)
  ·
    refine ⟨22879797852246405297273835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122025588545314161585460453 22879797852246405297273835)
    ·
      refine ⟨34319696778369607945910753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22879797852246405297273835 34319696778369607945910753)
      ·
        refine ⟨25739772583777205959433065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34319696778369607945910753 25739772583777205959433065)
        ·
          refine ⟨19304829437832904469574799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25739772583777205959433065 19304829437832904469574799)
          ·
            refine ⟨28957244156749356704362199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19304829437832904469574799 28957244156749356704362199)
            ·
              refine ⟨43435866235124035056543299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28957244156749356704362199 43435866235124035056543299)
              ·
                refine ⟨65153799352686052584814949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43435866235124035056543299 65153799352686052584814949)
                ·
                  refine ⟨12216337378628634859652803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65153799352686052584814949 12216337378628634859652803)
                  ·
                    refine ⟨18324506067942952289479205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12216337378628634859652803 18324506067942952289479205)
                    ·
                      refine ⟨3435844887739303554277351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18324506067942952289479205 3435844887739303554277351)
                      ·
                        rfl

theorem cell23_6691284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_6691284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691284 prefixEnd_6691284 := by exact prefixLift 6691284
  have htrace : WordTrace (prefixWord ++ tailWord_6691284) baseStart_6691284 baseEnd_6691284 := by
    simpa [prefixWord, tailWord_6691284, baseEnd_6691284] using wordTrace_append hprefix tailTrace_6691284
  have hstable : (prefixWord ++ tailWord_6691284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691284).length < 2 ^ (prefixWord ++ tailWord_6691284).sum := by decide
  have hdescent : baseEnd_6691284 < baseStart_6691284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691307 : List Nat := [1, 1, 1, 1, 2, 3, 5, 3, 6]
def baseStart_6691307 : Nat := 118140960795 + 6691307 * 2 ^ 59
def prefixEnd_6691307 : Nat := 4983230072969 + 3 ^ 40 * 6691307 * 2
def baseEnd_6691307 : Nat := 381761855310484107143305

theorem tailTrace_6691307 : CollatzResearch.WordTrace tailWord_6691307 prefixEnd_6691307 381761855310484107143305 := by
  unfold tailWord_6691307
  simp only [CollatzResearch.WordTrace]
  refine ⟨244052015969544998099008175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162701343979696665399338783 244052015969544998099008175)
  ·
    refine ⟨366078023954317497148512263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244052015969544998099008175 366078023954317497148512263)
    ·
      refine ⟨549117035931476245722768395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366078023954317497148512263 549117035931476245722768395)
      ·
        refine ⟨823675553897214368584152593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549117035931476245722768395 823675553897214368584152593)
        ·
          refine ⟨617756665422910776438114445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 823675553897214368584152593 617756665422910776438114445)
          ·
            refine ⟨231658749533591541164292917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 617756665422910776438114445 231658749533591541164292917)
            ·
              refine ⟨21718007768774206984152461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 231658749533591541164292917 21718007768774206984152461)
              ·
                refine ⟨8144252913290327619057173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21718007768774206984152461 8144252913290327619057173)
                ·
                  refine ⟨381761855310484107143305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8144252913290327619057173 381761855310484107143305)
                  ·
                    rfl

theorem cell23_6691307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 6].length) (baseStart_6691307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691307 prefixEnd_6691307 := by exact prefixLift 6691307
  have htrace : WordTrace (prefixWord ++ tailWord_6691307) baseStart_6691307 baseEnd_6691307 := by
    simpa [prefixWord, tailWord_6691307, baseEnd_6691307] using wordTrace_append hprefix tailTrace_6691307
  have hstable : (prefixWord ++ tailWord_6691307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691307).length < 2 ^ (prefixWord ++ tailWord_6691307).sum := by decide
  have hdescent : baseEnd_6691307 < baseStart_6691307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691344 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 8, 3, 2]
def baseStart_6691344 : Nat := 118140960795 + 6691344 * 2 ^ 59
def prefixEnd_6691344 : Nat := 4983230072969 + 3 ^ 40 * 6691344 * 2
def baseEnd_6691344 : Nat := 3435875696578573319527075

theorem tailTrace_6691344 : CollatzResearch.WordTrace tailWord_6691344 prefixEnd_6691344 3435875696578573319527075 := by
  unfold tailWord_6691344
  simp only [CollatzResearch.WordTrace]
  refine ⟨122026682735205476709052543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162702243646940635612070057 122026682735205476709052543)
  ·
    refine ⟨183040024102808215063578815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122026682735205476709052543 183040024102808215063578815)
    ·
      refine ⟨274560036154212322595368223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183040024102808215063578815 274560036154212322595368223)
      ·
        refine ⟨411840054231318483893052335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274560036154212322595368223 411840054231318483893052335)
        ·
          refine ⟨617760081346977725839578503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411840054231318483893052335 617760081346977725839578503)
          ·
            refine ⟨926640122020466588759367755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617760081346977725839578503 926640122020466588759367755)
            ·
              refine ⟨1389960183030699883139051633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926640122020466588759367755 1389960183030699883139051633)
              ·
                refine ⟨1042470137273024912354288725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1389960183030699883139051633 1042470137273024912354288725)
                ·
                  refine ⟨12216446921168260691651821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1042470137273024912354288725 12216446921168260691651821)
                  ·
                    refine ⟨4581167595438097759369433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12216446921168260691651821 4581167595438097759369433)
                    ·
                      refine ⟨3435875696578573319527075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4581167595438097759369433 3435875696578573319527075)
                      ·
                        rfl

theorem cell23_6691344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 8, 3, 2].length) (baseStart_6691344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691344 prefixEnd_6691344 := by exact prefixLift 6691344
  have htrace : WordTrace (prefixWord ++ tailWord_6691344) baseStart_6691344 baseEnd_6691344 := by
    simpa [prefixWord, tailWord_6691344, baseEnd_6691344] using wordTrace_append hprefix tailTrace_6691344
  have hstable : (prefixWord ++ tailWord_6691344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691344).length < 2 ^ (prefixWord ++ tailWord_6691344).sum := by decide
  have hdescent : baseEnd_6691344 < baseStart_6691344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691368 : List Nat := [2, 1, 5, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_6691368 : Nat := 118140960795 + 6691368 * 2 ^ 59
def prefixEnd_6691368 : Nat := 4983230072969 + 3 ^ 40 * 6691368 * 2
def baseEnd_6691368 : Nat := 3435888020114281225626965

theorem tailTrace_6691368 : CollatzResearch.WordTrace tailWord_6691368 prefixEnd_6691368 3435888020114281225626965 := by
  unfold tailWord_6691368
  simp only [CollatzResearch.WordTrace]
  refine ⟨122027120411162002758489379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162702827214882670344652505 122027120411162002758489379)
  ·
    refine ⟨183040680616743004137734069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122027120411162002758489379 183040680616743004137734069)
    ·
      refine ⟨17160063807819656637912569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183040680616743004137734069 17160063807819656637912569)
      ·
        refine ⟨12870047855864742478434427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17160063807819656637912569 12870047855864742478434427)
        ·
          refine ⟨19305071783797113717651641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12870047855864742478434427 19305071783797113717651641)
          ·
            refine ⟨14478803837847835288238731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19305071783797113717651641 14478803837847835288238731)
            ·
              refine ⟨21718205756771752932358097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14478803837847835288238731 21718205756771752932358097)
              ·
                refine ⟨16288654317578814699268573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21718205756771752932358097 16288654317578814699268573)
                ·
                  refine ⟨6108245369092055512225715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16288654317578814699268573 6108245369092055512225715)
                  ·
                    refine ⟨9162368053638083268338573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6108245369092055512225715 9162368053638083268338573)
                    ·
                      refine ⟨3435888020114281225626965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9162368053638083268338573 3435888020114281225626965)
                      ·
                        rfl

theorem cell23_6691368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_6691368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691368 prefixEnd_6691368 := by exact prefixLift 6691368
  have htrace : WordTrace (prefixWord ++ tailWord_6691368) baseStart_6691368 baseEnd_6691368 := by
    simpa [prefixWord, tailWord_6691368, baseEnd_6691368] using wordTrace_append hprefix tailTrace_6691368
  have hstable : (prefixWord ++ tailWord_6691368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691368).length < 2 ^ (prefixWord ++ tailWord_6691368).sum := by decide
  have hdescent : baseEnd_6691368 < baseStart_6691368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691384 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 4, 4]
def baseStart_6691384 : Nat := 118140960795 + 6691384 * 2 ^ 59
def prefixEnd_6691384 : Nat := 4983230072969 + 3 ^ 40 * 6691384 * 2
def baseEnd_6691384 : Nat := 1145298745268251054342297

theorem tailTrace_6691384 : CollatzResearch.WordTrace tailWord_6691384 prefixEnd_6691384 1145298745268251054342297 := by
  unfold tailWord_6691384
  simp only [CollatzResearch.WordTrace]
  refine ⟨122027412195133020124780603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162703216260177360166374137 122027412195133020124780603)
  ·
    refine ⟨183041118292699530187170905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122027412195133020124780603 183041118292699530187170905)
    ·
      refine ⟨137280838719524647640378179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183041118292699530187170905 137280838719524647640378179)
      ·
        refine ⟨205921258079286971460567269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137280838719524647640378179 205921258079286971460567269)
        ·
          refine ⟨38610235889866307148856363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205921258079286971460567269 38610235889866307148856363)
          ·
            refine ⟨57915353834799460723284545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38610235889866307148856363 57915353834799460723284545)
            ·
              refine ⟨43436515376099595542463409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57915353834799460723284545 43436515376099595542463409)
              ·
                refine ⟨32577386532074696656847557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43436515376099595542463409 32577386532074696656847557)
                ·
                  refine ⟨6108259974764005623158917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32577386532074696656847557 6108259974764005623158917)
                  ·
                    refine ⟨1145298745268251054342297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6108259974764005623158917 1145298745268251054342297)
                    ·
                      rfl

theorem cell23_6691384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 4, 4].length) (baseStart_6691384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691384 prefixEnd_6691384 := by exact prefixLift 6691384
  have htrace : WordTrace (prefixWord ++ tailWord_6691384) baseStart_6691384 baseEnd_6691384 := by
    simpa [prefixWord, tailWord_6691384, baseEnd_6691384] using wordTrace_append hprefix tailTrace_6691384
  have hstable : (prefixWord ++ tailWord_6691384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691384).length < 2 ^ (prefixWord ++ tailWord_6691384).sum := by decide
  have hdescent : baseEnd_6691384 < baseStart_6691384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691387 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 4]
def baseStart_6691387 : Nat := 118140960795 + 6691387 * 2 ^ 59
def prefixEnd_6691387 : Nat := 4983230072969 + 3 ^ 40 * 6691387 * 2
def baseEnd_6691387 : Nat := 3435897776246716651289377

theorem tailTrace_6691387 : CollatzResearch.WordTrace tailWord_6691387 prefixEnd_6691387 3435897776246716651289377 := by
  unfold tailWord_6691387
  simp only [CollatzResearch.WordTrace]
  refine ⟨244054933809255171761920415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162703289206170114507946943 244054933809255171761920415)
  ·
    refine ⟨366082400713882757642880623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244054933809255171761920415 366082400713882757642880623)
    ·
      refine ⟨549123601070824136464320935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366082400713882757642880623 549123601070824136464320935)
      ·
        refine ⟨823685401606236204696481403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549123601070824136464320935 823685401606236204696481403)
        ·
          refine ⟨1235528102409354307044722105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 823685401606236204696481403 1235528102409354307044722105)
          ·
            refine ⟨926646076807015730283541579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1235528102409354307044722105 926646076807015730283541579)
            ·
              refine ⟨1389969115210523595425312369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926646076807015730283541579 1389969115210523595425312369)
              ·
                refine ⟨1042476836407892696568984277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1389969115210523595425312369 1042476836407892696568984277)
                ·
                  refine ⟨24433050853309985075835569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1042476836407892696568984277 24433050853309985075835569)
                  ·
                    refine ⟨18324788139982488806876677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24433050853309985075835569 18324788139982488806876677)
                    ·
                      refine ⟨3435897776246716651289377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18324788139982488806876677 3435897776246716651289377)
                      ·
                        rfl

theorem cell23_6691387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 4].length) (baseStart_6691387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691387 prefixEnd_6691387 := by exact prefixLift 6691387
  have htrace : WordTrace (prefixWord ++ tailWord_6691387) baseStart_6691387 baseEnd_6691387 := by
    simpa [prefixWord, tailWord_6691387, baseEnd_6691387] using wordTrace_append hprefix tailTrace_6691387
  have hstable : (prefixWord ++ tailWord_6691387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691387).length < 2 ^ (prefixWord ++ tailWord_6691387).sum := by decide
  have hdescent : baseEnd_6691387 < baseStart_6691387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691388 : List Nat := [2, 2, 2, 2, 3, 3, 2, 1, 1, 5]
def baseStart_6691388 : Nat := 118140960795 + 6691388 * 2 ^ 59
def prefixEnd_6691388 : Nat := 4983230072969 + 3 ^ 40 * 6691388 * 2
def baseEnd_6691388 : Nat := 1145299429909123715792291

theorem tailTrace_6691388 : CollatzResearch.WordTrace tailWord_6691388 prefixEnd_6691388 1145299429909123715792291 := by
  unfold tailWord_6691388
  simp only [CollatzResearch.WordTrace]
  refine ⟨122027485141125774466353409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162703313521501032621804545 122027485141125774466353409)
  ·
    refine ⟨91520613855844330849765057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122027485141125774466353409 91520613855844330849765057)
    ·
      refine ⟨68640460391883248137323793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91520613855844330849765057 68640460391883248137323793)
      ·
        refine ⟨51480345293912436102992845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68640460391883248137323793 51480345293912436102992845)
        ·
          refine ⟨19305129485217163538622317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51480345293912436102992845 19305129485217163538622317)
          ·
            refine ⟨7239423556956436326983369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19305129485217163538622317 7239423556956436326983369)
            ·
              refine ⟨5429567667717327245237527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7239423556956436326983369 5429567667717327245237527)
              ·
                refine ⟨8144351501575990867856291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5429567667717327245237527 8144351501575990867856291)
                ·
                  refine ⟨12216527252363986301784437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8144351501575990867856291 12216527252363986301784437)
                  ·
                    refine ⟨1145299429909123715792291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12216527252363986301784437 1145299429909123715792291)
                    ·
                      rfl

theorem cell23_6691388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_6691388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691388 prefixEnd_6691388 := by exact prefixLift 6691388
  have htrace : WordTrace (prefixWord ++ tailWord_6691388) baseStart_6691388 baseEnd_6691388 := by
    simpa [prefixWord, tailWord_6691388, baseEnd_6691388] using wordTrace_append hprefix tailTrace_6691388
  have hstable : (prefixWord ++ tailWord_6691388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691388).length < 2 ^ (prefixWord ++ tailWord_6691388).sum := by decide
  have hdescent : baseEnd_6691388 < baseStart_6691388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691391 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 5, 2, 2]
def baseStart_6691391 : Nat := 118140960795 + 6691391 * 2 ^ 59
def prefixEnd_6691391 : Nat := 4983230072969 + 3 ^ 40 * 6691391 * 2
def baseEnd_6691391 : Nat := 3435899830169334635639359

theorem tailTrace_6691391 : CollatzResearch.WordTrace tailWord_6691391 prefixEnd_6691391 3435899830169334635639359 := by
  unfold tailWord_6691391
  simp only [CollatzResearch.WordTrace]
  refine ⟨244055079701240680445066027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162703386467493786963377351 244055079701240680445066027)
  ·
    refine ⟨366082619551861020667599041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244055079701240680445066027 366082619551861020667599041)
    ·
      refine ⟨274561964663895765500699281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366082619551861020667599041 274561964663895765500699281)
      ·
        refine ⟨205921473497921824125524461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274561964663895765500699281 205921473497921824125524461)
        ·
          refine ⟨77220552561720684047071673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205921473497921824125524461 77220552561720684047071673)
          ·
            refine ⟨57915414421290513035303755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77220552561720684047071673 57915414421290513035303755)
            ·
              refine ⟨86873121631935769552955633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57915414421290513035303755 86873121631935769552955633)
              ·
                refine ⟨65154841223951827164716725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86873121631935769552955633 65154841223951827164716725)
                ·
                  refine ⟨6108266364745483796692193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65154841223951827164716725 6108266364745483796692193)
                  ·
                    refine ⟨4581199773559112847519145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6108266364745483796692193 4581199773559112847519145)
                    ·
                      refine ⟨3435899830169334635639359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4581199773559112847519145 3435899830169334635639359)
                      ·
                        rfl

theorem cell23_6691391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 2, 2].length) (baseStart_6691391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691391 prefixEnd_6691391 := by exact prefixLift 6691391
  have htrace : WordTrace (prefixWord ++ tailWord_6691391) baseStart_6691391 baseEnd_6691391 := by
    simpa [prefixWord, tailWord_6691391, baseEnd_6691391] using wordTrace_append hprefix tailTrace_6691391
  have hstable : (prefixWord ++ tailWord_6691391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691391).length < 2 ^ (prefixWord ++ tailWord_6691391).sum := by decide
  have hdescent : baseEnd_6691391 < baseStart_6691391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691397 : List Nat := [1, 3, 1, 1, 1, 6, 10]
def baseStart_6691397 : Nat := 118140960795 + 6691397 * 2 ^ 59
def prefixEnd_6691397 : Nat := 4983230072969 + 3 ^ 40 * 6691397 * 2
def baseEnd_6691397 : Nat := 42418554457447674224251

theorem tailTrace_6691397 : CollatzResearch.WordTrace tailWord_6691397 prefixEnd_6691397 42418554457447674224251 := by
  unfold tailWord_6691397
  simp only [CollatzResearch.WordTrace]
  refine ⟨244055298539218943469784445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162703532359479295646522963 244055298539218943469784445)
  ·
    refine ⟨91520736952207103801169167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244055298539218943469784445 91520736952207103801169167)
    ·
      refine ⟨137281105428310655701753751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91520736952207103801169167 137281105428310655701753751)
      ·
        refine ⟨205921658142465983552630627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137281105428310655701753751 205921658142465983552630627)
        ·
          refine ⟨308882487213698975328945941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205921658142465983552630627 308882487213698975328945941)
          ·
            refine ⟨14478866588142139468544341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 308882487213698975328945941 14478866588142139468544341)
            ·
              refine ⟨42418554457447674224251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14478866588142139468544341 42418554457447674224251)
              ·
                rfl

theorem cell23_6691397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 10].length) (baseStart_6691397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691397 prefixEnd_6691397 := by exact prefixLift 6691397
  have htrace : WordTrace (prefixWord ++ tailWord_6691397) baseStart_6691397 baseEnd_6691397 := by
    simpa [prefixWord, tailWord_6691397, baseEnd_6691397] using wordTrace_append hprefix tailTrace_6691397
  have hstable : (prefixWord ++ tailWord_6691397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691397).length < 2 ^ (prefixWord ++ tailWord_6691397).sum := by decide
  have hdescent : baseEnd_6691397 < baseStart_6691397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691422 : List Nat := [4, 4, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_6691422 : Nat := 118140960795 + 6691422 * 2 ^ 59
def prefixEnd_6691422 : Nat := 4983230072969 + 3 ^ 40 * 6691422 * 2
def baseEnd_6691422 : Nat := 1145305249356541338117239

theorem tailTrace_6691422 : CollatzResearch.WordTrace tailWord_6691422 prefixEnd_6691422 1145305249356541338117239 := by
  unfold tailWord_6691422
  simp only [CollatzResearch.WordTrace]
  refine ⟨30507026295516046592430565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162704140242752248492963013 30507026295516046592430565)
  ·
    refine ⟨5720067430409258736080731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30507026295516046592430565 5720067430409258736080731)
    ·
      refine ⟨8580101145613888104121097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5720067430409258736080731 8580101145613888104121097)
      ·
        refine ⟨6435075859210416078090823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8580101145613888104121097 6435075859210416078090823)
        ·
          refine ⟨9652613788815624117136235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6435075859210416078090823 9652613788815624117136235)
          ·
            refine ⟨14478920683223436175704353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9652613788815624117136235 14478920683223436175704353)
            ·
              refine ⟨10859190512417577131778265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14478920683223436175704353 10859190512417577131778265)
              ·
                refine ⟨8144392884313182848833699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10859190512417577131778265 8144392884313182848833699)
                ·
                  refine ⟨12216589326469774273250549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8144392884313182848833699 12216589326469774273250549)
                  ·
                    refine ⟨1145305249356541338117239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12216589326469774273250549 1145305249356541338117239)
                    ·
                      rfl

theorem cell23_6691422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_6691422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691422 prefixEnd_6691422 := by exact prefixLift 6691422
  have htrace : WordTrace (prefixWord ++ tailWord_6691422) baseStart_6691422 baseEnd_6691422 := by
    simpa [prefixWord, tailWord_6691422, baseEnd_6691422] using wordTrace_append hprefix tailTrace_6691422
  have hstable : (prefixWord ++ tailWord_6691422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691422).length < 2 ^ (prefixWord ++ tailWord_6691422).sum := by decide
  have hdescent : baseEnd_6691422 < baseStart_6691422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691481 : List Nat := [1, 2, 1, 2, 1, 2, 4, 3, 1, 4, 2]
def baseStart_6691481 : Nat := 118140960795 + 6691481 * 2 ^ 59
def prefixEnd_6691481 : Nat := 4983230072969 + 3 ^ 40 * 6691481 * 2
def baseEnd_6691481 : Nat := 3435946043428239283513945

theorem tailTrace_6691481 : CollatzResearch.WordTrace tailWord_6691481 prefixEnd_6691481 3435946043428239283513945 := by
  unfold tailWord_6691481
  simp only [CollatzResearch.WordTrace]
  refine ⟨244058362270914625815842297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162705574847276417210561531 244058362270914625815842297)
  ·
    refine ⟨183043771703185969361881723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244058362270914625815842297 183043771703185969361881723)
    ·
      refine ⟨274565657554778954042822585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183043771703185969361881723 274565657554778954042822585)
      ·
        refine ⟨205924243166084215532116939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274565657554778954042822585 205924243166084215532116939)
        ·
          refine ⟨308886364749126323298175409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205924243166084215532116939 308886364749126323298175409)
          ·
            refine ⟨231664773561844742473631557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308886364749126323298175409 231664773561844742473631557)
            ·
              refine ⟨43437145042845889213805917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231664773561844742473631557 43437145042845889213805917)
              ·
                refine ⟨16288929391067208455177219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43437145042845889213805917 16288929391067208455177219)
                ·
                  refine ⟨24433394086600812682765829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16288929391067208455177219 24433394086600812682765829)
                  ·
                    refine ⟨4581261391237652378018593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24433394086600812682765829 4581261391237652378018593)
                    ·
                      refine ⟨3435946043428239283513945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4581261391237652378018593 3435946043428239283513945)
                      ·
                        rfl

theorem cell23_6691481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 4, 2].length) (baseStart_6691481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691481 prefixEnd_6691481 := by exact prefixLift 6691481
  have htrace : WordTrace (prefixWord ++ tailWord_6691481) baseStart_6691481 baseEnd_6691481 := by
    simpa [prefixWord, tailWord_6691481, baseEnd_6691481] using wordTrace_append hprefix tailTrace_6691481
  have hstable : (prefixWord ++ tailWord_6691481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691481).length < 2 ^ (prefixWord ++ tailWord_6691481).sum := by decide
  have hdescent : baseEnd_6691481 < baseStart_6691481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691501 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_6691501 : Nat := 118140960795 + 6691501 * 2 ^ 59
def prefixEnd_6691501 : Nat := 4983230072969 + 3 ^ 40 * 6691501 * 2
def baseEnd_6691501 : Nat := 3435956313041329205263853

theorem tailTrace_6691501 : CollatzResearch.WordTrace tailWord_6691501 prefixEnd_6691501 3435956313041329205263853 := by
  unfold tailWord_6691501
  simp only [CollatzResearch.WordTrace]
  refine ⟨244059091730842169231570357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162706061153894779487713571 244059091730842169231570357)
  ·
    refine ⟨22880539849766453365459721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244059091730842169231570357 22880539849766453365459721)
    ·
      refine ⟨17160404887324840024094791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22880539849766453365459721 17160404887324840024094791)
      ·
        refine ⟨25740607330987260036142187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17160404887324840024094791 25740607330987260036142187)
        ·
          refine ⟨38610910996480890054213281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25740607330987260036142187 38610910996480890054213281)
          ·
            refine ⟨28958183247360667540659961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38610910996480890054213281 28958183247360667540659961)
            ·
              refine ⟨21718637435520500655494971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28958183247360667540659961 21718637435520500655494971)
              ·
                refine ⟨32577956153280750983242457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21718637435520500655494971 32577956153280750983242457)
                ·
                  refine ⟨24433467114960563237431843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32577956153280750983242457 24433467114960563237431843)
                  ·
                    refine ⟨36650200672440844856147765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24433467114960563237431843 36650200672440844856147765)
                    ·
                      refine ⟨3435956313041329205263853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36650200672440844856147765 3435956313041329205263853)
                      ·
                        rfl

theorem cell23_6691501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_6691501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691501 prefixEnd_6691501 := by exact prefixLift 6691501
  have htrace : WordTrace (prefixWord ++ tailWord_6691501) baseStart_6691501 baseEnd_6691501 := by
    simpa [prefixWord, tailWord_6691501, baseEnd_6691501] using wordTrace_append hprefix tailTrace_6691501
  have hstable : (prefixWord ++ tailWord_6691501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691501).length < 2 ^ (prefixWord ++ tailWord_6691501).sum := by decide
  have hdescent : baseEnd_6691501 < baseStart_6691501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691551 : List Nat := [1, 1, 2, 3, 2, 3, 3, 1, 2, 5]
def baseStart_6691551 : Nat := 118140960795 + 6691551 * 2 ^ 59
def prefixEnd_6691551 : Nat := 4983230072969 + 3 ^ 40 * 6691551 * 2
def baseEnd_6691551 : Nat := 1145327329024684669879541

theorem tailTrace_6691551 : CollatzResearch.WordTrace tailWord_6691551 prefixEnd_6691551 1145327329024684669879541 := by
  unfold tailWord_6691551
  simp only [CollatzResearch.WordTrace]
  refine ⟨244060915380661027770890507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162707276920440685180593671 244060915380661027770890507)
  ·
    refine ⟨366091373070991541656335761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244060915380661027770890507 366091373070991541656335761)
    ·
      refine ⟨274568529803243656242251821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366091373070991541656335761 274568529803243656242251821)
      ·
        refine ⟨102963198676216371090844433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274568529803243656242251821 102963198676216371090844433)
        ·
          refine ⟨77222399007162278318133325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102963198676216371090844433 77222399007162278318133325)
          ·
            refine ⟨28958399627685854369299997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77222399007162278318133325 28958399627685854369299997)
            ·
              refine ⟨10859399860382195388487499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28958399627685854369299997 10859399860382195388487499)
              ·
                refine ⟨16289099790573293082731249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10859399860382195388487499 16289099790573293082731249)
                ·
                  refine ⟨12216824842929969812048437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16289099790573293082731249 12216824842929969812048437)
                  ·
                    refine ⟨1145327329024684669879541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12216824842929969812048437 1145327329024684669879541)
                    ·
                      rfl

theorem cell23_6691551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 5].length) (baseStart_6691551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691551 prefixEnd_6691551 := by exact prefixLift 6691551
  have htrace : WordTrace (prefixWord ++ tailWord_6691551) baseStart_6691551 baseEnd_6691551 := by
    simpa [prefixWord, tailWord_6691551, baseEnd_6691551] using wordTrace_append hprefix tailTrace_6691551
  have hstable : (prefixWord ++ tailWord_6691551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691551).length < 2 ^ (prefixWord ++ tailWord_6691551).sum := by decide
  have hdescent : baseEnd_6691551 < baseStart_6691551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691584 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 4]
def baseStart_6691584 : Nat := 118140960795 + 6691584 * 2 ^ 59
def prefixEnd_6691584 : Nat := 4983230072969 + 3 ^ 40 * 6691584 * 2
def baseEnd_6691584 : Nat := 3435998931935652380525971

theorem tailTrace_6691584 : CollatzResearch.WordTrace tailWord_6691584 prefixEnd_6691584 3435998931935652380525971 := by
  unfold tailWord_6691584
  simp only [CollatzResearch.WordTrace]
  refine ⟨122031059494770737203420903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162708079326360982937894537 122031059494770737203420903)
  ·
    refine ⟨183046589242156105805131355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122031059494770737203420903 183046589242156105805131355)
    ·
      refine ⟨274569883863234158707697033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183046589242156105805131355 274569883863234158707697033)
      ·
        refine ⟨205927412897425619030772775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274569883863234158707697033 205927412897425619030772775)
        ·
          refine ⟨308891119346138428546159163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205927412897425619030772775 308891119346138428546159163)
          ·
            refine ⟨463336679019207642819238745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308891119346138428546159163 463336679019207642819238745)
            ·
              refine ⟨347502509264405732114429059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463336679019207642819238745 347502509264405732114429059)
              ·
                refine ⟨521253763896608598171643589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347502509264405732114429059 521253763896608598171643589)
                ·
                  refine ⟨97735080730614112157183173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 521253763896608598171643589 97735080730614112157183173)
                  ·
                    refine ⟨18325327636990146029471845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97735080730614112157183173 18325327636990146029471845)
                    ·
                      refine ⟨3435998931935652380525971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18325327636990146029471845 3435998931935652380525971)
                      ·
                        rfl

theorem cell23_6691584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_6691584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691584 prefixEnd_6691584 := by exact prefixLift 6691584
  have htrace : WordTrace (prefixWord ++ tailWord_6691584) baseStart_6691584 baseEnd_6691584 := by
    simpa [prefixWord, tailWord_6691584, baseEnd_6691584] using wordTrace_append hprefix tailTrace_6691584
  have hstable : (prefixWord ++ tailWord_6691584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691584).length < 2 ^ (prefixWord ++ tailWord_6691584).sum := by decide
  have hdescent : baseEnd_6691584 < baseStart_6691584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691588 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 2, 4, 2]
def baseStart_6691588 : Nat := 118140960795 + 6691588 * 2 ^ 59
def prefixEnd_6691588 : Nat := 4983230072969 + 3 ^ 40 * 6691588 * 2
def baseEnd_6691588 : Nat := 3436000985858270364875953

theorem tailTrace_6691588 : CollatzResearch.WordTrace tailWord_6691588 prefixEnd_6691588 3436000985858270364875953 := by
  unfold tailWord_6691588
  simp only [CollatzResearch.WordTrace]
  refine ⟨122031132440763491544993709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162708176587684655393324945 122031132440763491544993709)
  ·
    refine ⟨45761674665286309329372641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122031132440763491544993709 45761674665286309329372641)
    ·
      refine ⟨34321255998964731997029481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45761674665286309329372641 34321255998964731997029481)
      ·
        refine ⟨25740941999223548997772111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34321255998964731997029481 25740941999223548997772111)
        ·
          refine ⟨38611412998835323496658167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25740941999223548997772111 38611412998835323496658167)
          ·
            refine ⟨57917119498252985244987251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38611412998835323496658167 57917119498252985244987251)
            ·
              refine ⟨86875679247379477867480877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57917119498252985244987251 86875679247379477867480877)
              ·
                refine ⟨32578379717767304200305329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86875679247379477867480877 32578379717767304200305329)
                ·
                  refine ⟨24433784788325478150228997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32578379717767304200305329 24433784788325478150228997)
                  ·
                    refine ⟨4581334647811027153167937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24433784788325478150228997 4581334647811027153167937)
                    ·
                      refine ⟨3436000985858270364875953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4581334647811027153167937 3436000985858270364875953)
                      ·
                        rfl

theorem cell23_6691588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_6691588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691588 prefixEnd_6691588 := by exact prefixLift 6691588
  have htrace : WordTrace (prefixWord ++ tailWord_6691588) baseStart_6691588 baseEnd_6691588 := by
    simpa [prefixWord, tailWord_6691588, baseEnd_6691588] using wordTrace_append hprefix tailTrace_6691588
  have hstable : (prefixWord ++ tailWord_6691588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691588).length < 2 ^ (prefixWord ++ tailWord_6691588).sum := by decide
  have hdescent : baseEnd_6691588 < baseStart_6691588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691615 : List Nat := [1, 1, 2, 4, 2, 2, 3, 3, 1, 4]
def baseStart_6691615 : Nat := 118140960795 + 6691615 * 2 ^ 59
def prefixEnd_6691615 : Nat := 4983230072969 + 3 ^ 40 * 6691615 * 2
def baseEnd_6691615 : Nat := 1145338283278647253079443

theorem tailTrace_6691615 : CollatzResearch.WordTrace tailWord_6691615 prefixEnd_6691615 1145338283278647253079443 := by
  unfold tailWord_6691615
  simp only [CollatzResearch.WordTrace]
  refine ⟨244063249652429166701220299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162708833101619444467480199 244063249652429166701220299)
  ·
    refine ⟨366094874478643750051830449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244063249652429166701220299 366094874478643750051830449)
    ·
      refine ⟨274571155858982812538872837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366094874478643750051830449 274571155858982812538872837)
      ·
        refine ⟨51482091723559277351038657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274571155858982812538872837 51482091723559277351038657)
        ·
          refine ⟨38611568792669458013278993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51482091723559277351038657 38611568792669458013278993)
          ·
            refine ⟨28958676594502093509959245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38611568792669458013278993 28958676594502093509959245)
            ·
              refine ⟨10859503722938285066234717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28958676594502093509959245 10859503722938285066234717)
              ·
                refine ⟨4072313896101856899838019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10859503722938285066234717 4072313896101856899838019)
                ·
                  refine ⟨6108470844152785349757029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4072313896101856899838019 6108470844152785349757029)
                  ·
                    refine ⟨1145338283278647253079443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6108470844152785349757029 1145338283278647253079443)
                    ·
                      rfl

theorem cell23_6691615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 1, 4].length) (baseStart_6691615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691615 prefixEnd_6691615 := by exact prefixLift 6691615
  have htrace : WordTrace (prefixWord ++ tailWord_6691615) baseStart_6691615 baseEnd_6691615 := by
    simpa [prefixWord, tailWord_6691615, baseEnd_6691615] using wordTrace_append hprefix tailTrace_6691615
  have hstable : (prefixWord ++ tailWord_6691615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691615).length < 2 ^ (prefixWord ++ tailWord_6691615).sum := by decide
  have hdescent : baseEnd_6691615 < baseStart_6691615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691671 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 3, 6]
def baseStart_6691671 : Nat := 118140960795 + 6691671 * 2 ^ 59
def prefixEnd_6691671 : Nat := 4983230072969 + 3 ^ 40 * 6691671 * 2
def baseEnd_6691671 : Nat := 1145347868250864513379357

theorem tailTrace_6691671 : CollatzResearch.WordTrace tailWord_6691671 prefixEnd_6691671 1145347868250864513379357 := by
  unfold tailWord_6691671
  simp only [CollatzResearch.WordTrace]
  refine ⟨244065292140226288265258867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162710194760150858843505911 244065292140226288265258867)
  ·
    refine ⟨366097938210339432397888301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244065292140226288265258867 366097938210339432397888301)
    ·
      refine ⟨137286726828877287149208113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366097938210339432397888301 137286726828877287149208113)
      ·
        refine ⟨102965045121657965361906085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137286726828877287149208113 102965045121657965361906085)
        ·
          refine ⟨19305945960310868505357391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102965045121657965361906085 19305945960310868505357391)
          ·
            refine ⟨28958918940466302758036087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19305945960310868505357391 28958918940466302758036087)
            ·
              refine ⟨43438378410699454137054131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28958918940466302758036087 43438378410699454137054131)
              ·
                refine ⟨65157567616049181205581197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43438378410699454137054131 65157567616049181205581197)
                ·
                  refine ⟨24434087856018442952092949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65157567616049181205581197 24434087856018442952092949)
                  ·
                    refine ⟨1145347868250864513379357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24434087856018442952092949 1145347868250864513379357)
                    ·
                      rfl

theorem cell23_6691671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_6691671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691671 prefixEnd_6691671 := by exact prefixLift 6691671
  have htrace : WordTrace (prefixWord ++ tailWord_6691671) baseStart_6691671 baseEnd_6691671 := by
    simpa [prefixWord, tailWord_6691671, baseEnd_6691671] using wordTrace_append hprefix tailTrace_6691671
  have hstable : (prefixWord ++ tailWord_6691671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691671).length < 2 ^ (prefixWord ++ tailWord_6691671).sum := by decide
  have hdescent : baseEnd_6691671 < baseStart_6691671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691681 : List Nat := [1, 2, 3, 1, 1, 1, 2, 5, 1, 1, 5]
def baseStart_6691681 : Nat := 118140960795 + 6691681 * 2 ^ 59
def prefixEnd_6691681 : Nat := 4983230072969 + 3 ^ 40 * 6691681 * 2
def baseEnd_6691681 : Nat := 3436048739559138501013025

theorem tailTrace_6691681 : CollatzResearch.WordTrace tailWord_6691681 prefixEnd_6691681 3436048739559138501013025 := by
  unfold tailWord_6691681
  simp only [CollatzResearch.WordTrace]
  refine ⟨244065656870190059973122897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162710437913460039982081931 244065656870190059973122897)
  ·
    refine ⟨183049242652642544979842173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244065656870190059973122897 183049242652642544979842173)
    ·
      refine ⟨68643465994740954367440815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183049242652642544979842173 68643465994740954367440815)
      ·
        refine ⟨102965198992111431551161223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68643465994740954367440815 102965198992111431551161223)
        ·
          refine ⟨154447798488167147326741835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102965198992111431551161223 154447798488167147326741835)
          ·
            refine ⟨231671697732250720990112753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154447798488167147326741835 231671697732250720990112753)
            ·
              refine ⟨173753773299188040742584565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231671697732250720990112753 173753773299188040742584565)
              ·
                refine ⟨16289416246798878819617303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173753773299188040742584565 16289416246798878819617303)
                ·
                  refine ⟨24434124370198318229425955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16289416246798878819617303 24434124370198318229425955)
                  ·
                    refine ⟨36651186555297477344138933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24434124370198318229425955 36651186555297477344138933)
                    ·
                      refine ⟨3436048739559138501013025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36651186555297477344138933 3436048739559138501013025)
                      ·
                        rfl

theorem cell23_6691681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_6691681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691681 prefixEnd_6691681 := by exact prefixLift 6691681
  have htrace : WordTrace (prefixWord ++ tailWord_6691681) baseStart_6691681 baseEnd_6691681 := by
    simpa [prefixWord, tailWord_6691681, baseEnd_6691681] using wordTrace_append hprefix tailTrace_6691681
  have hstable : (prefixWord ++ tailWord_6691681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691681).length < 2 ^ (prefixWord ++ tailWord_6691681).sum := by decide
  have hdescent : baseEnd_6691681 < baseStart_6691681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691698 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 3, 2, 3]
def baseStart_6691698 : Nat := 118140960795 + 6691698 * 2 ^ 59
def prefixEnd_6691698 : Nat := 4983230072969 + 3 ^ 40 * 6691698 * 2
def baseEnd_6691698 : Nat := 3436057468730264934500447

theorem tailTrace_6691698 : CollatzResearch.WordTrace tailWord_6691698 prefixEnd_6691698 3436057468730264934500447 := by
  unfold tailWord_6691698
  simp only [CollatzResearch.WordTrace]
  refine ⟨61016569227782117969122937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162710851274085647917661165 61016569227782117969122937)
  ·
    refine ⟨45762426920836588476842203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61016569227782117969122937 45762426920836588476842203)
    ·
      refine ⟨68643640381254882715263305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45762426920836588476842203 68643640381254882715263305)
      ·
        refine ⟨51482730285941162036447479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68643640381254882715263305 51482730285941162036447479)
        ·
          refine ⟨77224095428911743054671219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51482730285941162036447479 77224095428911743054671219)
          ·
            refine ⟨115836143143367614582006829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77224095428911743054671219 115836143143367614582006829)
            ·
              refine ⟨43438553678762855468252561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115836143143367614582006829 43438553678762855468252561)
              ·
                refine ⟨32578915259072141601189421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43438553678762855468252561 32578915259072141601189421)
                ·
                  refine ⟨12217093222152053100446033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32578915259072141601189421 12217093222152053100446033)
                  ·
                    refine ⟨9162819916614039825334525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12217093222152053100446033 9162819916614039825334525)
                    ·
                      refine ⟨3436057468730264934500447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9162819916614039825334525 3436057468730264934500447)
                      ·
                        rfl

theorem cell23_6691698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_6691698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691698 prefixEnd_6691698 := by exact prefixLift 6691698
  have htrace : WordTrace (prefixWord ++ tailWord_6691698) baseStart_6691698 baseEnd_6691698 := by
    simpa [prefixWord, tailWord_6691698, baseEnd_6691698] using wordTrace_append hprefix tailTrace_6691698
  have hstable : (prefixWord ++ tailWord_6691698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691698).length < 2 ^ (prefixWord ++ tailWord_6691698).sum := by decide
  have hdescent : baseEnd_6691698 < baseStart_6691698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691780 : List Nat := [2, 3, 3, 3, 2, 1, 1, 3, 1, 2, 2]
def baseStart_6691780 : Nat := 118140960795 + 6691780 * 2 ^ 59
def prefixEnd_6691780 : Nat := 4983230072969 + 3 ^ 40 * 6691780 * 2
def baseEnd_6691780 : Nat := 3436099574143933613675071

theorem tailTrace_6691780 : CollatzResearch.WordTrace tailWord_6691780 prefixEnd_6691780 3436099574143933613675071 := by
  unfold tailWord_6691780
  simp only [CollatzResearch.WordTrace]
  refine ⟨122034633848415699940488397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162712845131220933253984529 122034633848415699940488397)
  ·
    refine ⟨45762987693155887477683149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122034633848415699940488397 45762987693155887477683149)
    ·
      refine ⟨17161120384933457804131181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45762987693155887477683149 17161120384933457804131181)
      ·
        refine ⟨6435420144350046676549193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17161120384933457804131181 6435420144350046676549193)
        ·
          refine ⟨4826565108262535007411895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6435420144350046676549193 4826565108262535007411895)
          ·
            refine ⟨7239847662393802511117843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4826565108262535007411895 7239847662393802511117843)
            ·
              refine ⟨10859771493590703766676765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7239847662393802511117843 10859771493590703766676765)
              ·
                refine ⟨4072414310096513912503787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10859771493590703766676765 4072414310096513912503787)
                ·
                  refine ⟨6108621465144770868755681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4072414310096513912503787 6108621465144770868755681)
                  ·
                    refine ⟨4581466098858578151566761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6108621465144770868755681 4581466098858578151566761)
                    ·
                      refine ⟨3436099574143933613675071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4581466098858578151566761 3436099574143933613675071)
                      ·
                        rfl

theorem cell23_6691780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_6691780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691780 prefixEnd_6691780 := by exact prefixLift 6691780
  have htrace : WordTrace (prefixWord ++ tailWord_6691780) baseStart_6691780 baseEnd_6691780 := by
    simpa [prefixWord, tailWord_6691780, baseEnd_6691780] using wordTrace_append hprefix tailTrace_6691780
  have hstable : (prefixWord ++ tailWord_6691780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691780).length < 2 ^ (prefixWord ++ tailWord_6691780).sum := by decide
  have hdescent : baseEnd_6691780 < baseStart_6691780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691788 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 2, 1, 5]
def baseStart_6691788 : Nat := 118140960795 + 6691788 * 2 ^ 59
def prefixEnd_6691788 : Nat := 4983230072969 + 3 ^ 40 * 6691788 * 2
def baseEnd_6691788 : Nat := 3436103681989169582375033

theorem tailTrace_6691788 : CollatzResearch.WordTrace tailWord_6691788 prefixEnd_6691788 3436103681989169582375033 := by
  unfold tailWord_6691788
  simp only [CollatzResearch.WordTrace]
  refine ⟨122034779740401208623634009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162713039653868278164845345 122034779740401208623634009)
  ·
    refine ⟨91526084805300906467725507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122034779740401208623634009 91526084805300906467725507)
    ·
      refine ⟨137289127207951359701588261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91526084805300906467725507 137289127207951359701588261)
      ·
        refine ⟨25741711351490879944047799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137289127207951359701588261 25741711351490879944047799)
        ·
          refine ⟨38612567027236319916071699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25741711351490879944047799 38612567027236319916071699)
          ·
            refine ⟨57918850540854479874107549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38612567027236319916071699 57918850540854479874107549)
            ·
              refine ⟨21719568952820429952790331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57918850540854479874107549 21719568952820429952790331)
              ·
                refine ⟨32579353429230644929185497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21719568952820429952790331 32579353429230644929185497)
                ·
                  refine ⟨24434515071922983696889123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32579353429230644929185497 24434515071922983696889123)
                  ·
                    refine ⟨36651772607884475545333685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24434515071922983696889123 36651772607884475545333685)
                    ·
                      refine ⟨3436103681989169582375033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36651772607884475545333685 3436103681989169582375033)
                      ·
                        rfl

theorem cell23_6691788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_6691788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691788 prefixEnd_6691788 := by exact prefixLift 6691788
  have htrace : WordTrace (prefixWord ++ tailWord_6691788) baseStart_6691788 baseEnd_6691788 := by
    simpa [prefixWord, tailWord_6691788, baseEnd_6691788] using wordTrace_append hprefix tailTrace_6691788
  have hstable : (prefixWord ++ tailWord_6691788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691788).length < 2 ^ (prefixWord ++ tailWord_6691788).sum := by decide
  have hdescent : baseEnd_6691788 < baseStart_6691788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691802 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2]
def baseStart_6691802 : Nat := 118140960795 + 6691802 * 2 ^ 59
def prefixEnd_6691802 : Nat := 4983230072969 + 3 ^ 40 * 6691802 * 2
def baseEnd_6691802 : Nat := 3436110870718332527599969

theorem tailTrace_6691802 : CollatzResearch.WordTrace tailWord_6691802 prefixEnd_6691802 3436110870718332527599969 := by
  unfold tailWord_6691802
  simp only [CollatzResearch.WordTrace]
  refine ⟨61017517525687924409569415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162713380068501131758851773 61017517525687924409569415)
  ·
    refine ⟨91526276288531886614354123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61017517525687924409569415 91526276288531886614354123)
    ·
      refine ⟨137289414432797829921531185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91526276288531886614354123 137289414432797829921531185)
      ·
        refine ⟨102967060824598372441148389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137289414432797829921531185 102967060824598372441148389)
        ·
          refine ⟨19306323904612194832715323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102967060824598372441148389 19306323904612194832715323)
          ·
            refine ⟨28959485856918292249072985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19306323904612194832715323 28959485856918292249072985)
            ·
              refine ⟨21719614392688719186804739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28959485856918292249072985 21719614392688719186804739)
              ·
                refine ⟨32579421589033078780207109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21719614392688719186804739 32579421589033078780207109)
                ·
                  refine ⟨6108641547943702271288833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32579421589033078780207109 6108641547943702271288833)
                  ·
                    refine ⟨4581481160957776703466625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6108641547943702271288833 4581481160957776703466625)
                    ·
                      refine ⟨3436110870718332527599969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4581481160957776703466625 3436110870718332527599969)
                      ·
                        rfl

theorem cell23_6691802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2].length) (baseStart_6691802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691802 prefixEnd_6691802 := by exact prefixLift 6691802
  have htrace : WordTrace (prefixWord ++ tailWord_6691802) baseStart_6691802 baseEnd_6691802 := by
    simpa [prefixWord, tailWord_6691802, baseEnd_6691802] using wordTrace_append hprefix tailTrace_6691802
  have hstable : (prefixWord ++ tailWord_6691802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691802).length < 2 ^ (prefixWord ++ tailWord_6691802).sum := by decide
  have hdescent : baseEnd_6691802 < baseStart_6691802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691813 : List Nat := [1, 3, 1, 6, 2, 1, 2, 1, 2, 1, 3]
def baseStart_6691813 : Nat := 118140960795 + 6691813 * 2 ^ 59
def prefixEnd_6691813 : Nat := 4983230072969 + 3 ^ 40 * 6691813 * 2
def baseEnd_6691813 : Nat := 3436116519005531984562419

theorem tailTrace_6691813 : CollatzResearch.WordTrace tailWord_6691813 prefixEnd_6691813 3436116519005531984562419 := by
  unfold tailWord_6691813
  simp only [CollatzResearch.WordTrace]
  refine ⟨244070471305711846516928093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162713647537141231011285395 244070471305711846516928093)
  ·
    refine ⟨91526426739641942443848035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244070471305711846516928093 91526426739641942443848035)
    ·
      refine ⟨137289640109462913665772053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91526426739641942443848035 137289640109462913665772053)
      ·
        refine ⟨6435451880131074078083065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 137289640109462913665772053 6435451880131074078083065)
        ·
          refine ⟨4826588910098305558562299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6435451880131074078083065 4826588910098305558562299)
          ·
            refine ⟨7239883365147458337843449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4826588910098305558562299 7239883365147458337843449)
            ·
              refine ⟨5429912523860593753382587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7239883365147458337843449 5429912523860593753382587)
              ·
                refine ⟨8144868785790890630073881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5429912523860593753382587 8144868785790890630073881)
                ·
                  refine ⟨6108651589343167972555411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8144868785790890630073881 6108651589343167972555411)
                  ·
                    refine ⟨9162977384014751958833117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6108651589343167972555411 9162977384014751958833117)
                    ·
                      refine ⟨3436116519005531984562419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9162977384014751958833117 3436116519005531984562419)
                      ·
                        rfl

theorem cell23_6691813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_6691813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691813 prefixEnd_6691813 := by exact prefixLift 6691813
  have htrace : WordTrace (prefixWord ++ tailWord_6691813) baseStart_6691813 baseEnd_6691813 := by
    simpa [prefixWord, tailWord_6691813, baseEnd_6691813] using wordTrace_append hprefix tailTrace_6691813
  have hstable : (prefixWord ++ tailWord_6691813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691813).length < 2 ^ (prefixWord ++ tailWord_6691813).sum := by decide
  have hdescent : baseEnd_6691813 < baseStart_6691813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691848 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 1, 2, 5]
def baseStart_6691848 : Nat := 118140960795 + 6691848 * 2 ^ 59
def prefixEnd_6691848 : Nat := 4983230072969 + 3 ^ 40 * 6691848 * 2
def baseEnd_6691848 : Nat := 3436134490828439347624757

theorem tailTrace_6691848 : CollatzResearch.WordTrace tailWord_6691848 prefixEnd_6691848 3436134490828439347624757 := by
  unfold tailWord_6691848
  simp only [CollatzResearch.WordTrace]
  refine ⟨122035873930292523747226099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162714498573723364996301465 122035873930292523747226099)
  ·
    refine ⟨183053810895438785620839149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122035873930292523747226099 183053810895438785620839149)
    ·
      refine ⟨68645179085789544607814681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183053810895438785620839149 68645179085789544607814681)
      ·
        refine ⟨51483884314342158455861011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68645179085789544607814681 51483884314342158455861011)
        ·
          refine ⟨77225826471513237683791517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51483884314342158455861011 77225826471513237683791517)
          ·
            refine ⟨28959684926817464131421819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77225826471513237683791517 28959684926817464131421819)
            ·
              refine ⟨43439527390226196197132729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28959684926817464131421819 43439527390226196197132729)
              ·
                refine ⟨32579645542669647147849547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43439527390226196197132729 32579645542669647147849547)
                ·
                  refine ⟨48869468314004470721774321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32579645542669647147849547 48869468314004470721774321)
                  ·
                    refine ⟨36652101235503353041330741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48869468314004470721774321 36652101235503353041330741)
                    ·
                      refine ⟨3436134490828439347624757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36652101235503353041330741 3436134490828439347624757)
                      ·
                        rfl

theorem cell23_6691848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_6691848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691848 prefixEnd_6691848 := by exact prefixLift 6691848
  have htrace : WordTrace (prefixWord ++ tailWord_6691848) baseStart_6691848 baseEnd_6691848 := by
    simpa [prefixWord, tailWord_6691848, baseEnd_6691848] using wordTrace_append hprefix tailTrace_6691848
  have hstable : (prefixWord ++ tailWord_6691848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691848).length < 2 ^ (prefixWord ++ tailWord_6691848).sum := by decide
  have hdescent : baseEnd_6691848 < baseStart_6691848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691875 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 1, 6, 2]
def baseStart_6691875 : Nat := 118140960795 + 6691875 * 2 ^ 59
def prefixEnd_6691875 : Nat := 4983230072969 + 3 ^ 40 * 6691875 * 2
def baseEnd_6691875 : Nat := 3436148354806110741987133

theorem tailTrace_6691875 : CollatzResearch.WordTrace tailWord_6691875 prefixEnd_6691875 3436148354806110741987133 := by
  unfold tailWord_6691875
  simp only [CollatzResearch.WordTrace]
  refine ⟨244072732631487231105685079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162715155087658154070456719 244072732631487231105685079)
  ·
    refine ⟨366109098947230846658527619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244072732631487231105685079 366109098947230846658527619)
    ·
      refine ⟨549163648420846269987791429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366109098947230846658527619 549163648420846269987791429)
      ·
        refine ⟨102968184078908675622710893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 549163648420846269987791429 102968184078908675622710893)
        ·
          refine ⟨38613069029590753358516585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102968184078908675622710893 38613069029590753358516585)
          ·
            refine ⟨28959801772193065018887439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38613069029590753358516585 28959801772193065018887439)
            ·
              refine ⟨43439702658289597528331159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28959801772193065018887439 43439702658289597528331159)
              ·
                refine ⟨65159553987434396292496739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43439702658289597528331159 65159553987434396292496739)
                ·
                  refine ⟨97739330981151594438745109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65159553987434396292496739 97739330981151594438745109)
                  ·
                    refine ⟨4581531139741480989316177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97739330981151594438745109 4581531139741480989316177)
                    ·
                      refine ⟨3436148354806110741987133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4581531139741480989316177 3436148354806110741987133)
                      ·
                        rfl

theorem cell23_6691875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 6, 2].length) (baseStart_6691875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691875 prefixEnd_6691875 := by exact prefixLift 6691875
  have htrace : WordTrace (prefixWord ++ tailWord_6691875) baseStart_6691875 baseEnd_6691875 := by
    simpa [prefixWord, tailWord_6691875, baseEnd_6691875] using wordTrace_append hprefix tailTrace_6691875
  have hstable : (prefixWord ++ tailWord_6691875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691875).length < 2 ^ (prefixWord ++ tailWord_6691875).sum := by decide
  have hdescent : baseEnd_6691875 < baseStart_6691875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691892 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_6691892 : Nat := 118140960795 + 6691892 * 2 ^ 59
def prefixEnd_6691892 : Nat := 4983230072969 + 3 ^ 40 * 6691892 * 2
def baseEnd_6691892 : Nat := 3436157083977237175474555

theorem tailTrace_6691892 : CollatzResearch.WordTrace tailWord_6691892 prefixEnd_6691892 3436157083977237175474555 := by
  unfold tailWord_6691892
  simp only [CollatzResearch.WordTrace]
  refine ⟨122036676336212821504526965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162715568448283762006035953 122036676336212821504526965)
  ·
    refine ⟨11440938406519952016049403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122036676336212821504526965 11440938406519952016049403)
    ·
      refine ⟨17161407609779928024074105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11440938406519952016049403 17161407609779928024074105)
      ·
        refine ⟨12871055707334946018055579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17161407609779928024074105 12871055707334946018055579)
        ·
          refine ⟨19306583561002419027083369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12871055707334946018055579 19306583561002419027083369)
          ·
            refine ⟨14479937670751814270312527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19306583561002419027083369 14479937670751814270312527)
            ·
              refine ⟨21719906506127721405468791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14479937670751814270312527 21719906506127721405468791)
              ·
                refine ⟨32579859759191582108203187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21719906506127721405468791 32579859759191582108203187)
                ·
                  refine ⟨48869789638787373162304781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32579859759191582108203187 48869789638787373162304781)
                  ·
                    refine ⟨18326171114545264935864293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48869789638787373162304781 18326171114545264935864293)
                    ·
                      refine ⟨3436157083977237175474555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18326171114545264935864293 3436157083977237175474555)
                      ·
                        rfl

theorem cell23_6691892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_6691892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691892 prefixEnd_6691892 := by exact prefixLift 6691892
  have htrace : WordTrace (prefixWord ++ tailWord_6691892) baseStart_6691892 baseEnd_6691892 := by
    simpa [prefixWord, tailWord_6691892, baseEnd_6691892] using wordTrace_append hprefix tailTrace_6691892
  have hstable : (prefixWord ++ tailWord_6691892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691892).length < 2 ^ (prefixWord ++ tailWord_6691892).sum := by decide
  have hdescent : baseEnd_6691892 < baseStart_6691892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691918 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8]
def baseStart_6691918 : Nat := 118140960795 + 6691918 * 2 ^ 59
def prefixEnd_6691918 : Nat := 4983230072969 + 3 ^ 40 * 6691918 * 2
def baseEnd_6691918 : Nat := 3436170434474254073749435

theorem tailTrace_6691918 : CollatzResearch.WordTrace tailWord_6691918 prefixEnd_6691918 3436170434474254073749435 := by
  unfold tailWord_6691918
  simp only [CollatzResearch.WordTrace]
  refine ⟨30509287621291431181187551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162716200646887632966333605 30509287621291431181187551)
  ·
    refine ⟨45763931431937146771781327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30509287621291431181187551 45763931431937146771781327)
    ·
      refine ⟨68645897147905720157671991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45763931431937146771781327 68645897147905720157671991)
      ·
        refine ⟨102968845721858580236507987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68645897147905720157671991 102968845721858580236507987)
        ·
          refine ⟨154453268582787870354761981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102968845721858580236507987 154453268582787870354761981)
          ·
            refine ⟨57919975718545451383035743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154453268582787870354761981 57919975718545451383035743)
            ·
              refine ⟨86879963577818177074553615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57919975718545451383035743 86879963577818177074553615)
              ·
                refine ⟨130319945366727265611830423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86879963577818177074553615 130319945366727265611830423)
                ·
                  refine ⟨195479918050090898417745635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130319945366727265611830423 195479918050090898417745635)
                  ·
                    refine ⟨293219877075136347626618453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 195479918050090898417745635 293219877075136347626618453)
                    ·
                      refine ⟨3436170434474254073749435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 293219877075136347626618453 3436170434474254073749435)
                      ·
                        rfl

theorem cell23_6691918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_6691918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691918 prefixEnd_6691918 := by exact prefixLift 6691918
  have htrace : WordTrace (prefixWord ++ tailWord_6691918) baseStart_6691918 baseEnd_6691918 := by
    simpa [prefixWord, tailWord_6691918, baseEnd_6691918] using wordTrace_append hprefix tailTrace_6691918
  have hstable : (prefixWord ++ tailWord_6691918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691918).length < 2 ^ (prefixWord ++ tailWord_6691918).sum := by decide
  have hdescent : baseEnd_6691918 < baseStart_6691918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691932 : List Nat := [2, 2, 4, 1, 1, 1, 5, 1, 6]
def baseStart_6691932 : Nat := 118140960795 + 6691932 * 2 ^ 59
def prefixEnd_6691932 : Nat := 4983230072969 + 3 ^ 40 * 6691932 * 2
def baseEnd_6691932 : Nat := 381797513689268557663819

theorem tailTrace_6691932 : CollatzResearch.WordTrace tailWord_6691932 prefixEnd_6691932 381797513689268557663819 := by
  unfold tailWord_6691932
  simp only [CollatzResearch.WordTrace]
  refine ⟨122037405796140364920255025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162716541061520486560340033 122037405796140364920255025)
  ·
    refine ⟨91528054347105273690191269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122037405796140364920255025 91528054347105273690191269)
    ·
      refine ⟨17161510190082238816910863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91528054347105273690191269 17161510190082238816910863)
      ·
        refine ⟨25742265285123358225366295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17161510190082238816910863 25742265285123358225366295)
        ·
          refine ⟨38613397927685037338049443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25742265285123358225366295 38613397927685037338049443)
          ·
            refine ⟨57920096891527556007074165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38613397927685037338049443 57920096891527556007074165)
            ·
              refine ⟨5430009083580708375663203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57920096891527556007074165 5430009083580708375663203)
              ·
                refine ⟨8145013625371062563494805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5430009083580708375663203 8145013625371062563494805)
                ·
                  refine ⟨381797513689268557663819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8145013625371062563494805 381797513689268557663819)
                  ·
                    rfl

theorem cell23_6691932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 6].length) (baseStart_6691932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691932 prefixEnd_6691932 := by exact prefixLift 6691932
  have htrace : WordTrace (prefixWord ++ tailWord_6691932) baseStart_6691932 baseEnd_6691932 := by
    simpa [prefixWord, tailWord_6691932, baseEnd_6691932] using wordTrace_append hprefix tailTrace_6691932
  have hstable : (prefixWord ++ tailWord_6691932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691932).length < 2 ^ (prefixWord ++ tailWord_6691932).sum := by decide
  have hdescent : baseEnd_6691932 < baseStart_6691932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691935 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 3, 5, 2]
def baseStart_6691935 : Nat := 118140960795 + 6691935 * 2 ^ 59
def prefixEnd_6691935 : Nat := 4983230072969 + 3 ^ 40 * 6691935 * 2
def baseEnd_6691935 : Nat := 3436179163645380507236857

theorem tailTrace_6691935 : CollatzResearch.WordTrace tailWord_6691935 prefixEnd_6691935 3436179163645380507236857 := by
  unfold tailWord_6691935
  simp only [CollatzResearch.WordTrace]
  refine ⟨244074921011269861352869259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162716614007513240901912839 244074921011269861352869259)
  ·
    refine ⟨366112381516904792029303889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244074921011269861352869259 366112381516904792029303889)
    ·
      refine ⟨274584286137678594021977917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366112381516904792029303889 274584286137678594021977917)
      ·
        refine ⟨102969107301629472758241719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274584286137678594021977917 102969107301629472758241719)
        ·
          refine ⟨154453660952444209137362579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102969107301629472758241719 154453660952444209137362579)
          ·
            refine ⟨231680491428666313706043869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154453660952444209137362579 231680491428666313706043869)
            ·
              refine ⟨86880184285749867639766451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231680491428666313706043869 86880184285749867639766451)
              ·
                refine ⟨130320276428624801459649677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86880184285749867639766451 130320276428624801459649677)
                ·
                  refine ⟨48870103660734300547368629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130320276428624801459649677 48870103660734300547368629)
                  ·
                    refine ⟨4581572218193840676315809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48870103660734300547368629 4581572218193840676315809)
                    ·
                      refine ⟨3436179163645380507236857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4581572218193840676315809 3436179163645380507236857)
                      ·
                        rfl

theorem cell23_6691935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 5, 2].length) (baseStart_6691935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691935 prefixEnd_6691935 := by exact prefixLift 6691935
  have htrace : WordTrace (prefixWord ++ tailWord_6691935) baseStart_6691935 baseEnd_6691935 := by
    simpa [prefixWord, tailWord_6691935, baseEnd_6691935] using wordTrace_append hprefix tailTrace_6691935
  have hstable : (prefixWord ++ tailWord_6691935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691935).length < 2 ^ (prefixWord ++ tailWord_6691935).sum := by decide
  have hdescent : baseEnd_6691935 < baseStart_6691935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691945 : List Nat := [1, 2, 1, 1, 1, 6, 1, 4, 1, 5]
def baseStart_6691945 : Nat := 118140960795 + 6691945 * 2 ^ 59
def prefixEnd_6691945 : Nat := 4983230072969 + 3 ^ 40 * 6691945 * 2
def baseEnd_6691945 : Nat := 1145394766150641822703937

theorem tailTrace_6691945 : CollatzResearch.WordTrace tailWord_6691945 prefixEnd_6691945 1145394766150641822703937 := by
  unfold tailWord_6691945
  simp only [CollatzResearch.WordTrace]
  refine ⟨244075285741233633060733289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162716857160822422040488859 244075285741233633060733289)
  ·
    refine ⟨183056464305925224795549967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244075285741233633060733289 183056464305925224795549967)
    ·
      refine ⟨274584696458887837193324951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183056464305925224795549967 274584696458887837193324951)
      ·
        refine ⟨411877044688331755789987427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274584696458887837193324951 411877044688331755789987427)
        ·
          refine ⟨617815567032497633684981141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411877044688331755789987427 617815567032497633684981141)
          ·
            refine ⟨28960104704648326578983491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 617815567032497633684981141 28960104704648326578983491)
            ·
              refine ⟨43440157056972489868475237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28960104704648326578983491 43440157056972489868475237)
              ·
                refine ⟨8145029448182341850339107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43440157056972489868475237 8145029448182341850339107)
                ·
                  refine ⟨12217544172273512775508661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8145029448182341850339107 12217544172273512775508661)
                  ·
                    refine ⟨1145394766150641822703937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12217544172273512775508661 1145394766150641822703937)
                    ·
                      rfl

theorem cell23_6691945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 5].length) (baseStart_6691945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691945 prefixEnd_6691945 := by exact prefixLift 6691945
  have htrace : WordTrace (prefixWord ++ tailWord_6691945) baseStart_6691945 baseEnd_6691945 := by
    simpa [prefixWord, tailWord_6691945, baseEnd_6691945] using wordTrace_append hprefix tailTrace_6691945
  have hstable : (prefixWord ++ tailWord_6691945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691945).length < 2 ^ (prefixWord ++ tailWord_6691945).sum := by decide
  have hdescent : baseEnd_6691945 < baseStart_6691945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691952 : List Nat := [2, 1, 1, 1, 5, 1, 2, 3, 2, 3, 2]
def baseStart_6691952 : Nat := 118140960795 + 6691952 * 2 ^ 59
def prefixEnd_6691952 : Nat := 4983230072969 + 3 ^ 40 * 6691952 * 2
def baseEnd_6691952 : Nat := 3436187892816506940724279

theorem tailTrace_6691952 : CollatzResearch.WordTrace tailWord_6691952 prefixEnd_6691952 3436187892816506940724279 := by
  unfold tailWord_6691952
  simp only [CollatzResearch.WordTrace]
  refine ⟨122037770526104136628119055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162717027368138848837492073 122037770526104136628119055)
  ·
    refine ⟨183056655789156204942178583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122037770526104136628119055 183056655789156204942178583)
    ·
      refine ⟨274584983683734307413267875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183056655789156204942178583 274584983683734307413267875)
      ·
        refine ⟨411877475525601461119901813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274584983683734307413267875 411877475525601461119901813)
        ·
          refine ⟨38613513330525136979990795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 411877475525601461119901813 38613513330525136979990795)
          ·
            refine ⟨57920269995787705469986193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38613513330525136979990795 57920269995787705469986193)
            ·
              refine ⟨43440202496840779102489645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57920269995787705469986193 43440202496840779102489645)
              ·
                refine ⟨16290075936315292163433617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43440202496840779102489645 16290075936315292163433617)
                ·
                  refine ⟨12217556952236469122575213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16290075936315292163433617 12217556952236469122575213)
                  ·
                    refine ⟨4581583857088675920965705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12217556952236469122575213 4581583857088675920965705)
                    ·
                      refine ⟨3436187892816506940724279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4581583857088675920965705 3436187892816506940724279)
                      ·
                        rfl

theorem cell23_6691952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 2, 3, 2].length) (baseStart_6691952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691952 prefixEnd_6691952 := by exact prefixLift 6691952
  have htrace : WordTrace (prefixWord ++ tailWord_6691952) baseStart_6691952 baseEnd_6691952 := by
    simpa [prefixWord, tailWord_6691952, baseEnd_6691952] using wordTrace_append hprefix tailTrace_6691952
  have hstable : (prefixWord ++ tailWord_6691952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691952).length < 2 ^ (prefixWord ++ tailWord_6691952).sum := by decide
  have hdescent : baseEnd_6691952 < baseStart_6691952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691969 : List Nat := [1, 2, 4, 2, 2, 2, 1, 2, 2, 3, 2]
def baseStart_6691969 : Nat := 118140960795 + 6691969 * 2 ^ 59
def prefixEnd_6691969 : Nat := 4983230072969 + 3 ^ 40 * 6691969 * 2
def baseEnd_6691969 : Nat := 3436196621987633374211701

theorem tailTrace_6691969 : CollatzResearch.WordTrace tailWord_6691969 prefixEnd_6691969 3436196621987633374211701 := by
  unfold tailWord_6691969
  simp only [CollatzResearch.WordTrace]
  refine ⟨244076161093146685159606961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162717440728764456773071307 244076161093146685159606961)
  ·
    refine ⟨183057120819860013869705221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244076161093146685159606961 183057120819860013869705221)
    ·
      refine ⟨34323210153723752600569729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183057120819860013869705221 34323210153723752600569729)
      ·
        refine ⟨25742407615292814450427297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34323210153723752600569729 25742407615292814450427297)
        ·
          refine ⟨19306805711469610837820473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25742407615292814450427297 19306805711469610837820473)
          ·
            refine ⟨14480104283602208128365355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19306805711469610837820473 14480104283602208128365355)
            ·
              refine ⟨21720156425403312192548033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14480104283602208128365355 21720156425403312192548033)
              ·
                refine ⟨16290117319052484144411025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21720156425403312192548033 16290117319052484144411025)
                ·
                  refine ⟨12217587989289363108308269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16290117319052484144411025 12217587989289363108308269)
                  ·
                    refine ⟨4581595495983511165615601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12217587989289363108308269 4581595495983511165615601)
                    ·
                      refine ⟨3436196621987633374211701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4581595495983511165615601 3436196621987633374211701)
                      ·
                        rfl

theorem cell23_6691969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_6691969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691969 prefixEnd_6691969 := by exact prefixLift 6691969
  have htrace : WordTrace (prefixWord ++ tailWord_6691969) baseStart_6691969 baseEnd_6691969 := by
    simpa [prefixWord, tailWord_6691969, baseEnd_6691969] using wordTrace_append hprefix tailTrace_6691969
  have hstable : (prefixWord ++ tailWord_6691969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691969).length < 2 ^ (prefixWord ++ tailWord_6691969).sum := by decide
  have hdescent : baseEnd_6691969 < baseStart_6691969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6691976 : List Nat := [2, 1, 3, 4, 2, 2, 1, 1, 3, 1, 3]
def baseStart_6691976 : Nat := 118140960795 + 6691976 * 2 ^ 59
def prefixEnd_6691976 : Nat := 4983230072969 + 3 ^ 40 * 6691976 * 2
def baseEnd_6691976 : Nat := 3436200216352214846824169

theorem tailTrace_6691976 : CollatzResearch.WordTrace tailWord_6691976 prefixEnd_6691976 3436200216352214846824169 := by
  unfold tailWord_6691976
  simp only [CollatzResearch.WordTrace]
  refine ⟨122038208202060662677555891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162717610936080883570074521 122038208202060662677555891)
  ·
    refine ⟨183057312303090994016333837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122038208202060662677555891 183057312303090994016333837)
    ·
      refine ⟨68646492113659122756125189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183057312303090994016333837 68646492113659122756125189)
      ·
        refine ⟨12871217271311085516773473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68646492113659122756125189 12871217271311085516773473)
        ·
          refine ⟨9653412953483314137580105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12871217271311085516773473 9653412953483314137580105)
          ·
            refine ⟨7240059715112485603185079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9653412953483314137580105 7240059715112485603185079)
            ·
              refine ⟨10860089572668728404777619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7240059715112485603185079 10860089572668728404777619)
              ·
                refine ⟨16290134359003092607166429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10860089572668728404777619 16290134359003092607166429)
                ·
                  refine ⟨6108800384626159727687411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16290134359003092607166429 6108800384626159727687411)
                  ·
                    refine ⟨9163200576939239591531117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6108800384626159727687411 9163200576939239591531117)
                    ·
                      refine ⟨3436200216352214846824169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9163200576939239591531117 3436200216352214846824169)
                      ·
                        rfl

theorem cell23_6691976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_6691976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6691976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6691976 prefixEnd_6691976 := by exact prefixLift 6691976
  have htrace : WordTrace (prefixWord ++ tailWord_6691976) baseStart_6691976 baseEnd_6691976 := by
    simpa [prefixWord, tailWord_6691976, baseEnd_6691976] using wordTrace_append hprefix tailTrace_6691976
  have hstable : (prefixWord ++ tailWord_6691976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6691976).length < 2 ^ (prefixWord ++ tailWord_6691976).sum := by decide
  have hdescent : baseEnd_6691976 < baseStart_6691976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6691976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692015 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 3]
def baseStart_6692015 : Nat := 118140960795 + 6692015 * 2 ^ 59
def prefixEnd_6692015 : Nat := 4983230072969 + 3 ^ 40 * 6692015 * 2
def baseEnd_6692015 : Nat := 3436220242097740194236489

theorem tailTrace_6692015 : CollatzResearch.WordTrace tailWord_6692015 prefixEnd_6692015 3436220242097740194236489 := by
  unfold tailWord_6692015
  simp only [CollatzResearch.WordTrace]
  refine ⟨244077838850980035015781499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162718559233986690010520999 244077838850980035015781499)
  ·
    refine ⟨366116758276470052523672249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244077838850980035015781499 366116758276470052523672249)
    ·
      refine ⟨274587568707352539392754187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366116758276470052523672249 274587568707352539392754187)
      ·
        refine ⟨411881353061028809089131281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274587568707352539392754187 411881353061028809089131281)
        ·
          refine ⟨308911014795771606816848461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411881353061028809089131281 308911014795771606816848461)
          ·
            refine ⟨115841630548414352556318173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308911014795771606816848461 115841630548414352556318173)
            ·
              refine ⟨43440611455655382208619315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115841630548414352556318173 43440611455655382208619315)
              ·
                refine ⟨65160917183483073312928973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43440611455655382208619315 65160917183483073312928973)
                ·
                  refine ⟨24435343943806152492348365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65160917183483073312928973 24435343943806152492348365)
                  ·
                    refine ⟨9163253978927307184630637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24435343943806152492348365 9163253978927307184630637)
                    ·
                      refine ⟨3436220242097740194236489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9163253978927307184630637 3436220242097740194236489)
                      ·
                        rfl

theorem cell23_6692015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 3].length) (baseStart_6692015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692015 prefixEnd_6692015 := by exact prefixLift 6692015
  have htrace : WordTrace (prefixWord ++ tailWord_6692015) baseStart_6692015 baseEnd_6692015 := by
    simpa [prefixWord, tailWord_6692015, baseEnd_6692015] using wordTrace_append hprefix tailTrace_6692015
  have hstable : (prefixWord ++ tailWord_6692015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692015).length < 2 ^ (prefixWord ++ tailWord_6692015).sum := by decide
  have hdescent : baseEnd_6692015 < baseStart_6692015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692022 : List Nat := [5, 1, 3, 2, 12]
def baseStart_6692022 : Nat := 118140960795 + 6692022 * 2 ^ 59
def prefixEnd_6692022 : Nat := 4983230072969 + 3 ^ 40 * 6692022 * 2
def baseEnd_6692022 : Nat := 4713612944392759488133

theorem tailTrace_6692022 : CollatzResearch.WordTrace tailWord_6692022 prefixEnd_6692022 4713612944392759488133 := by
  unfold tailWord_6692022
  simp only [CollatzResearch.WordTrace]
  refine ⟨15254880885122167200705395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162718729441303116807524213 15254880885122167200705395)
  ·
    refine ⟨22882321327683250801058093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15254880885122167200705395 22882321327683250801058093)
    ·
      refine ⟨8580870497881219050396785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22882321327683250801058093 8580870497881219050396785)
      ·
        refine ⟨6435652873410914287797589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8580870497881219050396785 6435652873410914287797589)
        ·
          refine ⟨4713612944392759488133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6435652873410914287797589 4713612944392759488133)
          ·
            rfl

theorem cell23_6692022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 12].length) (baseStart_6692022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692022 prefixEnd_6692022 := by exact prefixLift 6692022
  have htrace : WordTrace (prefixWord ++ tailWord_6692022) baseStart_6692022 baseEnd_6692022 := by
    simpa [prefixWord, tailWord_6692022, baseEnd_6692022] using wordTrace_append hprefix tailTrace_6692022
  have hstable : (prefixWord ++ tailWord_6692022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692022).length < 2 ^ (prefixWord ++ tailWord_6692022).sum := by decide
  have hdescent : baseEnd_6692022 < baseStart_6692022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692076 : List Nat := [2, 2, 1, 1, 2, 4, 4, 1, 1, 3, 2]
def baseStart_6692076 : Nat := 118140960795 + 6692076 * 2 ^ 59
def prefixEnd_6692076 : Nat := 4983230072969 + 3 ^ 40 * 6692076 * 2
def baseEnd_6692076 : Nat := 3436251564417664455573709

theorem tailTrace_6692076 : CollatzResearch.WordTrace tailWord_6692076 prefixEnd_6692076 3436251564417664455573709 := by
  unfold tailWord_6692076
  simp only [CollatzResearch.WordTrace]
  refine ⟨122040031851879521216876041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162720042469172694955834721 122040031851879521216876041)
  ·
    refine ⟨91530023888909640912657031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122040031851879521216876041 91530023888909640912657031)
    ·
      refine ⟨137295035833364461368985547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91530023888909640912657031 137295035833364461368985547)
      ·
        refine ⟨205942553750046692053478321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137295035833364461368985547 205942553750046692053478321)
        ·
          refine ⟨154456915312535019040108741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205942553750046692053478321 154456915312535019040108741)
          ·
            refine ⟨28960671621100316070020389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154456915312535019040108741 28960671621100316070020389)
            ·
              refine ⟨5430125928956309263128823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28960671621100316070020389 5430125928956309263128823)
              ·
                refine ⟨8145188893434463894693235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5430125928956309263128823 8145188893434463894693235)
                ·
                  refine ⟨12217783340151695842039853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8145188893434463894693235 12217783340151695842039853)
                  ·
                    refine ⟨4581668752556885940764945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12217783340151695842039853 4581668752556885940764945)
                    ·
                      refine ⟨3436251564417664455573709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4581668752556885940764945 3436251564417664455573709)
                      ·
                        rfl

theorem cell23_6692076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 3, 2].length) (baseStart_6692076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692076 prefixEnd_6692076 := by exact prefixLift 6692076
  have htrace : WordTrace (prefixWord ++ tailWord_6692076) baseStart_6692076 baseEnd_6692076 := by
    simpa [prefixWord, tailWord_6692076, baseEnd_6692076] using wordTrace_append hprefix tailTrace_6692076
  have hstable : (prefixWord ++ tailWord_6692076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692076).length < 2 ^ (prefixWord ++ tailWord_6692076).sum := by decide
  have hdescent : baseEnd_6692076 < baseStart_6692076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692089 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 4, 2, 2]
def baseStart_6692089 : Nat := 118140960795 + 6692089 * 2 ^ 59
def prefixEnd_6692089 : Nat := 4983230072969 + 3 ^ 40 * 6692089 * 2
def baseEnd_6692089 : Nat := 3436258239666172904711149

theorem tailTrace_6692089 : CollatzResearch.WordTrace tailWord_6692089 prefixEnd_6692089 3436258239666172904711149 := by
  unfold tailWord_6692089
  simp only [CollatzResearch.WordTrace]
  refine ⟨244080537852711945653975321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162720358568474630435983547 244080537852711945653975321)
  ·
    refine ⟨183060403389533959240481491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244080537852711945653975321 183060403389533959240481491)
    ·
      refine ⟨274590605084300938860722237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183060403389533959240481491 274590605084300938860722237)
      ·
        refine ⟨102971476906612852072770839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274590605084300938860722237 102971476906612852072770839)
        ·
          refine ⟨154457215359919278109156259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102971476906612852072770839 154457215359919278109156259)
          ·
            refine ⟨231685823039878917163734389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154457215359919278109156259 231685823039878917163734389)
            ·
              refine ⟨21720545909988648484100099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 231685823039878917163734389 21720545909988648484100099)
              ·
                refine ⟨32580818864982972726150149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21720545909988648484100099 32580818864982972726150149)
                ·
                  refine ⟨6108903537184307386153153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32580818864982972726150149 6108903537184307386153153)
                  ·
                    refine ⟨4581677652888230539614865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6108903537184307386153153 4581677652888230539614865)
                    ·
                      refine ⟨3436258239666172904711149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4581677652888230539614865 3436258239666172904711149)
                      ·
                        rfl

theorem cell23_6692089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 2, 2].length) (baseStart_6692089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692089 prefixEnd_6692089 := by exact prefixLift 6692089
  have htrace : WordTrace (prefixWord ++ tailWord_6692089) baseStart_6692089 baseEnd_6692089 := by
    simpa [prefixWord, tailWord_6692089, baseEnd_6692089] using wordTrace_append hprefix tailTrace_6692089
  have hstable : (prefixWord ++ tailWord_6692089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692089).length < 2 ^ (prefixWord ++ tailWord_6692089).sum := by decide
  have hdescent : baseEnd_6692089 < baseStart_6692089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692095 : List Nat := [1, 1, 2, 2, 1, 5, 1, 3, 7]
def baseStart_6692095 : Nat := 118140960795 + 6692095 * 2 ^ 59
def prefixEnd_6692095 : Nat := 4983230072969 + 3 ^ 40 * 6692095 * 2
def baseEnd_6692095 : Nat := 381806813394455542359569

theorem tailTrace_6692095 : CollatzResearch.WordTrace tailWord_6692095 prefixEnd_6692095 381806813394455542359569 := by
  unfold tailWord_6692095
  simp only [CollatzResearch.WordTrace]
  refine ⟨244080756690690208678693739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162720504460460139119129159 244080756690690208678693739)
  ·
    refine ⟨366121135036035313018040609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244080756690690208678693739 366121135036035313018040609)
    ·
      refine ⟨274590851277026484763530457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366121135036035313018040609 274590851277026484763530457)
      ·
        refine ⟨205943138457769863572647843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274590851277026484763530457 205943138457769863572647843)
        ·
          refine ⟨308914707686654795358971765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205943138457769863572647843 308914707686654795358971765)
          ·
            refine ⟨28960753845623887064903603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 308914707686654795358971765 28960753845623887064903603)
            ·
              refine ⟨43441130768435830597355405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28960753845623887064903603 43441130768435830597355405)
              ·
                refine ⟨16290424038163436474008277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43441130768435830597355405 16290424038163436474008277)
                ·
                  refine ⟨381806813394455542359569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16290424038163436474008277 381806813394455542359569)
                  ·
                    rfl

theorem cell23_6692095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 7].length) (baseStart_6692095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692095 prefixEnd_6692095 := by exact prefixLift 6692095
  have htrace : WordTrace (prefixWord ++ tailWord_6692095) baseStart_6692095 baseEnd_6692095 := by
    simpa [prefixWord, tailWord_6692095, baseEnd_6692095] using wordTrace_append hprefix tailTrace_6692095
  have hstable : (prefixWord ++ tailWord_6692095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692095).length < 2 ^ (prefixWord ++ tailWord_6692095).sum := by decide
  have hdescent : baseEnd_6692095 < baseStart_6692095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692126 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_6692126 : Nat := 118140960795 + 6692126 * 2 ^ 59
def prefixEnd_6692126 : Nat := 4983230072969 + 3 ^ 40 * 6692126 * 2
def baseEnd_6692126 : Nat := 3436277238450389259948479

theorem tailTrace_6692126 : CollatzResearch.WordTrace tailWord_6692126 prefixEnd_6692126 3436277238450389259948479 := by
  unfold tailWord_6692126
  simp only [CollatzResearch.WordTrace]
  refine ⟨30510235919197237621634029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162721258235718600648714821 30510235919197237621634029)
  ·
    refine ⟨11441338469698964108112761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30510235919197237621634029 11441338469698964108112761)
    ·
      refine ⟨8581003852274223081084571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11441338469698964108112761 8581003852274223081084571)
      ·
        refine ⟨12871505778411334621626857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8581003852274223081084571 12871505778411334621626857)
        ·
          refine ⟨9653629333808500966220143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12871505778411334621626857 9653629333808500966220143)
          ·
            refine ⟨14480444000712751449330215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9653629333808500966220143 14480444000712751449330215)
            ·
              refine ⟨21720666001069127173995323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14480444000712751449330215 21720666001069127173995323)
              ·
                refine ⟨32580999001603690760992985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21720666001069127173995323 32580999001603690760992985)
                ·
                  refine ⟨24435749251202768070744739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32580999001603690760992985 24435749251202768070744739)
                  ·
                    refine ⟨36653623876804152106117109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24435749251202768070744739 36653623876804152106117109)
                    ·
                      refine ⟨3436277238450389259948479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36653623876804152106117109 3436277238450389259948479)
                      ·
                        rfl

theorem cell23_6692126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_6692126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692126 prefixEnd_6692126 := by exact prefixLift 6692126
  have htrace : WordTrace (prefixWord ++ tailWord_6692126) baseStart_6692126 baseEnd_6692126 := by
    simpa [prefixWord, tailWord_6692126, baseEnd_6692126] using wordTrace_append hprefix tailTrace_6692126
  have hstable : (prefixWord ++ tailWord_6692126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692126).length < 2 ^ (prefixWord ++ tailWord_6692126).sum := by decide
  have hdescent : baseEnd_6692126 < baseStart_6692126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692146 : List Nat := [3, 2, 1, 1, 4, 2, 3, 2, 5]
def baseStart_6692146 : Nat := 118140960795 + 6692146 * 2 ^ 59
def prefixEnd_6692146 : Nat := 4983230072969 + 3 ^ 40 * 6692146 * 2
def baseEnd_6692146 : Nat := 381809723118164353522043

theorem tailTrace_6692146 : CollatzResearch.WordTrace tailWord_6692146 prefixEnd_6692146 381809723118164353522043 := by
  unfold tailWord_6692146
  simp only [CollatzResearch.WordTrace]
  refine ⟨61020654203376361097200073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162721744542336962925866861 61020654203376361097200073)
  ·
    refine ⟨45765490652532270822900055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61020654203376361097200073 45765490652532270822900055)
    ·
      refine ⟨68648235978798406234350083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45765490652532270822900055 68648235978798406234350083)
      ·
        refine ⟨102972353968197609351525125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68648235978798406234350083 102972353968197609351525125)
        ·
          refine ⟨19307316369037051753410961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102972353968197609351525125 19307316369037051753410961)
          ·
            refine ⟨14480487276777788815058221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19307316369037051753410961 14480487276777788815058221)
            ·
              refine ⟨5430182728791670805646833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14480487276777788815058221 5430182728791670805646833)
              ·
                refine ⟨4072637046593753104235125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5430182728791670805646833 4072637046593753104235125)
                ·
                  refine ⟨381809723118164353522043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4072637046593753104235125 381809723118164353522043)
                  ·
                    rfl

theorem cell23_6692146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_6692146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692146 prefixEnd_6692146 := by exact prefixLift 6692146
  have htrace : WordTrace (prefixWord ++ tailWord_6692146) baseStart_6692146 baseEnd_6692146 := by
    simpa [prefixWord, tailWord_6692146, baseEnd_6692146] using wordTrace_append hprefix tailTrace_6692146
  have hstable : (prefixWord ++ tailWord_6692146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692146).length < 2 ^ (prefixWord ++ tailWord_6692146).sum := by decide
  have hdescent : baseEnd_6692146 < baseStart_6692146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692157 : List Nat := [1, 4, 1, 5, 1, 2, 2, 1, 2, 2, 2]
def baseStart_6692157 : Nat := 118140960795 + 6692157 * 2 ^ 59
def prefixEnd_6692157 : Nat := 4983230072969 + 3 ^ 40 * 6692157 * 2
def baseEnd_6692157 : Nat := 3436293156350678638660837

theorem tailTrace_6692157 : CollatzResearch.WordTrace tailWord_6692157 prefixEnd_6692157 3436293156350678638660837 := by
  unfold tailWord_6692157
  simp only [CollatzResearch.WordTrace]
  refine ⟨244083018016465593267450725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162722012010977062178300483 244083018016465593267450725)
  ·
    refine ⟨45765565878087298737647011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244083018016465593267450725 45765565878087298737647011)
    ·
      refine ⟨68648348817130948106470517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45765565878087298737647011 68648348817130948106470517)
      ·
        refine ⟨6435782701606026384981611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68648348817130948106470517 6435782701606026384981611)
        ·
          refine ⟨9653674052409039577472417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6435782701606026384981611 9653674052409039577472417)
          ·
            refine ⟨7240255539306779683104313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9653674052409039577472417 7240255539306779683104313)
            ·
              refine ⟨5430191654480084762328235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7240255539306779683104313 5430191654480084762328235)
              ·
                refine ⟨8145287481720127143492353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5430191654480084762328235 8145287481720127143492353)
                ·
                  refine ⟨6108965611290095357619265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8145287481720127143492353 6108965611290095357619265)
                  ·
                    refine ⟨4581724208467571518214449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6108965611290095357619265 4581724208467571518214449)
                    ·
                      refine ⟨3436293156350678638660837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4581724208467571518214449 3436293156350678638660837)
                      ·
                        rfl

theorem cell23_6692157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_6692157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692157 prefixEnd_6692157 := by exact prefixLift 6692157
  have htrace : WordTrace (prefixWord ++ tailWord_6692157) baseStart_6692157 baseEnd_6692157 := by
    simpa [prefixWord, tailWord_6692157, baseEnd_6692157] using wordTrace_append hprefix tailTrace_6692157
  have hstable : (prefixWord ++ tailWord_6692157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692157).length < 2 ^ (prefixWord ++ tailWord_6692157).sum := by decide
  have hdescent : baseEnd_6692157 < baseStart_6692157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692165 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 1, 5, 5]
def baseStart_6692165 : Nat := 118140960795 + 6692165 * 2 ^ 59
def prefixEnd_6692165 : Nat := 4983230072969 + 3 ^ 40 * 6692165 * 2
def baseEnd_6692165 : Nat := 3436297264195914607360799

theorem tailTrace_6692165 : CollatzResearch.WordTrace tailWord_6692165 prefixEnd_6692165 3436297264195914607360799 := by
  unfold tailWord_6692165
  simp only [CollatzResearch.WordTrace]
  refine ⟨244083309800436610633741949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162722206533624407089161299 244083309800436610633741949)
  ·
    refine ⟨91531241175163728987653231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244083309800436610633741949 91531241175163728987653231)
    ·
      refine ⟨137296861762745593481479847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91531241175163728987653231 137296861762745593481479847)
      ·
        refine ⟨205945292644118390222219771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137296861762745593481479847 205945292644118390222219771)
        ·
          refine ⟨308917938966177585333329657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205945292644118390222219771 308917938966177585333329657)
          ·
            refine ⟨231688454224633188999997243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308917938966177585333329657 231688454224633188999997243)
            ·
              refine ⟨347532681336949783499995865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231688454224633188999997243 347532681336949783499995865)
              ·
                refine ⟨260649511002712337624996899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347532681336949783499995865 260649511002712337624996899)
                ·
                  refine ⟨390974266504068506437495349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 260649511002712337624996899 390974266504068506437495349)
                  ·
                    refine ⟨36653837484756422478515189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 390974266504068506437495349 36653837484756422478515189)
                    ·
                      refine ⟨3436297264195914607360799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36653837484756422478515189 3436297264195914607360799)
                      ·
                        rfl

theorem cell23_6692165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_6692165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692165 prefixEnd_6692165 := by exact prefixLift 6692165
  have htrace : WordTrace (prefixWord ++ tailWord_6692165) baseStart_6692165 baseEnd_6692165 := by
    simpa [prefixWord, tailWord_6692165, baseEnd_6692165] using wordTrace_append hprefix tailTrace_6692165
  have hstable : (prefixWord ++ tailWord_6692165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692165).length < 2 ^ (prefixWord ++ tailWord_6692165).sum := by decide
  have hdescent : baseEnd_6692165 < baseStart_6692165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692185 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 10]
def baseStart_6692185 : Nat := 118140960795 + 6692185 * 2 ^ 59
def prefixEnd_6692185 : Nat := 4983230072969 + 3 ^ 40 * 6692185 * 2
def baseEnd_6692185 : Nat := 381811948201000503234523

theorem tailTrace_6692185 : CollatzResearch.WordTrace tailWord_6692185 prefixEnd_6692185 381811948201000503234523 := by
  unfold tailWord_6692185
  simp only [CollatzResearch.WordTrace]
  refine ⟨244084039260364154049470009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162722692840242769366313339 244084039260364154049470009)
  ·
    refine ⟨183063029445273115537102507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244084039260364154049470009 183063029445273115537102507)
    ·
      refine ⟨274594544167909673305653761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183063029445273115537102507 274594544167909673305653761)
      ·
        refine ⟨205945908125932254979240321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274594544167909673305653761 205945908125932254979240321)
        ·
          refine ⟨154459431094449191234430241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205945908125932254979240321 154459431094449191234430241)
          ·
            refine ⟨115844573320836893425822681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154459431094449191234430241 115844573320836893425822681)
            ·
              refine ⟨86883429990627670069367011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115844573320836893425822681 86883429990627670069367011)
              ·
                refine ⟨130325144985941505104050517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86883429990627670069367011 130325144985941505104050517)
                ·
                  refine ⟨381811948201000503234523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 130325144985941505104050517 381811948201000503234523)
                  ·
                    rfl

theorem cell23_6692185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 10].length) (baseStart_6692185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692185 prefixEnd_6692185 := by exact prefixLift 6692185
  have htrace : WordTrace (prefixWord ++ tailWord_6692185) baseStart_6692185 baseEnd_6692185 := by
    simpa [prefixWord, tailWord_6692185, baseEnd_6692185] using wordTrace_append hprefix tailTrace_6692185
  have hstable : (prefixWord ++ tailWord_6692185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692185).length < 2 ^ (prefixWord ++ tailWord_6692185).sum := by decide
  have hdescent : baseEnd_6692185 < baseStart_6692185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692229 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 5, 1, 3]
def baseStart_6692229 : Nat := 118140960795 + 6692229 * 2 ^ 59
def prefixEnd_6692229 : Nat := 4983230072969 + 3 ^ 40 * 6692229 * 2
def baseEnd_6692229 : Nat := 3436330126957802356960505

theorem tailTrace_6692229 : CollatzResearch.WordTrace tailWord_6692229 prefixEnd_6692229 3436330126957802356960505 := by
  unfold tailWord_6692229
  simp only [CollatzResearch.WordTrace]
  refine ⟨244085644072204749564071741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162723762714803166376047827 244085644072204749564071741)
  ·
    refine ⟨91532116527076781086526903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244085644072204749564071741 91532116527076781086526903)
    ·
      refine ⟨137298174790615171629790355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91532116527076781086526903 137298174790615171629790355)
      ·
        refine ⟨205947262185922757444685533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137298174790615171629790355 205947262185922757444685533)
        ·
          refine ⟨77230223319721034041757075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205947262185922757444685533 77230223319721034041757075)
          ·
            refine ⟨115845334979581551062635613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77230223319721034041757075 115845334979581551062635613)
            ·
              refine ⟨43442000617343081648488355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115845334979581551062635613 43442000617343081648488355)
              ·
                refine ⟨65163000926014622472732533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43442000617343081648488355 65163000926014622472732533)
                ·
                  refine ⟨6109031336813870856818675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65163000926014622472732533 6109031336813870856818675)
                  ·
                    refine ⟨9163547005220806285228013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6109031336813870856818675 9163547005220806285228013)
                    ·
                      refine ⟨3436330126957802356960505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9163547005220806285228013 3436330126957802356960505)
                      ·
                        rfl

theorem cell23_6692229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 1, 3].length) (baseStart_6692229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692229 prefixEnd_6692229 := by exact prefixLift 6692229
  have htrace : WordTrace (prefixWord ++ tailWord_6692229) baseStart_6692229 baseEnd_6692229 := by
    simpa [prefixWord, tailWord_6692229, baseEnd_6692229] using wordTrace_append hprefix tailTrace_6692229
  have hstable : (prefixWord ++ tailWord_6692229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692229).length < 2 ^ (prefixWord ++ tailWord_6692229).sum := by decide
  have hdescent : baseEnd_6692229 < baseStart_6692229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692233 : List Nat := [1, 2, 1, 1, 8, 1, 1, 1, 2, 2, 3]
def baseStart_6692233 : Nat := 118140960795 + 6692233 * 2 ^ 59
def prefixEnd_6692233 : Nat := 4983230072969 + 3 ^ 40 * 6692233 * 2
def baseEnd_6692233 : Nat := 3436332180880420341310487

theorem tailTrace_6692233 : CollatzResearch.WordTrace tailWord_6692233 prefixEnd_6692233 3436332180880420341310487 := by
  unfold tailWord_6692233
  simp only [CollatzResearch.WordTrace]
  refine ⟨244085789964190258247217353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162723859976126838831478235 244085789964190258247217353)
  ·
    refine ⟨183064342473142693685413015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244085789964190258247217353 183064342473142693685413015)
    ·
      refine ⟨274596513709714040528119523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183064342473142693685413015 274596513709714040528119523)
      ·
        refine ⟨411894770564571060792179285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274596513709714040528119523 411894770564571060792179285)
        ·
          refine ⟨4826891842553567118658351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 411894770564571060792179285 4826891842553567118658351)
          ·
            refine ⟨7240337763830350677987527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4826891842553567118658351 7240337763830350677987527)
            ·
              refine ⟨10860506645745526016981291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7240337763830350677987527 10860506645745526016981291)
              ·
                refine ⟨16290759968618289025471937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10860506645745526016981291 16290759968618289025471937)
                ·
                  refine ⟨12218069976463716769103953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16290759968618289025471937 12218069976463716769103953)
                  ·
                    refine ⟨9163552482347787576827965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12218069976463716769103953 9163552482347787576827965)
                    ·
                      refine ⟨3436332180880420341310487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9163552482347787576827965 3436332180880420341310487)
                      ·
                        rfl

theorem cell23_6692233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 2, 2, 3].length) (baseStart_6692233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692233 prefixEnd_6692233 := by exact prefixLift 6692233
  have htrace : WordTrace (prefixWord ++ tailWord_6692233) baseStart_6692233 baseEnd_6692233 := by
    simpa [prefixWord, tailWord_6692233, baseEnd_6692233] using wordTrace_append hprefix tailTrace_6692233
  have hstable : (prefixWord ++ tailWord_6692233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692233).length < 2 ^ (prefixWord ++ tailWord_6692233).sum := by decide
  have hdescent : baseEnd_6692233 < baseStart_6692233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692249 : List Nat := [1, 2, 1, 2, 1, 6, 1, 3, 1, 5]
def baseStart_6692249 : Nat := 118140960795 + 6692249 * 2 ^ 59
def prefixEnd_6692249 : Nat := 4983230072969 + 3 ^ 40 * 6692249 * 2
def baseEnd_6692249 : Nat := 1145446798856964092903471

theorem tailTrace_6692249 : CollatzResearch.WordTrace tailWord_6692249 prefixEnd_6692249 1145446798856964092903471 := by
  unfold tailWord_6692249
  simp only [CollatzResearch.WordTrace]
  refine ⟨244086373532132292979799801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162724249021421528653199867 244086373532132292979799801)
  ·
    refine ⟨183064780149099219734849851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244086373532132292979799801 183064780149099219734849851)
    ·
      refine ⟨274597170223648829602274777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183064780149099219734849851 274597170223648829602274777)
      ·
        refine ⟨205947877667736622201706083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274597170223648829602274777 205947877667736622201706083)
        ·
          refine ⟨308921816501604933302559125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205947877667736622201706083 308921816501604933302559125)
          ·
            refine ⟨14480710148512731248557459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 308921816501604933302559125 14480710148512731248557459)
            ·
              refine ⟨21721065222769096872836189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14480710148512731248557459 21721065222769096872836189)
              ·
                refine ⟨8145399458538411327313571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21721065222769096872836189 8145399458538411327313571)
                ·
                  refine ⟨12218099187807616990970357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8145399458538411327313571 12218099187807616990970357)
                  ·
                    refine ⟨1145446798856964092903471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12218099187807616990970357 1145446798856964092903471)
                    ·
                      rfl

theorem cell23_6692249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 5].length) (baseStart_6692249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692249 prefixEnd_6692249 := by exact prefixLift 6692249
  have htrace : WordTrace (prefixWord ++ tailWord_6692249) baseStart_6692249 baseEnd_6692249 := by
    simpa [prefixWord, tailWord_6692249, baseEnd_6692249] using wordTrace_append hprefix tailTrace_6692249
  have hstable : (prefixWord ++ tailWord_6692249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692249).length < 2 ^ (prefixWord ++ tailWord_6692249).sum := by decide
  have hdescent : baseEnd_6692249 < baseStart_6692249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692263 : List Nat := [1, 1, 6, 1, 1, 1, 1, 6, 1, 1, 3]
def baseStart_6692263 : Nat := 118140960795 + 6692263 * 2 ^ 59
def prefixEnd_6692263 : Nat := 4983230072969 + 3 ^ 40 * 6692263 * 2
def baseEnd_6692263 : Nat := 3436347585300055223935349

theorem tailTrace_6692263 : CollatzResearch.WordTrace tailWord_6692263 prefixEnd_6692263 3436347585300055223935349 := by
  unfold tailWord_6692263
  simp only [CollatzResearch.WordTrace]
  refine ⟨244086884154081573370809443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162724589436054382247206295 244086884154081573370809443)
  ·
    refine ⟨366130326231122360056214165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244086884154081573370809443 366130326231122360056214165)
    ·
      refine ⟨17162359042083860627635039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 366130326231122360056214165 17162359042083860627635039)
      ·
        refine ⟨25743538563125790941452559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17162359042083860627635039 25743538563125790941452559)
        ·
          refine ⟨38615307844688686412178839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25743538563125790941452559 38615307844688686412178839)
          ·
            refine ⟨57922961767033029618268259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38615307844688686412178839 57922961767033029618268259)
            ·
              refine ⟨86884442650549544427402389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57922961767033029618268259 86884442650549544427402389)
              ·
                refine ⟨4072708249244509895034487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86884442650549544427402389 4072708249244509895034487)
                ·
                  refine ⟨6109062373866764842551731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4072708249244509895034487 6109062373866764842551731)
                  ·
                    refine ⟨9163593560800147263827597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6109062373866764842551731 9163593560800147263827597)
                    ·
                      refine ⟨3436347585300055223935349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9163593560800147263827597 3436347585300055223935349)
                      ·
                        rfl

theorem cell23_6692263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_6692263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692263 prefixEnd_6692263 := by exact prefixLift 6692263
  have htrace : WordTrace (prefixWord ++ tailWord_6692263) baseStart_6692263 baseEnd_6692263 := by
    simpa [prefixWord, tailWord_6692263, baseEnd_6692263] using wordTrace_append hprefix tailTrace_6692263
  have hstable : (prefixWord ++ tailWord_6692263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692263).length < 2 ^ (prefixWord ++ tailWord_6692263).sum := by decide
  have hdescent : baseEnd_6692263 < baseStart_6692263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692272 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 3]
def baseStart_6692272 : Nat := 118140960795 + 6692272 * 2 ^ 59
def prefixEnd_6692272 : Nat := 4983230072969 + 3 ^ 40 * 6692272 * 2
def baseEnd_6692272 : Nat := 3436352206625945688722807

theorem tailTrace_6692272 : CollatzResearch.WordTrace tailWord_6692272 prefixEnd_6692272 3436352206625945688722807 := by
  unfold tailWord_6692272
  simp only [CollatzResearch.WordTrace]
  refine ⟨122043606205524483953943535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162724808274032645271924713 122043606205524483953943535)
  ·
    refine ⟨183065409308286725930915303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122043606205524483953943535 183065409308286725930915303)
    ·
      refine ⟨274598113962430088896372955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183065409308286725930915303 274598113962430088896372955)
      ·
        refine ⟨411897170943645133344559433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274598113962430088896372955 411897170943645133344559433)
        ·
          refine ⟨308922878207733850008419575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411897170943645133344559433 308922878207733850008419575)
          ·
            refine ⟨463384317311600775012629363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308922878207733850008419575 463384317311600775012629363)
            ·
              refine ⟨695076475967401162518944045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463384317311600775012629363 695076475967401162518944045)
              ·
                refine ⟨260653678487775435944604017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 695076475967401162518944045 260653678487775435944604017)
                ·
                  refine ⟨195490258865831576958453013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260653678487775435944604017 195490258865831576958453013)
                  ·
                    refine ⟨9163605884335855169927485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 195490258865831576958453013 9163605884335855169927485)
                    ·
                      refine ⟨3436352206625945688722807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9163605884335855169927485 3436352206625945688722807)
                      ·
                        rfl

theorem cell23_6692272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 3].length) (baseStart_6692272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692272 prefixEnd_6692272 := by exact prefixLift 6692272
  have htrace : WordTrace (prefixWord ++ tailWord_6692272) baseStart_6692272 baseEnd_6692272 := by
    simpa [prefixWord, tailWord_6692272, baseEnd_6692272] using wordTrace_append hprefix tailTrace_6692272
  have hstable : (prefixWord ++ tailWord_6692272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692272).length < 2 ^ (prefixWord ++ tailWord_6692272).sum := by decide
  have hdescent : baseEnd_6692272 < baseStart_6692272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692330 : List Nat := [3, 1, 3, 1, 4, 2, 2, 1, 2, 4]
def baseStart_6692330 : Nat := 118140960795 + 6692330 * 2 ^ 59
def prefixEnd_6692330 : Nat := 4983230072969 + 3 ^ 40 * 6692330 * 2
def baseEnd_6692330 : Nat := 1145460662834635487265847

theorem tailTrace_6692330 : CollatzResearch.WordTrace tailWord_6692330 prefixEnd_6692330 1145460662834635487265847 := by
  unfold tailWord_6692330
  simp only [CollatzResearch.WordTrace]
  refine ⟨61022331961209710953374611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162726218563225895875665629 61022331961209710953374611)
  ·
    refine ⟨91533497941814566430061917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61022331961209710953374611 91533497941814566430061917)
    ·
      refine ⟨34325061728180462411273219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91533497941814566430061917 34325061728180462411273219)
      ·
        refine ⟨51487592592270693616909829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34325061728180462411273219 51487592592270693616909829)
        ·
          refine ⟨9653923611050755053170593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51487592592270693616909829 9653923611050755053170593)
          ·
            refine ⟨7240442708288066289877945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9653923611050755053170593 7240442708288066289877945)
            ·
              refine ⟨5430332031216049717408459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7240442708288066289877945 5430332031216049717408459)
              ·
                refine ⟨8145498046824074576112689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5430332031216049717408459 8145498046824074576112689)
                ·
                  refine ⟨6109123535118055932084517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8145498046824074576112689 6109123535118055932084517)
                  ·
                    refine ⟨1145460662834635487265847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6109123535118055932084517 1145460662834635487265847)
                    ·
                      rfl

theorem cell23_6692330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_6692330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692330 prefixEnd_6692330 := by exact prefixLift 6692330
  have htrace : WordTrace (prefixWord ++ tailWord_6692330) baseStart_6692330 baseEnd_6692330 := by
    simpa [prefixWord, tailWord_6692330, baseEnd_6692330] using wordTrace_append hprefix tailTrace_6692330
  have hstable : (prefixWord ++ tailWord_6692330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692330).length < 2 ^ (prefixWord ++ tailWord_6692330).sum := by decide
  have hdescent : baseEnd_6692330 < baseStart_6692330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692332 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 5]
def baseStart_6692332 : Nat := 118140960795 + 6692332 * 2 ^ 59
def prefixEnd_6692332 : Nat := 4983230072969 + 3 ^ 40 * 6692332 * 2
def baseEnd_6692332 : Nat := 3436383015465215453972531

theorem tailTrace_6692332 : CollatzResearch.WordTrace tailWord_6692332 prefixEnd_6692332 3436383015465215453972531 := by
  unfold tailWord_6692332
  simp only [CollatzResearch.WordTrace]
  refine ⟨122044700395415799077535625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162726267193887732103380833 122044700395415799077535625)
  ·
    refine ⟨91533525296561849308151719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122044700395415799077535625 91533525296561849308151719)
    ·
      refine ⟨137300287944842773962227579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91533525296561849308151719 137300287944842773962227579)
      ·
        refine ⟨205950431917264160943341369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137300287944842773962227579 205950431917264160943341369)
        ·
          refine ⟨154462823937948120707506027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205950431917264160943341369 154462823937948120707506027)
          ·
            refine ⟨231694235906922181061259041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154462823937948120707506027 231694235906922181061259041)
            ·
              refine ⟨173770676930191635795944281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231694235906922181061259041 173770676930191635795944281)
              ·
                refine ⟨130328007697643726846958211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173770676930191635795944281 130328007697643726846958211)
                ·
                  refine ⟨195492011546465590270437317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130328007697643726846958211 195492011546465590270437317)
                  ·
                    refine ⟨36654752164962298175706997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 195492011546465590270437317 36654752164962298175706997)
                    ·
                      refine ⟨3436383015465215453972531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36654752164962298175706997 3436383015465215453972531)
                      ·
                        rfl

theorem cell23_6692332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_6692332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692332 prefixEnd_6692332 := by exact prefixLift 6692332
  have htrace : WordTrace (prefixWord ++ tailWord_6692332) baseStart_6692332 baseEnd_6692332 := by
    simpa [prefixWord, tailWord_6692332, baseEnd_6692332] using wordTrace_append hprefix tailTrace_6692332
  have hstable : (prefixWord ++ tailWord_6692332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692332).length < 2 ^ (prefixWord ++ tailWord_6692332).sum := by decide
  have hdescent : baseEnd_6692332 < baseStart_6692332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692346 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2]
def baseStart_6692346 : Nat := 118140960795 + 6692346 * 2 ^ 59
def prefixEnd_6692346 : Nat := 4983230072969 + 3 ^ 40 * 6692346 * 2
def baseEnd_6692346 : Nat := 3436390204194378399197467

theorem tailTrace_6692346 : CollatzResearch.WordTrace tailWord_6692346 prefixEnd_6692346 3436390204194378399197467 := by
  unfold tailWord_6692346
  simp only [CollatzResearch.WordTrace]
  refine ⟨61022477853195219636520223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162726607608520585697387261 61022477853195219636520223)
  ·
    refine ⟨91533716779792829454780335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61022477853195219636520223 91533716779792829454780335)
    ·
      refine ⟨137300575169689244182170503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91533716779792829454780335 137300575169689244182170503)
      ·
        refine ⟨205950862754533866273255755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137300575169689244182170503 205950862754533866273255755)
        ·
          refine ⟨308926294131800799409883633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205950862754533866273255755 308926294131800799409883633)
          ·
            refine ⟨231694720598850599557412725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308926294131800799409883633 231694720598850599557412725)
            ·
              refine ⟨21721380056142243708507443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 231694720598850599557412725 21721380056142243708507443)
              ·
                refine ⟨32582070084213365562761165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21721380056142243708507443 32582070084213365562761165)
                ·
                  refine ⟨12218276281580012086035437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32582070084213365562761165 12218276281580012086035437)
                  ·
                    refine ⟨4581853605592504532263289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12218276281580012086035437 4581853605592504532263289)
                    ·
                      refine ⟨3436390204194378399197467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4581853605592504532263289 3436390204194378399197467)
                      ·
                        rfl

theorem cell23_6692346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2].length) (baseStart_6692346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692346 prefixEnd_6692346 := by exact prefixLift 6692346
  have htrace : WordTrace (prefixWord ++ tailWord_6692346) baseStart_6692346 baseEnd_6692346 := by
    simpa [prefixWord, tailWord_6692346, baseEnd_6692346] using wordTrace_append hprefix tailTrace_6692346
  have hstable : (prefixWord ++ tailWord_6692346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692346).length < 2 ^ (prefixWord ++ tailWord_6692346).sum := by decide
  have hdescent : baseEnd_6692346 < baseStart_6692346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692449 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 3, 3, 4]
def baseStart_6692449 : Nat := 118140960795 + 6692449 * 2 ^ 59
def prefixEnd_6692449 : Nat := 4983230072969 + 3 ^ 40 * 6692449 * 2
def baseEnd_6692449 : Nat := 3436443092701791496209493

theorem tailTrace_6692449 : CollatzResearch.WordTrace tailWord_6692449 prefixEnd_6692449 3436443092701791496209493 := by
  unfold tailWord_6692449
  simp only [CollatzResearch.WordTrace]
  refine ⟨244093668131407727137080401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162729112087605151424720267 244093668131407727137080401)
  ·
    refine ⟨183070251098555795352810301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244093668131407727137080401 183070251098555795352810301)
    ·
      refine ⟨68651344161958423257303863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183070251098555795352810301 68651344161958423257303863)
      ·
        refine ⟨102977016242937634885955795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68651344161958423257303863 102977016242937634885955795)
        ·
          refine ⟨154465524364406452328933693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102977016242937634885955795 154465524364406452328933693)
          ·
            refine ⟨57924571636652419623350135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154465524364406452328933693 57924571636652419623350135)
            ·
              refine ⟨86886857454978629435025203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57924571636652419623350135 86886857454978629435025203)
              ·
                refine ⟨130330286182467944152537805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86886857454978629435025203 130330286182467944152537805)
                ·
                  refine ⟨48873857318425479057201677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130330286182467944152537805 48873857318425479057201677)
                  ·
                    refine ⟨18327696494409554646450629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48873857318425479057201677 18327696494409554646450629)
                    ·
                      refine ⟨3436443092701791496209493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18327696494409554646450629 3436443092701791496209493)
                      ·
                        rfl

theorem cell23_6692449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_6692449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692449 prefixEnd_6692449 := by exact prefixLift 6692449
  have htrace : WordTrace (prefixWord ++ tailWord_6692449) baseStart_6692449 baseEnd_6692449 := by
    simpa [prefixWord, tailWord_6692449, baseEnd_6692449] using wordTrace_append hprefix tailTrace_6692449
  have hstable : (prefixWord ++ tailWord_6692449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692449).length < 2 ^ (prefixWord ++ tailWord_6692449).sum := by decide
  have hdescent : baseEnd_6692449 < baseStart_6692449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692466 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 1, 3, 4]
def baseStart_6692466 : Nat := 118140960795 + 6692466 * 2 ^ 59
def prefixEnd_6692466 : Nat := 4983230072969 + 3 ^ 40 * 6692466 * 2
def baseEnd_6692466 : Nat := 3436451821872917929696915

theorem tailTrace_6692466 : CollatzResearch.WordTrace tailWord_6692466 prefixEnd_6692466 3436451821872917929696915 := by
  unfold tailWord_6692466
  simp only [CollatzResearch.WordTrace]
  refine ⟨61023572043086534760112313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162729525448230759360299501 61023572043086534760112313)
  ·
    refine ⟨45767679032314901070084235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61023572043086534760112313 45767679032314901070084235)
    ·
      refine ⟨68651518548472351605126353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45767679032314901070084235 68651518548472351605126353)
      ·
        refine ⟨51488638911354263703844765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68651518548472351605126353 51488638911354263703844765)
        ·
          refine ⟨19308239591757848888941787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51488638911354263703844765 19308239591757848888941787)
          ·
            refine ⟨28962359387636773333412681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19308239591757848888941787 28962359387636773333412681)
            ·
              refine ⟨21721769540727580000059511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28962359387636773333412681 21721769540727580000059511)
              ·
                refine ⟨32582654311091370000089267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21721769540727580000059511 32582654311091370000089267)
                ·
                  refine ⟨48873981466637055000133901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32582654311091370000089267 48873981466637055000133901)
                  ·
                    refine ⟨18327743049988895625050213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48873981466637055000133901 18327743049988895625050213)
                    ·
                      refine ⟨3436451821872917929696915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18327743049988895625050213 3436451821872917929696915)
                      ·
                        rfl

theorem cell23_6692466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_6692466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692466 prefixEnd_6692466 := by exact prefixLift 6692466
  have htrace : WordTrace (prefixWord ++ tailWord_6692466) baseStart_6692466 baseEnd_6692466 := by
    simpa [prefixWord, tailWord_6692466, baseEnd_6692466] using wordTrace_append hprefix tailTrace_6692466
  have hstable : (prefixWord ++ tailWord_6692466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692466).length < 2 ^ (prefixWord ++ tailWord_6692466).sum := by decide
  have hdescent : baseEnd_6692466 < baseStart_6692466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692489 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 8]
def baseStart_6692489 : Nat := 118140960795 + 6692489 * 2 ^ 59
def prefixEnd_6692489 : Nat := 4983230072969 + 3 ^ 40 * 6692489 * 2
def baseEnd_6692489 : Nat := 381829292436441259967701

theorem tailTrace_6692489 : CollatzResearch.WordTrace tailWord_6692489 prefixEnd_6692489 381829292436441259967701 := by
  unfold tailWord_6692489
  simp only [CollatzResearch.WordTrace]
  refine ⟨244095127051262813968536521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162730084700841875979024347 244095127051262813968536521)
  ·
    refine ⟨183071345288447110476402391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244095127051262813968536521 183071345288447110476402391)
    ·
      refine ⟨274607017932670665714603587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183071345288447110476402391 274607017932670665714603587)
      ·
        refine ⟨411910526899005998571905381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274607017932670665714603587 411910526899005998571905381)
        ·
          refine ⟨77233223793563624732232259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 411910526899005998571905381 77233223793563624732232259)
          ·
            refine ⟨115849835690345437098348389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77233223793563624732232259 115849835690345437098348389)
            ·
              refine ⟨21721844191939769455940323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115849835690345437098348389 21721844191939769455940323)
              ·
                refine ⟨32582766287909654183910485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21721844191939769455940323 32582766287909654183910485)
                ·
                  refine ⟨381829292436441259967701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32582766287909654183910485 381829292436441259967701)
                  ·
                    rfl

theorem cell23_6692489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 8].length) (baseStart_6692489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692489 prefixEnd_6692489 := by exact prefixLift 6692489
  have htrace : WordTrace (prefixWord ++ tailWord_6692489) baseStart_6692489 baseEnd_6692489 := by
    simpa [prefixWord, tailWord_6692489, baseEnd_6692489] using wordTrace_append hprefix tailTrace_6692489
  have hstable : (prefixWord ++ tailWord_6692489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692489).length < 2 ^ (prefixWord ++ tailWord_6692489).sum := by decide
  have hdescent : baseEnd_6692489 < baseStart_6692489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692536 : List Nat := [2, 1, 2, 1, 2, 1, 1, 7, 1, 5]
def baseStart_6692536 : Nat := 118140960795 + 6692536 * 2 ^ 59
def prefixEnd_6692536 : Nat := 4983230072969 + 3 ^ 40 * 6692536 * 2
def baseEnd_6692536 : Nat := 1145495921839577551940531

theorem tailTrace_6692536 : CollatzResearch.WordTrace tailWord_6692536 prefixEnd_6692536 1145495921839577551940531 := by
  unfold tailWord_6692536
  simp only [CollatzResearch.WordTrace]
  refine ⟨122048420641046270497748731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162731227521395027330331641 122048420641046270497748731)
  ·
    refine ⟨183072630961569405746623097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122048420641046270497748731 183072630961569405746623097)
    ·
      refine ⟨137304473221177054309967323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183072630961569405746623097 137304473221177054309967323)
      ·
        refine ⟨205956709831765581464950985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137304473221177054309967323 205956709831765581464950985)
        ·
          refine ⟨154467532373824186098713239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205956709831765581464950985 154467532373824186098713239)
          ·
            refine ⟨231701298560736279148069859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154467532373824186098713239 231701298560736279148069859)
            ·
              refine ⟨347551947841104418722104789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231701298560736279148069859 347551947841104418722104789)
              ·
                refine ⟨8145748777525884813799331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 347551947841104418722104789 8145748777525884813799331)
                ·
                  refine ⟨12218623166288827220698997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8145748777525884813799331 12218623166288827220698997)
                  ·
                    refine ⟨1145495921839577551940531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12218623166288827220698997 1145495921839577551940531)
                    ·
                      rfl

theorem cell23_6692536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 1, 5].length) (baseStart_6692536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692536 prefixEnd_6692536 := by exact prefixLift 6692536
  have htrace : WordTrace (prefixWord ++ tailWord_6692536) baseStart_6692536 baseEnd_6692536 := by
    simpa [prefixWord, tailWord_6692536, baseEnd_6692536] using wordTrace_append hprefix tailTrace_6692536
  have hstable : (prefixWord ++ tailWord_6692536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692536).length < 2 ^ (prefixWord ++ tailWord_6692536).sum := by decide
  have hdescent : baseEnd_6692536 < baseStart_6692536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692543 : List Nat := [1, 1, 2, 2, 2, 3, 1, 4, 2, 3, 2]
def baseStart_6692543 : Nat := 118140960795 + 6692543 * 2 ^ 59
def prefixEnd_6692543 : Nat := 4983230072969 + 3 ^ 40 * 6692543 * 2
def baseEnd_6692543 : Nat := 3436491359883314128434061

theorem tailTrace_6692543 : CollatzResearch.WordTrace tailWord_6692543 prefixEnd_6692543 3436491359883314128434061 := by
  unfold tailWord_6692543
  simp only [CollatzResearch.WordTrace]
  refine ⟨244097096593067181191002283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162731397728711454127334855 244097096593067181191002283)
  ·
    refine ⟨366145644889600771786503425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244097096593067181191002283 366145644889600771786503425)
    ·
      refine ⟨274609233667200578839877569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366145644889600771786503425 274609233667200578839877569)
      ·
        refine ⟨205956925250400434129908177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274609233667200578839877569 205956925250400434129908177)
        ·
          refine ⟨154467693937800325597431133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205956925250400434129908177 154467693937800325597431133)
          ·
            refine ⟨57925385226675122099036675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154467693937800325597431133 57925385226675122099036675)
            ·
              refine ⟨86888077840012683148555013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57925385226675122099036675 86888077840012683148555013)
              ·
                refine ⟨16291514595002378090354065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86888077840012683148555013 16291514595002378090354065)
                ·
                  refine ⟨12218635946251783567765549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16291514595002378090354065 12218635946251783567765549)
                  ·
                    refine ⟨4581988479844418837912081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12218635946251783567765549 4581988479844418837912081)
                    ·
                      refine ⟨3436491359883314128434061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4581988479844418837912081 3436491359883314128434061)
                      ·
                        rfl

theorem cell23_6692543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 3, 2].length) (baseStart_6692543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692543 prefixEnd_6692543 := by exact prefixLift 6692543
  have htrace : WordTrace (prefixWord ++ tailWord_6692543) baseStart_6692543 baseEnd_6692543 := by
    simpa [prefixWord, tailWord_6692543, baseEnd_6692543] using wordTrace_append hprefix tailTrace_6692543
  have hstable : (prefixWord ++ tailWord_6692543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692543).length < 2 ^ (prefixWord ++ tailWord_6692543).sum := by decide
  have hdescent : baseEnd_6692543 < baseStart_6692543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692577 : List Nat := [1, 2, 3, 1, 5, 2, 1, 1, 2, 3, 2]
def baseStart_6692577 : Nat := 118140960795 + 6692577 * 2 ^ 59
def prefixEnd_6692577 : Nat := 4983230072969 + 3 ^ 40 * 6692577 * 2
def baseEnd_6692577 : Nat := 3436508818225566995408905

theorem tailTrace_6692577 : CollatzResearch.WordTrace tailWord_6692577 prefixEnd_6692577 3436508818225566995408905 := by
  unfold tailWord_6692577
  simp only [CollatzResearch.WordTrace]
  refine ⟨244098336674944004997739985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162732224449962669998493323 244098336674944004997739985)
  ·
    refine ⟨183073752506208003748304989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244098336674944004997739985 183073752506208003748304989)
    ·
      refine ⟨68652657189828001405614371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183073752506208003748304989 68652657189828001405614371)
      ·
        refine ⟨102978985784742002108421557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68652657189828001405614371 102978985784742002108421557)
        ·
          refine ⟨9654279917319562697664521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102978985784742002108421557 9654279917319562697664521)
          ·
            refine ⟨7240709937989672023248391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9654279917319562697664521 7240709937989672023248391)
            ·
              refine ⟨10861064906984508034872587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7240709937989672023248391 10861064906984508034872587)
              ·
                refine ⟨16291597360476762052308881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10861064906984508034872587 16291597360476762052308881)
                ·
                  refine ⟨12218698020357571539231661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16291597360476762052308881 12218698020357571539231661)
                  ·
                    refine ⟨4582011757634089327211873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12218698020357571539231661 4582011757634089327211873)
                    ·
                      refine ⟨3436508818225566995408905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4582011757634089327211873 3436508818225566995408905)
                      ·
                        rfl

theorem cell23_6692577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 3, 2].length) (baseStart_6692577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692577 prefixEnd_6692577 := by exact prefixLift 6692577
  have htrace : WordTrace (prefixWord ++ tailWord_6692577) baseStart_6692577 baseEnd_6692577 := by
    simpa [prefixWord, tailWord_6692577, baseEnd_6692577] using wordTrace_append hprefix tailTrace_6692577
  have hstable : (prefixWord ++ tailWord_6692577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692577).length < 2 ^ (prefixWord ++ tailWord_6692577).sum := by decide
  have hdescent : baseEnd_6692577 < baseStart_6692577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692590 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 5, 2, 2]
def baseStart_6692590 : Nat := 118140960795 + 6692590 * 2 ^ 59
def prefixEnd_6692590 : Nat := 4983230072969 + 3 ^ 40 * 6692590 * 2
def baseEnd_6692590 : Nat := 3436515493474075444546345

theorem tailTrace_6692590 : CollatzResearch.WordTrace tailWord_6692590 prefixEnd_6692590 3436515493474075444546345 := by
  unfold tailWord_6692590
  simp only [CollatzResearch.WordTrace]
  refine ⟨30512351352987113527245403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162732540549264605478642149 30512351352987113527245403)
  ·
    refine ⟨45768527029480670290868105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30512351352987113527245403 45768527029480670290868105)
    ·
      refine ⟨34326395272110502718151079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45768527029480670290868105 34326395272110502718151079)
      ·
        refine ⟨51489592908165754077226619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34326395272110502718151079 51489592908165754077226619)
        ·
          refine ⟨77234389362248631115839929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51489592908165754077226619 77234389362248631115839929)
          ·
            refine ⟨57925792021686473336879947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77234389362248631115839929 57925792021686473336879947)
            ·
              refine ⟨86888688032529710005319921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57925792021686473336879947 86888688032529710005319921)
              ·
                refine ⟨65166516024397282503989941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86888688032529710005319921 65166516024397282503989941)
                ·
                  refine ⟨6109360877287245234749057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65166516024397282503989941 6109360877287245234749057)
                  ·
                    refine ⟨4582020657965433926061793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6109360877287245234749057 4582020657965433926061793)
                    ·
                      refine ⟨3436515493474075444546345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4582020657965433926061793 3436515493474075444546345)
                      ·
                        rfl

theorem cell23_6692590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_6692590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692590 prefixEnd_6692590 := by exact prefixLift 6692590
  have htrace : WordTrace (prefixWord ++ tailWord_6692590) baseStart_6692590 baseEnd_6692590 := by
    simpa [prefixWord, tailWord_6692590, baseEnd_6692590] using wordTrace_append hprefix tailTrace_6692590
  have hstable : (prefixWord ++ tailWord_6692590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692590).length < 2 ^ (prefixWord ++ tailWord_6692590).sum := by decide
  have hdescent : baseEnd_6692590 < baseStart_6692590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692607 : List Nat := [1, 1, 2, 2, 1, 3, 4, 4, 1, 2, 2]
def baseStart_6692607 : Nat := 118140960795 + 6692607 * 2 ^ 59
def prefixEnd_6692607 : Nat := 4983230072969 + 3 ^ 40 * 6692607 * 2
def baseEnd_6692607 : Nat := 3436524222645201878033767

theorem tailTrace_6692607 : CollatzResearch.WordTrace tailWord_6692607 prefixEnd_6692607 3436524222645201878033767 := by
  unfold tailWord_6692607
  simp only [CollatzResearch.WordTrace]
  refine ⟨244099430864835320121332075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162732953909890213414221383 244099430864835320121332075)
  ·
    refine ⟨366149146297252980181998113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244099430864835320121332075 366149146297252980181998113)
    ·
      refine ⟨274611859722939735136498585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366149146297252980181998113 274611859722939735136498585)
      ·
        refine ⟨205958894792204801352373939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274611859722939735136498585 205958894792204801352373939)
        ·
          refine ⟨308938342188307202028560909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205958894792204801352373939 308938342188307202028560909)
          ·
            refine ⟨115851878320615200760710341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308938342188307202028560909 115851878320615200760710341)
            ·
              refine ⟨21722227185115350142633189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115851878320615200760710341 21722227185115350142633189)
              ·
                refine ⟨4072917597209128151743723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21722227185115350142633189 4072917597209128151743723)
                ·
                  refine ⟨6109376395813692227615585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4072917597209128151743723 6109376395813692227615585)
                  ·
                    refine ⟨4582032296860269170711689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6109376395813692227615585 4582032296860269170711689)
                    ·
                      refine ⟨3436524222645201878033767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4582032296860269170711689 3436524222645201878033767)
                      ·
                        rfl

theorem cell23_6692607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 1, 2, 2].length) (baseStart_6692607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692607 prefixEnd_6692607 := by exact prefixLift 6692607
  have htrace : WordTrace (prefixWord ++ tailWord_6692607) baseStart_6692607 baseEnd_6692607 := by
    simpa [prefixWord, tailWord_6692607, baseEnd_6692607] using wordTrace_append hprefix tailTrace_6692607
  have hstable : (prefixWord ++ tailWord_6692607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692607).length < 2 ^ (prefixWord ++ tailWord_6692607).sum := by decide
  have hdescent : baseEnd_6692607 < baseStart_6692607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692621 : List Nat := [1, 7, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_6692621 : Nat := 118140960795 + 6692621 * 2 ^ 59
def prefixEnd_6692621 : Nat := 4983230072969 + 3 ^ 40 * 6692621 * 2
def baseEnd_6692621 : Nat := 1145510470458121607752901

theorem tailTrace_6692621 : CollatzResearch.WordTrace tailWord_6692621 prefixEnd_6692621 1145510470458121607752901 := by
  unfold tailWord_6692621
  simp only [CollatzResearch.WordTrace]
  refine ⟨244099941486784600512341717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162733294324523067008227811 244099941486784600512341717)
  ·
    refine ⟨5721092378596514074508009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 244099941486784600512341717 5721092378596514074508009)
    ·
      refine ⟨4290819283947385555881007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5721092378596514074508009 4290819283947385555881007)
      ·
        refine ⟨6436228925921078333821511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4290819283947385555881007 6436228925921078333821511)
        ·
          refine ⟨9654343388881617500732267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6436228925921078333821511 9654343388881617500732267)
          ·
            refine ⟨14481515083322426251098401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9654343388881617500732267 14481515083322426251098401)
            ·
              refine ⟨10861136312491819688323801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14481515083322426251098401 10861136312491819688323801)
              ·
                refine ⟨8145852234368864766242851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10861136312491819688323801 8145852234368864766242851)
                ·
                  refine ⟨12218778351553297149364277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8145852234368864766242851 12218778351553297149364277)
                  ·
                    refine ⟨1145510470458121607752901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12218778351553297149364277 1145510470458121607752901)
                    ·
                      rfl

theorem cell23_6692621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_6692621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692621 prefixEnd_6692621 := by exact prefixLift 6692621
  have htrace : WordTrace (prefixWord ++ tailWord_6692621) baseStart_6692621 baseEnd_6692621 := by
    simpa [prefixWord, tailWord_6692621, baseEnd_6692621] using wordTrace_append hprefix tailTrace_6692621
  have hstable : (prefixWord ++ tailWord_6692621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692621).length < 2 ^ (prefixWord ++ tailWord_6692621).sum := by decide
  have hdescent : baseEnd_6692621 < baseStart_6692621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692633 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 7, 3, 2]
def baseStart_6692633 : Nat := 118140960795 + 6692633 * 2 ^ 59
def prefixEnd_6692633 : Nat := 4983230072969 + 3 ^ 40 * 6692633 * 2
def baseEnd_6692633 : Nat := 3436537573142218776308647

theorem tailTrace_6692633 : CollatzResearch.WordTrace tailWord_6692633 prefixEnd_6692633 3436537573142218776308647 := by
  unfold tailWord_6692633
  simp only [CollatzResearch.WordTrace]
  refine ⟨244100379162741126561778553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162733586108494084374519035 244100379162741126561778553)
  ·
    refine ⟨183075284372055844921333915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244100379162741126561778553 183075284372055844921333915)
    ·
      refine ⟨274612926558083767382000873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183075284372055844921333915 274612926558083767382000873)
      ·
        refine ⟨205959694918562825536500655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274612926558083767382000873 205959694918562825536500655)
        ·
          refine ⟨308939542377844238304750983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205959694918562825536500655 308939542377844238304750983)
          ·
            refine ⟨463409313566766357457126475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308939542377844238304750983 463409313566766357457126475)
            ·
              refine ⟨695113970350149536185689713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463409313566766357457126475 695113970350149536185689713)
              ·
                refine ⟨521335477762612152139267285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 695113970350149536185689713 521335477762612152139267285)
                ·
                  refine ⟨12218800260061222315764077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 521335477762612152139267285 12218800260061222315764077)
                  ·
                    refine ⟨4582050097522958368411529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12218800260061222315764077 4582050097522958368411529)
                    ·
                      refine ⟨3436537573142218776308647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4582050097522958368411529 3436537573142218776308647)
                      ·
                        rfl

theorem cell23_6692633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 3, 2].length) (baseStart_6692633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692633 prefixEnd_6692633 := by exact prefixLift 6692633
  have htrace : WordTrace (prefixWord ++ tailWord_6692633) baseStart_6692633 baseEnd_6692633 := by
    simpa [prefixWord, tailWord_6692633, baseEnd_6692633] using wordTrace_append hprefix tailTrace_6692633
  have hstable : (prefixWord ++ tailWord_6692633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692633).length < 2 ^ (prefixWord ++ tailWord_6692633).sum := by decide
  have hdescent : baseEnd_6692633 < baseStart_6692633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692636 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_6692636 : Nat := 118140960795 + 6692636 * 2 ^ 59
def prefixEnd_6692636 : Nat := 4983230072969 + 3 ^ 40 * 6692636 * 2
def baseEnd_6692636 : Nat := 3436539113584182264571133

theorem tailTrace_6692636 : CollatzResearch.WordTrace tailWord_6692636 prefixEnd_6692636 3436539113584182264571133 := by
  unfold tailWord_6692636
  simp only [CollatzResearch.WordTrace]
  refine ⟨122050244290865129037068881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162733659054486838716091841 122050244290865129037068881)
  ·
    refine ⟨91537683218148846777801661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122050244290865129037068881 91537683218148846777801661)
    ·
      refine ⟨34326631206805817541675623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91537683218148846777801661 34326631206805817541675623)
      ·
        refine ⟨51489946810208726312513435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34326631206805817541675623 51489946810208726312513435)
        ·
          refine ⟨77234920215313089468770153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51489946810208726312513435 77234920215313089468770153)
          ·
            refine ⟨57926190161484817101577615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77234920215313089468770153 57926190161484817101577615)
            ·
              refine ⟨86889285242227225652366423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57926190161484817101577615 86889285242227225652366423)
              ·
                refine ⟨130333927863340838478549635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86889285242227225652366423 130333927863340838478549635)
                ·
                  refine ⟨195500891795011257717824453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130333927863340838478549635 195500891795011257717824453)
                  ·
                    refine ⟨36656417211564610822092085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 195500891795011257717824453 36656417211564610822092085)
                    ·
                      refine ⟨3436539113584182264571133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36656417211564610822092085 3436539113584182264571133)
                      ·
                        rfl

theorem cell23_6692636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_6692636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692636 prefixEnd_6692636 := by exact prefixLift 6692636
  have htrace : WordTrace (prefixWord ++ tailWord_6692636) baseStart_6692636 baseEnd_6692636 := by
    simpa [prefixWord, tailWord_6692636, baseEnd_6692636] using wordTrace_append hprefix tailTrace_6692636
  have hstable : (prefixWord ++ tailWord_6692636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692636).length < 2 ^ (prefixWord ++ tailWord_6692636).sum := by decide
  have hdescent : baseEnd_6692636 < baseStart_6692636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692663 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 5, 4, 2]
def baseStart_6692663 : Nat := 118140960795 + 6692663 * 2 ^ 59
def prefixEnd_6692663 : Nat := 4983230072969 + 3 ^ 40 * 6692663 * 2
def baseEnd_6692663 : Nat := 3436552977561853658933509

theorem tailTrace_6692663 : CollatzResearch.WordTrace tailWord_6692663 prefixEnd_6692663 3436552977561853658933509 := by
  unfold tailWord_6692663
  simp only [CollatzResearch.WordTrace]
  refine ⟨244101473352632441685370643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162734315568421627790247095 244101473352632441685370643)
  ·
    refine ⟨366152210028948662528055965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244101473352632441685370643 366152210028948662528055965)
    ·
      refine ⟨137307078760855748448020987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366152210028948662528055965 137307078760855748448020987)
      ·
        refine ⟨205960618141283622672031481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137307078760855748448020987 205960618141283622672031481)
        ·
          refine ⟨154470463605962717004023611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205960618141283622672031481 154470463605962717004023611)
          ·
            refine ⟨231705695408944075506035417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154470463605962717004023611 231705695408944075506035417)
            ·
              refine ⟨173779271556708056629526563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231705695408944075506035417 173779271556708056629526563)
              ·
                refine ⟨260668907335062084944289845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173779271556708056629526563 260668907335062084944289845)
                ·
                  refine ⟨24437710062662070463527173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 260668907335062084944289845 24437710062662070463527173)
                  ·
                    refine ⟨4582070636749138211911345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24437710062662070463527173 4582070636749138211911345)
                    ·
                      refine ⟨3436552977561853658933509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4582070636749138211911345 3436552977561853658933509)
                      ·
                        rfl

theorem cell23_6692663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 4, 2].length) (baseStart_6692663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692663 prefixEnd_6692663 := by exact prefixLift 6692663
  have htrace : WordTrace (prefixWord ++ tailWord_6692663) baseStart_6692663 baseEnd_6692663 := by
    simpa [prefixWord, tailWord_6692663, baseEnd_6692663] using wordTrace_append hprefix tailTrace_6692663
  have hstable : (prefixWord ++ tailWord_6692663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692663).length < 2 ^ (prefixWord ++ tailWord_6692663).sum := by decide
  have hdescent : baseEnd_6692663 < baseStart_6692663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692684 : List Nat := [2, 2, 1, 3, 4, 2, 1, 2, 1, 3, 2]
def baseStart_6692684 : Nat := 118140960795 + 6692684 * 2 ^ 59
def prefixEnd_6692684 : Nat := 4983230072969 + 3 ^ 40 * 6692684 * 2
def baseEnd_6692684 : Nat := 3436563760655598076770913

theorem tailTrace_6692684 : CollatzResearch.WordTrace tailWord_6692684 prefixEnd_6692684 3436563760655598076770913 := by
  unfold tailWord_6692684
  simp only [CollatzResearch.WordTrace]
  refine ⟨122051119642778181135942553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162734826190370908181256737 122051119642778181135942553)
  ·
    refine ⟨91538339732083635851956915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122051119642778181135942553 91538339732083635851956915)
    ·
      refine ⟨137307509598125453777935373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91538339732083635851956915 137307509598125453777935373)
      ·
        refine ⟨51490316099297045166725765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137307509598125453777935373 51490316099297045166725765)
        ·
          refine ⟨9654434268618195968761081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51490316099297045166725765 9654434268618195968761081)
          ·
            refine ⟨7240825701463646976570811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9654434268618195968761081 7240825701463646976570811)
            ·
              refine ⟨10861238552195470464856217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7240825701463646976570811 10861238552195470464856217)
              ·
                refine ⟨8145928914146602848642163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10861238552195470464856217 8145928914146602848642163)
                ·
                  refine ⟨12218893371219904272963245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8145928914146602848642163 12218893371219904272963245)
                  ·
                    refine ⟨4582085014207464102361217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12218893371219904272963245 4582085014207464102361217)
                    ·
                      refine ⟨3436563760655598076770913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4582085014207464102361217 3436563760655598076770913)
                      ·
                        rfl

theorem cell23_6692684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_6692684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692684 prefixEnd_6692684 := by exact prefixLift 6692684
  have htrace : WordTrace (prefixWord ++ tailWord_6692684) baseStart_6692684 baseEnd_6692684 := by
    simpa [prefixWord, tailWord_6692684, baseEnd_6692684] using wordTrace_append hprefix tailTrace_6692684
  have hstable : (prefixWord ++ tailWord_6692684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692684).length < 2 ^ (prefixWord ++ tailWord_6692684).sum := by decide
  have hdescent : baseEnd_6692684 < baseStart_6692684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692857 : List Nat := [1, 2, 1, 3, 1, 6, 1, 2, 1, 5]
def baseStart_6692857 : Nat := 118140960795 + 6692857 * 2 ^ 59
def prefixEnd_6692857 : Nat := 4983230072969 + 3 ^ 40 * 6692857 * 2
def baseEnd_6692857 : Nat := 1145550864269608633302539

theorem tailTrace_6692857 : CollatzResearch.WordTrace tailWord_6692857 prefixEnd_6692857 1145550864269608633302539 := by
  unfold tailWord_6692857
  simp only [CollatzResearch.WordTrace]
  refine ⟨244108549113929612817932825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162739032742619741878621883 244108549113929612817932825)
  ·
    refine ⟨183081411835447209613449619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244108549113929612817932825 183081411835447209613449619)
    ·
      refine ⟨274622117753170814420174429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183081411835447209613449619 274622117753170814420174429)
      ·
        refine ⟨102983294157439055407565411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274622117753170814420174429 102983294157439055407565411)
        ·
          refine ⟨154474941236158583111348117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102983294157439055407565411 154474941236158583111348117)
          ·
            refine ⟨7241012870444933583344443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 154474941236158583111348117 7241012870444933583344443)
            ·
              refine ⟨10861519305667400375016665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7241012870444933583344443 10861519305667400375016665)
              ·
                refine ⟨8146139479250550281262499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10861519305667400375016665 8146139479250550281262499)
                ·
                  refine ⟨12219209218875825421893749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8146139479250550281262499 12219209218875825421893749)
                  ·
                    refine ⟨1145550864269608633302539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12219209218875825421893749 1145550864269608633302539)
                    ·
                      rfl

theorem cell23_6692857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 5].length) (baseStart_6692857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692857 prefixEnd_6692857 := by exact prefixLift 6692857
  have htrace : WordTrace (prefixWord ++ tailWord_6692857) baseStart_6692857 baseEnd_6692857 := by
    simpa [prefixWord, tailWord_6692857, baseEnd_6692857] using wordTrace_append hprefix tailTrace_6692857
  have hstable : (prefixWord ++ tailWord_6692857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692857).length < 2 ^ (prefixWord ++ tailWord_6692857).sum := by decide
  have hdescent : baseEnd_6692857 < baseStart_6692857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692860 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 3, 1, 4]
def baseStart_6692860 : Nat := 118140960795 + 6692860 * 2 ^ 59
def prefixEnd_6692860 : Nat := 4983230072969 + 3 ^ 40 * 6692860 * 2
def baseEnd_6692860 : Nat := 3436654133250789388170103

theorem tailTrace_6692860 : CollatzResearch.WordTrace tailWord_6692860 prefixEnd_6692860 3436654133250789388170103 := by
  unfold tailWord_6692860
  simp only [CollatzResearch.WordTrace]
  refine ⟨122054329266459372165146017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162739105688612496220194689 122054329266459372165146017)
  ·
    refine ⟨91540746949844529123859513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122054329266459372165146017 91540746949844529123859513)
    ·
      refine ⟨68655560212383396842894635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91540746949844529123859513 68655560212383396842894635)
      ·
        refine ⟨102983340318575095264341953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68655560212383396842894635 102983340318575095264341953)
        ·
          refine ⟨77237505238931321448256465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102983340318575095264341953 77237505238931321448256465)
          ·
            refine ⟨57928128929198491086192349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77237505238931321448256465 57928128929198491086192349)
            ·
              refine ⟨21723048348449434157322131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57928128929198491086192349 21723048348449434157322131)
              ·
                refine ⟨32584572522674151235983197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21723048348449434157322131 32584572522674151235983197)
                ·
                  refine ⟨12219214696002806713493699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32584572522674151235983197 12219214696002806713493699)
                  ·
                    refine ⟨18328822044004210070240549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12219214696002806713493699 18328822044004210070240549)
                    ·
                      refine ⟨3436654133250789388170103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18328822044004210070240549 3436654133250789388170103)
                      ·
                        rfl

theorem cell23_6692860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_6692860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692860 prefixEnd_6692860 := by exact prefixLift 6692860
  have htrace : WordTrace (prefixWord ++ tailWord_6692860) baseStart_6692860 baseEnd_6692860 := by
    simpa [prefixWord, tailWord_6692860, baseEnd_6692860] using wordTrace_append hprefix tailTrace_6692860
  have hstable : (prefixWord ++ tailWord_6692860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692860).length < 2 ^ (prefixWord ++ tailWord_6692860).sum := by decide
  have hdescent : baseEnd_6692860 < baseStart_6692860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692863 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 5]
def baseStart_6692863 : Nat := 118140960795 + 6692863 * 2 ^ 59
def prefixEnd_6692863 : Nat := 4983230072969 + 3 ^ 40 * 6692863 * 2
def baseEnd_6692863 : Nat := 3436655673692752876432589

theorem tailTrace_6692863 : CollatzResearch.WordTrace tailWord_6692863 prefixEnd_6692863 3436655673692752876432589 := by
  unfold tailWord_6692863
  simp only [CollatzResearch.WordTrace]
  refine ⟨244108767951907875842651243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162739178634605250561767495 244108767951907875842651243)
  ·
    refine ⟨366163151927861813763976865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244108767951907875842651243 366163151927861813763976865)
    ·
      refine ⟨274622363945896360322982649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366163151927861813763976865 274622363945896360322982649)
      ·
        refine ⟨205966772959422270242236987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274622363945896360322982649 205966772959422270242236987)
        ·
          refine ⟨308950159439133405363355481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205966772959422270242236987 308950159439133405363355481)
          ·
            refine ⟨231712619579350054022516611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308950159439133405363355481 231712619579350054022516611)
            ·
              refine ⟨347568929369025081033774917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231712619579350054022516611 347568929369025081033774917)
              ·
                refine ⟨65169174256692202693832797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 347568929369025081033774917 65169174256692202693832797)
                ·
                  refine ⟨24438440346259576010187299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65169174256692202693832797 24438440346259576010187299)
                  ·
                    refine ⟨36657660519389364015280949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24438440346259576010187299 36657660519389364015280949)
                    ·
                      refine ⟨3436655673692752876432589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36657660519389364015280949 3436655673692752876432589)
                      ·
                        rfl

theorem cell23_6692863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_6692863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692863 prefixEnd_6692863 := by exact prefixLift 6692863
  have htrace : WordTrace (prefixWord ++ tailWord_6692863) baseStart_6692863 baseEnd_6692863 := by
    simpa [prefixWord, tailWord_6692863, baseEnd_6692863] using wordTrace_append hprefix tailTrace_6692863
  have hstable : (prefixWord ++ tailWord_6692863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692863).length < 2 ^ (prefixWord ++ tailWord_6692863).sum := by decide
  have hdescent : baseEnd_6692863 < baseStart_6692863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692874 : List Nat := [3, 1, 2, 2, 4, 1, 3, 1, 1, 5]
def baseStart_6692874 : Nat := 118140960795 + 6692874 * 2 ^ 59
def prefixEnd_6692874 : Nat := 4983230072969 + 3 ^ 40 * 6692874 * 2
def baseEnd_6692874 : Nat := 1145553773993317444465013

theorem tailTrace_6692874 : CollatzResearch.WordTrace tailWord_6692874 prefixEnd_6692874 1145553773993317444465013 := by
  unfold tailWord_6692874
  simp only [CollatzResearch.WordTrace]
  refine ⟨61027292288717006180325419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162739446103245349814201117 61027292288717006180325419)
  ·
    refine ⟨91540938433075509270488129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61027292288717006180325419 91540938433075509270488129)
    ·
      refine ⟨68655703824806631952866097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91540938433075509270488129 68655703824806631952866097)
      ·
        refine ⟨51491777868604973964649573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68655703824806631952866097 51491777868604973964649573)
        ·
          refine ⟨9654708350363432618371795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51491777868604973964649573 9654708350363432618371795)
          ·
            refine ⟨14482062525545148927557693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9654708350363432618371795 14482062525545148927557693)
            ·
              refine ⟨5430773447079430847834135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14482062525545148927557693 5430773447079430847834135)
              ·
                refine ⟨8146160170619146271751203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5430773447079430847834135 8146160170619146271751203)
                ·
                  refine ⟨12219240255928719407626805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8146160170619146271751203 12219240255928719407626805)
                  ·
                    refine ⟨1145553773993317444465013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12219240255928719407626805 1145553773993317444465013)
                    ·
                      rfl

theorem cell23_6692874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_6692874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692874 prefixEnd_6692874 := by exact prefixLift 6692874
  have htrace : WordTrace (prefixWord ++ tailWord_6692874) baseStart_6692874 baseEnd_6692874 := by
    simpa [prefixWord, tailWord_6692874, baseEnd_6692874] using wordTrace_append hprefix tailTrace_6692874
  have hstable : (prefixWord ++ tailWord_6692874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692874).length < 2 ^ (prefixWord ++ tailWord_6692874).sum := by decide
  have hdescent : baseEnd_6692874 < baseStart_6692874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692904 : List Nat := [2, 1, 5, 3, 1, 1, 2, 1, 1, 6]
def baseStart_6692904 : Nat := 118140960795 + 6692904 * 2 ^ 59
def prefixEnd_6692904 : Nat := 4983230072969 + 3 ^ 40 * 6692904 * 2
def baseEnd_6692904 : Nat := 1145558908799862405339967

theorem tailTrace_6692904 : CollatzResearch.WordTrace tailWord_6692904 prefixEnd_6692904 1145558908799862405339967 := by
  unfold tailWord_6692904
  simp only [CollatzResearch.WordTrace]
  refine ⟨122055131672379669922446883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162740175563172893229929177 122055131672379669922446883)
  ·
    refine ⟨183082697508569504883670325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122055131672379669922446883 183082697508569504883670325)
    ·
      refine ⟨17164002891428391082844093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183082697508569504883670325 17164002891428391082844093)
      ·
        refine ⟨6436501084285646656066535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17164002891428391082844093 6436501084285646656066535)
        ·
          refine ⟨9654751626428469984099803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6436501084285646656066535 9654751626428469984099803)
          ·
            refine ⟨14482127439642704976149705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9654751626428469984099803 14482127439642704976149705)
            ·
              refine ⟨10861595579732028732112279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14482127439642704976149705 10861595579732028732112279)
              ·
                refine ⟨16292393369598043098168419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10861595579732028732112279 16292393369598043098168419)
                ·
                  refine ⟨24438590054397064647252629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16292393369598043098168419 24438590054397064647252629)
                  ·
                    refine ⟨1145558908799862405339967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24438590054397064647252629 1145558908799862405339967)
                    ·
                      rfl

theorem cell23_6692904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_6692904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692904 prefixEnd_6692904 := by exact prefixLift 6692904
  have htrace : WordTrace (prefixWord ++ tailWord_6692904) baseStart_6692904 baseEnd_6692904 := by
    simpa [prefixWord, tailWord_6692904, baseEnd_6692904] using wordTrace_append hprefix tailTrace_6692904
  have hstable : (prefixWord ++ tailWord_6692904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692904).length < 2 ^ (prefixWord ++ tailWord_6692904).sum := by decide
  have hdescent : baseEnd_6692904 < baseStart_6692904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692923 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 5]
def baseStart_6692923 : Nat := 118140960795 + 6692923 * 2 ^ 59
def prefixEnd_6692923 : Nat := 4983230072969 + 3 ^ 40 * 6692923 * 2
def baseEnd_6692923 : Nat := 3436686482532022641682313

theorem tailTrace_6692923 : CollatzResearch.WordTrace tailWord_6692923 prefixEnd_6692923 3436686482532022641682313 := by
  unfold tailWord_6692923
  simp only [CollatzResearch.WordTrace]
  refine ⟨244110956331690506089835423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162740637554460337393223615 244110956331690506089835423)
  ·
    refine ⟨366166434497535759134753135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244110956331690506089835423 366166434497535759134753135)
    ·
      refine ⟨549249651746303638702129703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366166434497535759134753135 549249651746303638702129703)
      ·
        refine ⟨823874477619455458053194555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549249651746303638702129703 823874477619455458053194555)
        ·
          refine ⟨1235811716429183187079791833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 823874477619455458053194555 1235811716429183187079791833)
          ·
            refine ⟨926858787321887390309843875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1235811716429183187079791833 926858787321887390309843875)
            ·
              refine ⟨1390288180982831085464765813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926858787321887390309843875 1390288180982831085464765813)
              ·
                refine ⟨130339516967140414262321795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1390288180982831085464765813 130339516967140414262321795)
                ·
                  refine ⟨195509275450710621393482693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130339516967140414262321795 195509275450710621393482693)
                  ·
                    refine ⟨36657989147008241511278005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 195509275450710621393482693 36657989147008241511278005)
                    ·
                      refine ⟨3436686482532022641682313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36657989147008241511278005 3436686482532022641682313)
                      ·
                        rfl

theorem cell23_6692923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 5].length) (baseStart_6692923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692923 prefixEnd_6692923 := by exact prefixLift 6692923
  have htrace : WordTrace (prefixWord ++ tailWord_6692923) baseStart_6692923 baseEnd_6692923 := by
    simpa [prefixWord, tailWord_6692923, baseEnd_6692923] using wordTrace_append hprefix tailTrace_6692923
  have hstable : (prefixWord ++ tailWord_6692923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692923).length < 2 ^ (prefixWord ++ tailWord_6692923).sum := by decide
  have hdescent : baseEnd_6692923 < baseStart_6692923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692943 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 3, 8]
def baseStart_6692943 : Nat := 118140960795 + 6692943 * 2 ^ 59
def prefixEnd_6692943 : Nat := 4983230072969 + 3 ^ 40 * 6692943 * 2
def baseEnd_6692943 : Nat := 1145565584048370854477407

theorem tailTrace_6692943 : CollatzResearch.WordTrace tailWord_6692943 prefixEnd_6692943 1145565584048370854477407 := by
  unfold tailWord_6692943
  simp only [CollatzResearch.WordTrace]
  refine ⟨244111685791618049505563483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162741123861078699670375655 244111685791618049505563483)
  ·
    refine ⟨366167528687427074258345225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244111685791618049505563483 366167528687427074258345225)
    ·
      refine ⟨274625646515570305693758919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366167528687427074258345225 274625646515570305693758919)
      ·
        refine ⟨411938469773355458540638379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274625646515570305693758919 411938469773355458540638379)
        ·
          refine ⟨617907704660033187810957569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411938469773355458540638379 617907704660033187810957569)
          ·
            refine ⟨463430778495024890858218177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 617907704660033187810957569 463430778495024890858218177)
            ·
              refine ⟨347573083871268668143663633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463430778495024890858218177 347573083871268668143663633)
              ·
                refine ⟨260679812903451501107747725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347573083871268668143663633 260679812903451501107747725)
                ·
                  refine ⟨97754929838794312915405397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260679812903451501107747725 97754929838794312915405397)
                  ·
                    refine ⟨1145565584048370854477407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97754929838794312915405397 1145565584048370854477407)
                    ·
                      rfl

theorem cell23_6692943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 8].length) (baseStart_6692943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692943 prefixEnd_6692943 := by exact prefixLift 6692943
  have htrace : WordTrace (prefixWord ++ tailWord_6692943) baseStart_6692943 baseEnd_6692943 := by
    simpa [prefixWord, tailWord_6692943, baseEnd_6692943] using wordTrace_append hprefix tailTrace_6692943
  have hstable : (prefixWord ++ tailWord_6692943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692943).length < 2 ^ (prefixWord ++ tailWord_6692943).sum := by decide
  have hdescent : baseEnd_6692943 < baseStart_6692943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692958 : List Nat := [4, 4, 1, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_6692958 : Nat := 118140960795 + 6692958 * 2 ^ 59
def prefixEnd_6692958 : Nat := 4983230072969 + 3 ^ 40 * 6692958 * 2
def baseEnd_6692958 : Nat := 3436704454354930004744653

theorem tailTrace_6692958 : CollatzResearch.WordTrace tailWord_6692958 prefixEnd_6692958 3436704454354930004744653 := by
  unfold tailWord_6692958
  simp only [CollatzResearch.WordTrace]
  refine ⟨30514029110820463383419941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162741488591042471378239685 30514029110820463383419941)
  ·
    refine ⟨5721380458278836884391239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30514029110820463383419941 5721380458278836884391239)
    ·
      refine ⟨8582070687418255326586859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5721380458278836884391239 8582070687418255326586859)
      ·
        refine ⟨12873106031127382989880289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8582070687418255326586859 12873106031127382989880289)
        ·
          refine ⟨9654829523345537242410217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12873106031127382989880289 9654829523345537242410217)
          ·
            refine ⟨7241122142509152931807663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9654829523345537242410217 7241122142509152931807663)
            ·
              refine ⟨10861683213763729397711495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7241122142509152931807663 10861683213763729397711495)
              ·
                refine ⟨16292524820645594096567243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10861683213763729397711495 16292524820645594096567243)
                ·
                  refine ⟨24438787230968391144850865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16292524820645594096567243 24438787230968391144850865)
                  ·
                    refine ⟨18329090423226293358638149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24438787230968391144850865 18329090423226293358638149)
                    ·
                      refine ⟨3436704454354930004744653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18329090423226293358638149 3436704454354930004744653)
                      ·
                        rfl

theorem cell23_6692958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_6692958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692958 prefixEnd_6692958 := by exact prefixLift 6692958
  have htrace : WordTrace (prefixWord ++ tailWord_6692958) baseStart_6692958 baseEnd_6692958 := by
    simpa [prefixWord, tailWord_6692958, baseEnd_6692958] using wordTrace_append hprefix tailTrace_6692958
  have hstable : (prefixWord ++ tailWord_6692958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692958).length < 2 ^ (prefixWord ++ tailWord_6692958).sum := by decide
  have hdescent : baseEnd_6692958 < baseStart_6692958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692960 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 2, 6]
def baseStart_6692960 : Nat := 118140960795 + 6692960 * 2 ^ 59
def prefixEnd_6692960 : Nat := 4983230072969 + 3 ^ 40 * 6692960 * 2
def baseEnd_6692960 : Nat := 1145568493772079665639881

theorem tailTrace_6692960 : CollatzResearch.WordTrace tailWord_6692960 prefixEnd_6692960 1145568493772079665639881 := by
  unfold tailWord_6692960
  simp only [CollatzResearch.WordTrace]
  refine ⟨122056152916278230704466167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162741537221704307605954889 122056152916278230704466167)
  ·
    refine ⟨183084229374417346056699251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122056152916278230704466167 183084229374417346056699251)
    ·
      refine ⟨274626344061626019085048877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183084229374417346056699251 274626344061626019085048877)
      ·
        refine ⟨102984879023109757156893329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274626344061626019085048877 102984879023109757156893329)
        ·
          refine ⟨77238659267332317867669997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102984879023109757156893329 77238659267332317867669997)
          ·
            refine ⟨28964497225249619200376249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77238659267332317867669997 28964497225249619200376249)
            ·
              refine ⟨21723372918937214400282187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28964497225249619200376249 21723372918937214400282187)
              ·
                refine ⟨32585059378405821600423281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21723372918937214400282187 32585059378405821600423281)
                ·
                  refine ⟨24438794533804366200317461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32585059378405821600423281 24438794533804366200317461)
                  ·
                    refine ⟨1145568493772079665639881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24438794533804366200317461 1145568493772079665639881)
                    ·
                      rfl

theorem cell23_6692960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 2, 6].length) (baseStart_6692960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6692960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6692960 prefixEnd_6692960 := by exact prefixLift 6692960
  have htrace : WordTrace (prefixWord ++ tailWord_6692960) baseStart_6692960 baseEnd_6692960 := by
    simpa [prefixWord, tailWord_6692960, baseEnd_6692960] using wordTrace_append hprefix tailTrace_6692960
  have hstable : (prefixWord ++ tailWord_6692960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692960).length < 2 ^ (prefixWord ++ tailWord_6692960).sum := by decide
  have hdescent : baseEnd_6692960 < baseStart_6692960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693012 : List Nat := [2, 4, 2, 3, 2, 1, 2, 1, 2, 1, 3]
def baseStart_6693012 : Nat := 118140960795 + 6693012 * 2 ^ 59
def prefixEnd_6693012 : Nat := 4983230072969 + 3 ^ 40 * 6693012 * 2
def baseEnd_6693012 : Nat := 3436732182310272793469405

theorem tailTrace_6693012 : CollatzResearch.WordTrace tailWord_6693012 prefixEnd_6693012 3436732182310272793469405 := by
  unfold tailWord_6693012
  simp only [CollatzResearch.WordTrace]
  refine ⟨122057101214184037144912645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162742801618912049526550193 122057101214184037144912645)
  ·
    refine ⟨22885706477659506964671121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122057101214184037144912645 22885706477659506964671121)
    ·
      refine ⟨17164279858244630223503341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22885706477659506964671121 17164279858244630223503341)
      ·
        refine ⟨6436604946841736333813753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17164279858244630223503341 6436604946841736333813753)
        ·
          refine ⟨4827453710131302250360315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6436604946841736333813753 4827453710131302250360315)
          ·
            refine ⟨7241180565196953375540473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4827453710131302250360315 7241180565196953375540473)
            ·
              refine ⟨5430885423897715031655355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7241180565196953375540473 5430885423897715031655355)
              ·
                refine ⟨8146328135846572547483033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5430885423897715031655355 8146328135846572547483033)
                ·
                  refine ⟨6109746101884929410612275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8146328135846572547483033 6109746101884929410612275)
                  ·
                    refine ⟨9164619152827394115918413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6109746101884929410612275 9164619152827394115918413)
                    ·
                      refine ⟨3436732182310272793469405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9164619152827394115918413 3436732182310272793469405)
                      ·
                        rfl

theorem cell23_6693012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_6693012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693012 prefixEnd_6693012 := by exact prefixLift 6693012
  have htrace : WordTrace (prefixWord ++ tailWord_6693012) baseStart_6693012 baseEnd_6693012 := by
    simpa [prefixWord, tailWord_6693012, baseEnd_6693012] using wordTrace_append hprefix tailTrace_6693012
  have hstable : (prefixWord ++ tailWord_6693012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693012).length < 2 ^ (prefixWord ++ tailWord_6693012).sum := by decide
  have hdescent : baseEnd_6693012 < baseStart_6693012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693018 : List Nat := [3, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2]
def baseStart_6693018 : Nat := 118140960795 + 6693018 * 2 ^ 59
def prefixEnd_6693018 : Nat := 4983230072969 + 3 ^ 40 * 6693018 * 2
def baseEnd_6693018 : Nat := 3436735263194199769994377

theorem tailTrace_6693018 : CollatzResearch.WordTrace tailWord_6693018 prefixEnd_6693018 3436735263194199769994377 := by
  unfold tailWord_6693018
  simp only [CollatzResearch.WordTrace]
  refine ⟨61028605316586584328635927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162742947510897558209695805 61028605316586584328635927)
  ·
    refine ⟨91542907974879876492953891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61028605316586584328635927 91542907974879876492953891)
    ·
      refine ⟨137314361962319814739430837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91542907974879876492953891 137314361962319814739430837)
      ·
        refine ⟨12873221433967482631821641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137314361962319814739430837 12873221433967482631821641)
        ·
          refine ⟨9654916075475611973866231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12873221433967482631821641 9654916075475611973866231)
          ·
            refine ⟨14482374113213417960799347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9654916075475611973866231 14482374113213417960799347)
            ·
              refine ⟨21723561169820126941199021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14482374113213417960799347 21723561169820126941199021)
              ·
                refine ⟨8146335438682547602949633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21723561169820126941199021 8146335438682547602949633)
                ·
                  refine ⟨6109751579011910702212225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8146335438682547602949633 6109751579011910702212225)
                  ·
                    refine ⟨4582313684258933026659169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6109751579011910702212225 4582313684258933026659169)
                    ·
                      refine ⟨3436735263194199769994377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4582313684258933026659169 3436735263194199769994377)
                      ·
                        rfl

theorem cell23_6693018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_6693018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693018 prefixEnd_6693018 := by exact prefixLift 6693018
  have htrace : WordTrace (prefixWord ++ tailWord_6693018) baseStart_6693018 baseEnd_6693018 := by
    simpa [prefixWord, tailWord_6693018, baseEnd_6693018] using wordTrace_append hprefix tailTrace_6693018
  have hstable : (prefixWord ++ tailWord_6693018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693018).length < 2 ^ (prefixWord ++ tailWord_6693018).sum := by decide
  have hdescent : baseEnd_6693018 < baseStart_6693018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693058 : List Nat := [3, 5, 1, 1, 1, 2, 1, 4, 5]
def baseStart_6693058 : Nat := 118140960795 + 6693058 * 2 ^ 59
def prefixEnd_6693058 : Nat := 4983230072969 + 3 ^ 40 * 6693058 * 2
def baseEnd_6693058 : Nat := 381861755824486623721577

theorem tailTrace_6693058 : CollatzResearch.WordTrace tailWord_6693058 prefixEnd_6693058 381861755824486623721577 := by
  unfold tailWord_6693058
  simp only [CollatzResearch.WordTrace]
  refine ⟨61028970046550356036499957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162743920124134282763999885 61028970046550356036499957)
  ·
    refine ⟨5721465941864095878421871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61028970046550356036499957 5721465941864095878421871)
    ·
      refine ⟨8582198912796143817632807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5721465941864095878421871 8582198912796143817632807)
      ·
        refine ⟨12873298369194215726449211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8582198912796143817632807 12873298369194215726449211)
        ·
          refine ⟨19309947553791323589673817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12873298369194215726449211 19309947553791323589673817)
          ·
            refine ⟨14482460665343492692255363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19309947553791323589673817 14482460665343492692255363)
            ·
              refine ⟨21723690998015239038383045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14482460665343492692255363 21723690998015239038383045)
              ·
                refine ⟨4073192062127857319696821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21723690998015239038383045 4073192062127857319696821)
                ·
                  refine ⟨381861755824486623721577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4073192062127857319696821 381861755824486623721577)
                  ·
                    rfl

theorem cell23_6693058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_6693058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693058 prefixEnd_6693058 := by exact prefixLift 6693058
  have htrace : WordTrace (prefixWord ++ tailWord_6693058) baseStart_6693058 baseEnd_6693058 := by
    simpa [prefixWord, tailWord_6693058, baseEnd_6693058] using wordTrace_append hprefix tailTrace_6693058
  have hstable : (prefixWord ++ tailWord_6693058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693058).length < 2 ^ (prefixWord ++ tailWord_6693058).sum := by decide
  have hdescent : baseEnd_6693058 < baseStart_6693058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693067 : List Nat := [1, 1, 1, 1, 3, 2, 4, 3, 3, 4]
def baseStart_6693067 : Nat := 118140960795 + 6693067 * 2 ^ 59
def prefixEnd_6693067 : Nat := 4983230072969 + 3 ^ 40 * 6693067 * 2
def baseEnd_6693067 : Nat := 1145586807915423359427217

theorem tailTrace_6693067 : CollatzResearch.WordTrace tailWord_6693067 prefixEnd_6693067 1145586807915423359427217 := by
  unfold tailWord_6693067
  simp only [CollatzResearch.WordTrace]
  refine ⟨244116208443168818683077455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162744138962112545788718303 244116208443168818683077455)
  ·
    refine ⟨366174312664753228024616183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244116208443168818683077455 366174312664753228024616183)
    ·
      refine ⟨549261468997129842036924275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366174312664753228024616183 549261468997129842036924275)
      ·
        refine ⟨823892203495694763055386413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549261468997129842036924275 823892203495694763055386413)
        ·
          refine ⟨308959576310885536145769905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 823892203495694763055386413 308959576310885536145769905)
          ·
            refine ⟨231719682233164152109327429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308959576310885536145769905 231719682233164152109327429)
            ·
              refine ⟨43447440418718278520498893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231719682233164152109327429 43447440418718278520498893)
              ·
                refine ⟨16292790157019354445187085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43447440418718278520498893 16292790157019354445187085)
                ·
                  refine ⟨6109796308882257916945157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16292790157019354445187085 6109796308882257916945157)
                  ·
                    refine ⟨1145586807915423359427217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6109796308882257916945157 1145586807915423359427217)
                    ·
                      rfl

theorem cell23_6693067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 4].length) (baseStart_6693067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693067 prefixEnd_6693067 := by exact prefixLift 6693067
  have htrace : WordTrace (prefixWord ++ tailWord_6693067) baseStart_6693067 baseEnd_6693067 := by
    simpa [prefixWord, tailWord_6693067, baseEnd_6693067] using wordTrace_append hprefix tailTrace_6693067
  have hstable : (prefixWord ++ tailWord_6693067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693067).length < 2 ^ (prefixWord ++ tailWord_6693067).sum := by decide
  have hdescent : baseEnd_6693067 < baseStart_6693067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693074 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 1, 6, 2]
def baseStart_6693074 : Nat := 118140960795 + 6693074 * 2 ^ 59
def prefixEnd_6693074 : Nat := 4983230072969 + 3 ^ 40 * 6693074 * 2
def baseEnd_6693074 : Nat := 3436764018110851550894119

theorem tailTrace_6693074 : CollatzResearch.WordTrace tailWord_6693074 prefixEnd_6693074 3436764018110851550894119 := by
  unfold tailWord_6693074
  simp only [CollatzResearch.WordTrace]
  refine ⟨61029115938535864719645569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162744309169428972585721517 61029115938535864719645569)
  ·
    refine ⟨45771836953901898539734177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61029115938535864719645569 45771836953901898539734177)
    ·
      refine ⟨34328877715426423904800633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45771836953901898539734177 34328877715426423904800633)
      ·
        refine ⟨25746658286569817928600475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34328877715426423904800633 25746658286569817928600475)
        ·
          refine ⟨38619987429854726892900713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25746658286569817928600475 38619987429854726892900713)
          ·
            refine ⟨28964990572391045169675535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38619987429854726892900713 28964990572391045169675535)
            ·
              refine ⟨43447485858586567754513303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28964990572391045169675535 43447485858586567754513303)
              ·
                refine ⟨65171228787879851631769955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43447485858586567754513303 65171228787879851631769955)
                ·
                  refine ⟨97756843181819777447654933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65171228787879851631769955 97756843181819777447654933)
                  ·
                    refine ⟨4582352024147802067858825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97756843181819777447654933 4582352024147802067858825)
                    ·
                      refine ⟨3436764018110851550894119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4582352024147802067858825 3436764018110851550894119)
                      ·
                        rfl

theorem cell23_6693074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_6693074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693074 prefixEnd_6693074 := by exact prefixLift 6693074
  have htrace : WordTrace (prefixWord ++ tailWord_6693074) baseStart_6693074 baseEnd_6693074 := by
    simpa [prefixWord, tailWord_6693074, baseEnd_6693074] using wordTrace_append hprefix tailTrace_6693074
  have hstable : (prefixWord ++ tailWord_6693074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693074).length < 2 ^ (prefixWord ++ tailWord_6693074).sum := by decide
  have hdescent : baseEnd_6693074 < baseStart_6693074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693114 : List Nat := [3, 1, 1, 1, 1, 7, 1, 2, 6]
def baseStart_6693114 : Nat := 118140960795 + 6693114 * 2 ^ 59
def prefixEnd_6693114 : Nat := 4983230072969 + 3 ^ 40 * 6693114 * 2
def baseEnd_6693114 : Nat := 381864950815225710488215

theorem tailTrace_6693114 : CollatzResearch.WordTrace tailWord_6693114 prefixEnd_6693114 381864950815225710488215 := by
  unfold tailWord_6693114
  simp only [CollatzResearch.WordTrace]
  refine ⟨61029480668499636427509599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162745281782665697140025597 61029480668499636427509599)
  ·
    refine ⟨91544221002749454641264399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61029480668499636427509599 91544221002749454641264399)
    ·
      refine ⟨137316331504124181961896599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91544221002749454641264399 137316331504124181961896599)
      ·
        refine ⟨205974497256186272942844899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137316331504124181961896599 205974497256186272942844899)
        ·
          refine ⟨308961745884279409414267349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205974497256186272942844899 308961745884279409414267349)
          ·
            refine ⟨7241290919162798658146891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 308961745884279409414267349 7241290919162798658146891)
            ·
              refine ⟨10861936378744197987220337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7241290919162798658146891 10861936378744197987220337)
              ·
                refine ⟨8146452284058148490415253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10861936378744197987220337 8146452284058148490415253)
                ·
                  refine ⟨381864950815225710488215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8146452284058148490415253 381864950815225710488215)
                  ·
                    rfl

theorem cell23_6693114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 6].length) (baseStart_6693114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693114 prefixEnd_6693114 := by exact prefixLift 6693114
  have htrace : WordTrace (prefixWord ++ tailWord_6693114) baseStart_6693114 baseEnd_6693114 := by
    simpa [prefixWord, tailWord_6693114, baseEnd_6693114] using wordTrace_append hprefix tailTrace_6693114
  have hstable : (prefixWord ++ tailWord_6693114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693114).length < 2 ^ (prefixWord ++ tailWord_6693114).sum := by decide
  have hdescent : baseEnd_6693114 < baseStart_6693114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693134 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2]
def baseStart_6693134 : Nat := 118140960795 + 6693134 * 2 ^ 59
def prefixEnd_6693134 : Nat := 4983230072969 + 3 ^ 40 * 6693134 * 2
def baseEnd_6693134 : Nat := 3436794826950121316143843

theorem tailTrace_6693134 : CollatzResearch.WordTrace tailWord_6693134 prefixEnd_6693134 3436794826950121316143843 := by
  unfold tailWord_6693134
  simp only [CollatzResearch.WordTrace]
  refine ⟨30514831516740761140720807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162745768089284059417177637 30514831516740761140720807)
  ·
    refine ⟨45772247275111141711081211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30514831516740761140720807 45772247275111141711081211)
    ·
      refine ⟨68658370912666712566621817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45772247275111141711081211 68658370912666712566621817)
      ·
        refine ⟨51493778184500034424966363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68658370912666712566621817 51493778184500034424966363)
        ·
          refine ⟨77240667276750051637449545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51493778184500034424966363 77240667276750051637449545)
          ·
            refine ⟨57930500457562538728087159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77240667276750051637449545 57930500457562538728087159)
            ·
              refine ⟨86895750686343808092130739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57930500457562538728087159 86895750686343808092130739)
              ·
                refine ⟨130343626029515712138196109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86895750686343808092130739 130343626029515712138196109)
                ·
                  refine ⟨48878859761068392051823541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130343626029515712138196109 48878859761068392051823541)
                  ·
                    refine ⟨4582393102600161754858457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48878859761068392051823541 4582393102600161754858457)
                    ·
                      refine ⟨3436794826950121316143843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4582393102600161754858457 3436794826950121316143843)
                      ·
                        rfl

theorem cell23_6693134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_6693134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693134 prefixEnd_6693134 := by exact prefixLift 6693134
  have htrace : WordTrace (prefixWord ++ tailWord_6693134) baseStart_6693134 baseEnd_6693134 := by
    simpa [prefixWord, tailWord_6693134, baseEnd_6693134] using wordTrace_append hprefix tailTrace_6693134
  have hstable : (prefixWord ++ tailWord_6693134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693134).length < 2 ^ (prefixWord ++ tailWord_6693134).sum := by decide
  have hdescent : baseEnd_6693134 < baseStart_6693134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693144 : List Nat := [2, 1, 2, 3, 1, 2, 4, 2, 1, 5]
def baseStart_6693144 : Nat := 118140960795 + 6693144 * 2 ^ 59
def prefixEnd_6693144 : Nat := 4983230072969 + 3 ^ 40 * 6693144 * 2
def baseEnd_6693144 : Nat := 1145599987252222092339599

theorem tailTrace_6693144 : CollatzResearch.WordTrace tailWord_6693144 prefixEnd_6693144 1145599987252222092339599 := by
  unfold tailWord_6693144
  simp only [CollatzResearch.WordTrace]
  refine ⟨122059508431944930416815243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162746011242593240555753657 122059508431944930416815243)
  ·
    refine ⟨183089262647917395625222865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122059508431944930416815243 183089262647917395625222865)
    ·
      refine ⟨137316946985938046718917149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183089262647917395625222865 137316946985938046718917149)
      ·
        refine ⟨51493855119726767519593931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137316946985938046718917149 51493855119726767519593931)
        ·
          refine ⟨77240782679590151279390897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51493855119726767519593931 77240782679590151279390897)
          ·
            refine ⟨57930587009692613459543173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77240782679590151279390897 57930587009692613459543173)
            ·
              refine ⟨10861985064317365023664345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57930587009692613459543173 10861985064317365023664345)
              ·
                refine ⟨8146488798238023767748259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10861985064317365023664345 8146488798238023767748259)
                ·
                  refine ⟨12219733197357035651622389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8146488798238023767748259 12219733197357035651622389)
                  ·
                    refine ⟨1145599987252222092339599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12219733197357035651622389 1145599987252222092339599)
                    ·
                      rfl

theorem cell23_6693144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 1, 5].length) (baseStart_6693144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693144 prefixEnd_6693144 := by exact prefixLift 6693144
  have htrace : WordTrace (prefixWord ++ tailWord_6693144) baseStart_6693144 baseEnd_6693144 := by
    simpa [prefixWord, tailWord_6693144, baseEnd_6693144] using wordTrace_append hprefix tailTrace_6693144
  have hstable : (prefixWord ++ tailWord_6693144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693144).length < 2 ^ (prefixWord ++ tailWord_6693144).sum := by decide
  have hdescent : baseEnd_6693144 < baseStart_6693144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693147 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 4]
def baseStart_6693147 : Nat := 118140960795 + 6693147 * 2 ^ 59
def prefixEnd_6693147 : Nat := 4983230072969 + 3 ^ 40 * 6693147 * 2
def baseEnd_6693147 : Nat := 3436801502198629765281283

theorem tailTrace_6693147 : CollatzResearch.WordTrace tailWord_6693147 prefixEnd_6693147 3436801502198629765281283 := by
  unfold tailWord_6693147
  simp only [CollatzResearch.WordTrace]
  refine ⟨244119126282878992345989695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162746084188585994897326463 244119126282878992345989695)
  ·
    refine ⟨366178689424318488518984543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244119126282878992345989695 366178689424318488518984543)
    ·
      refine ⟨549268034136477732778476815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366178689424318488518984543 549268034136477732778476815)
      ·
        refine ⟨823902051204716599167715223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549268034136477732778476815 823902051204716599167715223)
        ·
          refine ⟨1235853076807074898751572835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 823902051204716599167715223 1235853076807074898751572835)
          ·
            refine ⟨1853779615210612348127359253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1235853076807074898751572835 1853779615210612348127359253)
            ·
              refine ⟨86895919462997453818469965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1853779615210612348127359253 86895919462997453818469965)
              ·
                refine ⟨32585969798624045181926237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86895919462997453818469965 32585969798624045181926237)
                ·
                  refine ⟨12219738674484016943222339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32585969798624045181926237 12219738674484016943222339)
                  ·
                    refine ⟨18329608011726025414833509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12219738674484016943222339 18329608011726025414833509)
                    ·
                      refine ⟨3436801502198629765281283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18329608011726025414833509 3436801502198629765281283)
                      ·
                        rfl

theorem cell23_6693147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 4].length) (baseStart_6693147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693147 prefixEnd_6693147 := by exact prefixLift 6693147
  have htrace : WordTrace (prefixWord ++ tailWord_6693147) baseStart_6693147 baseEnd_6693147 := by
    simpa [prefixWord, tailWord_6693147, baseEnd_6693147] using wordTrace_append hprefix tailTrace_6693147
  have hstable : (prefixWord ++ tailWord_6693147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693147).length < 2 ^ (prefixWord ++ tailWord_6693147).sum := by decide
  have hdescent : baseEnd_6693147 < baseStart_6693147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693164 : List Nat := [2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 4]
def baseStart_6693164 : Nat := 118140960795 + 6693164 * 2 ^ 59
def prefixEnd_6693164 : Nat := 4983230072969 + 3 ^ 40 * 6693164 * 2
def baseEnd_6693164 : Nat := 3436810231369756198768705

theorem tailTrace_6693164 : CollatzResearch.WordTrace tailWord_6693164 prefixEnd_6693164 3436810231369756198768705 := by
  unfold tailWord_6693164
  simp only [CollatzResearch.WordTrace]
  refine ⟨122059873161908702124679273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162746497549211602832905697 122059873161908702124679273)
  ·
    refine ⟨91544904871431526593509455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122059873161908702124679273 91544904871431526593509455)
    ·
      refine ⟨137317357307147289890264183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91544904871431526593509455 137317357307147289890264183)
      ·
        refine ⟨205976035960720934835396275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137317357307147289890264183 205976035960720934835396275)
        ·
          refine ⟨308964053941081402253094413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205976035960720934835396275 308964053941081402253094413)
          ·
            refine ⟨115861520227905525844910405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308964053941081402253094413 115861520227905525844910405)
            ·
              refine ⟨21724035042732286095920701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115861520227905525844910405 21724035042732286095920701)
              ·
                refine ⟨8146513141024607285970263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21724035042732286095920701 8146513141024607285970263)
                ·
                  refine ⟨12219769711536910928955395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8146513141024607285970263 12219769711536910928955395)
                  ·
                    refine ⟨18329654567305366393433093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12219769711536910928955395 18329654567305366393433093)
                    ·
                      refine ⟨3436810231369756198768705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18329654567305366393433093 3436810231369756198768705)
                      ·
                        rfl

theorem cell23_6693164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 4].length) (baseStart_6693164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693164 prefixEnd_6693164 := by exact prefixLift 6693164
  have htrace : WordTrace (prefixWord ++ tailWord_6693164) baseStart_6693164 baseEnd_6693164 := by
    simpa [prefixWord, tailWord_6693164, baseEnd_6693164] using wordTrace_append hprefix tailTrace_6693164
  have hstable : (prefixWord ++ tailWord_6693164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693164).length < 2 ^ (prefixWord ++ tailWord_6693164).sum := by decide
  have hdescent : baseEnd_6693164 < baseStart_6693164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693167 : List Nat := [1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 5]
def baseStart_6693167 : Nat := 118140960795 + 6693167 * 2 ^ 59
def prefixEnd_6693167 : Nat := 4983230072969 + 3 ^ 40 * 6693167 * 2
def baseEnd_6693167 : Nat := 3436811771811719687031191

theorem tailTrace_6693167 : CollatzResearch.WordTrace tailWord_6693167 prefixEnd_6693167 3436811771811719687031191 := by
  unfold tailWord_6693167
  simp only [CollatzResearch.WordTrace]
  refine ⟨244119855742806535761717755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162746570495204357174478503 244119855742806535761717755)
  ·
    refine ⟨366179783614209803642576633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244119855742806535761717755 366179783614209803642576633)
    ·
      refine ⟨274634837710657352731932475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366179783614209803642576633 274634837710657352731932475)
      ·
        refine ⟨411952256565986029097898713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274634837710657352731932475 411952256565986029097898713)
        ·
          refine ⟨308964192424489521823424035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411952256565986029097898713 308964192424489521823424035)
          ·
            refine ⟨463446288636734282735136053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308964192424489521823424035 463446288636734282735136053)
            ·
              refine ⟨43448089559693839006419005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 463446288636734282735136053 43448089559693839006419005)
              ·
                refine ⟨16293033584885189627407127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43448089559693839006419005 16293033584885189627407127)
                ·
                  refine ⟨24439550377327784441110691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16293033584885189627407127 24439550377327784441110691)
                  ·
                    refine ⟨36659325565991676661666037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24439550377327784441110691 36659325565991676661666037)
                    ·
                      refine ⟨3436811771811719687031191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36659325565991676661666037 3436811771811719687031191)
                      ·
                        rfl

theorem cell23_6693167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 5].length) (baseStart_6693167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693167 prefixEnd_6693167 := by exact prefixLift 6693167
  have htrace : WordTrace (prefixWord ++ tailWord_6693167) baseStart_6693167 baseEnd_6693167 := by
    simpa [prefixWord, tailWord_6693167, baseEnd_6693167] using wordTrace_append hprefix tailTrace_6693167
  have hstable : (prefixWord ++ tailWord_6693167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693167).length < 2 ^ (prefixWord ++ tailWord_6693167).sum := by decide
  have hdescent : baseEnd_6693167 < baseStart_6693167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693201 : List Nat := [1, 2, 2, 1, 4, 2, 3, 2, 1, 2, 3]
def baseStart_6693201 : Nat := 118140960795 + 6693201 * 2 ^ 59
def prefixEnd_6693201 : Nat := 4983230072969 + 3 ^ 40 * 6693201 * 2
def baseEnd_6693201 : Nat := 3436829230153972554006035

theorem tailTrace_6693201 : CollatzResearch.WordTrace tailWord_6693201 prefixEnd_6693201 3436829230153972554006035 := by
  unfold tailWord_6693201
  simp only [CollatzResearch.WordTrace]
  refine ⟨244121095824683359568455457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162747397216455573045636971 244121095824683359568455457)
  ·
    refine ⟨183090821868512519676341593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244121095824683359568455457 183090821868512519676341593)
    ·
      refine ⟨137318116401384389757256195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183090821868512519676341593 137318116401384389757256195)
      ·
        refine ⟨205977174602076584635884293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137318116401384389757256195 205977174602076584635884293)
        ·
          refine ⟨38620720237889359619228305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205977174602076584635884293 38620720237889359619228305)
          ·
            refine ⟨28965540178417019714421229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38620720237889359619228305 28965540178417019714421229)
            ·
              refine ⟨10862077566906382392907961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28965540178417019714421229 10862077566906382392907961)
              ·
                refine ⟨8146558175179786794680971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10862077566906382392907961 8146558175179786794680971)
                ·
                  refine ⟨12219837262769680192021457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8146558175179786794680971 12219837262769680192021457)
                  ·
                    refine ⟨9164877947077260144016093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12219837262769680192021457 9164877947077260144016093)
                    ·
                      refine ⟨3436829230153972554006035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9164877947077260144016093 3436829230153972554006035)
                      ·
                        rfl

theorem cell23_6693201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 2, 3].length) (baseStart_6693201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693201 prefixEnd_6693201 := by exact prefixLift 6693201
  have htrace : WordTrace (prefixWord ++ tailWord_6693201) baseStart_6693201 baseEnd_6693201 := by
    simpa [prefixWord, tailWord_6693201, baseEnd_6693201] using wordTrace_append hprefix tailTrace_6693201
  have hstable : (prefixWord ++ tailWord_6693201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693201).length < 2 ^ (prefixWord ++ tailWord_6693201).sum := by decide
  have hdescent : baseEnd_6693201 < baseStart_6693201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693232 : List Nat := [2, 1, 1, 1, 4, 5, 2, 2, 1, 2, 2]
def baseStart_6693232 : Nat := 118140960795 + 6693232 * 2 ^ 59
def prefixEnd_6693232 : Nat := 4983230072969 + 3 ^ 40 * 6693232 * 2
def baseEnd_6693232 : Nat := 3436845148054261932718393

theorem tailTrace_6693232 : CollatzResearch.WordTrace tailWord_6693232 prefixEnd_6693232 3436845148054261932718393 := by
  unfold tailWord_6693232
  simp only [CollatzResearch.WordTrace]
  refine ⟨122061113243785525931416975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162748150991714034575222633 122061113243785525931416975)
  ·
    refine ⟨183091669865678288897125463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122061113243785525931416975 183091669865678288897125463)
    ·
      refine ⟨274637504798517433345688195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183091669865678288897125463 274637504798517433345688195)
      ·
        refine ⟨411956257197776150018532293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274637504798517433345688195 411956257197776150018532293)
        ·
          refine ⟨77241798224583028128474805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 411956257197776150018532293 77241798224583028128474805)
          ·
            refine ⟨7241418583554658887044513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77241798224583028128474805 7241418583554658887044513)
            ·
              refine ⟨5431063937665994165283385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7241418583554658887044513 5431063937665994165283385)
              ·
                refine ⟨4073297953249495623962539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5431063937665994165283385 4073297953249495623962539)
                ·
                  refine ⟨6109946929874243435943809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4073297953249495623962539 6109946929874243435943809)
                  ·
                    refine ⟨4582460197405682576957857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6109946929874243435943809 4582460197405682576957857)
                    ·
                      refine ⟨3436845148054261932718393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4582460197405682576957857 3436845148054261932718393)
                      ·
                        rfl

theorem cell23_6693232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 1, 2, 2].length) (baseStart_6693232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693232 prefixEnd_6693232 := by exact prefixLift 6693232
  have htrace : WordTrace (prefixWord ++ tailWord_6693232) baseStart_6693232 baseEnd_6693232 := by
    simpa [prefixWord, tailWord_6693232, baseEnd_6693232] using wordTrace_append hprefix tailTrace_6693232
  have hstable : (prefixWord ++ tailWord_6693232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693232).length < 2 ^ (prefixWord ++ tailWord_6693232).sum := by decide
  have hdescent : baseEnd_6693232 < baseStart_6693232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
