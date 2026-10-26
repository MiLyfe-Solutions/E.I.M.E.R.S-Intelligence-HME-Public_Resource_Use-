import V185TrunkScan23Chunk0955

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5660325 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 5, 2, 3]
def baseStart_5660325 : Nat := 118140960795 + 5660325 * 2 ^ 59
def prefixEnd_5660325 : Nat := 4983230072969 + 3 ^ 40 * 5660325 * 2
def baseEnd_5660325 : Nat := 2906467385660671686106145

theorem tailTrace_5660325 : CollatzResearch.WordTrace tailWord_5660325 prefixEnd_5660325 2906467385660671686106145 := by
  unfold tailWord_5660325
  simp only [CollatzResearch.WordTrace]
  refine ⟨206449013218616706391670429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137632675479077804261113619 206449013218616706391670429)
  ·
    refine ⟨77418379956981264896876411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206449013218616706391670429 77418379956981264896876411)
    ·
      refine ⟨116127569935471897345314617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77418379956981264896876411 116127569935471897345314617)
      ·
        refine ⟨87095677451603923008985963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116127569935471897345314617 87095677451603923008985963)
        ·
          refine ⟨130643516177405884513478945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87095677451603923008985963 130643516177405884513478945)
          ·
            refine ⟨97982637133054413385109209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130643516177405884513478945 97982637133054413385109209)
            ·
              refine ⟨73486977849790810038831907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97982637133054413385109209 73486977849790810038831907)
              ·
                refine ⟨110230466774686215058247861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73486977849790810038831907 110230466774686215058247861)
                ·
                  refine ⟨10334106260126832661710737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110230466774686215058247861 10334106260126832661710737)
                  ·
                    refine ⟨7750579695095124496283053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10334106260126832661710737 7750579695095124496283053)
                    ·
                      refine ⟨2906467385660671686106145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7750579695095124496283053 2906467385660671686106145)
                      ·
                        rfl

theorem cell23_5660325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_5660325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660325 prefixEnd_5660325 := by exact prefixLift 5660325
  have htrace : WordTrace (prefixWord ++ tailWord_5660325) baseStart_5660325 baseEnd_5660325 := by
    simpa [prefixWord, tailWord_5660325, baseEnd_5660325] using wordTrace_append hprefix tailTrace_5660325
  have hstable : (prefixWord ++ tailWord_5660325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660325).length < 2 ^ (prefixWord ++ tailWord_5660325).sum := by decide
  have hdescent : baseEnd_5660325 < baseStart_5660325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660345 : List Nat := [1, 2, 1, 4, 1, 1, 6, 7]
def baseStart_5660345 : Nat := 118140960795 + 5660345 * 2 ^ 59
def prefixEnd_5660345 : Nat := 4983230072969 + 3 ^ 40 * 5660345 * 2
def baseEnd_5660345 : Nat := 107647320565694874365039

theorem tailTrace_5660345 : CollatzResearch.WordTrace tailWord_5660345 prefixEnd_5660345 107647320565694874365039 := by
  unfold tailWord_5660345
  simp only [CollatzResearch.WordTrace]
  refine ⟨206449742678544249807398489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137633161785696166538265659 206449742678544249807398489)
  ·
    refine ⟨154837307008908187355548867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206449742678544249807398489 154837307008908187355548867)
    ·
      refine ⟨232255960513362281033323301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154837307008908187355548867 232255960513362281033323301)
      ·
        refine ⟨43547992596255427693748119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232255960513362281033323301 43547992596255427693748119)
        ·
          refine ⟨65321988894383141540622179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43547992596255427693748119 65321988894383141540622179)
          ·
            refine ⟨97982983341574712310933269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65321988894383141540622179 97982983341574712310933269)
            ·
              refine ⟨4592952344136314639574997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97982983341574712310933269 4592952344136314639574997)
              ·
                refine ⟨107647320565694874365039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4592952344136314639574997 107647320565694874365039)
                ·
                  rfl

theorem cell23_5660345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 7].length) (baseStart_5660345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660345 prefixEnd_5660345 := by exact prefixLift 5660345
  have htrace : WordTrace (prefixWord ++ tailWord_5660345) baseStart_5660345 baseEnd_5660345 := by
    simpa [prefixWord, tailWord_5660345, baseEnd_5660345] using wordTrace_append hprefix tailTrace_5660345
  have hstable : (prefixWord ++ tailWord_5660345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660345).length < 2 ^ (prefixWord ++ tailWord_5660345).sum := by decide
  have hdescent : baseEnd_5660345 < baseStart_5660345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660362 : List Nat := [3, 1, 2, 1, 6, 1, 9]
def baseStart_5660362 : Nat := 118140960795 + 5660362 * 2 ^ 59
def prefixEnd_5660362 : Nat := 4983230072969 + 3 ^ 40 * 5660362 * 2
def baseEnd_5660362 : Nat := 35882547956109728905475

theorem tailTrace_5660362 : CollatzResearch.WordTrace tailWord_5660362 prefixEnd_5660362 35882547956109728905475 := by
  unfold tailWord_5660362
  simp only [CollatzResearch.WordTrace]
  refine ⟨51612590679870665427691835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137633575146321774473844893 51612590679870665427691835)
  ·
    refine ⟨77418886019805998141537753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51612590679870665427691835 77418886019805998141537753)
    ·
      refine ⟨58064164514854498606153315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77418886019805998141537753 58064164514854498606153315)
      ·
        refine ⟨87096246772281747909229973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58064164514854498606153315 87096246772281747909229973)
        ·
          refine ⟨4082636567450706933245155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 87096246772281747909229973 4082636567450706933245155)
          ·
            refine ⟨6123954851176060399867733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4082636567450706933245155 6123954851176060399867733)
            ·
              refine ⟨35882547956109728905475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6123954851176060399867733 35882547956109728905475)
              ·
                rfl

theorem cell23_5660362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 9].length) (baseStart_5660362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660362 prefixEnd_5660362 := by exact prefixLift 5660362
  have htrace : WordTrace (prefixWord ++ tailWord_5660362) baseStart_5660362 baseEnd_5660362 := by
    simpa [prefixWord, tailWord_5660362, baseEnd_5660362] using wordTrace_append hprefix tailTrace_5660362
  have hstable : (prefixWord ++ tailWord_5660362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660362).length < 2 ^ (prefixWord ++ tailWord_5660362).sum := by decide
  have hdescent : baseEnd_5660362 < baseStart_5660362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660389 : List Nat := [1, 3, 1, 4, 1, 1, 3, 3, 2, 1, 3]
def baseStart_5660389 : Nat := 118140960795 + 5660389 * 2 ^ 59
def prefixEnd_5660389 : Nat := 4983230072969 + 3 ^ 40 * 5660389 * 2
def baseEnd_5660389 : Nat := 2906500248422559435705851

theorem tailTrace_5660389 : CollatzResearch.WordTrace tailWord_5660389 prefixEnd_5660389 2906500248422559435705851 := by
  unfold tailWord_5660389
  simp only [CollatzResearch.WordTrace]
  refine ⟨206451347490384845322000221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137634231660256563548000147 206451347490384845322000221)
  ·
    refine ⟨77419255308894316995750083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206451347490384845322000221 77419255308894316995750083)
    ·
      refine ⟨116128882963341475493625125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77419255308894316995750083 116128882963341475493625125)
      ·
        refine ⟨21774165555626526655054711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116128882963341475493625125 21774165555626526655054711)
        ·
          refine ⟨32661248333439789982582067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21774165555626526655054711 32661248333439789982582067)
          ·
            refine ⟨48991872500159684973873101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32661248333439789982582067 48991872500159684973873101)
            ·
              refine ⟨18371952187559881865202413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48991872500159684973873101 18371952187559881865202413)
              ·
                refine ⟨6889482070334955699450905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18371952187559881865202413 6889482070334955699450905)
                ·
                  refine ⟨5167111552751216774588179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6889482070334955699450905 5167111552751216774588179)
                  ·
                    refine ⟨7750667329126825161882269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5167111552751216774588179 7750667329126825161882269)
                    ·
                      refine ⟨2906500248422559435705851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7750667329126825161882269 2906500248422559435705851)
                      ·
                        rfl

theorem cell23_5660389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_5660389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660389 prefixEnd_5660389 := by exact prefixLift 5660389
  have htrace : WordTrace (prefixWord ++ tailWord_5660389) baseStart_5660389 baseEnd_5660389 := by
    simpa [prefixWord, tailWord_5660389, baseEnd_5660389] using wordTrace_append hprefix tailTrace_5660389
  have hstable : (prefixWord ++ tailWord_5660389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660389).length < 2 ^ (prefixWord ++ tailWord_5660389).sum := by decide
  have hdescent : baseEnd_5660389 < baseStart_5660389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660415 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 5]
def baseStart_5660415 : Nat := 118140960795 + 5660415 * 2 ^ 59
def prefixEnd_5660415 : Nat := 4983230072969 + 3 ^ 40 * 5660415 * 2
def baseEnd_5660415 : Nat := 2906513598919576333980731

theorem tailTrace_5660415 : CollatzResearch.WordTrace tailWord_5660415 prefixEnd_5660415 2906513598919576333980731 := by
  unfold tailWord_5660415
  simp only [CollatzResearch.WordTrace]
  refine ⟨206452295788290651762446699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137634863858860434508297799 206452295788290651762446699)
  ·
    refine ⟨309678443682435977643670049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206452295788290651762446699 309678443682435977643670049)
    ·
      refine ⟨232258832761826983232752537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309678443682435977643670049 232258832761826983232752537)
      ·
        refine ⟨174194124571370237424564403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232258832761826983232752537 174194124571370237424564403)
        ·
          refine ⟨261291186857055356136846605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174194124571370237424564403 261291186857055356136846605)
          ·
            refine ⟨97984195071395758551317477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261291186857055356136846605 97984195071395758551317477)
            ·
              refine ⟨18372036575886704728372027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97984195071395758551317477 18372036575886704728372027)
              ·
                refine ⟨27558054863830057092558041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18372036575886704728372027 27558054863830057092558041)
                ·
                  refine ⟨20668541147872542819418531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27558054863830057092558041 20668541147872542819418531)
                  ·
                    refine ⟨31002811721808814229127797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20668541147872542819418531 31002811721808814229127797)
                    ·
                      refine ⟨2906513598919576333980731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31002811721808814229127797 2906513598919576333980731)
                      ·
                        rfl

theorem cell23_5660415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_5660415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660415 prefixEnd_5660415 := by exact prefixLift 5660415
  have htrace : WordTrace (prefixWord ++ tailWord_5660415) baseStart_5660415 baseEnd_5660415 := by
    simpa [prefixWord, tailWord_5660415, baseEnd_5660415] using wordTrace_append hprefix tailTrace_5660415
  have hstable : (prefixWord ++ tailWord_5660415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660415).length < 2 ^ (prefixWord ++ tailWord_5660415).sum := by decide
  have hdescent : baseEnd_5660415 < baseStart_5660415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660425 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 2, 2, 4]
def baseStart_5660425 : Nat := 118140960795 + 5660425 * 2 ^ 59
def prefixEnd_5660425 : Nat := 4983230072969 + 3 ^ 40 * 5660425 * 2
def baseEnd_5660425 : Nat := 2906518733726121294855685

theorem tailTrace_5660425 : CollatzResearch.WordTrace tailWord_5660425 prefixEnd_5660425 2906518733726121294855685 := by
  unfold tailWord_5660425
  simp only [CollatzResearch.WordTrace]
  refine ⟨206452660518254423470310729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137635107012169615646873819 206452660518254423470310729)
  ·
    refine ⟨154839495388690817602733047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206452660518254423470310729 154839495388690817602733047)
    ·
      refine ⟨232259243083036226404099571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154839495388690817602733047 232259243083036226404099571)
      ·
        refine ⟨348388864624554339606149357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232259243083036226404099571 348388864624554339606149357)
        ·
          refine ⟨130645824234207877352306009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 348388864624554339606149357 130645824234207877352306009)
          ·
            refine ⟨97984368175655908014229507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130645824234207877352306009 97984368175655908014229507)
            ·
              refine ⟨146976552263483862021344261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97984368175655908014229507 146976552263483862021344261)
              ·
                refine ⟨27558103549403224129002049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146976552263483862021344261 27558103549403224129002049)
                ·
                  refine ⟨20668577662052418096751537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27558103549403224129002049 20668577662052418096751537)
                  ·
                    refine ⟨15501433246539313572563653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20668577662052418096751537 15501433246539313572563653)
                    ·
                      refine ⟨2906518733726121294855685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15501433246539313572563653 2906518733726121294855685)
                      ·
                        rfl

theorem cell23_5660425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 2, 4].length) (baseStart_5660425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660425 prefixEnd_5660425 := by exact prefixLift 5660425
  have htrace : WordTrace (prefixWord ++ tailWord_5660425) baseStart_5660425 baseEnd_5660425 := by
    simpa [prefixWord, tailWord_5660425, baseEnd_5660425] using wordTrace_append hprefix tailTrace_5660425
  have hstable : (prefixWord ++ tailWord_5660425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660425).length < 2 ^ (prefixWord ++ tailWord_5660425).sum := by decide
  have hdescent : baseEnd_5660425 < baseStart_5660425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660442 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4]
def baseStart_5660442 : Nat := 118140960795 + 5660442 * 2 ^ 59
def prefixEnd_5660442 : Nat := 4983230072969 + 3 ^ 40 * 5660442 * 2
def baseEnd_5660442 : Nat := 2906527462897247728343107

theorem tailTrace_5660442 : CollatzResearch.WordTrace tailWord_5660442 prefixEnd_5660442 2906527462897247728343107 := by
  unfold tailWord_5660442
  simp only [CollatzResearch.WordTrace]
  refine ⟨51613320139798208843419895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137635520372795223582453053 51613320139798208843419895)
  ·
    refine ⟨77419980209697313265129843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51613320139798208843419895 77419980209697313265129843)
    ·
      refine ⟨116129970314545969897694765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77419980209697313265129843 116129970314545969897694765)
      ·
        refine ⟨43548738867954738711635537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116129970314545969897694765 43548738867954738711635537)
        ·
          refine ⟨32661554150966054033726653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43548738867954738711635537 32661554150966054033726653)
          ·
            refine ⟨12248082806612270262647495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32661554150966054033726653 12248082806612270262647495)
            ·
              refine ⟨18372124209918405393971243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12248082806612270262647495 18372124209918405393971243)
              ·
                refine ⟨27558186314877608090956865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18372124209918405393971243 27558186314877608090956865)
                ·
                  refine ⟨20668639736158206068217649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27558186314877608090956865 20668639736158206068217649)
                  ·
                    refine ⟨15501479802118654551163237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20668639736158206068217649 15501479802118654551163237)
                    ·
                      refine ⟨2906527462897247728343107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15501479802118654551163237 2906527462897247728343107)
                      ·
                        rfl

theorem cell23_5660442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_5660442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660442 prefixEnd_5660442 := by exact prefixLift 5660442
  have htrace : WordTrace (prefixWord ++ tailWord_5660442) baseStart_5660442 baseEnd_5660442 := by
    simpa [prefixWord, tailWord_5660442, baseEnd_5660442] using wordTrace_append hprefix tailTrace_5660442
  have hstable : (prefixWord ++ tailWord_5660442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660442).length < 2 ^ (prefixWord ++ tailWord_5660442).sum := by decide
  have hdescent : baseEnd_5660442 < baseStart_5660442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660452 : List Nat := [2, 3, 1, 3, 2, 2, 1, 2, 7]
def baseStart_5660452 : Nat := 118140960795 + 5660452 * 2 ^ 59
def prefixEnd_5660452 : Nat := 4983230072969 + 3 ^ 40 * 5660452 * 2
def baseEnd_5660452 : Nat := 322948066411532521024229

theorem tailTrace_5660452 : CollatzResearch.WordTrace tailWord_5660452 prefixEnd_5660452 322948066411532521024229 := by
  unfold tailWord_5660452
  simp only [CollatzResearch.WordTrace]
  refine ⟨103226822644578303540771805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137635763526104404721029073 103226822644578303540771805)
  ·
    refine ⟨38710058491716863827789427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103226822644578303540771805 38710058491716863827789427)
    ·
      refine ⟨58065087737575295741684141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38710058491716863827789427 58065087737575295741684141)
      ·
        refine ⟨21774407901590735903131553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58065087737575295741684141 21774407901590735903131553)
        ·
          refine ⟨16330805926193051927348665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21774407901590735903131553 16330805926193051927348665)
          ·
            refine ⟨12248104444644788945511499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16330805926193051927348665 12248104444644788945511499)
            ·
              refine ⟨18372156666967183418267249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12248104444644788945511499 18372156666967183418267249)
              ·
                refine ⟨13779117500225387563700437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18372156666967183418267249 13779117500225387563700437)
                ·
                  refine ⟨322948066411532521024229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13779117500225387563700437 322948066411532521024229)
                  ·
                    rfl

theorem cell23_5660452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_5660452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660452 prefixEnd_5660452 := by exact prefixLift 5660452
  have htrace : WordTrace (prefixWord ++ tailWord_5660452) baseStart_5660452 baseEnd_5660452 := by
    simpa [prefixWord, tailWord_5660452, baseEnd_5660452] using wordTrace_append hprefix tailTrace_5660452
  have hstable : (prefixWord ++ tailWord_5660452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660452).length < 2 ^ (prefixWord ++ tailWord_5660452).sum := by decide
  have hdescent : baseEnd_5660452 < baseStart_5660452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660486 : List Nat := [6, 1, 1, 2, 1, 2, 2, 1, 7]
def baseStart_5660486 : Nat := 118140960795 + 5660486 * 2 ^ 59
def prefixEnd_5660486 : Nat := 4983230072969 + 3 ^ 40 * 5660486 * 2
def baseEnd_5660486 : Nat := 322950006227338395132545

theorem tailTrace_5660486 : CollatzResearch.WordTrace tailWord_5660486 prefixEnd_5660486 322950006227338395132545 := by
  unfold tailWord_5660486
  simp only [CollatzResearch.WordTrace]
  refine ⟨6451715167844794715258791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 137636590247355620592187541 6451715167844794715258791)
  ·
    refine ⟨9677572751767192072888187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6451715167844794715258791 9677572751767192072888187)
    ·
      refine ⟨14516359127650788109332281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9677572751767192072888187 14516359127650788109332281)
      ·
        refine ⟨10887269345738091081999211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14516359127650788109332281 10887269345738091081999211)
        ·
          refine ⟨16330904018607136622998817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10887269345738091081999211 16330904018607136622998817)
          ·
            refine ⟨12248178013955352467249113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16330904018607136622998817 12248178013955352467249113)
            ·
              refine ⟨9186133510466514350436835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12248178013955352467249113 9186133510466514350436835)
              ·
                refine ⟨13779200265699771525655253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9186133510466514350436835 13779200265699771525655253)
                ·
                  refine ⟨322950006227338395132545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13779200265699771525655253 322950006227338395132545)
                  ·
                    rfl

theorem cell23_5660486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_5660486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660486 prefixEnd_5660486 := by exact prefixLift 5660486
  have htrace : WordTrace (prefixWord ++ tailWord_5660486) baseStart_5660486 baseEnd_5660486 := by
    simpa [prefixWord, tailWord_5660486, baseEnd_5660486] using wordTrace_append hprefix tailTrace_5660486
  have hstable : (prefixWord ++ tailWord_5660486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660486).length < 2 ^ (prefixWord ++ tailWord_5660486).sum := by decide
  have hdescent : baseEnd_5660486 < baseStart_5660486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660555 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 2, 9]
def baseStart_5660555 : Nat := 118140960795 + 5660555 * 2 ^ 59
def prefixEnd_5660555 : Nat := 4983230072969 + 3 ^ 40 * 5660555 * 2
def baseEnd_5660555 : Nat := 968861828737068595410029

theorem tailTrace_5660555 : CollatzResearch.WordTrace tailWord_5660555 prefixEnd_5660555 968861828737068595410029 := by
  unfold tailWord_5660555
  simp only [CollatzResearch.WordTrace]
  refine ⟨206457402007783455672543119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137638268005188970448362079 206457402007783455672543119)
  ·
    refine ⟨309686103011675183508814679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206457402007783455672543119 309686103011675183508814679)
    ·
      refine ⟨464529154517512775263222019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309686103011675183508814679 464529154517512775263222019)
      ·
        refine ⟨696793731776269162894833029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464529154517512775263222019 696793731776269162894833029)
        ·
          refine ⟨130648824708050468042781193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 696793731776269162894833029 130648824708050468042781193)
          ·
            refine ⟨97986618531037851032085895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130648824708050468042781193 97986618531037851032085895)
            ·
              refine ⟨146979927796556776548128843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97986618531037851032085895 146979927796556776548128843)
              ·
                refine ⟨220469891694835164822193265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146979927796556776548128843 220469891694835164822193265)
                ·
                  refine ⟨165352418771126373616644949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220469891694835164822193265 165352418771126373616644949)
                  ·
                    refine ⟨968861828737068595410029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 165352418771126373616644949 968861828737068595410029)
                    ·
                      rfl

theorem cell23_5660555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 9].length) (baseStart_5660555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660555 prefixEnd_5660555 := by exact prefixLift 5660555
  have htrace : WordTrace (prefixWord ++ tailWord_5660555) baseStart_5660555 baseEnd_5660555 := by
    simpa [prefixWord, tailWord_5660555, baseEnd_5660555] using wordTrace_append hprefix tailTrace_5660555
  have hstable : (prefixWord ++ tailWord_5660555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660555).length < 2 ^ (prefixWord ++ tailWord_5660555).sum := by decide
  have hdescent : baseEnd_5660555 < baseStart_5660555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660569 : List Nat := [1, 2, 1, 2, 1, 3, 2, 4, 3, 1, 3]
def baseStart_5660569 : Nat := 118140960795 + 5660569 * 2 ^ 59
def prefixEnd_5660569 : Nat := 4983230072969 + 3 ^ 40 * 5660569 * 2
def baseEnd_5660569 : Nat := 2906592674940368731455023

theorem tailTrace_5660569 : CollatzResearch.WordTrace tailWord_5660569 prefixEnd_5660569 2906592674940368731455023 := by
  unfold tailWord_5660569
  simp only [CollatzResearch.WordTrace]
  refine ⟨206457912629732736063552761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137638608419821824042368507 206457912629732736063552761)
  ·
    refine ⟨154843434472299552047664571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206457912629732736063552761 154843434472299552047664571)
    ·
      refine ⟨232265151708449328071496857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154843434472299552047664571 232265151708449328071496857)
      ·
        refine ⟨174198863781336996053622643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232265151708449328071496857 174198863781336996053622643)
        ·
          refine ⟨261298295672005494080433965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174198863781336996053622643 261298295672005494080433965)
          ·
            refine ⟨97986860877002060280162737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261298295672005494080433965 97986860877002060280162737)
            ·
              refine ⟨73490145657751545210122053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97986860877002060280162737 73490145657751545210122053)
              ·
                refine ⟨13779402310828414726897885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73490145657751545210122053 13779402310828414726897885)
                ·
                  refine ⟨5167275866560655522586707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13779402310828414726897885 5167275866560655522586707)
                  ·
                    refine ⟨7750913799840983283880061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5167275866560655522586707 7750913799840983283880061)
                    ·
                      refine ⟨2906592674940368731455023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7750913799840983283880061 2906592674940368731455023)
                      ·
                        rfl

theorem cell23_5660569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 1, 3].length) (baseStart_5660569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660569 prefixEnd_5660569 := by exact prefixLift 5660569
  have htrace : WordTrace (prefixWord ++ tailWord_5660569) baseStart_5660569 baseEnd_5660569 := by
    simpa [prefixWord, tailWord_5660569, baseEnd_5660569] using wordTrace_append hprefix tailTrace_5660569
  have hstable : (prefixWord ++ tailWord_5660569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660569).length < 2 ^ (prefixWord ++ tailWord_5660569).sum := by decide
  have hdescent : baseEnd_5660569 < baseStart_5660569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660619 : List Nat := [1, 1, 1, 1, 3, 4, 1, 5, 2, 4]
def baseStart_5660619 : Nat := 118140960795 + 5660619 * 2 ^ 59
def prefixEnd_5660619 : Nat := 4983230072969 + 3 ^ 40 * 5660619 * 2
def baseEnd_5660619 : Nat := 968872782991031178609931

theorem tailTrace_5660619 : CollatzResearch.WordTrace tailWord_5660619 prefixEnd_5660619 968872782991031178609931 := by
  unfold tailWord_5660619
  simp only [CollatzResearch.WordTrace]
  refine ⟨206459736279551594602872911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137639824186367729735248607 206459736279551594602872911)
  ·
    refine ⟨309689604419327391904309367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206459736279551594602872911 309689604419327391904309367)
    ·
      refine ⟨464534406628991087856464051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309689604419327391904309367 464534406628991087856464051)
      ·
        refine ⟨696801609943486631784696077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464534406628991087856464051 696801609943486631784696077)
        ·
          refine ⟨261300603728807486919261029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 696801609943486631784696077 261300603728807486919261029)
          ·
            refine ⟨48993863199151403797361443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 261300603728807486919261029 48993863199151403797361443)
            ·
              refine ⟨73490794798727105696042165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48993863199151403797361443 73490794798727105696042165)
              ·
                refine ⟨6889762012380666159003953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73490794798727105696042165 6889762012380666159003953)
                ·
                  refine ⟨5167321509285499619252965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6889762012380666159003953 5167321509285499619252965)
                  ·
                    refine ⟨968872782991031178609931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5167321509285499619252965 968872782991031178609931)
                    ·
                      rfl

theorem cell23_5660619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 4].length) (baseStart_5660619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660619 prefixEnd_5660619 := by exact prefixLift 5660619
  have htrace : WordTrace (prefixWord ++ tailWord_5660619) baseStart_5660619 baseEnd_5660619 := by
    simpa [prefixWord, tailWord_5660619, baseEnd_5660619] using wordTrace_append hprefix tailTrace_5660619
  have hstable : (prefixWord ++ tailWord_5660619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660619).length < 2 ^ (prefixWord ++ tailWord_5660619).sum := by decide
  have hdescent : baseEnd_5660619 < baseStart_5660619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660639 : List Nat := [1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 4]
def baseStart_5660639 : Nat := 118140960795 + 5660639 * 2 ^ 59
def prefixEnd_5660639 : Nat := 4983230072969 + 3 ^ 40 * 5660639 * 2
def baseEnd_5660639 : Nat := 2906628618586183457579701

theorem tailTrace_5660639 : CollatzResearch.WordTrace tailWord_5660639 prefixEnd_5660639 2906628618586183457579701 := by
  unfold tailWord_5660639
  simp only [CollatzResearch.WordTrace]
  refine ⟨206460465739479138018600971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137640310492986092012400647 206460465739479138018600971)
  ·
    refine ⟨309690698609218707027901457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206460465739479138018600971 309690698609218707027901457)
    ·
      refine ⟨232268023956914030270926093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309690698609218707027901457 232268023956914030270926093)
      ·
        refine ⟨87100508983842761351597285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232268023956914030270926093 87100508983842761351597285)
        ·
          refine ⟨16331345434470517753424491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87100508983842761351597285 16331345434470517753424491)
          ·
            refine ⟨24497018151705776630136737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16331345434470517753424491 24497018151705776630136737)
            ·
              refine ⟨18372763613779332472602553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24497018151705776630136737 18372763613779332472602553)
              ·
                refine ⟨13779572710334499354451915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18372763613779332472602553 13779572710334499354451915)
                ·
                  refine ⟨20669359065501749031677873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13779572710334499354451915 20669359065501749031677873)
                  ·
                    refine ⟨15502019299126311773758405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20669359065501749031677873 15502019299126311773758405)
                    ·
                      refine ⟨2906628618586183457579701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15502019299126311773758405 2906628618586183457579701)
                      ·
                        rfl

theorem cell23_5660639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_5660639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660639 prefixEnd_5660639 := by exact prefixLift 5660639
  have htrace : WordTrace (prefixWord ++ tailWord_5660639) baseStart_5660639 baseEnd_5660639 := by
    simpa [prefixWord, tailWord_5660639, baseEnd_5660639] using wordTrace_append hprefix tailTrace_5660639
  have hstable : (prefixWord ++ tailWord_5660639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660639).length < 2 ^ (prefixWord ++ tailWord_5660639).sum := by decide
  have hdescent : baseEnd_5660639 < baseStart_5660639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660643 : List Nat := [1, 1, 1, 6, 1, 4, 2, 1, 1, 1, 4]
def baseStart_5660643 : Nat := 118140960795 + 5660643 * 2 ^ 59
def prefixEnd_5660643 : Nat := 4983230072969 + 3 ^ 40 * 5660643 * 2
def baseEnd_5660643 : Nat := 2906630672508801441929683

theorem tailTrace_5660643 : CollatzResearch.WordTrace tailWord_5660643 prefixEnd_5660643 2906630672508801441929683 := by
  unfold tailWord_5660643
  simp only [CollatzResearch.WordTrace]
  refine ⟨206460611631464646701746583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137640407754309764467831055 206460611631464646701746583)
  ·
    refine ⟨309690917447196970052619875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206460611631464646701746583 309690917447196970052619875)
    ·
      refine ⟨464536376170795455078929813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309690917447196970052619875 464536376170795455078929813)
      ·
        refine ⟨21775142633006036956824835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 464536376170795455078929813 21775142633006036956824835)
        ·
          refine ⟨32662713949509055435237253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21775142633006036956824835 32662713949509055435237253)
          ·
            refine ⟨6124258865532947894106985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32662713949509055435237253 6124258865532947894106985)
            ·
              refine ⟨4593194149149710920580239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6124258865532947894106985 4593194149149710920580239)
              ·
                refine ⟨6889791223724566380870359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4593194149149710920580239 6889791223724566380870359)
                ·
                  refine ⟨10334686835586849571305539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6889791223724566380870359 10334686835586849571305539)
                  ·
                    refine ⟨15502030253380274356958309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10334686835586849571305539 15502030253380274356958309)
                    ·
                      refine ⟨2906630672508801441929683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15502030253380274356958309 2906630672508801441929683)
                      ·
                        rfl

theorem cell23_5660643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_5660643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660643 prefixEnd_5660643 := by exact prefixLift 5660643
  have htrace : WordTrace (prefixWord ++ tailWord_5660643) baseStart_5660643 baseEnd_5660643 := by
    simpa [prefixWord, tailWord_5660643, baseEnd_5660643] using wordTrace_append hprefix tailTrace_5660643
  have hstable : (prefixWord ++ tailWord_5660643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660643).length < 2 ^ (prefixWord ++ tailWord_5660643).sum := by decide
  have hdescent : baseEnd_5660643 < baseStart_5660643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660653 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 4, 4]
def baseStart_5660653 : Nat := 118140960795 + 5660653 * 2 ^ 59
def prefixEnd_5660653 : Nat := 4983230072969 + 3 ^ 40 * 5660653 * 2
def baseEnd_5660653 : Nat := 968878602438448800934879

theorem tailTrace_5660653 : CollatzResearch.WordTrace tailWord_5660653 prefixEnd_5660653 968878602438448800934879 := by
  unfold tailWord_5660653
  simp only [CollatzResearch.WordTrace]
  refine ⟨206460976361428418409610613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137640650907618945606407075 206460976361428418409610613)
  ·
    refine ⟨19355716533883914225900995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 206460976361428418409610613 19355716533883914225900995)
    ·
      refine ⟨29033574800825871338851493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19355716533883914225900995 29033574800825871338851493)
      ·
        refine ⟨5443795275154850876034655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29033574800825871338851493 5443795275154850876034655)
        ·
          refine ⟨8165692912732276314051983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5443795275154850876034655 8165692912732276314051983)
          ·
            refine ⟨12248539369098414471077975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8165692912732276314051983 12248539369098414471077975)
            ·
              refine ⟨18372809053647621706616963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12248539369098414471077975 18372809053647621706616963)
              ·
                refine ⟨27559213580471432559925445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18372809053647621706616963 27559213580471432559925445)
                ·
                  refine ⟨5167352546338393604986021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27559213580471432559925445 5167352546338393604986021)
                  ·
                    refine ⟨968878602438448800934879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5167352546338393604986021 968878602438448800934879)
                    ·
                      rfl

theorem cell23_5660653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_5660653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660653 prefixEnd_5660653 := by exact prefixLift 5660653
  have htrace : WordTrace (prefixWord ++ tailWord_5660653) baseStart_5660653 baseEnd_5660653 := by
    simpa [prefixWord, tailWord_5660653, baseEnd_5660653] using wordTrace_append hprefix tailTrace_5660653
  have hstable : (prefixWord ++ tailWord_5660653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660653).length < 2 ^ (prefixWord ++ tailWord_5660653).sum := by decide
  have hdescent : baseEnd_5660653 < baseStart_5660653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660670 : List Nat := [4, 2, 2, 2, 1, 2, 3, 1, 2, 4]
def baseStart_5660670 : Nat := 118140960795 + 5660670 * 2 ^ 59
def prefixEnd_5660670 : Nat := 4983230072969 + 3 ^ 40 * 5660670 * 2
def baseEnd_5660670 : Nat := 968881512162157612097353

theorem tailTrace_5660670 : CollatzResearch.WordTrace tailWord_5660670 prefixEnd_5660670 968881512162157612097353 := by
  unfold tailWord_5660670
  simp only [CollatzResearch.WordTrace]
  refine ⟨25807699550295853789122433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137641064268244553541986309 25807699550295853789122433)
  ·
    refine ⟨19355774662721890341841825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25807699550295853789122433 19355774662721890341841825)
    ·
      refine ⟨14516830997041417756381369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19355774662721890341841825 14516830997041417756381369)
      ·
        refine ⟨10887623247781063317286027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14516830997041417756381369 10887623247781063317286027)
        ·
          refine ⟨16331434871671594975929041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10887623247781063317286027 16331434871671594975929041)
          ·
            refine ⟨12248576153753696231946781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16331434871671594975929041 12248576153753696231946781)
            ·
              refine ⟨4593216057657636086980043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12248576153753696231946781 4593216057657636086980043)
              ·
                refine ⟨6889824086486454130470065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4593216057657636086980043 6889824086486454130470065)
                ·
                  refine ⟨5167368064864840597852549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6889824086486454130470065 5167368064864840597852549)
                  ·
                    refine ⟨968881512162157612097353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5167368064864840597852549 968881512162157612097353)
                    ·
                      rfl

theorem cell23_5660670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_5660670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660670 prefixEnd_5660670 := by exact prefixLift 5660670
  have htrace : WordTrace (prefixWord ++ tailWord_5660670) baseStart_5660670 baseEnd_5660670 := by
    simpa [prefixWord, tailWord_5660670, baseEnd_5660670] using wordTrace_append hprefix tailTrace_5660670
  have hstable : (prefixWord ++ tailWord_5660670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660670).length < 2 ^ (prefixWord ++ tailWord_5660670).sum := by decide
  have hdescent : baseEnd_5660670 < baseStart_5660670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660756 : List Nat := [2, 4, 1, 1, 1, 1, 1, 7, 5]
def baseStart_5660756 : Nat := 118140960795 + 5660756 * 2 ^ 59
def prefixEnd_5660756 : Nat := 4983230072969 + 3 ^ 40 * 5660756 * 2
def baseEnd_5660756 : Nat := 322965410646973277757407

theorem tailTrace_5660756 : CollatzResearch.WordTrace tailWord_5660756 prefixEnd_5660756 322965410646973277757407 := by
  unfold tailWord_5660756
  simp only [CollatzResearch.WordTrace]
  refine ⟨103232366540027633500305061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137643155386703511333740081 103232366540027633500305061)
  ·
    refine ⟨19356068726255181281307199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103232366540027633500305061 19356068726255181281307199)
    ·
      refine ⟨29034103089382771921960799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19356068726255181281307199 29034103089382771921960799)
      ·
        refine ⟨43551154634074157882941199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29034103089382771921960799 43551154634074157882941199)
        ·
          refine ⟨65326731951111236824411799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43551154634074157882941199 65326731951111236824411799)
          ·
            refine ⟨97990097926666855236617699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65326731951111236824411799 97990097926666855236617699)
            ·
              refine ⟨146985146890000282854926549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97990097926666855236617699 146985146890000282854926549)
              ·
                refine ⟨3444964380234381629412341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 146985146890000282854926549 3444964380234381629412341)
                ·
                  refine ⟨322965410646973277757407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3444964380234381629412341 322965410646973277757407)
                  ·
                    rfl

theorem cell23_5660756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_5660756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660756 prefixEnd_5660756 := by exact prefixLift 5660756
  have htrace : WordTrace (prefixWord ++ tailWord_5660756) baseStart_5660756 baseEnd_5660756 := by
    simpa [prefixWord, tailWord_5660756, baseEnd_5660756] using wordTrace_append hprefix tailTrace_5660756
  have hstable : (prefixWord ++ tailWord_5660756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660756).length < 2 ^ (prefixWord ++ tailWord_5660756).sum := by decide
  have hdescent : baseEnd_5660756 < baseStart_5660756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660773 : List Nat := [1, 3, 1, 3, 2, 2, 4, 2, 5]
def baseStart_5660773 : Nat := 118140960795 + 5660773 * 2 ^ 59
def prefixEnd_5660773 : Nat := 4983230072969 + 3 ^ 40 * 5660773 * 2
def baseEnd_5660773 : Nat := 322966380554876214811565

theorem tailTrace_5660773 : CollatzResearch.WordTrace tailWord_5660773 prefixEnd_5660773 322966380554876214811565 := by
  unfold tailWord_5660773
  simp only [CollatzResearch.WordTrace]
  refine ⟨206465353120993678903978973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137643568747329119269319315 206465353120993678903978973)
  ·
    refine ⟨77424507420372629588992115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206465353120993678903978973 77424507420372629588992115)
    ·
      refine ⟨116136761130558944383488173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77424507420372629588992115 116136761130558944383488173)
      ·
        refine ⟨43551285423959604143808065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116136761130558944383488173 43551285423959604143808065)
        ·
          refine ⟨32663464067969703107856049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43551285423959604143808065 32663464067969703107856049)
          ·
            refine ⟨24497598050977277330892037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32663464067969703107856049 24497598050977277330892037)
            ·
              refine ⟨4593299634558239499542257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24497598050977277330892037 4593299634558239499542257)
              ·
                refine ⟨3444974725918679624656693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4593299634558239499542257 3444974725918679624656693)
                ·
                  refine ⟨322966380554876214811565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3444974725918679624656693 322966380554876214811565)
                  ·
                    rfl

theorem cell23_5660773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 5].length) (baseStart_5660773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660773 prefixEnd_5660773 := by exact prefixLift 5660773
  have htrace : WordTrace (prefixWord ++ tailWord_5660773) baseStart_5660773 baseEnd_5660773 := by
    simpa [prefixWord, tailWord_5660773, baseEnd_5660773] using wordTrace_append hprefix tailTrace_5660773
  have hstable : (prefixWord ++ tailWord_5660773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660773).length < 2 ^ (prefixWord ++ tailWord_5660773).sum := by decide
  have hdescent : baseEnd_5660773 < baseStart_5660773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660833 : List Nat := [1, 2, 3, 3, 1, 3, 2, 1, 3, 4]
def baseStart_5660833 : Nat := 118140960795 + 5660833 * 2 ^ 59
def prefixEnd_5660833 : Nat := 4983230072969 + 3 ^ 40 * 5660833 * 2
def baseEnd_5660833 : Nat := 968909411277718566184603

theorem tailTrace_5660833 : CollatzResearch.WordTrace tailWord_5660833 prefixEnd_5660833 968909411277718566184603 := by
  unfold tailWord_5660833
  simp only [CollatzResearch.WordTrace]
  refine ⟨206467541500776309151163153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137645027667184206100775435 206467541500776309151163153)
  ·
    refine ⟨154850656125582231863372365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206467541500776309151163153 154850656125582231863372365)
    ·
      refine ⟨58068996047093336948764637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154850656125582231863372365 58068996047093336948764637)
      ·
        refine ⟨21775873517660001355786739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58068996047093336948764637 21775873517660001355786739)
        ·
          refine ⟨32663810276490002033680109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21775873517660001355786739 32663810276490002033680109)
          ·
            refine ⟨12248928853683750762630041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32663810276490002033680109 12248928853683750762630041)
            ·
              refine ⟨9186696640262813071972531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12248928853683750762630041 9186696640262813071972531)
              ·
                refine ⟨13780044960394219607958797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9186696640262813071972531 13780044960394219607958797)
                ·
                  refine ⟨5167516860147832352984549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13780044960394219607958797 5167516860147832352984549)
                  ·
                    refine ⟨968909411277718566184603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5167516860147832352984549 968909411277718566184603)
                    ·
                      rfl

theorem cell23_5660833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_5660833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660833 prefixEnd_5660833 := by exact prefixLift 5660833
  have htrace : WordTrace (prefixWord ++ tailWord_5660833) baseStart_5660833 baseEnd_5660833 := by
    simpa [prefixWord, tailWord_5660833, baseEnd_5660833] using wordTrace_append hprefix tailTrace_5660833
  have hstable : (prefixWord ++ tailWord_5660833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660833).length < 2 ^ (prefixWord ++ tailWord_5660833).sum := by decide
  have hdescent : baseEnd_5660833 < baseStart_5660833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660890 : List Nat := [3, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3]
def baseStart_5660890 : Nat := 118140960795 + 5660890 * 2 ^ 59
def prefixEnd_5660890 : Nat := 4983230072969 + 3 ^ 40 * 5660890 * 2
def baseEnd_5660890 : Nat := 2906757502230461975541047

theorem tailTrace_5660890 : CollatzResearch.WordTrace tailWord_5660890 prefixEnd_5660890 2906757502230461975541047 := by
  unfold tailWord_5660890
  simp only [CollatzResearch.WordTrace]
  refine ⟨51617405115392451971497031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137646413641046538590658749 51617405115392451971497031)
  ·
    refine ⟨77426107673088677957245547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51617405115392451971497031 77426107673088677957245547)
    ·
      refine ⟨116139161509633016935868321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77426107673088677957245547 116139161509633016935868321)
      ·
        refine ⟨87104371132224762701901241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116139161509633016935868321 87104371132224762701901241)
        ·
          refine ⟨65328278349168572026425931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87104371132224762701901241 65328278349168572026425931)
          ·
            refine ⟨97992417523752858039638897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65328278349168572026425931 97992417523752858039638897)
            ·
              refine ⟨73494313142814643529729173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97992417523752858039638897 73494313142814643529729173)
              ·
                refine ⟨3445045928569436415456055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73494313142814643529729173 3445045928569436415456055)
                ·
                  refine ⟨5167568892854154623184083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3445045928569436415456055 5167568892854154623184083)
                  ·
                    refine ⟨7751353339281231934776125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5167568892854154623184083 7751353339281231934776125)
                    ·
                      refine ⟨2906757502230461975541047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7751353339281231934776125 2906757502230461975541047)
                      ·
                        rfl

theorem cell23_5660890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3].length) (baseStart_5660890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660890 prefixEnd_5660890 := by exact prefixLift 5660890
  have htrace : WordTrace (prefixWord ++ tailWord_5660890) baseStart_5660890 baseEnd_5660890 := by
    simpa [prefixWord, tailWord_5660890, baseEnd_5660890] using wordTrace_append hprefix tailTrace_5660890
  have hstable : (prefixWord ++ tailWord_5660890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660890).length < 2 ^ (prefixWord ++ tailWord_5660890).sum := by decide
  have hdescent : baseEnd_5660890 < baseStart_5660890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660896 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 4]
def baseStart_5660896 : Nat := 118140960795 + 5660896 * 2 ^ 59
def prefixEnd_5660896 : Nat := 4983230072969 + 3 ^ 40 * 5660896 * 2
def baseEnd_5660896 : Nat := 2906760583114388952066019

theorem tailTrace_5660896 : CollatzResearch.WordTrace tailWord_5660896 prefixEnd_5660896 2906760583114388952066019 := by
  unfold tailWord_5660896
  simp only [CollatzResearch.WordTrace]
  refine ⟨103234919649774035455353271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137646559533032047273804361 103234919649774035455353271)
  ·
    refine ⟨154852379474661053183029907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103234919649774035455353271 154852379474661053183029907)
    ·
      refine ⟨232278569211991579774544861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154852379474661053183029907 232278569211991579774544861)
      ·
        refine ⟨87104463454496842415454323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232278569211991579774544861 87104463454496842415454323)
        ·
          refine ⟨130656695181745263623181485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87104463454496842415454323 130656695181745263623181485)
          ·
            refine ⟨48996260693154473858693057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130656695181745263623181485 48996260693154473858693057)
            ·
              refine ⟨36747195519865855394019793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48996260693154473858693057 36747195519865855394019793)
              ·
                refine ⟨27560396639899391545514845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36747195519865855394019793 27560396639899391545514845)
                ·
                  refine ⟨10335148739962271829568067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27560396639899391545514845 10335148739962271829568067)
                  ·
                    refine ⟨15502723109943407744352101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10335148739962271829568067 15502723109943407744352101)
                    ·
                      refine ⟨2906760583114388952066019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15502723109943407744352101 2906760583114388952066019)
                      ·
                        rfl

theorem cell23_5660896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_5660896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660896 prefixEnd_5660896 := by exact prefixLift 5660896
  have htrace : WordTrace (prefixWord ++ tailWord_5660896) baseStart_5660896 baseEnd_5660896 := by
    simpa [prefixWord, tailWord_5660896, baseEnd_5660896] using wordTrace_append hprefix tailTrace_5660896
  have hstable : (prefixWord ++ tailWord_5660896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660896).length < 2 ^ (prefixWord ++ tailWord_5660896).sum := by decide
  have hdescent : baseEnd_5660896 < baseStart_5660896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660906 : List Nat := [3, 1, 3, 1, 1, 2, 2, 3, 1, 6]
def baseStart_5660906 : Nat := 118140960795 + 5660906 * 2 ^ 59
def prefixEnd_5660906 : Nat := 4983230072969 + 3 ^ 40 * 5660906 * 2
def baseEnd_5660906 : Nat := 968921905973644637646991

theorem tailTrace_5660906 : CollatzResearch.WordTrace tailWord_5660906 prefixEnd_5660906 968921905973644637646991 := by
  unfold tailWord_5660906
  simp only [CollatzResearch.WordTrace]
  refine ⟨51617551007377960654642643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137646802686341228412380381 51617551007377960654642643)
  ·
    refine ⟨77426326511066940981963965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51617551007377960654642643 77426326511066940981963965)
    ·
      refine ⟨29034872441650102868236487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77426326511066940981963965 29034872441650102868236487)
      ·
        refine ⟨43552308662475154302354731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29034872441650102868236487 43552308662475154302354731)
        ·
          refine ⟨65328462993712731453532097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43552308662475154302354731 65328462993712731453532097)
          ·
            refine ⟨48996347245284548590149073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65328462993712731453532097 48996347245284548590149073)
            ·
              refine ⟨36747260433963411442611805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48996347245284548590149073 36747260433963411442611805)
              ·
                refine ⟨13780222662736279290979427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36747260433963411442611805 13780222662736279290979427)
                ·
                  refine ⟨20670333994104418936469141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13780222662736279290979427 20670333994104418936469141)
                  ·
                    refine ⟨968921905973644637646991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20670333994104418936469141 968921905973644637646991)
                    ·
                      rfl

theorem cell23_5660906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_5660906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660906 prefixEnd_5660906 := by exact prefixLift 5660906
  have htrace : WordTrace (prefixWord ++ tailWord_5660906) baseStart_5660906 baseEnd_5660906 := by
    simpa [prefixWord, tailWord_5660906, baseEnd_5660906] using wordTrace_append hprefix tailTrace_5660906
  have hstable : (prefixWord ++ tailWord_5660906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660906).length < 2 ^ (prefixWord ++ tailWord_5660906).sum := by decide
  have hdescent : baseEnd_5660906 < baseStart_5660906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660913 : List Nat := [1, 2, 2, 2, 2, 1, 5, 2, 1, 1, 4]
def baseStart_5660913 : Nat := 118140960795 + 5660913 * 2 ^ 59
def prefixEnd_5660913 : Nat := 4983230072969 + 3 ^ 40 * 5660913 * 2
def baseEnd_5660913 : Nat := 2906769312285515385553441

theorem tailTrace_5660913 : CollatzResearch.WordTrace tailWord_5660913 prefixEnd_5660913 2906769312285515385553441 := by
  unfold tailWord_5660913
  simp only [CollatzResearch.WordTrace]
  refine ⟨206470459340486482814075393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137646972893657655209383595 206470459340486482814075393)
  ·
    refine ⟨154852844505364862110556545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206470459340486482814075393 154852844505364862110556545)
    ·
      refine ⟨116139633379023646582917409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154852844505364862110556545 116139633379023646582917409)
      ·
        refine ⟨87104725034267734937188057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116139633379023646582917409 87104725034267734937188057)
        ·
          refine ⟨65328543775700801202891043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87104725034267734937188057 65328543775700801202891043)
          ·
            refine ⟨97992815663551201804336565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65328543775700801202891043 97992815663551201804336565)
            ·
              refine ⟨9186826468457925169156553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97992815663551201804336565 9186826468457925169156553)
              ·
                refine ⟨6890119851343443876867415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9186826468457925169156553 6890119851343443876867415)
                ·
                  refine ⟨10335179777015165815301123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6890119851343443876867415 10335179777015165815301123)
                  ·
                    refine ⟨15502769665522748722951685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10335179777015165815301123 15502769665522748722951685)
                    ·
                      refine ⟨2906769312285515385553441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15502769665522748722951685 2906769312285515385553441)
                      ·
                        rfl

theorem cell23_5660913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_5660913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660913 prefixEnd_5660913 := by exact prefixLift 5660913
  have htrace : WordTrace (prefixWord ++ tailWord_5660913) baseStart_5660913 baseEnd_5660913 := by
    simpa [prefixWord, tailWord_5660913, baseEnd_5660913] using wordTrace_append hprefix tailTrace_5660913
  have hstable : (prefixWord ++ tailWord_5660913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660913).length < 2 ^ (prefixWord ++ tailWord_5660913).sum := by decide
  have hdescent : baseEnd_5660913 < baseStart_5660913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660963 : List Nat := [1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 3]
def baseStart_5660963 : Nat := 118140960795 + 5660963 * 2 ^ 59
def prefixEnd_5660963 : Nat := 4983230072969 + 3 ^ 40 * 5660963 * 2
def baseEnd_5660963 : Nat := 2906794986318240189928211

theorem tailTrace_5660963 : CollatzResearch.WordTrace tailWord_5660963 prefixEnd_5660963 2906794986318240189928211 := by
  unfold tailWord_5660963
  simp only [CollatzResearch.WordTrace]
  refine ⟨206472282990305341353395543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137648188660203560902263695 206472282990305341353395543)
  ·
    refine ⟨309708424485458012030093315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206472282990305341353395543 309708424485458012030093315)
    ·
      refine ⟨464562636728187018045139973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309708424485458012030093315 464562636728187018045139973)
      ·
        refine ⟨87105494386535065883463745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 464562636728187018045139973 87105494386535065883463745)
        ·
          refine ⟨65329120789901299412597809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87105494386535065883463745 65329120789901299412597809)
          ·
            refine ⟨48996840592425974559448357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65329120789901299412597809 48996840592425974559448357)
            ·
              refine ⟨9186907611079870229896567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48996840592425974559448357 9186907611079870229896567)
              ·
                refine ⟨13780361416619805344844851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9186907611079870229896567 13780361416619805344844851)
                ·
                  refine ⟨20670542124929708017267277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13780361416619805344844851 20670542124929708017267277)
                  ·
                    refine ⟨7751453296848640506475229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20670542124929708017267277 7751453296848640506475229)
                    ·
                      refine ⟨2906794986318240189928211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7751453296848640506475229 2906794986318240189928211)
                      ·
                        rfl

theorem cell23_5660963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_5660963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660963 prefixEnd_5660963 := by exact prefixLift 5660963
  have htrace : WordTrace (prefixWord ++ tailWord_5660963) baseStart_5660963 baseEnd_5660963 := by
    simpa [prefixWord, tailWord_5660963, baseEnd_5660963] using wordTrace_append hprefix tailTrace_5660963
  have hstable : (prefixWord ++ tailWord_5660963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660963).length < 2 ^ (prefixWord ++ tailWord_5660963).sum := by decide
  have hdescent : baseEnd_5660963 < baseStart_5660963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660970 : List Nat := [3, 1, 4, 2, 2, 1, 3, 7]
def baseStart_5660970 : Nat := 118140960795 + 5660970 * 2 ^ 59
def prefixEnd_5660970 : Nat := 4983230072969 + 3 ^ 40 * 5660970 * 2
def baseEnd_5660970 : Nat := 107659206691956357871877

theorem tailTrace_5660970 : CollatzResearch.WordTrace tailWord_5660970 prefixEnd_5660970 107659206691956357871877 := by
  unfold tailWord_5660970
  simp only [CollatzResearch.WordTrace]
  refine ⟨51618134575319995387225091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137648358867519987699266909 51618134575319995387225091)
  ·
    refine ⟨77427201862979993080837637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51618134575319995387225091 77427201862979993080837637)
    ·
      refine ⟨14517600349308748702657057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77427201862979993080837637 14517600349308748702657057)
      ·
        refine ⟨10888200261981561526992793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14517600349308748702657057 10888200261981561526992793)
        ·
          refine ⟨8166150196486171145244595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10888200261981561526992793 8166150196486171145244595)
          ·
            refine ⟨12249225294729256717866893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8166150196486171145244595 12249225294729256717866893)
            ·
              refine ⟨4593459485523471269200085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12249225294729256717866893 4593459485523471269200085)
              ·
                refine ⟨107659206691956357871877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4593459485523471269200085 107659206691956357871877)
                ·
                  rfl

theorem cell23_5660970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 7].length) (baseStart_5660970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660970 prefixEnd_5660970 := by exact prefixLift 5660970
  have htrace : WordTrace (prefixWord ++ tailWord_5660970) baseStart_5660970 baseEnd_5660970 := by
    simpa [prefixWord, tailWord_5660970, baseEnd_5660970] using wordTrace_append hprefix tailTrace_5660970
  have hstable : (prefixWord ++ tailWord_5660970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660970).length < 2 ^ (prefixWord ++ tailWord_5660970).sum := by decide
  have hdescent : baseEnd_5660970 < baseStart_5660970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660980 : List Nat := [2, 5, 1, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_5660980 : Nat := 118140960795 + 5660980 * 2 ^ 59
def prefixEnd_5660980 : Nat := 4983230072969 + 3 ^ 40 * 5660980 * 2
def baseEnd_5660980 : Nat := 2906803715489366623415633

theorem tailTrace_5660980 : CollatzResearch.WordTrace tailWord_5660980 prefixEnd_5660980 2906803715489366623415633 := by
  unfold tailWord_5660980
  simp only [CollatzResearch.WordTrace]
  refine ⟨103236451515621876628382197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137648602020829168837842929 103236451515621876628382197)
  ·
    refine ⟨9678417329589550933910831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103236451515621876628382197 9678417329589550933910831)
    ·
      refine ⟨14517625994384326400866247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9678417329589550933910831 14517625994384326400866247)
      ·
        refine ⟨21776438991576489601299371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14517625994384326400866247 21776438991576489601299371)
        ·
          refine ⟨32664658487364734401949057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21776438991576489601299371 32664658487364734401949057)
          ·
            refine ⟨24498493865523550801461793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32664658487364734401949057 24498493865523550801461793)
            ·
              refine ⟨18373870399142663101096345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24498493865523550801461793 18373870399142663101096345)
              ·
                refine ⟨13780402799356997325822259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18373870399142663101096345 13780402799356997325822259)
                ·
                  refine ⟨20670604199035495988733389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13780402799356997325822259 20670604199035495988733389)
                  ·
                    refine ⟨7751476574638310995775021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20670604199035495988733389 7751476574638310995775021)
                    ·
                      refine ⟨2906803715489366623415633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7751476574638310995775021 2906803715489366623415633)
                      ·
                        rfl

theorem cell23_5660980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_5660980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660980 prefixEnd_5660980 := by exact prefixLift 5660980
  have htrace : WordTrace (prefixWord ++ tailWord_5660980) baseStart_5660980 baseEnd_5660980 := by
    simpa [prefixWord, tailWord_5660980, baseEnd_5660980] using wordTrace_append hprefix tailTrace_5660980
  have hstable : (prefixWord ++ tailWord_5660980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660980).length < 2 ^ (prefixWord ++ tailWord_5660980).sum := by decide
  have hdescent : baseEnd_5660980 < baseStart_5660980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661006 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5]
def baseStart_5661006 : Nat := 118140960795 + 5661006 * 2 ^ 59
def prefixEnd_5661006 : Nat := 4983230072969 + 3 ^ 40 * 5661006 * 2
def baseEnd_5661006 : Nat := 2906817065986383521690513

theorem tailTrace_5661006 : CollatzResearch.WordTrace tailWord_5661006 prefixEnd_5661006 2906817065986383521690513 := by
  unfold tailWord_5661006
  simp only [CollatzResearch.WordTrace]
  refine ⟨25809231416143694962151359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137649234219433039798140581 25809231416143694962151359)
  ·
    refine ⟨38713847124215542443227039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25809231416143694962151359 38713847124215542443227039)
    ·
      refine ⟨58070770686323313664840559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38713847124215542443227039 58070770686323313664840559)
      ·
        refine ⟨87106156029484970497260839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58070770686323313664840559 87106156029484970497260839)
        ·
          refine ⟨130659234044227455745891259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87106156029484970497260839 130659234044227455745891259)
          ·
            refine ⟨195988851066341183618836889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130659234044227455745891259 195988851066341183618836889)
            ·
              refine ⟨146991638299755887714127667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195988851066341183618836889 146991638299755887714127667)
              ·
                refine ⟨220487457449633831571191501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146991638299755887714127667 220487457449633831571191501)
                ·
                  refine ⟨82682796543612686839196813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 220487457449633831571191501 82682796543612686839196813)
                  ·
                    refine ⟨31006048703854757564698805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82682796543612686839196813 31006048703854757564698805)
                    ·
                      refine ⟨2906817065986383521690513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31006048703854757564698805 2906817065986383521690513)
                      ·
                        rfl

theorem cell23_5661006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_5661006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661006 prefixEnd_5661006 := by exact prefixLift 5661006
  have htrace : WordTrace (prefixWord ++ tailWord_5661006) baseStart_5661006 baseEnd_5661006 := by
    simpa [prefixWord, tailWord_5661006, baseEnd_5661006] using wordTrace_append hprefix tailTrace_5661006
  have hstable : (prefixWord ++ tailWord_5661006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661006).length < 2 ^ (prefixWord ++ tailWord_5661006).sum := by decide
  have hdescent : baseEnd_5661006 < baseStart_5661006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661016 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 1, 4, 4]
def baseStart_5661016 : Nat := 118140960795 + 5661016 * 2 ^ 59
def prefixEnd_5661016 : Nat := 4983230072969 + 3 ^ 40 * 5661016 * 2
def baseEnd_5661016 : Nat := 2906822200792928482565467

theorem tailTrace_5661016 : CollatzResearch.WordTrace tailWord_5661016 prefixEnd_5661016 2906822200792928482565467 := by
  unfold tailWord_5661016
  simp only [CollatzResearch.WordTrace]
  refine ⟨103237108029556665702537451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137649477372742220936716601 103237108029556665702537451)
  ·
    refine ⟨154855662044334998553806177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103237108029556665702537451 154855662044334998553806177)
    ·
      refine ⟨116141746533251248915354633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154855662044334998553806177 116141746533251248915354633)
      ·
        refine ⟨87106309899938436686515975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116141746533251248915354633 87106309899938436686515975)
        ·
          refine ⟨130659464849907655029773963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87106309899938436686515975 130659464849907655029773963)
          ·
            refine ⟨195989197274861482544660945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130659464849907655029773963 195989197274861482544660945)
            ·
              refine ⟨146991897956146111908495709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195989197274861482544660945 146991897956146111908495709)
              ·
                refine ⟨55121961733554791965685891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146991897956146111908495709 55121961733554791965685891)
                ·
                  refine ⟨82682942600332187948528837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55121961733554791965685891 82682942600332187948528837)
                  ·
                    refine ⟨15503051737562285240349157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82682942600332187948528837 15503051737562285240349157)
                    ·
                      refine ⟨2906822200792928482565467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15503051737562285240349157 2906822200792928482565467)
                      ·
                        rfl

theorem cell23_5661016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_5661016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661016 prefixEnd_5661016 := by exact prefixLift 5661016
  have htrace : WordTrace (prefixWord ++ tailWord_5661016) baseStart_5661016 baseEnd_5661016 := by
    simpa [prefixWord, tailWord_5661016, baseEnd_5661016] using wordTrace_append hprefix tailTrace_5661016
  have hstable : (prefixWord ++ tailWord_5661016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661016).length < 2 ^ (prefixWord ++ tailWord_5661016).sum := by decide
  have hdescent : baseEnd_5661016 < baseStart_5661016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661090 : List Nat := [3, 3, 1, 2, 1, 1, 4, 1, 2, 5]
def baseStart_5661090 : Nat := 118140960795 + 5661090 * 2 ^ 59
def prefixEnd_5661090 : Nat := 4983230072969 + 3 ^ 40 * 5661090 * 2
def baseEnd_5661090 : Nat := 968953399453787064346709

theorem tailTrace_5661090 : CollatzResearch.WordTrace tailWord_5661090 prefixEnd_5661090 968953399453787064346709 := by
  unfold tailWord_5661090
  simp only [CollatzResearch.WordTrace]
  refine ⟨51619228765211310510817181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137651276707230161362179149 51619228765211310510817181)
  ·
    refine ⟨19357210786954241441556443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51619228765211310510817181 19357210786954241441556443)
    ·
      refine ⟨29035816180431362162334665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19357210786954241441556443 29035816180431362162334665)
      ·
        refine ⟨21776862135323521621750999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29035816180431362162334665 21776862135323521621750999)
        ·
          refine ⟨32665293202985282432626499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21776862135323521621750999 32665293202985282432626499)
          ·
            refine ⟨48997939804477923648939749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32665293202985282432626499 48997939804477923648939749)
            ·
              refine ⟨9187113713339610684176203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48997939804477923648939749 9187113713339610684176203)
              ·
                refine ⟨13780670570009416026264305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9187113713339610684176203 13780670570009416026264305)
                ·
                  refine ⟨10335502927507062019698229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13780670570009416026264305 10335502927507062019698229)
                  ·
                    refine ⟨968953399453787064346709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10335502927507062019698229 968953399453787064346709)
                    ·
                      rfl

theorem cell23_5661090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_5661090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661090 prefixEnd_5661090 := by exact prefixLift 5661090
  have htrace : WordTrace (prefixWord ++ tailWord_5661090) baseStart_5661090 baseEnd_5661090 := by
    simpa [prefixWord, tailWord_5661090, baseEnd_5661090] using wordTrace_append hprefix tailTrace_5661090
  have hstable : (prefixWord ++ tailWord_5661090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661090).length < 2 ^ (prefixWord ++ tailWord_5661090).sum := by decide
  have hdescent : baseEnd_5661090 < baseStart_5661090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661193 : List Nat := [1, 2, 1, 1, 3, 1, 2, 5, 1, 6]
def baseStart_5661193 : Nat := 118140960795 + 5661193 * 2 ^ 59
def prefixEnd_5661193 : Nat := 4983230072969 + 3 ^ 40 * 5661193 * 2
def baseEnd_5661193 : Nat := 968971028956258096684051

theorem tailTrace_5661193 : CollatzResearch.WordTrace tailWord_5661193 prefixEnd_5661193 968971028956258096684051 := by
  unfold tailWord_5661193
  simp only [CollatzResearch.WordTrace]
  refine ⟨206480671779472090634268233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137653781186314727089512155 206480671779472090634268233)
  ·
    refine ⟨154860503834604067975701175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206480671779472090634268233 154860503834604067975701175)
    ·
      refine ⟨232290755751906101963551763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154860503834604067975701175 232290755751906101963551763)
      ·
        refine ⟨348436133627859152945327645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232290755751906101963551763 348436133627859152945327645)
        ·
          refine ⟨130663550110447182354497867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 348436133627859152945327645 130663550110447182354497867)
          ·
            refine ⟨195995325165670773531746801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130663550110447182354497867 195995325165670773531746801)
            ·
              refine ⟨146996493874253080148810101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195995325165670773531746801 146996493874253080148810101)
              ·
                refine ⟨13780921300711226263950947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 146996493874253080148810101 13780921300711226263950947)
                ·
                  refine ⟨20671381951066839395926421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13780921300711226263950947 20671381951066839395926421)
                  ·
                    refine ⟨968971028956258096684051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20671381951066839395926421 968971028956258096684051)
                    ·
                      rfl

theorem cell23_5661193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 6].length) (baseStart_5661193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661193 prefixEnd_5661193 := by exact prefixLift 5661193
  have htrace : WordTrace (prefixWord ++ tailWord_5661193) baseStart_5661193 baseEnd_5661193 := by
    simpa [prefixWord, tailWord_5661193, baseEnd_5661193] using wordTrace_append hprefix tailTrace_5661193
  have hstable : (prefixWord ++ tailWord_5661193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661193).length < 2 ^ (prefixWord ++ tailWord_5661193).sum := by decide
  have hdescent : baseEnd_5661193 < baseStart_5661193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661203 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 5]
def baseStart_5661203 : Nat := 118140960795 + 5661203 * 2 ^ 59
def prefixEnd_5661203 : Nat := 4983230072969 + 3 ^ 40 * 5661203 * 2
def baseEnd_5661203 : Nat := 2906918221675319250927107

theorem tailTrace_5661203 : CollatzResearch.WordTrace tailWord_5661203 prefixEnd_5661203 2906918221675319250927107 := by
  unfold tailWord_5661203
  simp only [CollatzResearch.WordTrace]
  refine ⟨206481036509435862342132263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137654024339623908228088175 206481036509435862342132263)
  ·
    refine ⟨309721554764153793513198395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206481036509435862342132263 309721554764153793513198395)
    ·
      refine ⟨464582332146230690269797593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309721554764153793513198395 464582332146230690269797593)
      ·
        refine ⟨348436749109673017702348195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 464582332146230690269797593 348436749109673017702348195)
        ·
          refine ⟨522655123664509526553522293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348436749109673017702348195 522655123664509526553522293)
          ·
            refine ⟨48998917843547768114392715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 522655123664509526553522293 48998917843547768114392715)
            ·
              refine ⟨73498376765321652171589073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48998917843547768114392715 73498376765321652171589073)
              ·
                refine ⟨55123782573991239128691805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73498376765321652171589073 55123782573991239128691805)
                ·
                  refine ⟨20671418465246714673259427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55123782573991239128691805 20671418465246714673259427)
                  ·
                    refine ⟨31007127697870072009889141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20671418465246714673259427 31007127697870072009889141)
                    ·
                      refine ⟨2906918221675319250927107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31007127697870072009889141 2906918221675319250927107)
                      ·
                        rfl

theorem cell23_5661203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 5].length) (baseStart_5661203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661203 prefixEnd_5661203 := by exact prefixLift 5661203
  have htrace : WordTrace (prefixWord ++ tailWord_5661203) baseStart_5661203 baseEnd_5661203 := by
    simpa [prefixWord, tailWord_5661203, baseEnd_5661203] using wordTrace_append hprefix tailTrace_5661203
  have hstable : (prefixWord ++ tailWord_5661203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661203).length < 2 ^ (prefixWord ++ tailWord_5661203).sum := by decide
  have hdescent : baseEnd_5661203 < baseStart_5661203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661204 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_5661204 : Nat := 118140960795 + 5661204 * 2 ^ 59
def prefixEnd_5661204 : Nat := 4983230072969 + 3 ^ 40 * 5661204 * 2
def baseEnd_5661204 : Nat := 2906918735155973747014603

theorem tailTrace_5661204 : CollatzResearch.WordTrace tailWord_5661204 prefixEnd_5661204 2906918735155973747014603 := by
  unfold tailWord_5661204
  simp only [CollatzResearch.WordTrace]
  refine ⟨103240536491216119756459333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137654048654954826341945777 103240536491216119756459333)
  ·
    refine ⟨19357600592103022454336125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103240536491216119756459333 19357600592103022454336125)
    ·
      refine ⟨7259100222038633420376047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19357600592103022454336125 7259100222038633420376047)
      ·
        refine ⟨10888650333057950130564071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7259100222038633420376047 10888650333057950130564071)
        ·
          refine ⟨16332975499586925195846107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10888650333057950130564071 16332975499586925195846107)
          ·
            refine ⟨24499463249380387793769161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16332975499586925195846107 24499463249380387793769161)
            ·
              refine ⟨18374597437035290845326871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24499463249380387793769161 18374597437035290845326871)
              ·
                refine ⟨27561896155552936267990307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18374597437035290845326871 27561896155552936267990307)
                ·
                  refine ⟨41342844233329404401985461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27561896155552936267990307 41342844233329404401985461)
                  ·
                    refine ⟨3875891646874631662686137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41342844233329404401985461 3875891646874631662686137)
                    ·
                      refine ⟨2906918735155973747014603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3875891646874631662686137 2906918735155973747014603)
                      ·
                        rfl

theorem cell23_5661204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_5661204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661204 prefixEnd_5661204 := by exact prefixLift 5661204
  have htrace : WordTrace (prefixWord ++ tailWord_5661204) baseStart_5661204 baseEnd_5661204 := by
    simpa [prefixWord, tailWord_5661204, baseEnd_5661204] using wordTrace_append hprefix tailTrace_5661204
  have hstable : (prefixWord ++ tailWord_5661204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661204).length < 2 ^ (prefixWord ++ tailWord_5661204).sum := by decide
  have hdescent : baseEnd_5661204 < baseStart_5661204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661210 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 4, 4]
def baseStart_5661210 : Nat := 118140960795 + 5661210 * 2 ^ 59
def prefixEnd_5661210 : Nat := 4983230072969 + 3 ^ 40 * 5661210 * 2
def baseEnd_5661210 : Nat := 968973938679966907846525

theorem tailTrace_5661210 : CollatzResearch.WordTrace tailWord_5661210 prefixEnd_5661210 968973938679966907846525 := by
  unfold tailWord_5661210
  simp only [CollatzResearch.WordTrace]
  refine ⟨51620322955102625634409271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137654194546940335025091389 51620322955102625634409271)
  ·
    refine ⟨77430484432653938451613907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51620322955102625634409271 77430484432653938451613907)
    ·
      refine ⟨116145726648980907677420861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77430484432653938451613907 116145726648980907677420861)
      ·
        refine ⟨43554647493367840379032823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116145726648980907677420861 43554647493367840379032823)
        ·
          refine ⟨65331971240051760568549235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43554647493367840379032823 65331971240051760568549235)
          ·
            refine ⟨97997956860077640852823853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65331971240051760568549235 97997956860077640852823853)
            ·
              refine ⟨36749233822529115319808945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97997956860077640852823853 36749233822529115319808945)
              ·
                refine ⟨27561925366896836489856709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36749233822529115319808945 27561925366896836489856709)
                ·
                  refine ⟨5167861006293156841848133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27561925366896836489856709 5167861006293156841848133)
                  ·
                    refine ⟨968973938679966907846525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5167861006293156841848133 968973938679966907846525)
                    ·
                      rfl

theorem cell23_5661210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 4, 4].length) (baseStart_5661210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661210 prefixEnd_5661210 := by exact prefixLift 5661210
  have htrace : WordTrace (prefixWord ++ tailWord_5661210) baseStart_5661210 baseEnd_5661210 := by
    simpa [prefixWord, tailWord_5661210, baseEnd_5661210] using wordTrace_append hprefix tailTrace_5661210
  have hstable : (prefixWord ++ tailWord_5661210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661210).length < 2 ^ (prefixWord ++ tailWord_5661210).sum := by decide
  have hdescent : baseEnd_5661210 < baseStart_5661210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661234 : List Nat := [3, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2]
def baseStart_5661234 : Nat := 118140960795 + 5661234 * 2 ^ 59
def prefixEnd_5661234 : Nat := 4983230072969 + 3 ^ 40 * 5661234 * 2
def baseEnd_5661234 : Nat := 2906934139575608629639465

theorem tailTrace_5661234 : CollatzResearch.WordTrace tailWord_5661234 prefixEnd_5661234 2906934139575608629639465 := by
  unfold tailWord_5661234
  simp only [CollatzResearch.WordTrace]
  refine ⟨51620541793080888659127689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137654778114882369757673837 51620541793080888659127689)
  ·
    refine ⟨38715406344810666494345767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51620541793080888659127689 38715406344810666494345767)
    ·
      refine ⟨58073109517215999741518651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38715406344810666494345767 58073109517215999741518651)
      ·
        refine ⟨87109664275823999612277977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58073109517215999741518651 87109664275823999612277977)
        ·
          refine ⟨65332248206867999709208483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87109664275823999612277977 65332248206867999709208483)
          ·
            refine ⟨97998372310301999563812725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65332248206867999709208483 97998372310301999563812725)
            ·
              refine ⟨9187347404090812459107443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97998372310301999563812725 9187347404090812459107443)
              ·
                refine ⟨13781021106136218688661165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9187347404090812459107443 13781021106136218688661165)
                ·
                  refine ⟨5167882914801082008247937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13781021106136218688661165 5167882914801082008247937)
                  ·
                    refine ⟨3875912186100811506185953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5167882914801082008247937 3875912186100811506185953)
                    ·
                      refine ⟨2906934139575608629639465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3875912186100811506185953 2906934139575608629639465)
                      ·
                        rfl

theorem cell23_5661234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2].length) (baseStart_5661234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661234 prefixEnd_5661234 := by exact prefixLift 5661234
  have htrace : WordTrace (prefixWord ++ tailWord_5661234) baseStart_5661234 baseEnd_5661234 := by
    simpa [prefixWord, tailWord_5661234, baseEnd_5661234] using wordTrace_append hprefix tailTrace_5661234
  have hstable : (prefixWord ++ tailWord_5661234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661234).length < 2 ^ (prefixWord ++ tailWord_5661234).sum := by decide
  have hdescent : baseEnd_5661234 < baseStart_5661234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661244 : List Nat := [2, 2, 2, 2, 3, 1, 4, 1, 2, 4]
def baseStart_5661244 : Nat := 118140960795 + 5661244 * 2 ^ 59
def prefixEnd_5661244 : Nat := 4983230072969 + 3 ^ 40 * 5661244 * 2
def baseEnd_5661244 : Nat := 968979758127384530171473

theorem tailTrace_5661244 : CollatzResearch.WordTrace tailWord_5661244 prefixEnd_5661244 968979758127384530171473 := by
  unfold tailWord_5661244
  simp only [CollatzResearch.WordTrace]
  refine ⟨103241265951143663172187393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137655021268191550896249857 103241265951143663172187393)
  ·
    refine ⟨77430949463357747379140545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103241265951143663172187393 77430949463357747379140545)
    ·
      refine ⟨58073212097518310534355409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77430949463357747379140545 58073212097518310534355409)
      ·
        refine ⟨43554909073138732900766557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58073212097518310534355409 43554909073138732900766557)
        ·
          refine ⟨16333090902427024837787459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43554909073138732900766557 16333090902427024837787459)
          ·
            refine ⟨24499636353640537256681189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16333090902427024837787459 24499636353640537256681189)
            ·
              refine ⟨4593681816307600735627723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24499636353640537256681189 4593681816307600735627723)
              ·
                refine ⟨6890522724461401103441585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4593681816307600735627723 6890522724461401103441585)
                ·
                  refine ⟨5167892043346050827581189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6890522724461401103441585 5167892043346050827581189)
                  ·
                    refine ⟨968979758127384530171473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5167892043346050827581189 968979758127384530171473)
                    ·
                      rfl

theorem cell23_5661244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_5661244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661244 prefixEnd_5661244 := by exact prefixLift 5661244
  have htrace : WordTrace (prefixWord ++ tailWord_5661244) baseStart_5661244 baseEnd_5661244 := by
    simpa [prefixWord, tailWord_5661244, baseEnd_5661244] using wordTrace_append hprefix tailTrace_5661244
  have hstable : (prefixWord ++ tailWord_5661244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661244).length < 2 ^ (prefixWord ++ tailWord_5661244).sum := by decide
  have hdescent : baseEnd_5661244 < baseStart_5661244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661263 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 5]
def baseStart_5661263 : Nat := 118140960795 + 5661263 * 2 ^ 59
def prefixEnd_5661263 : Nat := 4983230072969 + 3 ^ 40 * 5661263 * 2
def baseEnd_5661263 : Nat := 2906949030514589016176831

theorem tailTrace_5661263 : CollatzResearch.WordTrace tailWord_5661263 prefixEnd_5661263 2906949030514589016176831 := by
  unfold tailWord_5661263
  simp only [CollatzResearch.WordTrace]
  refine ⟨206483224889218492589316443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137655483259478995059544295 206483224889218492589316443)
  ·
    refine ⟨309724837333827738883974665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206483224889218492589316443 309724837333827738883974665)
    ·
      refine ⟨232293628000370804162980999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309724837333827738883974665 232293628000370804162980999)
      ·
        refine ⟨348440442000556206244471499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232293628000370804162980999 348440442000556206244471499)
        ·
          refine ⟨522660663000834309366707249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348440442000556206244471499 522660663000834309366707249)
          ·
            refine ⟨391995497250625732025030437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 522660663000834309366707249 391995497250625732025030437)
            ·
              refine ⟨73499155734492324754693207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 391995497250625732025030437 73499155734492324754693207)
              ·
                refine ⟨110248733601738487132039811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73499155734492324754693207 110248733601738487132039811)
                ·
                  refine ⟨165373100402607730698059717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110248733601738487132039811 165373100402607730698059717)
                  ·
                    refine ⟨31007456325488949505886197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 165373100402607730698059717 31007456325488949505886197)
                    ·
                      refine ⟨2906949030514589016176831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31007456325488949505886197 2906949030514589016176831)
                      ·
                        rfl

theorem cell23_5661263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_5661263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661263 prefixEnd_5661263 := by exact prefixLift 5661263
  have htrace : WordTrace (prefixWord ++ tailWord_5661263) baseStart_5661263 baseEnd_5661263 := by
    simpa [prefixWord, tailWord_5661263, baseEnd_5661263] using wordTrace_append hprefix tailTrace_5661263
  have hstable : (prefixWord ++ tailWord_5661263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661263).length < 2 ^ (prefixWord ++ tailWord_5661263).sum := by decide
  have hdescent : baseEnd_5661263 < baseStart_5661263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661284 : List Nat := [2, 3, 1, 1, 2, 2, 4, 2, 2, 1, 3]
def baseStart_5661284 : Nat := 118140960795 + 5661284 * 2 ^ 59
def prefixEnd_5661284 : Nat := 4983230072969 + 3 ^ 40 * 5661284 * 2
def baseEnd_5661284 : Nat := 2906959813608333434014235

theorem tailTrace_5661284 : CollatzResearch.WordTrace tailWord_5661284 prefixEnd_5661284 2906959813608333434014235 := by
  unfold tailWord_5661284
  simp only [CollatzResearch.WordTrace]
  refine ⟨103241995411071206587915453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137655993881428275450553937 103241995411071206587915453)
  ·
    refine ⟨38715748279151702470468295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103241995411071206587915453 38715748279151702470468295)
    ·
      refine ⟨58073622418727553705702443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38715748279151702470468295 58073622418727553705702443)
      ·
        refine ⟨87110433628091330558553665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58073622418727553705702443 87110433628091330558553665)
        ·
          refine ⟨65332825221068497918915249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87110433628091330558553665 65332825221068497918915249)
          ·
            refine ⟨48999618915801373439186437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65332825221068497918915249 48999618915801373439186437)
            ·
              refine ⟨9187428546712757519847457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48999618915801373439186437 9187428546712757519847457)
              ·
                refine ⟨6890571410034568139885593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9187428546712757519847457 6890571410034568139885593)
                ·
                  refine ⟨5167928557525926104914195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6890571410034568139885593 5167928557525926104914195)
                  ·
                    refine ⟨7751892836288889157371293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5167928557525926104914195 7751892836288889157371293)
                    ·
                      refine ⟨2906959813608333434014235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7751892836288889157371293 2906959813608333434014235)
                      ·
                        rfl

theorem cell23_5661284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_5661284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661284 prefixEnd_5661284 := by exact prefixLift 5661284
  have htrace : WordTrace (prefixWord ++ tailWord_5661284) baseStart_5661284 baseEnd_5661284 := by
    simpa [prefixWord, tailWord_5661284, baseEnd_5661284] using wordTrace_append hprefix tailTrace_5661284
  have hstable : (prefixWord ++ tailWord_5661284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661284).length < 2 ^ (prefixWord ++ tailWord_5661284).sum := by decide
  have hdescent : baseEnd_5661284 < baseStart_5661284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661285 : List Nat := [1, 3, 1, 3, 4, 2, 2, 2, 1, 2, 2]
def baseStart_5661285 : Nat := 118140960795 + 5661285 * 2 ^ 59
def prefixEnd_5661285 : Nat := 4983230072969 + 3 ^ 40 * 5661285 * 2
def baseEnd_5661285 : Nat := 2906960327088987930101731

theorem tailTrace_5661285 : CollatzResearch.WordTrace tailWord_5661285 prefixEnd_5661285 2906960327088987930101731 := by
  unfold tailWord_5661285
  simp only [CollatzResearch.WordTrace]
  refine ⟨206484027295138790346617309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137656018196759193564411539 206484027295138790346617309)
  ·
    refine ⟨77431510235677046379981491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206484027295138790346617309 77431510235677046379981491)
    ·
      refine ⟨116147265353515569569972237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77431510235677046379981491 116147265353515569569972237)
      ·
        refine ⟨43555224507568338588739589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116147265353515569569972237 43555224507568338588739589)
        ·
          refine ⟨8166604595169063485388673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43555224507568338588739589 8166604595169063485388673)
          ·
            refine ⟨6124953446376797614041505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8166604595169063485388673 6124953446376797614041505)
            ·
              refine ⟨4593715084782598210531129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6124953446376797614041505 4593715084782598210531129)
              ·
                refine ⟨3445286313586948657898347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4593715084782598210531129 3445286313586948657898347)
                ·
                  refine ⟨5167929470380422986847521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3445286313586948657898347 5167929470380422986847521)
                  ·
                    refine ⟨3875947102785317240135641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5167929470380422986847521 3875947102785317240135641)
                    ·
                      refine ⟨2906960327088987930101731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3875947102785317240135641 2906960327088987930101731)
                      ·
                        rfl

theorem cell23_5661285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_5661285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661285 prefixEnd_5661285 := by exact prefixLift 5661285
  have htrace : WordTrace (prefixWord ++ tailWord_5661285) baseStart_5661285 baseEnd_5661285 := by
    simpa [prefixWord, tailWord_5661285, baseEnd_5661285] using wordTrace_append hprefix tailTrace_5661285
  have hstable : (prefixWord ++ tailWord_5661285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661285).length < 2 ^ (prefixWord ++ tailWord_5661285).sum := by decide
  have hdescent : baseEnd_5661285 < baseStart_5661285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661290 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_5661290 : Nat := 118140960795 + 5661290 * 2 ^ 59
def prefixEnd_5661290 : Nat := 4983230072969 + 3 ^ 40 * 5661290 * 2
def baseEnd_5661290 : Nat := 2906962894492260410539207

theorem tailTrace_5661290 : CollatzResearch.WordTrace tailWord_5661290 prefixEnd_5661290 2906962894492260410539207 := by
  unfold tailWord_5661290
  simp only [CollatzResearch.WordTrace]
  refine ⟨51621052415030169050137331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137656139773413784133699549 51621052415030169050137331)
  ·
    refine ⟨77431578622545253575205997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51621052415030169050137331 77431578622545253575205997)
    ·
      refine ⟨29036841983454470090702249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77431578622545253575205997 29036841983454470090702249)
      ·
        refine ⟨21777631487590852568026687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29036841983454470090702249 21777631487590852568026687)
        ·
          refine ⟨32666447231386278852040031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21777631487590852568026687 32666447231386278852040031)
          ·
            refine ⟨48999670847079418278060047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32666447231386278852040031 48999670847079418278060047)
            ·
              refine ⟨73499506270619127417090071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48999670847079418278060047 73499506270619127417090071)
              ·
                refine ⟨110249259405928691125635107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73499506270619127417090071 110249259405928691125635107)
                ·
                  refine ⟨165373889108893036688452661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110249259405928691125635107 165373889108893036688452661)
                  ·
                    refine ⟨15503802103958722189542437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 165373889108893036688452661 15503802103958722189542437)
                    ·
                      refine ⟨2906962894492260410539207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15503802103958722189542437 2906962894492260410539207)
                      ·
                        rfl

theorem cell23_5661290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_5661290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661290 prefixEnd_5661290 := by exact prefixLift 5661290
  have htrace : WordTrace (prefixWord ++ tailWord_5661290) baseStart_5661290 baseEnd_5661290 := by
    simpa [prefixWord, tailWord_5661290, baseEnd_5661290] using wordTrace_append hprefix tailTrace_5661290
  have hstable : (prefixWord ++ tailWord_5661290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661290).length < 2 ^ (prefixWord ++ tailWord_5661290).sum := by decide
  have hdescent : baseEnd_5661290 < baseStart_5661290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661294 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 3, 3, 2]
def baseStart_5661294 : Nat := 118140960795 + 5661294 * 2 ^ 59
def prefixEnd_5661294 : Nat := 4983230072969 + 3 ^ 40 * 5661294 * 2
def baseEnd_5661294 : Nat := 2906964948414878394889189

theorem tailTrace_5661294 : CollatzResearch.WordTrace tailWord_5661294 prefixEnd_5661294 2906964948414878394889189 := by
  unfold tailWord_5661294
  simp only [CollatzResearch.WordTrace]
  refine ⟨25810544444013273110461867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137656237034737456589129957 25810544444013273110461867)
  ·
    refine ⟨38715816666019909665692801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25810544444013273110461867 38715816666019909665692801)
    ·
      refine ⟨29036862499514932249269601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38715816666019909665692801 29036862499514932249269601)
      ·
        refine ⟨21777646874636199186952201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29036862499514932249269601 21777646874636199186952201)
        ·
          refine ⟨16333235155977149390214151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21777646874636199186952201 16333235155977149390214151)
          ·
            refine ⟨24499852733965724085321227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16333235155977149390214151 24499852733965724085321227)
            ·
              refine ⟨36749779100948586127981841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24499852733965724085321227 36749779100948586127981841)
              ·
                refine ⟨27562334325711439595986381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36749779100948586127981841 27562334325711439595986381)
                ·
                  refine ⟨10335875372141789848494893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27562334325711439595986381 10335875372141789848494893)
                  ·
                    refine ⟨3875953264553171193185585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10335875372141789848494893 3875953264553171193185585)
                    ·
                      refine ⟨2906964948414878394889189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3875953264553171193185585 2906964948414878394889189)
                      ·
                        rfl

theorem cell23_5661294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_5661294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661294 prefixEnd_5661294 := by exact prefixLift 5661294
  have htrace : WordTrace (prefixWord ++ tailWord_5661294) baseStart_5661294 baseEnd_5661294 := by
    simpa [prefixWord, tailWord_5661294, baseEnd_5661294] using wordTrace_append hprefix tailTrace_5661294
  have hstable : (prefixWord ++ tailWord_5661294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661294).length < 2 ^ (prefixWord ++ tailWord_5661294).sum := by decide
  have hdescent : baseEnd_5661294 < baseStart_5661294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661341 : List Nat := [1, 4, 2, 1, 1, 1, 5, 2, 2, 2, 2]
def baseStart_5661341 : Nat := 118140960795 + 5661341 * 2 ^ 59
def prefixEnd_5661341 : Nat := 4983230072969 + 3 ^ 40 * 5661341 * 2
def baseEnd_5661341 : Nat := 2906989082005639711001473

theorem tailTrace_5661341 : CollatzResearch.WordTrace tailWord_5661341 prefixEnd_5661341 2906989082005639711001473 := by
  unfold tailWord_5661341
  simp only [CollatzResearch.WordTrace]
  refine ⟨206486069782935911910655877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137657379855290607940437251 206486069782935911910655877)
  ·
    refine ⟨38716138084300483483247977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206486069782935911910655877 38716138084300483483247977)
    ·
      refine ⟨29037103563225362612435983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38716138084300483483247977 29037103563225362612435983)
      ·
        refine ⟨43555655344838043918653975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29037103563225362612435983 43555655344838043918653975)
        ·
          refine ⟨65333483017257065877980963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43555655344838043918653975 65333483017257065877980963)
          ·
            refine ⟨98000224525885598816971445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65333483017257065877980963 98000224525885598816971445)
            ·
              refine ⟨9187521049301774889091073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98000224525885598816971445 9187521049301774889091073)
              ·
                refine ⟨6890640786976331166818305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9187521049301774889091073 6890640786976331166818305)
                ·
                  refine ⟨5167980590232248375113729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6890640786976331166818305 5167980590232248375113729)
                  ·
                    refine ⟨3875985442674186281335297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5167980590232248375113729 3875985442674186281335297)
                    ·
                      refine ⟨2906989082005639711001473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3875985442674186281335297 2906989082005639711001473)
                      ·
                        rfl

theorem cell23_5661341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_5661341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661341 prefixEnd_5661341 := by exact prefixLift 5661341
  have htrace : WordTrace (prefixWord ++ tailWord_5661341) baseStart_5661341 baseEnd_5661341 := by
    simpa [prefixWord, tailWord_5661341, baseEnd_5661341] using wordTrace_append hprefix tailTrace_5661341
  have hstable : (prefixWord ++ tailWord_5661341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661341).length < 2 ^ (prefixWord ++ tailWord_5661341).sum := by decide
  have hdescent : baseEnd_5661341 < baseStart_5661341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661358 : List Nat := [4, 1, 4, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_5661358 : Nat := 118140960795 + 5661358 * 2 ^ 59
def prefixEnd_5661358 : Nat := 4983230072969 + 3 ^ 40 * 5661358 * 2
def baseEnd_5661358 : Nat := 2906997811176766144488895

theorem tailTrace_5661358 : CollatzResearch.WordTrace tailWord_5661358 prefixEnd_5661358 2906997811176766144488895 := by
  unfold tailWord_5661358
  simp only [CollatzResearch.WordTrace]
  refine ⟨25810836227984290476753091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137657793215916215876016485 25810836227984290476753091)
  ·
    refine ⟨38716254341976435715129637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25810836227984290476753091 38716254341976435715129637)
    ·
      refine ⟨7259297689120581696586807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38716254341976435715129637 7259297689120581696586807)
      ·
        refine ⟨10888946533680872544880211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7259297689120581696586807 10888946533680872544880211)
        ·
          refine ⟨16333419800521308817320317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10888946533680872544880211 16333419800521308817320317)
          ·
            refine ⟨6125032425195490806495119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16333419800521308817320317 6125032425195490806495119)
            ·
              refine ⟨9187548637793236209742679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6125032425195490806495119 9187548637793236209742679)
              ·
                refine ⟨13781322956689854314614019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9187548637793236209742679 13781322956689854314614019)
                ·
                  refine ⟨20671984435034781471921029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13781322956689854314614019 20671984435034781471921029)
                  ·
                    refine ⟨3875997081569021525985193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20671984435034781471921029 3875997081569021525985193)
                    ·
                      refine ⟨2906997811176766144488895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3875997081569021525985193 2906997811176766144488895)
                      ·
                        rfl

theorem cell23_5661358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_5661358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661358 prefixEnd_5661358 := by exact prefixLift 5661358
  have htrace : WordTrace (prefixWord ++ tailWord_5661358) baseStart_5661358 baseEnd_5661358 := by
    simpa [prefixWord, tailWord_5661358, baseEnd_5661358] using wordTrace_append hprefix tailTrace_5661358
  have hstable : (prefixWord ++ tailWord_5661358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661358).length < 2 ^ (prefixWord ++ tailWord_5661358).sum := by decide
  have hdescent : baseEnd_5661358 < baseStart_5661358 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661394 : List Nat := [3, 2, 2, 2, 3, 1, 1, 2, 2, 5]
def baseStart_5661394 : Nat := 118140960795 + 5661394 * 2 ^ 59
def prefixEnd_5661394 : Nat := 4983230072969 + 3 ^ 40 * 5661394 * 2
def baseEnd_5661394 : Nat := 969005432160109334546243

theorem tailTrace_5661394 : CollatzResearch.WordTrace tailWord_5661394 prefixEnd_5661394 969005432160109334546243 := by
  unfold tailWord_5661394
  simp only [CollatzResearch.WordTrace]
  refine ⟨51622000712935975490583809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137658668567829267974890157 51622000712935975490583809)
  ·
    refine ⟨38716500534701981617937857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51622000712935975490583809 38716500534701981617937857)
    ·
      refine ⟨29037375401026486213453393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38716500534701981617937857 29037375401026486213453393)
      ·
        refine ⟨21778031550769864660090045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29037375401026486213453393 21778031550769864660090045)
        ·
          refine ⟨8166761831538699247533767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21778031550769864660090045 8166761831538699247533767)
          ·
            refine ⟨12250142747308048871300651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8166761831538699247533767 12250142747308048871300651)
            ·
              refine ⟨18375214120962073306950977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12250142747308048871300651 18375214120962073306950977)
              ·
                refine ⟨13781410590721554980213233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18375214120962073306950977 13781410590721554980213233)
                ·
                  refine ⟨10336057943041166235159925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13781410590721554980213233 10336057943041166235159925)
                  ·
                    refine ⟨969005432160109334546243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10336057943041166235159925 969005432160109334546243)
                    ·
                      rfl

theorem cell23_5661394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_5661394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661394 prefixEnd_5661394 := by exact prefixLift 5661394
  have htrace : WordTrace (prefixWord ++ tailWord_5661394) baseStart_5661394 baseEnd_5661394 := by
    simpa [prefixWord, tailWord_5661394, baseEnd_5661394] using wordTrace_append hprefix tailTrace_5661394
  have hstable : (prefixWord ++ tailWord_5661394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661394).length < 2 ^ (prefixWord ++ tailWord_5661394).sum := by decide
  have hdescent : baseEnd_5661394 < baseStart_5661394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661404 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_5661404 : Nat := 118140960795 + 5661404 * 2 ^ 59
def prefixEnd_5661404 : Nat := 4983230072969 + 3 ^ 40 * 5661404 * 2
def baseEnd_5661404 : Nat := 2907021431286872964513683

theorem tailTrace_5661404 : CollatzResearch.WordTrace tailWord_5661404 prefixEnd_5661404 2907021431286872964513683 := by
  unfold tailWord_5661404
  simp only [CollatzResearch.WordTrace]
  refine ⟨103244183790853836835099633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137658911721138449113466177 103244183790853836835099633)
  ·
    refine ⟨77433137843140377626324725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103244183790853836835099633 77433137843140377626324725)
    ·
      refine ⟨7259356672794410402467943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77433137843140377626324725 7259356672794410402467943)
      ·
        refine ⟨10889035009191615603701915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7259356672794410402467943 10889035009191615603701915)
        ·
          refine ⟨16333552513787423405552873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10889035009191615603701915 16333552513787423405552873)
          ·
            refine ⟨12250164385340567554164655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16333552513787423405552873 12250164385340567554164655)
            ·
              refine ⟨18375246578010851331246983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12250164385340567554164655 18375246578010851331246983)
              ·
                refine ⟨27562869867016276996870475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18375246578010851331246983 27562869867016276996870475)
                ·
                  refine ⟨41344304800524415495305713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27562869867016276996870475 41344304800524415495305713)
                  ·
                    refine ⟨31008228600393311621479285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41344304800524415495305713 31008228600393311621479285)
                    ·
                      refine ⟨2907021431286872964513683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31008228600393311621479285 2907021431286872964513683)
                      ·
                        rfl

theorem cell23_5661404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_5661404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661404 prefixEnd_5661404 := by exact prefixLift 5661404
  have htrace : WordTrace (prefixWord ++ tailWord_5661404) baseStart_5661404 baseEnd_5661404 := by
    simpa [prefixWord, tailWord_5661404, baseEnd_5661404] using wordTrace_append hprefix tailTrace_5661404
  have hstable : (prefixWord ++ tailWord_5661404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661404).length < 2 ^ (prefixWord ++ tailWord_5661404).sum := by decide
  have hdescent : baseEnd_5661404 < baseStart_5661404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661428 : List Nat := [2, 6, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_5661428 : Nat := 118140960795 + 5661428 * 2 ^ 59
def prefixEnd_5661428 : Nat := 4983230072969 + 3 ^ 40 * 5661428 * 2
def baseEnd_5661428 : Nat := 969011251607526956871191

theorem tailTrace_5661428 : CollatzResearch.WordTrace tailWord_5661428 prefixEnd_5661428 969011251607526956871191 := by
  unfold tailWord_5661428
  simp only [CollatzResearch.WordTrace]
  refine ⟨103244621466810362884536469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137659495289080483846048625 103244621466810362884536469)
  ·
    refine ⟨4839591631256735760212647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 103244621466810362884536469 4839591631256735760212647)
    ·
      refine ⟨7259387446885103640318971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4839591631256735760212647 7259387446885103640318971)
      ·
        refine ⟨10889081170327655460478457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7259387446885103640318971 10889081170327655460478457)
        ·
          refine ⟨8166810877745741595358843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10889081170327655460478457 8166810877745741595358843)
          ·
            refine ⟨12250216316618612393038265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8166810877745741595358843 12250216316618612393038265)
            ·
              refine ⟨9187662237463959294778699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12250216316618612393038265 9187662237463959294778699)
              ·
                refine ⟨13781493356195938942168049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9187662237463959294778699 13781493356195938942168049)
                ·
                  refine ⟨10336120017146954206626037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13781493356195938942168049 10336120017146954206626037)
                  ·
                    refine ⟨969011251607526956871191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10336120017146954206626037 969011251607526956871191)
                    ·
                      rfl

theorem cell23_5661428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_5661428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661428 prefixEnd_5661428 := by exact prefixLift 5661428
  have htrace : WordTrace (prefixWord ++ tailWord_5661428) baseStart_5661428 baseEnd_5661428 := by
    simpa [prefixWord, tailWord_5661428, baseEnd_5661428] using wordTrace_append hprefix tailTrace_5661428
  have hstable : (prefixWord ++ tailWord_5661428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661428).length < 2 ^ (prefixWord ++ tailWord_5661428).sum := by decide
  have hdescent : baseEnd_5661428 < baseStart_5661428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661464 : List Nat := [2, 1, 2, 3, 1, 1, 1, 5, 3, 1, 3]
def baseStart_5661464 : Nat := 118140960795 + 5661464 * 2 ^ 59
def prefixEnd_5661464 : Nat := 4983230072969 + 3 ^ 40 * 5661464 * 2
def baseEnd_5661464 : Nat := 2907052240126142729763407

theorem tailTrace_5661464 : CollatzResearch.WordTrace tailWord_5661464 prefixEnd_5661464 2907052240126142729763407 := by
  unfold tailWord_5661464
  simp only [CollatzResearch.WordTrace]
  refine ⟨103245277980745151958691723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137660370640993535944922297 103245277980745151958691723)
  ·
    refine ⟨154867916971117727938037585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103245277980745151958691723 154867916971117727938037585)
    ·
      refine ⟨116150937728338295953528189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154867916971117727938037585 116150937728338295953528189)
      ·
        refine ⟨43556601648126860982573071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116150937728338295953528189 43556601648126860982573071)
        ·
          refine ⟨65334902472190291473859607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43556601648126860982573071 65334902472190291473859607)
          ·
            refine ⟨98002353708285437210789411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65334902472190291473859607 98002353708285437210789411)
            ·
              refine ⟨147003530562428155816184117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98002353708285437210789411 147003530562428155816184117)
              ·
                refine ⟨13781580990227639607767261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 147003530562428155816184117 13781580990227639607767261)
                ·
                  refine ⟨5168092871335364852912723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13781580990227639607767261 5168092871335364852912723)
                  ·
                    refine ⟨7752139307003047279369085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5168092871335364852912723 7752139307003047279369085)
                    ·
                      refine ⟨2907052240126142729763407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7752139307003047279369085 2907052240126142729763407)
                      ·
                        rfl

theorem cell23_5661464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_5661464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661464 prefixEnd_5661464 := by exact prefixLift 5661464
  have htrace : WordTrace (prefixWord ++ tailWord_5661464) baseStart_5661464 baseEnd_5661464 := by
    simpa [prefixWord, tailWord_5661464, baseEnd_5661464] using wordTrace_append hprefix tailTrace_5661464
  have hstable : (prefixWord ++ tailWord_5661464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661464).length < 2 ^ (prefixWord ++ tailWord_5661464).sum := by decide
  have hdescent : baseEnd_5661464 < baseStart_5661464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661485 : List Nat := [1, 5, 3, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_5661485 : Nat := 118140960795 + 5661485 * 2 ^ 59
def prefixEnd_5661485 : Nat := 4983230072969 + 3 ^ 40 * 5661485 * 2
def baseEnd_5661485 : Nat := 2907063023219887147600811

theorem tailTrace_5661485 : CollatzResearch.WordTrace tailWord_5661485 prefixEnd_5661485 2907063023219887147600811 := by
  unfold tailWord_5661485
  simp only [CollatzResearch.WordTrace]
  refine ⟨206491321894414224503897909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137660881262942816335931939 206491321894414224503897909)
  ·
    refine ⟨19358561427601333547240429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 206491321894414224503897909 19358561427601333547240429)
    ·
      refine ⟨7259460535350500080215161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19358561427601333547240429 7259460535350500080215161)
      ·
        refine ⟨5444595401512875060161371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7259460535350500080215161 5444595401512875060161371)
        ·
          refine ⟨8166893102269312590242057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5444595401512875060161371 8166893102269312590242057)
          ·
            refine ⟨6125169826701984442681543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8166893102269312590242057 6125169826701984442681543)
            ·
              refine ⟨9187754740052976664022315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6125169826701984442681543 9187754740052976664022315)
              ·
                refine ⟨13781632110079464996033473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9187754740052976664022315 13781632110079464996033473)
                ·
                  refine ⟨10336224082559598747025105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13781632110079464996033473 10336224082559598747025105)
                  ·
                    refine ⟨7752168061919699060268829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10336224082559598747025105 7752168061919699060268829)
                    ·
                      refine ⟨2907063023219887147600811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7752168061919699060268829 2907063023219887147600811)
                      ·
                        rfl

theorem cell23_5661485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_5661485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661485 prefixEnd_5661485 := by exact prefixLift 5661485
  have htrace : WordTrace (prefixWord ++ tailWord_5661485) baseStart_5661485 baseEnd_5661485 := by
    simpa [prefixWord, tailWord_5661485, baseEnd_5661485] using wordTrace_append hprefix tailTrace_5661485
  have hstable : (prefixWord ++ tailWord_5661485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661485).length < 2 ^ (prefixWord ++ tailWord_5661485).sum := by decide
  have hdescent : baseEnd_5661485 < baseStart_5661485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661491 : List Nat := [1, 1, 1, 2, 6, 1, 3, 1, 2, 3, 2]
def baseStart_5661491 : Nat := 118140960795 + 5661491 * 2 ^ 59
def prefixEnd_5661491 : Nat := 4983230072969 + 3 ^ 40 * 5661491 * 2
def baseEnd_5661491 : Nat := 2907066104103814124125783

theorem tailTrace_5661491 : CollatzResearch.WordTrace tailWord_5661491 prefixEnd_5661491 2907066104103814124125783 := by
  unfold tailWord_5661491
  simp only [CollatzResearch.WordTrace]
  refine ⟨206491540732392487528616327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137661027154928325019077551 206491540732392487528616327)
  ·
    refine ⟨309737311098588731292924491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206491540732392487528616327 309737311098588731292924491)
    ·
      refine ⟨464605966647883096939386737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309737311098588731292924491 464605966647883096939386737)
      ·
        refine ⟨348454474985912322704540053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 464605966647883096939386737 348454474985912322704540053)
        ·
          refine ⟨16333803514964640126775315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 348454474985912322704540053 16333803514964640126775315)
          ·
            refine ⟨24500705272446960190162973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16333803514964640126775315 24500705272446960190162973)
            ·
              refine ⟨9187764477167610071311115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24500705272446960190162973 9187764477167610071311115)
              ·
                refine ⟨13781646715751415106966673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9187764477167610071311115 13781646715751415106966673)
                ·
                  refine ⟨10336235036813561330225005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13781646715751415106966673 10336235036813561330225005)
                  ·
                    refine ⟨3876088138805085498834377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10336235036813561330225005 3876088138805085498834377)
                    ·
                      refine ⟨2907066104103814124125783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3876088138805085498834377 2907066104103814124125783)
                      ·
                        rfl

theorem cell23_5661491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 3, 2].length) (baseStart_5661491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661491 prefixEnd_5661491 := by exact prefixLift 5661491
  have htrace : WordTrace (prefixWord ++ tailWord_5661491) baseStart_5661491 baseEnd_5661491 := by
    simpa [prefixWord, tailWord_5661491, baseEnd_5661491] using wordTrace_append hprefix tailTrace_5661491
  have hstable : (prefixWord ++ tailWord_5661491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661491).length < 2 ^ (prefixWord ++ tailWord_5661491).sum := by decide
  have hdescent : baseEnd_5661491 < baseStart_5661491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661501 : List Nat := [1, 4, 1, 4, 2, 1, 1, 3, 1, 5]
def baseStart_5661501 : Nat := 118140960795 + 5661501 * 2 ^ 59
def prefixEnd_5661501 : Nat := 4983230072969 + 3 ^ 40 * 5661501 * 2
def baseEnd_5661501 : Nat := 969023746303453028333579

theorem tailTrace_5661501 : CollatzResearch.WordTrace tailWord_5661501 prefixEnd_5661501 969023746303453028333579 := by
  unfold tailWord_5661501
  simp only [CollatzResearch.WordTrace]
  refine ⟨206491905462356259236480357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137661270308237506157653571 206491905462356259236480357)
  ·
    refine ⟨38717232274191798606840067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206491905462356259236480357 38717232274191798606840067)
    ·
      refine ⟨58075848411287697910260101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38717232274191798606840067 58075848411287697910260101)
      ·
        refine ⟨10889221577116443358173769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58075848411287697910260101 10889221577116443358173769)
        ·
          refine ⟨8166916182837332518630327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10889221577116443358173769 8166916182837332518630327)
          ·
            refine ⟨12250374274255998777945491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8166916182837332518630327 12250374274255998777945491)
            ·
              refine ⟨18375561411383998166918237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12250374274255998777945491 18375561411383998166918237)
              ·
                refine ⟨6890835529268999312594339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18375561411383998166918237 6890835529268999312594339)
                ·
                  refine ⟨10336253293903498968891509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6890835529268999312594339 10336253293903498968891509)
                  ·
                    refine ⟨969023746303453028333579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10336253293903498968891509 969023746303453028333579)
                    ·
                      rfl

theorem cell23_5661501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_5661501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661501 prefixEnd_5661501 := by exact prefixLift 5661501
  have htrace : WordTrace (prefixWord ++ tailWord_5661501) baseStart_5661501 baseEnd_5661501 := by
    simpa [prefixWord, tailWord_5661501, baseEnd_5661501] using wordTrace_append hprefix tailTrace_5661501
  have hstable : (prefixWord ++ tailWord_5661501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661501).length < 2 ^ (prefixWord ++ tailWord_5661501).sum := by decide
  have hdescent : baseEnd_5661501 < baseStart_5661501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661507 : List Nat := [1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 5]
def baseStart_5661507 : Nat := 118140960795 + 5661507 * 2 ^ 59
def prefixEnd_5661507 : Nat := 4983230072969 + 3 ^ 40 * 5661507 * 2
def baseEnd_5661507 : Nat := 2907074319794286061525709

theorem tailTrace_5661507 : CollatzResearch.WordTrace tailWord_5661507 prefixEnd_5661507 2907074319794286061525709 := by
  unfold tailWord_5661507
  simp only [CollatzResearch.WordTrace]
  refine ⟨206492124300334522261198775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137661416200223014840799183 206492124300334522261198775)
  ·
    refine ⟨309738186450501783391798163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206492124300334522261198775 309738186450501783391798163)
    ·
      refine ⟨464607279675752675087697245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309738186450501783391798163 464607279675752675087697245)
      ·
        refine ⟨174227729878407253157886467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 464607279675752675087697245 174227729878407253157886467)
        ·
          refine ⟨261341594817610879736829701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174227729878407253157886467 261341594817610879736829701)
          ·
            refine ⟨49001549028302039950655569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 261341594817610879736829701 49001549028302039950655569)
            ·
              refine ⟨36751161771226529962991677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49001549028302039950655569 36751161771226529962991677)
              ·
                refine ⟨13781685664209948736121879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36751161771226529962991677 13781685664209948736121879)
                ·
                  refine ⟨20672528496314923104182819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13781685664209948736121879 20672528496314923104182819)
                  ·
                    refine ⟨31008792744472384656274229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20672528496314923104182819 31008792744472384656274229)
                    ·
                      refine ⟨2907074319794286061525709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31008792744472384656274229 2907074319794286061525709)
                      ·
                        rfl

theorem cell23_5661507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_5661507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661507 prefixEnd_5661507 := by exact prefixLift 5661507
  have htrace : WordTrace (prefixWord ++ tailWord_5661507) baseStart_5661507 baseEnd_5661507 := by
    simpa [prefixWord, tailWord_5661507, baseEnd_5661507] using wordTrace_append hprefix tailTrace_5661507
  have hstable : (prefixWord ++ tailWord_5661507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661507).length < 2 ^ (prefixWord ++ tailWord_5661507).sum := by decide
  have hdescent : baseEnd_5661507 < baseStart_5661507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661514 : List Nat := [3, 1, 2, 1, 1, 1, 2, 6, 2, 4]
def baseStart_5661514 : Nat := 118140960795 + 5661514 * 2 ^ 59
def prefixEnd_5661514 : Nat := 4983230072969 + 3 ^ 40 * 5661514 * 2
def baseEnd_5661514 : Nat := 969025971386289178046059

theorem tailTrace_5661514 : CollatzResearch.WordTrace tailWord_5661514 prefixEnd_5661514 969025971386289178046059 := by
  unfold tailWord_5661514
  simp only [CollatzResearch.WordTrace]
  refine ⟨51623094902827290614175899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137661586407539441637802397 51623094902827290614175899)
  ·
    refine ⟨77434642354240935921263849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51623094902827290614175899 77434642354240935921263849)
    ·
      refine ⟨58075981765680701940947887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77434642354240935921263849 58075981765680701940947887)
      ·
        refine ⟨87113972648521052911421831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58075981765680701940947887 87113972648521052911421831)
        ·
          refine ⟨130670958972781579367132747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87113972648521052911421831 130670958972781579367132747)
          ·
            refine ⟨196006438459172369050699121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130670958972781579367132747 196006438459172369050699121)
            ·
              refine ⟨147004828844379276788024341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196006438459172369050699121 147004828844379276788024341)
              ·
                refine ⟨6890851352080278599438641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 147004828844379276788024341 6890851352080278599438641)
                ·
                  refine ⟨5168138514060208949578981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6890851352080278599438641 5168138514060208949578981)
                  ·
                    refine ⟨969025971386289178046059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5168138514060208949578981 969025971386289178046059)
                    ·
                      rfl

theorem cell23_5661514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_5661514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661514 prefixEnd_5661514 := by exact prefixLift 5661514
  have htrace : WordTrace (prefixWord ++ tailWord_5661514) baseStart_5661514 baseEnd_5661514 := by
    simpa [prefixWord, tailWord_5661514, baseEnd_5661514] using wordTrace_append hprefix tailTrace_5661514
  have hstable : (prefixWord ++ tailWord_5661514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661514).length < 2 ^ (prefixWord ++ tailWord_5661514).sum := by decide
  have hdescent : baseEnd_5661514 < baseStart_5661514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661538 : List Nat := [3, 3, 2, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_5661538 : Nat := 118140960795 + 5661538 * 2 ^ 59
def prefixEnd_5661538 : Nat := 4983230072969 + 3 ^ 40 * 5661538 * 2
def baseEnd_5661538 : Nat := 2907090237694575440238067

theorem tailTrace_5661538 : CollatzResearch.WordTrace tailWord_5661538 prefixEnd_5661538 2907090237694575440238067 := by
  unfold tailWord_5661538
  simp only [CollatzResearch.WordTrace]
  refine ⟨51623313740805553638894317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137662169975481476370384845 51623313740805553638894317)
  ·
    refine ⟨19358742652802082614585369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51623313740805553638894317 19358742652802082614585369)
    ·
      refine ⟨14519056989601561960939027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19358742652802082614585369 14519056989601561960939027)
      ·
        refine ⟨21778585484402342941408541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14519056989601561960939027 21778585484402342941408541)
        ·
          refine ⟨8166969556650878603028203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21778585484402342941408541 8166969556650878603028203)
          ·
            refine ⟨12250454334976317904542305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8166969556650878603028203 12250454334976317904542305)
            ·
              refine ⟨9187840751232238428406729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12250454334976317904542305 9187840751232238428406729)
              ·
                refine ⟨6890880563424178821305047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9187840751232238428406729 6890880563424178821305047)
                ·
                  refine ⟨10336320845136268231957571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6890880563424178821305047 10336320845136268231957571)
                  ·
                    refine ⟨15504481267704402347936357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10336320845136268231957571 15504481267704402347936357)
                    ·
                      refine ⟨2907090237694575440238067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15504481267704402347936357 2907090237694575440238067)
                      ·
                        rfl

theorem cell23_5661538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_5661538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661538 prefixEnd_5661538 := by exact prefixLift 5661538
  have htrace : WordTrace (prefixWord ++ tailWord_5661538) baseStart_5661538 baseEnd_5661538 := by
    simpa [prefixWord, tailWord_5661538, baseEnd_5661538] using wordTrace_append hprefix tailTrace_5661538
  have hstable : (prefixWord ++ tailWord_5661538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661538).length < 2 ^ (prefixWord ++ tailWord_5661538).sum := by decide
  have hdescent : baseEnd_5661538 < baseStart_5661538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661544 : List Nat := [2, 1, 4, 2, 1, 2, 4, 7]
def baseStart_5661544 : Nat := 118140960795 + 5661544 * 2 ^ 59
def prefixEnd_5661544 : Nat := 4983230072969 + 3 ^ 40 * 5661544 * 2
def baseEnd_5661544 : Nat := 107670122910314904324557

theorem tailTrace_5661544 : CollatzResearch.WordTrace tailWord_5661544 prefixEnd_5661544 107670122910314904324557 := by
  unfold tailWord_5661544
  simp only [CollatzResearch.WordTrace]
  refine ⟨103246736900600238790147843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137662315867466985053530457 103246736900600238790147843)
  ·
    refine ⟨154870105350900358185221765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103246736900600238790147843 154870105350900358185221765)
    ·
      refine ⟨29038144753293817159729081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154870105350900358185221765 29038144753293817159729081)
      ·
        refine ⟨21778608564970362869796811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29038144753293817159729081 21778608564970362869796811)
        ·
          refine ⟨32667912847455544304695217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21778608564970362869796811 32667912847455544304695217)
          ·
            refine ⟨24500934635591658228521413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32667912847455544304695217 24500934635591658228521413)
            ·
              refine ⟨4593925244173435917847765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24500934635591658228521413 4593925244173435917847765)
              ·
                refine ⟨107670122910314904324557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4593925244173435917847765 107670122910314904324557)
                ·
                  rfl

theorem cell23_5661544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 7].length) (baseStart_5661544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661544 prefixEnd_5661544 := by exact prefixLift 5661544
  have htrace : WordTrace (prefixWord ++ tailWord_5661544) baseStart_5661544 baseEnd_5661544 := by
    simpa [prefixWord, tailWord_5661544, baseEnd_5661544] using wordTrace_append hprefix tailTrace_5661544
  have hstable : (prefixWord ++ tailWord_5661544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661544).length < 2 ^ (prefixWord ++ tailWord_5661544).sum := by decide
  have hdescent : baseEnd_5661544 < baseStart_5661544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661554 : List Nat := [3, 2, 1, 2, 1, 1, 2, 4, 1, 3, 3]
def baseStart_5661554 : Nat := 118140960795 + 5661554 * 2 ^ 59
def prefixEnd_5661554 : Nat := 4983230072969 + 3 ^ 40 * 5661554 * 2
def baseEnd_5661554 : Nat := 2907098453385047377637993

theorem tailTrace_5661554 : CollatzResearch.WordTrace tailWord_5661554 prefixEnd_5661554 2907098453385047377637993 := by
  unfold tailWord_5661554
  simp only [CollatzResearch.WordTrace]
  refine ⟨51623459632791062322039929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137662559020776166192106477 51623459632791062322039929)
  ·
    refine ⟨38717594724593296741529947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51623459632791062322039929 38717594724593296741529947)
    ·
      refine ⟨58076392086889945112294921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38717594724593296741529947 58076392086889945112294921)
      ·
        refine ⟨43557294065167458834221191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58076392086889945112294921 43557294065167458834221191)
        ·
          refine ⟨65335941097751188251331787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43557294065167458834221191 65335941097751188251331787)
          ·
            refine ⟨98003911646626782376997681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65335941097751188251331787 98003911646626782376997681)
            ·
              refine ⟨73502933734970086782748261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98003911646626782376997681 73502933734970086782748261)
              ·
                refine ⟨13781800075306891271765299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73502933734970086782748261 13781800075306891271765299)
                ·
                  refine ⟨20672700112960336907647949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13781800075306891271765299 20672700112960336907647949)
                  ·
                    refine ⟨7752262542360126340367981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20672700112960336907647949 7752262542360126340367981)
                    ·
                      refine ⟨2907098453385047377637993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7752262542360126340367981 2907098453385047377637993)
                      ·
                        rfl

theorem cell23_5661554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_5661554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661554 prefixEnd_5661554 := by exact prefixLift 5661554
  have htrace : WordTrace (prefixWord ++ tailWord_5661554) baseStart_5661554 baseEnd_5661554 := by
    simpa [prefixWord, tailWord_5661554, baseEnd_5661554] using wordTrace_append hprefix tailTrace_5661554
  have hstable : (prefixWord ++ tailWord_5661554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661554).length < 2 ^ (prefixWord ++ tailWord_5661554).sum := by decide
  have hdescent : baseEnd_5661554 < baseStart_5661554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661558 : List Nat := [5, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3]
def baseStart_5661558 : Nat := 118140960795 + 5661558 * 2 ^ 59
def prefixEnd_5661558 : Nat := 4983230072969 + 3 ^ 40 * 5661558 * 2
def baseEnd_5661558 : Nat := 2907100507307665361987975

theorem tailTrace_5661558 : CollatzResearch.WordTrace tailWord_5661558 prefixEnd_5661558 2907100507307665361987975 := by
  unfold tailWord_5661558
  simp only [CollatzResearch.WordTrace]
  refine ⟨12905874026446859873206583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137662656282099838647536885 12905874026446859873206583)
  ·
    refine ⟨19358811039670289809809875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12905874026446859873206583 19358811039670289809809875)
    ·
      refine ⟨29038216559505434714714813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19358811039670289809809875 29038216559505434714714813)
      ·
        refine ⟨10889331209814538018018055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29038216559505434714714813 10889331209814538018018055)
        ·
          refine ⟨16333996814721807027027083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10889331209814538018018055 16333996814721807027027083)
          ·
            refine ⟨24500995222082710540540625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16333996814721807027027083 24500995222082710540540625)
            ·
              refine ⟨18375746416562032905405469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24500995222082710540540625 18375746416562032905405469)
              ·
                refine ⟨6890904906210762339527051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18375746416562032905405469 6890904906210762339527051)
                ·
                  refine ⟨10336357359316143509290577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6890904906210762339527051 10336357359316143509290577)
                  ·
                    refine ⟨7752268019487107631967933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10336357359316143509290577 7752268019487107631967933)
                    ·
                      refine ⟨2907100507307665361987975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7752268019487107631967933 2907100507307665361987975)
                      ·
                        rfl

theorem cell23_5661558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_5661558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661558 prefixEnd_5661558 := by exact prefixLift 5661558
  have htrace : WordTrace (prefixWord ++ tailWord_5661558) baseStart_5661558 baseEnd_5661558 := by
    simpa [prefixWord, tailWord_5661558, baseEnd_5661558] using wordTrace_append hprefix tailTrace_5661558
  have hstable : (prefixWord ++ tailWord_5661558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661558).length < 2 ^ (prefixWord ++ tailWord_5661558).sum := by decide
  have hdescent : baseEnd_5661558 < baseStart_5661558 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661571 : List Nat := [1, 1, 1, 3, 4, 1, 2, 4, 2, 1, 3]
def baseStart_5661571 : Nat := 118140960795 + 5661571 * 2 ^ 59
def prefixEnd_5661571 : Nat := 4983230072969 + 3 ^ 40 * 5661571 * 2
def baseEnd_5661571 : Nat := 2907107182556173811125415

theorem tailTrace_5661571 : CollatzResearch.WordTrace tailWord_5661571 prefixEnd_5661571 2907107182556173811125415 := by
  unfold tailWord_5661571
  simp only [CollatzResearch.WordTrace]
  refine ⟨206494458572102661191528567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137662972381401774127685711 206494458572102661191528567)
  ·
    refine ⟨309741687858153991787292851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206494458572102661191528567 309741687858153991787292851)
    ·
      refine ⟨464612531787230987680939277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309741687858153991787292851 464612531787230987680939277)
      ·
        refine ⟨174229699420211620380352229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 464612531787230987680939277 174229699420211620380352229)
        ·
          refine ⟨32668068641289678821316043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174229699420211620380352229 32668068641289678821316043)
          ·
            refine ⟨49002102961934518231974065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32668068641289678821316043 49002102961934518231974065)
            ·
              refine ⟨36751577221450888673980549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49002102961934518231974065 36751577221450888673980549)
              ·
                refine ⟨6890920729022041626371353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36751577221450888673980549 6890920729022041626371353)
                ·
                  refine ⟨5168190546766531219778515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6890920729022041626371353 5168190546766531219778515)
                  ·
                    refine ⟨7752285820149796829667773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5168190546766531219778515 7752285820149796829667773)
                    ·
                      refine ⟨2907107182556173811125415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7752285820149796829667773 2907107182556173811125415)
                      ·
                        rfl

theorem cell23_5661571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 1, 3].length) (baseStart_5661571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661571 prefixEnd_5661571 := by exact prefixLift 5661571
  have htrace : WordTrace (prefixWord ++ tailWord_5661571) baseStart_5661571 baseEnd_5661571 := by
    simpa [prefixWord, tailWord_5661571, baseEnd_5661571] using wordTrace_append hprefix tailTrace_5661571
  have hstable : (prefixWord ++ tailWord_5661571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661571).length < 2 ^ (prefixWord ++ tailWord_5661571).sum := by decide
  have hdescent : baseEnd_5661571 < baseStart_5661571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661588 : List Nat := [2, 4, 2, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_5661588 : Nat := 118140960795 + 5661588 * 2 ^ 59
def prefixEnd_5661588 : Nat := 4983230072969 + 3 ^ 40 * 5661588 * 2
def baseEnd_5661588 : Nat := 2907115911727300244612837

theorem tailTrace_5661588 : CollatzResearch.WordTrace tailWord_5661588 prefixEnd_5661588 2907115911727300244612837 := by
  unfold tailWord_5661588
  simp only [CollatzResearch.WordTrace]
  refine ⟨103247539306520536547448709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137663385742027382063264945 103247539306520536547448709)
  ·
    refine ⟨19358913619972600602646633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103247539306520536547448709 19358913619972600602646633)
    ·
      refine ⟨14519185214979450451984975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19358913619972600602646633 14519185214979450451984975)
      ·
        refine ⟨21778777822469175677977463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14519185214979450451984975 21778777822469175677977463)
        ·
          refine ⟨32668166733703763516966195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21778777822469175677977463 32668166733703763516966195)
          ·
            refine ⟨49002250100555645275449293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32668166733703763516966195 49002250100555645275449293)
            ·
              refine ⟨18375843787708366978293485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49002250100555645275449293 18375843787708366978293485)
              ·
                refine ⟨6890941420390637616860057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18375843787708366978293485 6890941420390637616860057)
                ·
                  refine ⟨5168206065292978212645043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6890941420390637616860057 5168206065292978212645043)
                  ·
                    refine ⟨7752309097939467318967565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5168206065292978212645043 7752309097939467318967565)
                    ·
                      refine ⟨2907115911727300244612837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7752309097939467318967565 2907115911727300244612837)
                      ·
                        rfl

theorem cell23_5661588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_5661588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661588 prefixEnd_5661588 := by exact prefixLift 5661588
  have htrace : WordTrace (prefixWord ++ tailWord_5661588) baseStart_5661588 baseEnd_5661588 := by
    simpa [prefixWord, tailWord_5661588, baseEnd_5661588] using wordTrace_append hprefix tailTrace_5661588
  have hstable : (prefixWord ++ tailWord_5661588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661588).length < 2 ^ (prefixWord ++ tailWord_5661588).sum := by decide
  have hdescent : baseEnd_5661588 < baseStart_5661588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661701 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 2, 4, 2]
def baseStart_5661701 : Nat := 118140960795 + 5661701 * 2 ^ 59
def prefixEnd_5661701 : Nat := 4983230072969 + 3 ^ 40 * 5661701 * 2
def baseEnd_5661701 : Nat := 2907173935041258302499817

theorem tailTrace_5661701 : CollatzResearch.WordTrace tailWord_5661701 prefixEnd_5661701 2907173935041258302499817 := by
  unfold tailWord_5661701
  simp only [CollatzResearch.WordTrace]
  refine ⟨206499200061631693393760957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137666133374421128929173971 206499200061631693393760957)
  ·
    refine ⟨77437200023111885022660359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206499200061631693393760957 77437200023111885022660359)
    ·
      refine ⟨116155800034667827533990539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77437200023111885022660359 116155800034667827533990539)
      ·
        refine ⟨174233700052001741300985809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116155800034667827533990539 174233700052001741300985809)
        ·
          refine ⟨130675275039001305975739357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174233700052001741300985809 130675275039001305975739357)
          ·
            refine ⟨49003228139625489740902259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130675275039001305975739357 49003228139625489740902259)
            ·
              refine ⟨73504842209438234611353389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49003228139625489740902259 73504842209438234611353389)
              ·
                refine ⟨27564315828539337979257521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73504842209438234611353389 27564315828539337979257521)
                ·
                  refine ⟨20673236871404503484443141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27564315828539337979257521 20673236871404503484443141)
                  ·
                    refine ⟨3876231913388344403333089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20673236871404503484443141 3876231913388344403333089)
                    ·
                      refine ⟨2907173935041258302499817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3876231913388344403333089 2907173935041258302499817)
                      ·
                        rfl

theorem cell23_5661701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 4, 2].length) (baseStart_5661701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661701 prefixEnd_5661701 := by exact prefixLift 5661701
  have htrace : WordTrace (prefixWord ++ tailWord_5661701) baseStart_5661701 baseEnd_5661701 := by
    simpa [prefixWord, tailWord_5661701, baseEnd_5661701] using wordTrace_append hprefix tailTrace_5661701
  have hstable : (prefixWord ++ tailWord_5661701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661701).length < 2 ^ (prefixWord ++ tailWord_5661701).sum := by decide
  have hdescent : baseEnd_5661701 < baseStart_5661701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661745 : List Nat := [1, 2, 2, 3, 1, 2, 5, 2, 1, 4]
def baseStart_5661745 : Nat := 118140960795 + 5661745 * 2 ^ 59
def prefixEnd_5661745 : Nat := 4983230072969 + 3 ^ 40 * 5661745 * 2
def baseEnd_5661745 : Nat := 969065509396685376783205

theorem tailTrace_5661745 : CollatzResearch.WordTrace tailWord_5661745 prefixEnd_5661745 969065509396685376783205 := by
  unfold tailWord_5661745
  simp only [CollatzResearch.WordTrace]
  refine ⟨206500804873472288908362689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137667203248981525938908459 206500804873472288908362689)
  ·
    refine ⟨154875603655104216681272017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206500804873472288908362689 154875603655104216681272017)
    ·
      refine ⟨116156702741328162510954013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154875603655104216681272017 116156702741328162510954013)
      ·
        refine ⟨43558763527998060941607755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116156702741328162510954013 43558763527998060941607755)
        ·
          refine ⟨65338145291997091412411633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43558763527998060941607755 65338145291997091412411633)
          ·
            refine ⟨49003608968997818559308725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65338145291997091412411633 49003608968997818559308725)
            ·
              refine ⟨4594088340843545489935193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49003608968997818559308725 4594088340843545489935193)
              ·
                refine ⟨3445566255632659117451395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4594088340843545489935193 3445566255632659117451395)
                ·
                  refine ⟨5168349383448988676177093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3445566255632659117451395 5168349383448988676177093)
                  ·
                    refine ⟨969065509396685376783205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5168349383448988676177093 969065509396685376783205)
                    ·
                      rfl

theorem cell23_5661745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 1, 4].length) (baseStart_5661745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661745 prefixEnd_5661745 := by exact prefixLift 5661745
  have htrace : WordTrace (prefixWord ++ tailWord_5661745) baseStart_5661745 baseEnd_5661745 := by
    simpa [prefixWord, tailWord_5661745, baseEnd_5661745] using wordTrace_append hprefix tailTrace_5661745
  have hstable : (prefixWord ++ tailWord_5661745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661745).length < 2 ^ (prefixWord ++ tailWord_5661745).sum := by decide
  have hdescent : baseEnd_5661745 < baseStart_5661745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661758 : List Nat := [4, 2, 1, 3, 1, 2, 1, 3, 6]
def baseStart_5661758 : Nat := 118140960795 + 5661758 * 2 ^ 59
def prefixEnd_5661758 : Nat := 4983230072969 + 3 ^ 40 * 5661758 * 2
def baseEnd_5661758 : Nat := 323022578159840508831895

theorem tailTrace_5661758 : CollatzResearch.WordTrace tailWord_5661758 prefixEnd_5661758 323022578159840508831895 := by
  unfold tailWord_5661758
  simp only [CollatzResearch.WordTrace]
  refine ⟨25812659877803149016073241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137667519348283461419057285 25812659877803149016073241)
  ·
    refine ⟨19359494908352361762054931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25812659877803149016073241 19359494908352361762054931)
    ·
      refine ⟨29039242362528542643082397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19359494908352361762054931 29039242362528542643082397)
      ·
        refine ⟨10889715885948203491155899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29039242362528542643082397 10889715885948203491155899)
        ·
          refine ⟨16334573828922305236733849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10889715885948203491155899 16334573828922305236733849)
          ·
            refine ⟨12250930371691728927550387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16334573828922305236733849 12250930371691728927550387)
            ·
              refine ⟨18376395557537593391325581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12250930371691728927550387 18376395557537593391325581)
              ·
                refine ⟨6891148334076597521747093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18376395557537593391325581 6891148334076597521747093)
                ·
                  refine ⟨323022578159840508831895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6891148334076597521747093 323022578159840508831895)
                  ·
                    rfl

theorem cell23_5661758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_5661758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661758 prefixEnd_5661758 := by exact prefixLift 5661758
  have htrace : WordTrace (prefixWord ++ tailWord_5661758) baseStart_5661758 baseEnd_5661758 := by
    simpa [prefixWord, tailWord_5661758, baseEnd_5661758] using wordTrace_append hprefix tailTrace_5661758
  have hstable : (prefixWord ++ tailWord_5661758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661758).length < 2 ^ (prefixWord ++ tailWord_5661758).sum := by decide
  have hdescent : baseEnd_5661758 < baseStart_5661758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661802 : List Nat := [3, 1, 3, 2, 2, 2, 1, 4, 1, 1, 3]
def baseStart_5661802 : Nat := 118140960795 + 5661802 * 2 ^ 59
def prefixEnd_5661802 : Nat := 4983230072969 + 3 ^ 40 * 5661802 * 2
def baseEnd_5661802 : Nat := 2907225796587362407336853

theorem tailTrace_5661802 : CollatzResearch.WordTrace tailWord_5661802 prefixEnd_5661802 2907225796587362407336853 := by
  unfold tailWord_5661802
  simp only [CollatzResearch.WordTrace]
  refine ⟨51625720958566446910796915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137668589222843858428791773 51625720958566446910796915)
  ·
    refine ⟨77438581437849670366195373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51625720958566446910796915 77438581437849670366195373)
    ·
      refine ⟨29039468039193626387323265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77438581437849670366195373 29039468039193626387323265)
      ·
        refine ⟨21779601029395219790492449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29039468039193626387323265 21779601029395219790492449)
        ·
          refine ⟨16334700772046414842869337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21779601029395219790492449 16334700772046414842869337)
          ·
            refine ⟨12251025579034811132152003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16334700772046414842869337 12251025579034811132152003)
            ·
              refine ⟨18376538368552216698228005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12251025579034811132152003 18376538368552216698228005)
              ·
                refine ⟨3445600944103540630917751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18376538368552216698228005 3445600944103540630917751)
                ·
                  refine ⟨5168401416155310946376627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3445600944103540630917751 5168401416155310946376627)
                  ·
                    refine ⟨7752602124232966419564941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5168401416155310946376627 7752602124232966419564941)
                    ·
                      refine ⟨2907225796587362407336853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7752602124232966419564941 2907225796587362407336853)
                      ·
                        rfl

theorem cell23_5661802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_5661802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661802 prefixEnd_5661802 := by exact prefixLift 5661802
  have htrace : WordTrace (prefixWord ++ tailWord_5661802) baseStart_5661802 baseEnd_5661802 := by
    simpa [prefixWord, tailWord_5661802, baseEnd_5661802] using wordTrace_append hprefix tailTrace_5661802
  have hstable : (prefixWord ++ tailWord_5661802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661802).length < 2 ^ (prefixWord ++ tailWord_5661802).sum := by decide
  have hdescent : baseEnd_5661802 < baseStart_5661802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661825 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 5, 2, 2]
def baseStart_5661825 : Nat := 118140960795 + 5661825 * 2 ^ 59
def prefixEnd_5661825 : Nat := 4983230072969 + 3 ^ 40 * 5661825 * 2
def baseEnd_5661825 : Nat := 2907237606642415817349247

theorem tailTrace_5661825 : CollatzResearch.WordTrace tailWord_5661825 prefixEnd_5661825 2907237606642415817349247 := by
  unfold tailWord_5661825
  simp only [CollatzResearch.WordTrace]
  refine ⟨206503722713182462571274929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137669148475454975047516619 206503722713182462571274929)
  ·
    refine ⟨154877792034886846928456197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206503722713182462571274929 154877792034886846928456197)
    ·
      refine ⟨29039586006541283799085537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154877792034886846928456197 29039586006541283799085537)
      ·
        refine ⟨21779689504905962849314153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29039586006541283799085537 21779689504905962849314153)
        ·
          refine ⟨16334767128679472136985615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21779689504905962849314153 16334767128679472136985615)
          ·
            refine ⟨24502150693019208205478423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16334767128679472136985615 24502150693019208205478423)
            ·
              refine ⟨36753226039528812308217635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24502150693019208205478423 36753226039528812308217635)
              ·
                refine ⟨55129839059293218462326453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36753226039528812308217635 55129839059293218462326453)
                ·
                  refine ⟨5168422411808739230843105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55129839059293218462326453 5168422411808739230843105)
                  ·
                    refine ⟨3876316808856554423132329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5168422411808739230843105 3876316808856554423132329)
                    ·
                      refine ⟨2907237606642415817349247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3876316808856554423132329 2907237606642415817349247)
                      ·
                        rfl

theorem cell23_5661825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_5661825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661825 prefixEnd_5661825 := by exact prefixLift 5661825
  have htrace : WordTrace (prefixWord ++ tailWord_5661825) baseStart_5661825 baseEnd_5661825 := by
    simpa [prefixWord, tailWord_5661825, baseEnd_5661825] using wordTrace_append hprefix tailTrace_5661825
  have hstable : (prefixWord ++ tailWord_5661825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661825).length < 2 ^ (prefixWord ++ tailWord_5661825).sum := by decide
  have hdescent : baseEnd_5661825 < baseStart_5661825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661828 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 3, 2, 3]
def baseStart_5661828 : Nat := 118140960795 + 5661828 * 2 ^ 59
def prefixEnd_5661828 : Nat := 4983230072969 + 3 ^ 40 * 5661828 * 2
def baseEnd_5661828 : Nat := 2907239147084379305611733

theorem tailTrace_5661828 : CollatzResearch.WordTrace tailWord_5661828 prefixEnd_5661828 2907239147084379305611733 := by
  unfold tailWord_5661828
  simp only [CollatzResearch.WordTrace]
  refine ⟨103251916066085797041817069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137669221421447729389089425 103251916066085797041817069)
  ·
    refine ⟨38719468524782173890681401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103251916066085797041817069 38719468524782173890681401)
    ·
      refine ⟨29039601393586630418011051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38719468524782173890681401 29039601393586630418011051)
      ·
        refine ⟨43559402090379945627016577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29039601393586630418011051 43559402090379945627016577)
        ·
          refine ⟨32669551567784959220262433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43559402090379945627016577 32669551567784959220262433)
          ·
            refine ⟨24502163675838719415196825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32669551567784959220262433 24502163675838719415196825)
            ·
              refine ⟨18376622756879039561397619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24502163675838719415196825 18376622756879039561397619)
              ·
                refine ⟨27564934135318559342096429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18376622756879039561397619 27564934135318559342096429)
                ·
                  refine ⟨10336850300744459753286161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27564934135318559342096429 10336850300744459753286161)
                  ·
                    refine ⟨7752637725558344814964621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10336850300744459753286161 7752637725558344814964621)
                    ·
                      refine ⟨2907239147084379305611733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7752637725558344814964621 2907239147084379305611733)
                      ·
                        rfl

theorem cell23_5661828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_5661828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661828 prefixEnd_5661828 := by exact prefixLift 5661828
  have htrace : WordTrace (prefixWord ++ tailWord_5661828) baseStart_5661828 baseEnd_5661828 := by
    simpa [prefixWord, tailWord_5661828, baseEnd_5661828] using wordTrace_append hprefix tailTrace_5661828
  have hstable : (prefixWord ++ tailWord_5661828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661828).length < 2 ^ (prefixWord ++ tailWord_5661828).sum := by decide
  have hdescent : baseEnd_5661828 < baseStart_5661828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661838 : List Nat := [4, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4]
def baseStart_5661838 : Nat := 118140960795 + 5661838 * 2 ^ 59
def prefixEnd_5661838 : Nat := 4983230072969 + 3 ^ 40 * 5661838 * 2
def baseEnd_5661838 : Nat := 2907244281890924266486687

theorem tailTrace_5661838 : CollatzResearch.WordTrace tailWord_5661838 prefixEnd_5661838 2907244281890924266486687 := by
  unfold tailWord_5661838
  simp only [CollatzResearch.WordTrace]
  refine ⟨25813024607766920723937271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137669464574756910527665445 25813024607766920723937271)
  ·
    refine ⟨38719536911650381085905907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25813024607766920723937271 38719536911650381085905907)
    ·
      refine ⟨58079305367475571628858861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38719536911650381085905907 58079305367475571628858861)
      ·
        refine ⟨21779739512803339360822073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58079305367475571628858861 21779739512803339360822073)
        ·
          refine ⟨16334804634602504520616555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21779739512803339360822073 16334804634602504520616555)
          ·
            refine ⟨24502206951903756780924833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16334804634602504520616555 24502206951903756780924833)
            ·
              refine ⟨18376655213927817585693625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24502206951903756780924833 18376655213927817585693625)
              ·
                refine ⟨13782491410445863189270219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18376655213927817585693625 13782491410445863189270219)
                ·
                  refine ⟨20673737115668794783905329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13782491410445863189270219 20673737115668794783905329)
                  ·
                    refine ⟨15505302836751596087928997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20673737115668794783905329 15505302836751596087928997)
                    ·
                      refine ⟨2907244281890924266486687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15505302836751596087928997 2907244281890924266486687)
                      ·
                        rfl

theorem cell23_5661838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_5661838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661838 prefixEnd_5661838 := by exact prefixLift 5661838
  have htrace : WordTrace (prefixWord ++ tailWord_5661838) baseStart_5661838 baseEnd_5661838 := by
    simpa [prefixWord, tailWord_5661838, baseEnd_5661838] using wordTrace_append hprefix tailTrace_5661838
  have hstable : (prefixWord ++ tailWord_5661838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661838).length < 2 ^ (prefixWord ++ tailWord_5661838).sum := by decide
  have hdescent : baseEnd_5661838 < baseStart_5661838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661842 : List Nat := [3, 2, 3, 1, 1, 4, 2, 1, 1, 1, 4]
def baseStart_5661842 : Nat := 118140960795 + 5661842 * 2 ^ 59
def prefixEnd_5661842 : Nat := 4983230072969 + 3 ^ 40 * 5661842 * 2
def baseEnd_5661842 : Nat := 2907246335813542250836669

theorem tailTrace_5661842 : CollatzResearch.WordTrace tailWord_5661842 prefixEnd_5661842 2907246335813542250836669 := by
  unfold tailWord_5661842
  simp only [CollatzResearch.WordTrace]
  refine ⟨51626085688530218618660945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137669561836080582983095853 51626085688530218618660945)
  ·
    refine ⟨38719564266397663963995709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51626085688530218618660945 38719564266397663963995709)
    ·
      refine ⟨14519836599899123986498391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38719564266397663963995709 14519836599899123986498391)
      ·
        refine ⟨21779754899848685979747587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14519836599899123986498391 21779754899848685979747587)
        ·
          refine ⟨32669632349773028969621381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21779754899848685979747587 32669632349773028969621381)
          ·
            refine ⟨6125556065582442931804009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32669632349773028969621381 6125556065582442931804009)
            ·
              refine ⟨4594167049186832198853007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6125556065582442931804009 4594167049186832198853007)
              ·
                refine ⟨6891250573780248298279511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4594167049186832198853007 6891250573780248298279511)
                ·
                  refine ⟨10336875860670372447419267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6891250573780248298279511 10336875860670372447419267)
                  ·
                    refine ⟨15505313791005558671128901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10336875860670372447419267 15505313791005558671128901)
                    ·
                      refine ⟨2907246335813542250836669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15505313791005558671128901 2907246335813542250836669)
                      ·
                        rfl

theorem cell23_5661842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_5661842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661842 prefixEnd_5661842 := by exact prefixLift 5661842
  have htrace : WordTrace (prefixWord ++ tailWord_5661842) baseStart_5661842 baseEnd_5661842 := by
    simpa [prefixWord, tailWord_5661842, baseEnd_5661842] using wordTrace_append hprefix tailTrace_5661842
  have hstable : (prefixWord ++ tailWord_5661842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661842).length < 2 ^ (prefixWord ++ tailWord_5661842).sum := by decide
  have hdescent : baseEnd_5661842 < baseStart_5661842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661868 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 3, 3, 2]
def baseStart_5661868 : Nat := 118140960795 + 5661868 * 2 ^ 59
def prefixEnd_5661868 : Nat := 4983230072969 + 3 ^ 40 * 5661868 * 2
def baseEnd_5661868 : Nat := 2907259686310559149111549

theorem tailTrace_5661868 : CollatzResearch.WordTrace tailWord_5661868 prefixEnd_5661868 2907259686310559149111549 := by
  unfold tailWord_5661868
  simp only [CollatzResearch.WordTrace]
  refine ⟨103252645526013340457545129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137670194034684453943393505 103252645526013340457545129)
  ·
    refine ⟨77439484144510005343158847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103252645526013340457545129 77439484144510005343158847)
    ·
      refine ⟨116159226216765008014738271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77439484144510005343158847 116159226216765008014738271)
      ·
        refine ⟨174238839325147512022107407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116159226216765008014738271 174238839325147512022107407)
        ·
          refine ⟨261358258987721268033161111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174238839325147512022107407 261358258987721268033161111)
          ·
            refine ⟨392037388481581902049741667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261358258987721268033161111 392037388481581902049741667)
            ·
              refine ⟨588056082722372853074612501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392037388481581902049741667 588056082722372853074612501)
              ·
                refine ⟨27565128877611227487872461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 588056082722372853074612501 27565128877611227487872461)
                ·
                  refine ⟨10336923329104210307952173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27565128877611227487872461 10336923329104210307952173)
                  ·
                    refine ⟨3876346248414078865482065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10336923329104210307952173 3876346248414078865482065)
                    ·
                      refine ⟨2907259686310559149111549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3876346248414078865482065 2907259686310559149111549)
                      ·
                        rfl

theorem cell23_5661868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 3, 2].length) (baseStart_5661868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661868 prefixEnd_5661868 := by exact prefixLift 5661868
  have htrace : WordTrace (prefixWord ++ tailWord_5661868) baseStart_5661868 baseEnd_5661868 := by
    simpa [prefixWord, tailWord_5661868, baseEnd_5661868] using wordTrace_append hprefix tailTrace_5661868
  have hstable : (prefixWord ++ tailWord_5661868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661868).length < 2 ^ (prefixWord ++ tailWord_5661868).sum := by decide
  have hdescent : baseEnd_5661868 < baseStart_5661868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661885 : List Nat := [1, 4, 1, 2, 1, 1, 3, 4, 1, 3, 2]
def baseStart_5661885 : Nat := 118140960795 + 5661885 * 2 ^ 59
def prefixEnd_5661885 : Nat := 4983230072969 + 3 ^ 40 * 5661885 * 2
def baseEnd_5661885 : Nat := 2907268415481685582598971

theorem tailTrace_5661885 : CollatzResearch.WordTrace tailWord_5661885 prefixEnd_5661885 2907268415481685582598971 := by
  unfold tailWord_5661885
  simp only [CollatzResearch.WordTrace]
  refine ⟨206505911092965092818459109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137670607395310061878972739 206505911092965092818459109)
  ·
    refine ⟨38719858329930954903461083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206505911092965092818459109 38719858329930954903461083)
    ·
      refine ⟨58079787494896432355191625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38719858329930954903461083 58079787494896432355191625)
      ·
        refine ⟨43559840621172324266393719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58079787494896432355191625 43559840621172324266393719)
        ·
          refine ⟨65339760931758486399590579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43559840621172324266393719 65339760931758486399590579)
          ·
            refine ⟨98009641397637729599385869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65339760931758486399590579 98009641397637729599385869)
            ·
              refine ⟨36753615524114148599769701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98009641397637729599385869 36753615524114148599769701)
              ·
                refine ⟨6891302910771402862456819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36753615524114148599769701 6891302910771402862456819)
                ·
                  refine ⟨10336954366157104293685229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6891302910771402862456819 10336954366157104293685229)
                  ·
                    refine ⟨3876357887308914110131961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10336954366157104293685229 3876357887308914110131961)
                    ·
                      refine ⟨2907268415481685582598971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3876357887308914110131961 2907268415481685582598971)
                      ·
                        rfl

theorem cell23_5661885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_5661885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661885 prefixEnd_5661885 := by exact prefixLift 5661885
  have htrace : WordTrace (prefixWord ++ tailWord_5661885) baseStart_5661885 baseEnd_5661885 := by
    simpa [prefixWord, tailWord_5661885, baseEnd_5661885] using wordTrace_append hprefix tailTrace_5661885
  have hstable : (prefixWord ++ tailWord_5661885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661885).length < 2 ^ (prefixWord ++ tailWord_5661885).sum := by decide
  have hdescent : baseEnd_5661885 < baseStart_5661885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661911 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 4]
def baseStart_5661911 : Nat := 118140960795 + 5661911 * 2 ^ 59
def prefixEnd_5661911 : Nat := 4983230072969 + 3 ^ 40 * 5661911 * 2
def baseEnd_5661911 : Nat := 2907281765978702480873851

theorem tailTrace_5661911 : CollatzResearch.WordTrace tailWord_5661911 prefixEnd_5661911 2907281765978702480873851 := by
  unfold tailWord_5661911
  simp only [CollatzResearch.WordTrace]
  refine ⟨206506859390870899258905587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137671239593913932839270391 206506859390870899258905587)
  ·
    refine ⟨309760289086306348888358381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206506859390870899258905587 309760289086306348888358381)
    ·
      refine ⟨116160108407364880833134393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 309760289086306348888358381 116160108407364880833134393)
      ·
        refine ⟨87120081305523660624850795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116160108407364880833134393 87120081305523660624850795)
        ·
          refine ⟨130680121958285490937276193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87120081305523660624850795 130680121958285490937276193)
          ·
            refine ⟨98010091468714118202957145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130680121958285490937276193 98010091468714118202957145)
            ·
              refine ⟨73507568601535588652217859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98010091468714118202957145 73507568601535588652217859)
              ·
                refine ⟨110261352902303382978326789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73507568601535588652217859 110261352902303382978326789)
                ·
                  refine ⟨20674003669181884308436273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110261352902303382978326789 20674003669181884308436273)
                  ·
                    refine ⟨15505502751886413231327205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20674003669181884308436273 15505502751886413231327205)
                    ·
                      refine ⟨2907281765978702480873851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15505502751886413231327205 2907281765978702480873851)
                      ·
                        rfl

theorem cell23_5661911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_5661911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661911 prefixEnd_5661911 := by exact prefixLift 5661911
  have htrace : WordTrace (prefixWord ++ tailWord_5661911) baseStart_5661911 baseEnd_5661911 := by
    simpa [prefixWord, tailWord_5661911, baseEnd_5661911] using wordTrace_append hprefix tailTrace_5661911
  have hstable : (prefixWord ++ tailWord_5661911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661911).length < 2 ^ (prefixWord ++ tailWord_5661911).sum := by decide
  have hdescent : baseEnd_5661911 < baseStart_5661911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661932 : List Nat := [2, 2, 1, 1, 2, 5, 1, 3, 2, 2, 2]
def baseStart_5661932 : Nat := 118140960795 + 5661932 * 2 ^ 59
def prefixEnd_5661932 : Nat := 4983230072969 + 3 ^ 40 * 5661932 * 2
def baseEnd_5661932 : Nat := 2907292549072446898711255

theorem tailTrace_5661932 : CollatzResearch.WordTrace tailWord_5661932 prefixEnd_5661932 2907292549072446898711255 := by
  unfold tailWord_5661932
  simp only [CollatzResearch.WordTrace]
  refine ⟨103253812661897409922710025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137671750215863213230280033 103253812661897409922710025)
  ·
    refine ⟨77440359496423057442032519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103253812661897409922710025 77440359496423057442032519)
    ·
      refine ⟨116160539244634586163048779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77440359496423057442032519 116160539244634586163048779)
      ·
        refine ⟨174240808866951879244573169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116160539244634586163048779 174240808866951879244573169)
        ·
          refine ⟨130680606650213909433429877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174240808866951879244573169 130680606650213909433429877)
          ·
            refine ⟨12251306873457554009384051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 130680606650213909433429877 12251306873457554009384051)
            ·
              refine ⟨18376960310186331014076077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12251306873457554009384051 18376960310186331014076077)
              ·
                refine ⟨6891360116319874130278529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18376960310186331014076077 6891360116319874130278529)
                ·
                  refine ⟨5168520087239905597708897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6891360116319874130278529 5168520087239905597708897)
                  ·
                    refine ⟨3876390065429929198281673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5168520087239905597708897 3876390065429929198281673)
                    ·
                      refine ⟨2907292549072446898711255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3876390065429929198281673 2907292549072446898711255)
                      ·
                        rfl

theorem cell23_5661932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 2, 2].length) (baseStart_5661932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661932 prefixEnd_5661932 := by exact prefixLift 5661932
  have htrace : WordTrace (prefixWord ++ tailWord_5661932) baseStart_5661932 baseEnd_5661932 := by
    simpa [prefixWord, tailWord_5661932, baseEnd_5661932] using wordTrace_append hprefix tailTrace_5661932
  have hstable : (prefixWord ++ tailWord_5661932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661932).length < 2 ^ (prefixWord ++ tailWord_5661932).sum := by decide
  have hdescent : baseEnd_5661932 < baseStart_5661932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661961 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 3, 2, 5]
def baseStart_5661961 : Nat := 118140960795 + 5661961 * 2 ^ 59
def prefixEnd_5661961 : Nat := 4983230072969 + 3 ^ 40 * 5661961 * 2
def baseEnd_5661961 : Nat := 2907307440011427285248621

theorem tailTrace_5661961 : CollatzResearch.WordTrace tailWord_5661961 prefixEnd_5661961 2907307440011427285248621 := by
  unfold tailWord_5661961
  simp only [CollatzResearch.WordTrace]
  refine ⟨206508683040689757798225737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137672455360459838532150491 206508683040689757798225737)
  ·
    refine ⟨154881512280517318348669303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206508683040689757798225737 154881512280517318348669303)
    ·
      refine ⟨232322268420775977523003955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154881512280517318348669303 232322268420775977523003955)
      ·
        refine ⟨348483402631163966284505933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232322268420775977523003955 348483402631163966284505933)
        ·
          refine ⟨130681275986686487356689725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 348483402631163966284505933 130681275986686487356689725)
          ·
            refine ⟨49005478495007432758758647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130681275986686487356689725 49005478495007432758758647)
            ·
              refine ⟨73508217742511149138137971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49005478495007432758758647 73508217742511149138137971)
              ·
                refine ⟨110262326613766723707206957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73508217742511149138137971 110262326613766723707206957)
                ·
                  refine ⟨41348372480162521390202609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110262326613766723707206957 41348372480162521390202609)
                  ·
                    refine ⟨31011279360121891042651957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41348372480162521390202609 31011279360121891042651957)
                    ·
                      refine ⟨2907307440011427285248621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31011279360121891042651957 2907307440011427285248621)
                      ·
                        rfl

theorem cell23_5661961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_5661961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661961 prefixEnd_5661961 := by exact prefixLift 5661961
  have htrace : WordTrace (prefixWord ++ tailWord_5661961) baseStart_5661961 baseEnd_5661961 := by
    simpa [prefixWord, tailWord_5661961, baseEnd_5661961] using wordTrace_append hprefix tailTrace_5661961
  have hstable : (prefixWord ++ tailWord_5661961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661961).length < 2 ^ (prefixWord ++ tailWord_5661961).sum := by decide
  have hdescent : baseEnd_5661961 < baseStart_5661961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661971 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 4]
def baseStart_5661971 : Nat := 118140960795 + 5661971 * 2 ^ 59
def prefixEnd_5661971 : Nat := 4983230072969 + 3 ^ 40 * 5661971 * 2
def baseEnd_5661971 : Nat := 2907312574817972246123575

theorem tailTrace_5661971 : CollatzResearch.WordTrace tailWord_5661971 prefixEnd_5661971 2907312574817972246123575 := by
  unfold tailWord_5661971
  simp only [CollatzResearch.WordTrace]
  refine ⟨206509047770653529506089767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137672698513769019670726511 206509047770653529506089767)
  ·
    refine ⟨309763571655980294259134651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206509047770653529506089767 309763571655980294259134651)
    ·
      refine ⟨464645357483970441388701977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309763571655980294259134651 464645357483970441388701977)
      ·
        refine ⟨348484018112977831041526483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 464645357483970441388701977 348484018112977831041526483)
        ·
          refine ⟨522726027169466746562289725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348484018112977831041526483 522726027169466746562289725)
          ·
            refine ⟨196022260188550029960858647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 522726027169466746562289725 196022260188550029960858647)
            ·
              refine ⟨294033390282825044941287971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196022260188550029960858647 294033390282825044941287971)
              ·
                refine ⟨441050085424237567411931957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294033390282825044941287971 441050085424237567411931957)
                ·
                  refine ⟨41348445508522271944868621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 441050085424237567411931957 41348445508522271944868621)
                  ·
                    refine ⟨15505667065695851979325733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41348445508522271944868621 15505667065695851979325733)
                    ·
                      refine ⟨2907312574817972246123575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15505667065695851979325733 2907312574817972246123575)
                      ·
                        rfl

theorem cell23_5661971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 4].length) (baseStart_5661971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661971 prefixEnd_5661971 := by exact prefixLift 5661971
  have htrace : WordTrace (prefixWord ++ tailWord_5661971) baseStart_5661971 baseEnd_5661971 := by
    simpa [prefixWord, tailWord_5661971, baseEnd_5661971] using wordTrace_append hprefix tailTrace_5661971
  have hstable : (prefixWord ++ tailWord_5661971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661971).length < 2 ^ (prefixWord ++ tailWord_5661971).sum := by decide
  have hdescent : baseEnd_5661971 < baseStart_5661971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661978 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5]
def baseStart_5661978 : Nat := 118140960795 + 5661978 * 2 ^ 59
def prefixEnd_5661978 : Nat := 4983230072969 + 3 ^ 40 * 5661978 * 2
def baseEnd_5661978 : Nat := 2907316169182553718736043

theorem tailTrace_5661978 : CollatzResearch.WordTrace tailWord_5661978 prefixEnd_5661978 2907316169182553718736043 := by
  unfold tailWord_5661978
  simp only [CollatzResearch.WordTrace]
  refine ⟨51627325770407042425398647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137672868721085446467729725 51627325770407042425398647)
  ·
    refine ⟨77440988655610563638097971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51627325770407042425398647 77440988655610563638097971)
    ·
      refine ⟨116161482983415845457146957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77440988655610563638097971 116161482983415845457146957)
      ·
        refine ⟨43560556118780942046430109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116161482983415845457146957 43560556118780942046430109)
        ·
          refine ⟨16335208544542853267411291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43560556118780942046430109 16335208544542853267411291)
          ·
            refine ⟨24502812816814279901116937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16335208544542853267411291 24502812816814279901116937)
            ·
              refine ⟨18377109612610709925837703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24502812816814279901116937 18377109612610709925837703)
              ·
                refine ⟨27565664418916064888756555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18377109612610709925837703 27565664418916064888756555)
                ·
                  refine ⟨41348496628374097333134833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27565664418916064888756555 41348496628374097333134833)
                  ·
                    refine ⟨31011372471280572999851125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41348496628374097333134833 31011372471280572999851125)
                    ·
                      refine ⟨2907316169182553718736043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31011372471280572999851125 2907316169182553718736043)
                      ·
                        rfl

theorem cell23_5661978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_5661978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661978 prefixEnd_5661978 := by exact prefixLift 5661978
  have htrace : WordTrace (prefixWord ++ tailWord_5661978) baseStart_5661978 baseEnd_5661978 := by
    simpa [prefixWord, tailWord_5661978, baseEnd_5661978] using wordTrace_append hprefix tailTrace_5661978
  have hstable : (prefixWord ++ tailWord_5661978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661978).length < 2 ^ (prefixWord ++ tailWord_5661978).sum := by decide
  have hdescent : baseEnd_5661978 < baseStart_5661978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5661988 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 1, 3, 4]
def baseStart_5661988 : Nat := 118140960795 + 5661988 * 2 ^ 59
def prefixEnd_5661988 : Nat := 4983230072969 + 3 ^ 40 * 5661988 * 2
def baseEnd_5661988 : Nat := 2907321303989098679610997

theorem tailTrace_5661988 : CollatzResearch.WordTrace tailWord_5661988 prefixEnd_5661988 2907321303989098679610997 := by
  unfold tailWord_5661988
  simp only [CollatzResearch.WordTrace]
  refine ⟨103254833905795970704729309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137673111874394627606305745 103254833905795970704729309)
  ·
    refine ⟨38720562714673489014273491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103254833905795970704729309 38720562714673489014273491)
    ·
      refine ⟨58080844072010233521410237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38720562714673489014273491 58080844072010233521410237)
      ·
        refine ⟨21780316527003837570528839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58080844072010233521410237 21780316527003837570528839)
        ·
          refine ⟨32670474790505756355793259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21780316527003837570528839 32670474790505756355793259)
          ·
            refine ⟨49005712185758634533689889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32670474790505756355793259 49005712185758634533689889)
            ·
              refine ⟨36754284139318975900267417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49005712185758634533689889 36754284139318975900267417)
              ·
                refine ⟨27565713104489231925200563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36754284139318975900267417 27565713104489231925200563)
                ·
                  refine ⟨41348569656733847887800845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27565713104489231925200563 41348569656733847887800845)
                  ·
                    refine ⟨15505713621275192957925317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41348569656733847887800845 15505713621275192957925317)
                    ·
                      refine ⟨2907321303989098679610997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15505713621275192957925317 2907321303989098679610997)
                      ·
                        rfl

theorem cell23_5661988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_5661988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5661988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5661988 prefixEnd_5661988 := by exact prefixLift 5661988
  have htrace : WordTrace (prefixWord ++ tailWord_5661988) baseStart_5661988 baseEnd_5661988 := by
    simpa [prefixWord, tailWord_5661988, baseEnd_5661988] using wordTrace_append hprefix tailTrace_5661988
  have hstable : (prefixWord ++ tailWord_5661988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5661988).length < 2 ^ (prefixWord ++ tailWord_5661988).sum := by decide
  have hdescent : baseEnd_5661988 < baseStart_5661988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5661988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662005 : List Nat := [1, 3, 3, 1, 2, 2, 3, 1, 2, 1, 4]
def baseStart_5662005 : Nat := 118140960795 + 5662005 * 2 ^ 59
def prefixEnd_5662005 : Nat := 4983230072969 + 3 ^ 40 * 5662005 * 2
def baseEnd_5662005 : Nat := 2907330033160225113098419

theorem tailTrace_5662005 : CollatzResearch.WordTrace tailWord_5662005 prefixEnd_5662005 2907330033160225113098419 := by
  unfold tailWord_5662005
  simp only [CollatzResearch.WordTrace]
  refine ⟨206510287852530353312827469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137673525235020235541884979 206510287852530353312827469)
  ·
    refine ⟨77441357944698882492310301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206510287852530353312827469 77441357944698882492310301)
    ·
      refine ⟨29040509229262080934616363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77441357944698882492310301 29040509229262080934616363)
      ·
        refine ⟨43560763843893121401924545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29040509229262080934616363 43560763843893121401924545)
        ·
          refine ⟨32670572882919841051443409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43560763843893121401924545 32670572882919841051443409)
          ·
            refine ⟨24502929662189880788582557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32670572882919841051443409 24502929662189880788582557)
            ·
              refine ⟨9188598623321205295718459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24502929662189880788582557 9188598623321205295718459)
              ·
                refine ⟨13782897934981807943577689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9188598623321205295718459 13782897934981807943577689)
                ·
                  refine ⟨10337173451236355957683267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13782897934981807943577689 10337173451236355957683267)
                  ·
                    refine ⟨15505760176854533936524901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10337173451236355957683267 15505760176854533936524901)
                    ·
                      refine ⟨2907330033160225113098419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15505760176854533936524901 2907330033160225113098419)
                      ·
                        rfl

theorem cell23_5662005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_5662005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662005 prefixEnd_5662005 := by exact prefixLift 5662005
  have htrace : WordTrace (prefixWord ++ tailWord_5662005) baseStart_5662005 baseEnd_5662005 := by
    simpa [prefixWord, tailWord_5662005, baseEnd_5662005] using wordTrace_append hprefix tailTrace_5662005
  have hstable : (prefixWord ++ tailWord_5662005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662005).length < 2 ^ (prefixWord ++ tailWord_5662005).sum := by decide
  have hdescent : baseEnd_5662005 < baseStart_5662005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662028 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 8]
def baseStart_5662028 : Nat := 118140960795 + 5662028 * 2 ^ 59
def prefixEnd_5662028 : Nat := 4983230072969 + 3 ^ 40 * 5662028 * 2
def baseEnd_5662028 : Nat := 323037982579475391456757

theorem tailTrace_5662028 : CollatzResearch.WordTrace tailWord_5662028 prefixEnd_5662028 323037982579475391456757 := by
  unfold tailWord_5662028
  simp only [CollatzResearch.WordTrace]
  refine ⟨103255563365723514120457369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137674084487631352160609825 103255563365723514120457369)
  ·
    refine ⟨77441672524292635590343027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103255563365723514120457369 77441672524292635590343027)
    ·
      refine ⟨116162508786438953385514541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77441672524292635590343027 116162508786438953385514541)
      ·
        refine ⟨43560940794914607519567953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116162508786438953385514541 43560940794914607519567953)
        ·
          refine ⟨32670705596185955639675965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43560940794914607519567953 32670705596185955639675965)
          ·
            refine ⟨12251514598569733364878487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32670705596185955639675965 12251514598569733364878487)
            ·
              refine ⟨18377271897854600047317731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12251514598569733364878487 18377271897854600047317731)
              ·
                refine ⟨27565907846781900070976597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18377271897854600047317731 27565907846781900070976597)
                ·
                  refine ⟨323037982579475391456757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27565907846781900070976597 323037982579475391456757)
                  ·
                    rfl

theorem cell23_5662028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 8].length) (baseStart_5662028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662028 prefixEnd_5662028 := by exact prefixLift 5662028
  have htrace : WordTrace (prefixWord ++ tailWord_5662028) baseStart_5662028 baseEnd_5662028 := by
    simpa [prefixWord, tailWord_5662028, baseEnd_5662028] using wordTrace_append hprefix tailTrace_5662028
  have hstable : (prefixWord ++ tailWord_5662028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662028).length < 2 ^ (prefixWord ++ tailWord_5662028).sum := by decide
  have hdescent : baseEnd_5662028 < baseStart_5662028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662065 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 1, 5, 2]
def baseStart_5662065 : Nat := 118140960795 + 5662065 * 2 ^ 59
def prefixEnd_5662065 : Nat := 4983230072969 + 3 ^ 40 * 5662065 * 2
def baseEnd_5662065 : Nat := 2907360841999494878348143

theorem tailTrace_5662065 : CollatzResearch.WordTrace tailWord_5662065 prefixEnd_5662065 2907360841999494878348143 := by
  unfold tailWord_5662065
  simp only [CollatzResearch.WordTrace]
  refine ⟨206512476232312983560011649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137674984154875322373341099 206512476232312983560011649)
  ·
    refine ⟨154884357174234737670008737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206512476232312983560011649 154884357174234737670008737)
    ·
      refine ⟨116163267880676053252506553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154884357174234737670008737 116163267880676053252506553)
      ·
        refine ⟨87122450910507039939379915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116163267880676053252506553 87122450910507039939379915)
        ·
          refine ⟨130683676365760559909069873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87122450910507039939379915 130683676365760559909069873)
          ·
            refine ⟨98012757274320419931802405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130683676365760559909069873 98012757274320419931802405)
            ·
              refine ⟨18377391988935078737212951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98012757274320419931802405 18377391988935078737212951)
              ·
                refine ⟨27566087983402618105819427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18377391988935078737212951 27566087983402618105819427)
                ·
                  refine ⟨41349131975103927158729141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27566087983402618105819427 41349131975103927158729141)
                  ·
                    refine ⟨3876481122665993171130857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41349131975103927158729141 3876481122665993171130857)
                    ·
                      refine ⟨2907360841999494878348143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3876481122665993171130857 2907360841999494878348143)
                      ·
                        rfl

theorem cell23_5662065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 5, 2].length) (baseStart_5662065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662065 prefixEnd_5662065 := by exact prefixLift 5662065
  have htrace : WordTrace (prefixWord ++ tailWord_5662065) baseStart_5662065 baseEnd_5662065 := by
    simpa [prefixWord, tailWord_5662065, baseEnd_5662065] using wordTrace_append hprefix tailTrace_5662065
  have hstable : (prefixWord ++ tailWord_5662065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662065).length < 2 ^ (prefixWord ++ tailWord_5662065).sum := by decide
  have hdescent : baseEnd_5662065 < baseStart_5662065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662089 : List Nat := [1, 2, 1, 1, 7, 2, 1, 1, 3, 1, 3]
def baseStart_5662089 : Nat := 118140960795 + 5662089 * 2 ^ 59
def prefixEnd_5662089 : Nat := 4983230072969 + 3 ^ 40 * 5662089 * 2
def baseEnd_5662089 : Nat := 2907373165535202784448033

theorem tailTrace_5662089 : CollatzResearch.WordTrace tailWord_5662089 prefixEnd_5662089 2907373165535202784448033 := by
  unfold tailWord_5662089
  simp only [CollatzResearch.WordTrace]
  refine ⟨206513351584226035658885321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137675567722817357105923547 206513351584226035658885321)
  ·
    refine ⟨154885013688169526744163991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206513351584226035658885321 154885013688169526744163991)
    ·
      refine ⟨232327520532254290116245987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154885013688169526744163991 232327520532254290116245987)
      ·
        refine ⟨348491280798381435174368981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232327520532254290116245987 348491280798381435174368981)
        ·
          refine ⟨8167764393712064886899273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 348491280798381435174368981 8167764393712064886899273)
          ·
            refine ⟨6125823295284048665174455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8167764393712064886899273 6125823295284048665174455)
            ·
              refine ⟨9188734942926072997761683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6125823295284048665174455 9188734942926072997761683)
              ·
                refine ⟨13783102414389109496642525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9188734942926072997761683 13783102414389109496642525)
                ·
                  refine ⟨5168663405395916061240947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13783102414389109496642525 5168663405395916061240947)
                  ·
                    refine ⟨7752995108093874091861421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5168663405395916061240947 7752995108093874091861421)
                    ·
                      refine ⟨2907373165535202784448033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7752995108093874091861421 2907373165535202784448033)
                      ·
                        rfl

theorem cell23_5662089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 1, 3].length) (baseStart_5662089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662089 prefixEnd_5662089 := by exact prefixLift 5662089
  have htrace : WordTrace (prefixWord ++ tailWord_5662089) baseStart_5662089 baseEnd_5662089 := by
    simpa [prefixWord, tailWord_5662089, baseEnd_5662089] using wordTrace_append hprefix tailTrace_5662089
  have hstable : (prefixWord ++ tailWord_5662089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662089).length < 2 ^ (prefixWord ++ tailWord_5662089).sum := by decide
  have hdescent : baseEnd_5662089 < baseStart_5662089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662112 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 5, 2, 2]
def baseStart_5662112 : Nat := 118140960795 + 5662112 * 2 ^ 59
def prefixEnd_5662112 : Nat := 4983230072969 + 3 ^ 40 * 5662112 * 2
def baseEnd_5662112 : Nat := 2907384975590256194460427

theorem tailTrace_5662112 : CollatzResearch.WordTrace tailWord_5662112 prefixEnd_5662112 2907384975590256194460427 := by
  unfold tailWord_5662112
  simp only [CollatzResearch.WordTrace]
  refine ⟨103257095231571355293486295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137676126975428473724648393 103257095231571355293486295)
  ·
    refine ⟨154885642847357032940229443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103257095231571355293486295 154885642847357032940229443)
    ·
      refine ⟨232328464271035549410344165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154885642847357032940229443 232328464271035549410344165)
      ·
        refine ⟨43561587050819165514439531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232328464271035549410344165 43561587050819165514439531)
        ·
          refine ⟨65342380576228748271659297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43561587050819165514439531 65342380576228748271659297)
          ·
            refine ⟨49006785432171561203744473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65342380576228748271659297 49006785432171561203744473)
            ·
              refine ⟨36755089074128670902808355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49006785432171561203744473 36755089074128670902808355)
              ·
                refine ⟨55132633611193006354212533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36755089074128670902808355 55132633611193006354212533)
                ·
                  refine ⟨5168684401049344345707425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55132633611193006354212533 5168684401049344345707425)
                  ·
                    refine ⟨3876513300787008259280569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5168684401049344345707425 3876513300787008259280569)
                    ·
                      refine ⟨2907384975590256194460427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3876513300787008259280569 2907384975590256194460427)
                      ·
                        rfl

theorem cell23_5662112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_5662112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662112 prefixEnd_5662112 := by exact prefixLift 5662112
  have htrace : WordTrace (prefixWord ++ tailWord_5662112) baseStart_5662112 baseEnd_5662112 := by
    simpa [prefixWord, tailWord_5662112, baseEnd_5662112] using wordTrace_append hprefix tailTrace_5662112
  have hstable : (prefixWord ++ tailWord_5662112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662112).length < 2 ^ (prefixWord ++ tailWord_5662112).sum := by decide
  have hdescent : baseEnd_5662112 < baseStart_5662112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662115 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 3]
def baseStart_5662115 : Nat := 118140960795 + 5662115 * 2 ^ 59
def prefixEnd_5662115 : Nat := 4983230072969 + 3 ^ 40 * 5662115 * 2
def baseEnd_5662115 : Nat := 2907386516032219682722913

theorem tailTrace_5662115 : CollatzResearch.WordTrace tailWord_5662115 prefixEnd_5662115 2907386516032219682722913 := by
  unfold tailWord_5662115
  simp only [CollatzResearch.WordTrace]
  refine ⟨206514299882131842099331799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137676199921421228066221199 206514299882131842099331799)
  ·
    refine ⟨309771449823197763148997699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206514299882131842099331799 309771449823197763148997699)
    ·
      refine ⟨464657174734796644723496549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309771449823197763148997699 464657174734796644723496549)
      ·
        refine ⟨87123220262774370885655603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 464657174734796644723496549 87123220262774370885655603)
        ·
          refine ⟨130684830394161556328483405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87123220262774370885655603 130684830394161556328483405)
          ·
            refine ⟨49006811397810583623181277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130684830394161556328483405 49006811397810583623181277)
            ·
              refine ⟨18377554274178968858692979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49006811397810583623181277 18377554274178968858692979)
              ·
                refine ⟨27566331411268453288039469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18377554274178968858692979 27566331411268453288039469)
                ·
                  refine ⟨10337374279225669983014801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27566331411268453288039469 10337374279225669983014801)
                  ·
                    refine ⟨7753030709419252487261101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10337374279225669983014801 7753030709419252487261101)
                    ·
                      refine ⟨2907386516032219682722913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7753030709419252487261101 2907386516032219682722913)
                      ·
                        rfl

theorem cell23_5662115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_5662115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662115 prefixEnd_5662115 := by exact prefixLift 5662115
  have htrace : WordTrace (prefixWord ++ tailWord_5662115) baseStart_5662115 baseEnd_5662115 := by
    simpa [prefixWord, tailWord_5662115, baseEnd_5662115] using wordTrace_append hprefix tailTrace_5662115
  have hstable : (prefixWord ++ tailWord_5662115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662115).length < 2 ^ (prefixWord ++ tailWord_5662115).sum := by decide
  have hdescent : baseEnd_5662115 < baseStart_5662115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662140 : List Nat := [2, 2, 2, 4, 3, 1, 2, 2, 1, 1, 3]
def baseStart_5662140 : Nat := 118140960795 + 5662140 * 2 ^ 59
def prefixEnd_5662140 : Nat := 4983230072969 + 3 ^ 40 * 5662140 * 2
def baseEnd_5662140 : Nat := 2907399353048582084910299

theorem tailTrace_5662140 : CollatzResearch.WordTrace tailWord_5662140 prefixEnd_5662140 2907399353048582084910299 := by
  unfold tailWord_5662140
  simp only [CollatzResearch.WordTrace]
  refine ⟨103257605853520635684495937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137676807804694180912661249 103257605853520635684495937)
  ·
    refine ⟨77443204390140476763371953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103257605853520635684495937 77443204390140476763371953)
    ·
      refine ⟨58082403292605357572528965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77443204390140476763371953 58082403292605357572528965)
      ·
        refine ⟨10890450617363504544849181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58082403292605357572528965 10890450617363504544849181)
        ·
          refine ⟨4083918981511314204318443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10890450617363504544849181 4083918981511314204318443)
          ·
            refine ⟨6125878472266971306477665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4083918981511314204318443 6125878472266971306477665)
            ·
              refine ⟨4594408854200228479858249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6125878472266971306477665 4594408854200228479858249)
              ·
                refine ⟨3445806640650171359893687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4594408854200228479858249 3445806640650171359893687)
                ·
                  refine ⟨5168709960975257039840531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3445806640650171359893687 5168709960975257039840531)
                  ·
                    refine ⟨7753064941462885559760797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5168709960975257039840531 7753064941462885559760797)
                    ·
                      refine ⟨2907399353048582084910299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7753064941462885559760797 2907399353048582084910299)
                      ·
                        rfl

theorem cell23_5662140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_5662140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662140 prefixEnd_5662140 := by exact prefixLift 5662140
  have htrace : WordTrace (prefixWord ++ tailWord_5662140) baseStart_5662140 baseEnd_5662140 := by
    simpa [prefixWord, tailWord_5662140, baseEnd_5662140] using wordTrace_append hprefix tailTrace_5662140
  have hstable : (prefixWord ++ tailWord_5662140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662140).length < 2 ^ (prefixWord ++ tailWord_5662140).sum := by decide
  have hdescent : baseEnd_5662140 < baseStart_5662140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662185 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 2, 8, 2]
def baseStart_5662185 : Nat := 118140960795 + 5662185 * 2 ^ 59
def prefixEnd_5662185 : Nat := 4983230072969 + 3 ^ 40 * 5662185 * 2
def baseEnd_5662185 : Nat := 2907422459678034408847591

theorem tailTrace_5662185 : CollatzResearch.WordTrace tailWord_5662185 prefixEnd_5662185 2907422459678034408847591 := by
  unfold tailWord_5662185
  simp only [CollatzResearch.WordTrace]
  refine ⟨206516852991878244054380009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137677901994585496036253339 206516852991878244054380009)
  ·
    refine ⟨154887639743908683040785007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206516852991878244054380009 154887639743908683040785007)
    ·
      refine ⟨232331459615863024561177511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154887639743908683040785007 232331459615863024561177511)
      ·
        refine ⟨348497189423794536841766267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232331459615863024561177511 348497189423794536841766267)
        ·
          refine ⟨522745784135691805262649401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348497189423794536841766267 522745784135691805262649401)
          ·
            refine ⟨392059338101768853946987051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 522745784135691805262649401 392059338101768853946987051)
            ·
              refine ⟨588089007152653280920480577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392059338101768853946987051 588089007152653280920480577)
              ·
                refine ⟨441066755364489960690360433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588089007152653280920480577 441066755364489960690360433)
                ·
                  refine ⟨330800066523367470517770325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441066755364489960690360433 330800066523367470517770325)
                  ·
                    refine ⟨3876563279570712545130121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 330800066523367470517770325 3876563279570712545130121)
                    ·
                      refine ⟨2907422459678034408847591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3876563279570712545130121 2907422459678034408847591)
                      ·
                        rfl

theorem cell23_5662185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 8, 2].length) (baseStart_5662185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662185 prefixEnd_5662185 := by exact prefixLift 5662185
  have htrace : WordTrace (prefixWord ++ tailWord_5662185) baseStart_5662185 baseEnd_5662185 := by
    simpa [prefixWord, tailWord_5662185, baseEnd_5662185] using wordTrace_append hprefix tailTrace_5662185
  have hstable : (prefixWord ++ tailWord_5662185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662185).length < 2 ^ (prefixWord ++ tailWord_5662185).sum := by decide
  have hdescent : baseEnd_5662185 < baseStart_5662185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662259 : List Nat := [1, 1, 1, 2, 4, 4, 3, 2, 5]
def baseStart_5662259 : Nat := 118140960795 + 5662259 * 2 ^ 59
def prefixEnd_5662259 : Nat := 4983230072969 + 3 ^ 40 * 5662259 * 2
def baseEnd_5662259 : Nat := 323051161916274124369139

theorem tailTrace_5662259 : CollatzResearch.WordTrace tailWord_5662259 prefixEnd_5662259 323051161916274124369139 := by
  unfold tailWord_5662259
  simp only [CollatzResearch.WordTrace]
  refine ⟨206519551993610154692573831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137679701329073436461715887 206519551993610154692573831)
  ·
    refine ⟨309779327990415232038860747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206519551993610154692573831 309779327990415232038860747)
    ·
      refine ⟨464668991985622848058291121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309779327990415232038860747 464668991985622848058291121)
      ·
        refine ⟨348501743989217136043718341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 464668991985622848058291121 348501743989217136043718341)
        ·
          refine ⟨65344076997978213008197189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 348501743989217136043718341 65344076997978213008197189)
          ·
            refine ⟨12252014437120914939036973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65344076997978213008197189 12252014437120914939036973)
            ·
              refine ⟨4594505413920343102138865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12252014437120914939036973 4594505413920343102138865)
              ·
                refine ⟨3445879060440257326604149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4594505413920343102138865 3445879060440257326604149)
                ·
                  refine ⟨323051161916274124369139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3445879060440257326604149 323051161916274124369139)
                  ·
                    rfl

theorem cell23_5662259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 5].length) (baseStart_5662259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662259 prefixEnd_5662259 := by exact prefixLift 5662259
  have htrace : WordTrace (prefixWord ++ tailWord_5662259) baseStart_5662259 baseEnd_5662259 := by
    simpa [prefixWord, tailWord_5662259, baseEnd_5662259] using wordTrace_append hprefix tailTrace_5662259
  have hstable : (prefixWord ++ tailWord_5662259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662259).length < 2 ^ (prefixWord ++ tailWord_5662259).sum := by decide
  have hdescent : baseEnd_5662259 < baseStart_5662259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662265 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 1, 1, 7]
def baseStart_5662265 : Nat := 118140960795 + 5662265 * 2 ^ 59
def prefixEnd_5662265 : Nat := 4983230072969 + 3 ^ 40 * 5662265 * 2
def baseEnd_5662265 : Nat := 2907463538130394095847223

theorem tailTrace_5662265 : CollatzResearch.WordTrace tailWord_5662265 prefixEnd_5662265 2907463538130394095847223 := by
  unfold tailWord_5662265
  simp only [CollatzResearch.WordTrace]
  refine ⟨206519770831588417717292249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137679847221058945144861499 206519770831588417717292249)
  ·
    refine ⟨154889828123691313287969187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206519770831588417717292249 154889828123691313287969187)
    ·
      refine ⟨232334742185536969931953781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154889828123691313287969187 232334742185536969931953781)
      ·
        refine ⟨21781382079894090931120667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 232334742185536969931953781 21781382079894090931120667)
        ·
          refine ⟨32672073119841136396681001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21781382079894090931120667 32672073119841136396681001)
          ·
            refine ⟨24504054839880852297510751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32672073119841136396681001 24504054839880852297510751)
            ·
              refine ⟨36756082259821278446266127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24504054839880852297510751 36756082259821278446266127)
              ·
                refine ⟨55134123389731917669399191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36756082259821278446266127 55134123389731917669399191)
                ·
                  refine ⟨82701185084597876504098787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55134123389731917669399191 82701185084597876504098787)
                  ·
                    refine ⟨124051777626896814756148181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82701185084597876504098787 124051777626896814756148181)
                    ·
                      refine ⟨2907463538130394095847223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124051777626896814756148181 2907463538130394095847223)
                      ·
                        rfl

theorem cell23_5662265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_5662265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662265 prefixEnd_5662265 := by exact prefixLift 5662265
  have htrace : WordTrace (prefixWord ++ tailWord_5662265) baseStart_5662265 baseEnd_5662265 := by
    simpa [prefixWord, tailWord_5662265, baseEnd_5662265] using wordTrace_append hprefix tailTrace_5662265
  have hstable : (prefixWord ++ tailWord_5662265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662265).length < 2 ^ (prefixWord ++ tailWord_5662265).sum := by decide
  have hdescent : baseEnd_5662265 < baseStart_5662265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662305 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 2, 1, 6]
def baseStart_5662305 : Nat := 118140960795 + 5662305 * 2 ^ 59
def prefixEnd_5662305 : Nat := 4983230072969 + 3 ^ 40 * 5662305 * 2
def baseEnd_5662305 : Nat := 2907484077356573939347039

theorem tailTrace_5662305 : CollatzResearch.WordTrace tailWord_5662305 prefixEnd_5662305 2907484077356573939347039 := by
  unfold tailWord_5662305
  simp only [CollatzResearch.WordTrace]
  refine ⟨206521229751443504548748369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137680819834295669699165579 206521229751443504548748369)
  ·
    refine ⟨154890922313582628411561277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206521229751443504548748369 154890922313582628411561277)
    ·
      refine ⟨58084095867593485654335479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154890922313582628411561277 58084095867593485654335479)
      ·
        refine ⟨87126143801390228481503219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58084095867593485654335479 87126143801390228481503219)
        ·
          refine ⟨130689215702085342722254829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87126143801390228481503219 130689215702085342722254829)
          ·
            refine ⟨49008455888282003520845561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130689215702085342722254829 49008455888282003520845561)
            ·
              refine ⟨36756341916211502640634171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49008455888282003520845561 36756341916211502640634171)
              ·
                refine ⟨55134512874317253960951257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36756341916211502640634171 55134512874317253960951257)
                ·
                  refine ⟨41350884655737940470713443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55134512874317253960951257 41350884655737940470713443)
                  ·
                    refine ⟨62026326983606910706070165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41350884655737940470713443 62026326983606910706070165)
                    ·
                      refine ⟨2907484077356573939347039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62026326983606910706070165 2907484077356573939347039)
                      ·
                        rfl

theorem cell23_5662305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_5662305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662305 prefixEnd_5662305 := by exact prefixLift 5662305
  have htrace : WordTrace (prefixWord ++ tailWord_5662305) baseStart_5662305 baseEnd_5662305 := by
    simpa [prefixWord, tailWord_5662305, baseEnd_5662305] using wordTrace_append hprefix tailTrace_5662305
  have hstable : (prefixWord ++ tailWord_5662305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662305).length < 2 ^ (prefixWord ++ tailWord_5662305).sum := by decide
  have hdescent : baseEnd_5662305 < baseStart_5662305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662326 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2]
def baseStart_5662326 : Nat := 118140960795 + 5662326 * 2 ^ 59
def prefixEnd_5662326 : Nat := 4983230072969 + 3 ^ 40 * 5662326 * 2
def baseEnd_5662326 : Nat := 2907494860450318357184443

theorem tailTrace_5662326 : CollatzResearch.WordTrace tailWord_5662326 prefixEnd_5662326 2907494860450318357184443 := by
  unfold tailWord_5662326
  simp only [CollatzResearch.WordTrace]
  refine ⟨12907624730272964070953927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137681330456244950090175221 12907624730272964070953927)
  ·
    refine ⟨19361437095409446106430891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12907624730272964070953927 19361437095409446106430891)
    ·
      refine ⟨29042155643114169159646337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19361437095409446106430891 29042155643114169159646337)
      ·
        refine ⟨21781616732335626869734753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29042155643114169159646337 21781616732335626869734753)
        ·
          refine ⟨16336212549251720152301065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21781616732335626869734753 16336212549251720152301065)
          ·
            refine ⟨12252159411938790114225799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16336212549251720152301065 12252159411938790114225799)
            ·
              refine ⟨18378239117908185171338699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12252159411938790114225799 18378239117908185171338699)
              ·
                refine ⟨27567358676862277757008049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18378239117908185171338699 27567358676862277757008049)
                ·
                  refine ⟨20675519007646708317756037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27567358676862277757008049 20675519007646708317756037)
                  ·
                    refine ⟨3876659813933757809579257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20675519007646708317756037 3876659813933757809579257)
                    ·
                      refine ⟨2907494860450318357184443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3876659813933757809579257 2907494860450318357184443)
                      ·
                        rfl

theorem cell23_5662326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_5662326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662326 prefixEnd_5662326 := by exact prefixLift 5662326
  have htrace : WordTrace (prefixWord ++ tailWord_5662326) baseStart_5662326 baseEnd_5662326 := by
    simpa [prefixWord, tailWord_5662326, baseEnd_5662326] using wordTrace_append hprefix tailTrace_5662326
  have hstable : (prefixWord ++ tailWord_5662326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662326).length < 2 ^ (prefixWord ++ tailWord_5662326).sum := by decide
  have hdescent : baseEnd_5662326 < baseStart_5662326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662346 : List Nat := [3, 1, 2, 3, 2, 3, 1, 1, 2, 2, 3]
def baseStart_5662346 : Nat := 118140960795 + 5662346 * 2 ^ 59
def prefixEnd_5662346 : Nat := 4983230072969 + 3 ^ 40 * 5662346 * 2
def baseEnd_5662346 : Nat := 2907505130063408278934351

theorem tailTrace_5662346 : CollatzResearch.WordTrace tailWord_5662346 prefixEnd_5662346 2907505130063408278934351 := by
  unfold tailWord_5662346
  simp only [CollatzResearch.WordTrace]
  refine ⟨51630681286073742137747723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137681816762863312367327261 51630681286073742137747723)
  ·
    refine ⟨77446021929110613206621585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51630681286073742137747723 77446021929110613206621585)
    ·
      refine ⟨58084516446832959904966189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77446021929110613206621585 58084516446832959904966189)
      ·
        refine ⟨21781693667562359964362321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58084516446832959904966189 21781693667562359964362321)
        ·
          refine ⟨16336270250671769973271741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21781693667562359964362321 16336270250671769973271741)
          ·
            refine ⟨6126101344001913739976903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16336270250671769973271741 6126101344001913739976903)
            ·
              refine ⟨9189152016002870609965355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6126101344001913739976903 9189152016002870609965355)
              ·
                refine ⟨13783728024004305914948033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9189152016002870609965355 13783728024004305914948033)
                ·
                  refine ⟨10337796018003229436211025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13783728024004305914948033 10337796018003229436211025)
                  ·
                    refine ⟨7753347013502422077158269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10337796018003229436211025 7753347013502422077158269)
                    ·
                      refine ⟨2907505130063408278934351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7753347013502422077158269 2907505130063408278934351)
                      ·
                        rfl

theorem cell23_5662346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_5662346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662346 prefixEnd_5662346 := by exact prefixLift 5662346
  have htrace : WordTrace (prefixWord ++ tailWord_5662346) baseStart_5662346 baseEnd_5662346 := by
    simpa [prefixWord, tailWord_5662346, baseEnd_5662346] using wordTrace_append hprefix tailTrace_5662346
  have hstable : (prefixWord ++ tailWord_5662346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662346).length < 2 ^ (prefixWord ++ tailWord_5662346).sum := by decide
  have hdescent : baseEnd_5662346 < baseStart_5662346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662366 : List Nat := [4, 3, 1, 1, 1, 4, 1, 2, 6]
def baseStart_5662366 : Nat := 118140960795 + 5662366 * 2 ^ 59
def prefixEnd_5662366 : Nat := 4983230072969 + 3 ^ 40 * 5662366 * 2
def baseEnd_5662366 : Nat := 323057266630722022298251

theorem tailTrace_5662366 : CollatzResearch.WordTrace tailWord_5662366 prefixEnd_5662366 323057266630722022298251 := by
  unfold tailWord_5662366
  simp only [CollatzResearch.WordTrace]
  refine ⟨25815431825527813995839869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137682303069481674644479301 25815431825527813995839869)
  ·
    refine ⟨9680786934572930248439951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25815431825527813995839869 9680786934572930248439951)
    ·
      refine ⟨14521180401859395372659927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9680786934572930248439951 14521180401859395372659927)
      ·
        refine ⟨21781770602789093058989891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14521180401859395372659927 21781770602789093058989891)
        ·
          refine ⟨32672655904183639588484837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21781770602789093058989891 32672655904183639588484837)
          ·
            refine ⟨6126122982034432422840907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32672655904183639588484837 6126122982034432422840907)
            ·
              refine ⟨9189184473051648634261361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6126122982034432422840907 9189184473051648634261361)
              ·
                refine ⟨6891888354788736475696021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9189184473051648634261361 6891888354788736475696021)
                ·
                  refine ⟨323057266630722022298251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6891888354788736475696021 323057266630722022298251)
                  ·
                    rfl

theorem cell23_5662366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_5662366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662366 prefixEnd_5662366 := by exact prefixLift 5662366
  have htrace : WordTrace (prefixWord ++ tailWord_5662366) baseStart_5662366 baseEnd_5662366 := by
    simpa [prefixWord, tailWord_5662366, baseEnd_5662366] using wordTrace_append hprefix tailTrace_5662366
  have hstable : (prefixWord ++ tailWord_5662366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662366).length < 2 ^ (prefixWord ++ tailWord_5662366).sum := by decide
  have hdescent : baseEnd_5662366 < baseStart_5662366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662399 : List Nat := [1, 1, 2, 2, 2, 3, 4, 2, 1, 1, 4]
def baseStart_5662399 : Nat := 118140960795 + 5662399 * 2 ^ 59
def prefixEnd_5662399 : Nat := 4983230072969 + 3 ^ 40 * 5662399 * 2
def baseEnd_5662399 : Nat := 2907532344538096571571607

theorem tailTrace_5662399 : CollatzResearch.WordTrace tailWord_5662399 prefixEnd_5662399 2907532344538096571571607 := by
  unfold tailWord_5662399
  simp only [CollatzResearch.WordTrace]
  refine ⟨206524658213102958602670251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137683105475401972401780167 206524658213102958602670251)
  ·
    refine ⟨309786987319654437904005377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206524658213102958602670251 309786987319654437904005377)
    ·
      refine ⟨232340240489740828428004033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309786987319654437904005377 232340240489740828428004033)
      ·
        refine ⟨174255180367305621321003025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232340240489740828428004033 174255180367305621321003025)
        ·
          refine ⟨130691385275479215990752269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174255180367305621321003025 130691385275479215990752269)
          ·
            refine ⟨49009269478304705996532101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130691385275479215990752269 49009269478304705996532101)
            ·
              refine ⟨9189238027182132374349769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49009269478304705996532101 9189238027182132374349769)
              ·
                refine ⟨6891928520386599280762327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9189238027182132374349769 6891928520386599280762327)
                ·
                  refine ⟨10337892780579898921143491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6891928520386599280762327 10337892780579898921143491)
                  ·
                    refine ⟨15506839170869848381715237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10337892780579898921143491 15506839170869848381715237)
                    ·
                      refine ⟨2907532344538096571571607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15506839170869848381715237 2907532344538096571571607)
                      ·
                        rfl

theorem cell23_5662399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 1, 4].length) (baseStart_5662399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662399 prefixEnd_5662399 := by exact prefixLift 5662399
  have htrace : WordTrace (prefixWord ++ tailWord_5662399) baseStart_5662399 baseEnd_5662399 := by
    simpa [prefixWord, tailWord_5662399, baseEnd_5662399] using wordTrace_append hprefix tailTrace_5662399
  have hstable : (prefixWord ++ tailWord_5662399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662399).length < 2 ^ (prefixWord ++ tailWord_5662399).sum := by decide
  have hdescent : baseEnd_5662399 < baseStart_5662399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662405 : List Nat := [1, 3, 1, 1, 1, 1, 2, 13]
def baseStart_5662405 : Nat := 118140960795 + 5662405 * 2 ^ 59
def prefixEnd_5662405 : Nat := 4983230072969 + 3 ^ 40 * 5662405 * 2
def baseEnd_5662405 : Nat := 107686497237852724003577

theorem tailTrace_5662405 : CollatzResearch.WordTrace tailWord_5662405 prefixEnd_5662405 107686497237852724003577 := by
  unfold tailWord_5662405
  simp only [CollatzResearch.WordTrace]
  refine ⟨206524877051081221627388669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137683251367387481084925779 206524877051081221627388669)
  ·
    refine ⟨77446828894155458110270751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206524877051081221627388669 77446828894155458110270751)
    ·
      refine ⟨116170243341233187165406127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77446828894155458110270751 116170243341233187165406127)
      ·
        refine ⟨174255365011849780748109191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116170243341233187165406127 174255365011849780748109191)
        ·
          refine ⟨261383047517774671122163787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174255365011849780748109191 261383047517774671122163787)
          ·
            refine ⟨392074571276662006683245681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261383047517774671122163787 392074571276662006683245681)
            ·
              refine ⟨294055928457496505012434261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 392074571276662006683245681 294055928457496505012434261)
              ·
                refine ⟨107686497237852724003577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 294055928457496505012434261 107686497237852724003577)
                ·
                  rfl

theorem cell23_5662405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 13].length) (baseStart_5662405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662405 prefixEnd_5662405 := by exact prefixLift 5662405
  have htrace : WordTrace (prefixWord ++ tailWord_5662405) baseStart_5662405 baseEnd_5662405 := by
    simpa [prefixWord, tailWord_5662405, baseEnd_5662405] using wordTrace_append hprefix tailTrace_5662405
  have hstable : (prefixWord ++ tailWord_5662405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662405).length < 2 ^ (prefixWord ++ tailWord_5662405).sum := by decide
  have hdescent : baseEnd_5662405 < baseStart_5662405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662410 : List Nat := [3, 1, 2, 1, 5, 2, 1, 3, 1, 1, 3]
def baseStart_5662410 : Nat := 118140960795 + 5662410 * 2 ^ 59
def prefixEnd_5662410 : Nat := 4983230072969 + 3 ^ 40 * 5662410 * 2
def baseEnd_5662410 : Nat := 2907537992825296028534057

theorem tailTrace_5662410 : CollatzResearch.WordTrace tailWord_5662410 prefixEnd_5662410 2907537992825296028534057 := by
  unfold tailWord_5662410
  simp only [CollatzResearch.WordTrace]
  refine ⟨51631264854015776870330171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137683372944042071654213789 51631264854015776870330171)
  ·
    refine ⟨77446897281023665305495257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51631264854015776870330171 77446897281023665305495257)
    ·
      refine ⟨58085172960767748979121443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77446897281023665305495257 58085172960767748979121443)
      ·
        refine ⟨87127759441151623468682165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58085172960767748979121443 87127759441151623468682165)
        ·
          refine ⟨8168227447607964700188953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87127759441151623468682165 8168227447607964700188953)
          ·
            refine ⟨6126170585705973525141715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8168227447607964700188953 6126170585705973525141715)
            ·
              refine ⟨9189255878558960287712573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6126170585705973525141715 9189255878558960287712573)
              ·
                refine ⟨3445970954459610107892215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9189255878558960287712573 3445970954459610107892215)
                ·
                  refine ⟨5168956431689415161838323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3445970954459610107892215 5168956431689415161838323)
                  ·
                    refine ⟨7753434647534122742757485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5168956431689415161838323 7753434647534122742757485)
                    ·
                      refine ⟨2907537992825296028534057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7753434647534122742757485 2907537992825296028534057)
                      ·
                        rfl

theorem cell23_5662410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 1, 1, 3].length) (baseStart_5662410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662410 prefixEnd_5662410 := by exact prefixLift 5662410
  have htrace : WordTrace (prefixWord ++ tailWord_5662410) baseStart_5662410 baseEnd_5662410 := by
    simpa [prefixWord, tailWord_5662410, baseEnd_5662410] using wordTrace_append hprefix tailTrace_5662410
  have hstable : (prefixWord ++ tailWord_5662410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662410).length < 2 ^ (prefixWord ++ tailWord_5662410).sum := by decide
  have hdescent : baseEnd_5662410 < baseStart_5662410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662466 : List Nat := [3, 4, 1, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_5662466 : Nat := 118140960795 + 5662466 * 2 ^ 59
def prefixEnd_5662466 : Nat := 4983230072969 + 3 ^ 40 * 5662466 * 2
def baseEnd_5662466 : Nat := 2907566747741947809433799

theorem tailTrace_5662466 : CollatzResearch.WordTrace tailWord_5662466 prefixEnd_5662466 2907566747741947809433799 := by
  unfold tailWord_5662466
  simp only [CollatzResearch.WordTrace]
  refine ⟨51631775475965057261339813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137684734602573486030239501 51631775475965057261339813)
  ·
    refine ⟨9680957901743448236501215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51631775475965057261339813 9680957901743448236501215)
    ·
      refine ⟨14521436852615172354751823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9680957901743448236501215 14521436852615172354751823)
      ·
        refine ⟨21782155278922758532127735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14521436852615172354751823 21782155278922758532127735)
        ·
          refine ⟨32673232918384137798191603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21782155278922758532127735 32673232918384137798191603)
          ·
            refine ⟨49009849377576206697287405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32673232918384137798191603 49009849377576206697287405)
            ·
              refine ⟨18378693516591077511482777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49009849377576206697287405 18378693516591077511482777)
              ·
                refine ⟨13784020137443308133612083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18378693516591077511482777 13784020137443308133612083)
                ·
                  refine ⟨20676030206164962200418125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13784020137443308133612083 20676030206164962200418125)
                  ·
                    refine ⟨7753511327311860825156797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20676030206164962200418125 7753511327311860825156797)
                    ·
                      refine ⟨2907566747741947809433799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7753511327311860825156797 2907566747741947809433799)
                      ·
                        rfl

theorem cell23_5662466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_5662466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662466 prefixEnd_5662466 := by exact prefixLift 5662466
  have htrace : WordTrace (prefixWord ++ tailWord_5662466) baseStart_5662466 baseEnd_5662466 := by
    simpa [prefixWord, tailWord_5662466, baseEnd_5662466] using wordTrace_append hprefix tailTrace_5662466
  have hstable : (prefixWord ++ tailWord_5662466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662466).length < 2 ^ (prefixWord ++ tailWord_5662466).sum := by decide
  have hdescent : baseEnd_5662466 < baseStart_5662466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662476 : List Nat := [2, 2, 1, 2, 2, 1, 2, 5, 1, 3, 2]
def baseStart_5662476 : Nat := 118140960795 + 5662476 * 2 ^ 59
def prefixEnd_5662476 : Nat := 4983230072969 + 3 ^ 40 * 5662476 * 2
def baseEnd_5662476 : Nat := 2907571882548492770308753

theorem tailTrace_5662476 : CollatzResearch.WordTrace tailWord_5662476 prefixEnd_5662476 2907571882548492770308753 := by
  unfold tailWord_5662476
  simp only [CollatzResearch.WordTrace]
  refine ⟨103263733316912000376611641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137684977755882667168815521 103263733316912000376611641)
  ·
    refine ⟨77447799987684000282458731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103263733316912000376611641 77447799987684000282458731)
    ·
      refine ⟨116171699981526000423688097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77447799987684000282458731 116171699981526000423688097)
      ·
        refine ⟨87128774986144500317766073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116171699981526000423688097 87128774986144500317766073)
        ·
          refine ⟨65346581239608375238324555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87128774986144500317766073 65346581239608375238324555)
          ·
            refine ⟨98019871859412562857486833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65346581239608375238324555 98019871859412562857486833)
            ·
              refine ⟨73514903894559422143115125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98019871859412562857486833 73514903894559422143115125)
              ·
                refine ⟨6892022240114945825917043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73514903894559422143115125 6892022240114945825917043)
                ·
                  refine ⟨10338033360172418738875565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6892022240114945825917043 10338033360172418738875565)
                  ·
                    refine ⟨3876762510064657027078337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10338033360172418738875565 3876762510064657027078337)
                    ·
                      refine ⟨2907571882548492770308753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3876762510064657027078337 2907571882548492770308753)
                      ·
                        rfl

theorem cell23_5662476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 1, 3, 2].length) (baseStart_5662476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662476 prefixEnd_5662476 := by exact prefixLift 5662476
  have htrace : WordTrace (prefixWord ++ tailWord_5662476) baseStart_5662476 baseEnd_5662476 := by
    simpa [prefixWord, tailWord_5662476, baseEnd_5662476] using wordTrace_append hprefix tailTrace_5662476
  have hstable : (prefixWord ++ tailWord_5662476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662476).length < 2 ^ (prefixWord ++ tailWord_5662476).sum := by decide
  have hdescent : baseEnd_5662476 < baseStart_5662476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662527 : List Nat := [1, 1, 2, 2, 7, 1, 2, 1, 1, 3, 2]
def baseStart_5662527 : Nat := 118140960795 + 5662527 * 2 ^ 59
def prefixEnd_5662527 : Nat := 4983230072969 + 3 ^ 40 * 5662527 * 2
def baseEnd_5662527 : Nat := 2907598070061872070771019

theorem tailTrace_5662527 : CollatzResearch.WordTrace tailWord_5662527 prefixEnd_5662527 2907598070061872070771019 := by
  unfold tailWord_5662527
  simp only [CollatzResearch.WordTrace]
  refine ⟨206529326756639236463329835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137686217837759490975553223 206529326756639236463329835)
  ·
    refine ⟨309793990134958854694994753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206529326756639236463329835 309793990134958854694994753)
    ·
      refine ⟨232345492601219141021246065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309793990134958854694994753 232345492601219141021246065)
      ·
        refine ⟨174259119450914355765934549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232345492601219141021246065 174259119450914355765934549)
        ·
          refine ⟨4084198112130805213264091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 174259119450914355765934549 4084198112130805213264091)
          ·
            refine ⟨6126297168196207819896137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4084198112130805213264091 6126297168196207819896137)
            ·
              refine ⟨4594722876147155864922103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6126297168196207819896137 4594722876147155864922103)
              ·
                refine ⟨6892084314220733797383155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4594722876147155864922103 6892084314220733797383155)
                ·
                  refine ⟨10338126471331100696074733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6892084314220733797383155 10338126471331100696074733)
                  ·
                    refine ⟨3876797426749162761028025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10338126471331100696074733 3876797426749162761028025)
                    ·
                      refine ⟨2907598070061872070771019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3876797426749162761028025 2907598070061872070771019)
                      ·
                        rfl

theorem cell23_5662527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 1, 3, 2].length) (baseStart_5662527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662527 prefixEnd_5662527 := by exact prefixLift 5662527
  have htrace : WordTrace (prefixWord ++ tailWord_5662527) baseStart_5662527 baseEnd_5662527 := by
    simpa [prefixWord, tailWord_5662527, baseEnd_5662527] using wordTrace_append hprefix tailTrace_5662527
  have hstable : (prefixWord ++ tailWord_5662527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662527).length < 2 ^ (prefixWord ++ tailWord_5662527).sum := by decide
  have hdescent : baseEnd_5662527 < baseStart_5662527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662546 : List Nat := [3, 2, 2, 1, 1, 3, 2, 4, 5]
def baseStart_5662546 : Nat := 118140960795 + 5662546 * 2 ^ 59
def prefixEnd_5662546 : Nat := 4983230072969 + 3 ^ 40 * 5662546 * 2
def baseEnd_5662546 : Nat := 323067536243811944048159

theorem tailTrace_5662546 : CollatzResearch.WordTrace tailWord_5662546 prefixEnd_5662546 323067536243811944048159 := by
  unfold tailWord_5662546
  simp only [CollatzResearch.WordTrace]
  refine ⟨51632504935892600677067873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137686679829046935138847661 51632504935892600677067873)
  ·
    refine ⟨38724378701919450507800905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51632504935892600677067873 38724378701919450507800905)
    ·
      refine ⟨29043284026439587880850679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38724378701919450507800905 29043284026439587880850679)
      ·
        refine ⟨43564926039659381821276019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29043284026439587880850679 43564926039659381821276019)
        ·
          refine ⟨65347389059489072731914029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43564926039659381821276019 65347389059489072731914029)
          ·
            refine ⟨24505270897308402274467761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65347389059489072731914029 24505270897308402274467761)
            ·
              refine ⟨18378953172981301705850821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24505270897308402274467761 18378953172981301705850821)
              ·
                refine ⟨3446053719933994069847029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18378953172981301705850821 3446053719933994069847029)
                ·
                  refine ⟨323067536243811944048159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3446053719933994069847029 323067536243811944048159)
                  ·
                    rfl

theorem cell23_5662546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_5662546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662546 prefixEnd_5662546 := by exact prefixLift 5662546
  have htrace : WordTrace (prefixWord ++ tailWord_5662546) baseStart_5662546 baseEnd_5662546 := by
    simpa [prefixWord, tailWord_5662546, baseEnd_5662546] using wordTrace_append hprefix tailTrace_5662546
  have hstable : (prefixWord ++ tailWord_5662546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662546).length < 2 ^ (prefixWord ++ tailWord_5662546).sum := by decide
  have hdescent : baseEnd_5662546 < baseStart_5662546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662579 : List Nat := [1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 4]
def baseStart_5662579 : Nat := 118140960795 + 5662579 * 2 ^ 59
def prefixEnd_5662579 : Nat := 4983230072969 + 3 ^ 40 * 5662579 * 2
def baseEnd_5662579 : Nat := 2907624771055905867320779

theorem tailTrace_5662579 : CollatzResearch.WordTrace tailWord_5662579 prefixEnd_5662579 2907624771055905867320779 := by
  unfold tailWord_5662579
  simp only [CollatzResearch.WordTrace]
  refine ⟨206531223352450849344222791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137687482234967232896148527 206531223352450849344222791)
  ·
    refine ⟨309796835028676274016334187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206531223352450849344222791 309796835028676274016334187)
    ·
      refine ⟨464695252543014411024501281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309796835028676274016334187 464695252543014411024501281)
      ·
        refine ⟨348521439407260808268375961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 464695252543014411024501281 348521439407260808268375961)
        ·
          refine ⟨261391079555445606201281971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348521439407260808268375961 261391079555445606201281971)
          ·
            refine ⟨392086619333168409301922957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261391079555445606201281971 392086619333168409301922957)
            ·
              refine ⟨147032482249938153488221109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 392086619333168409301922957 147032482249938153488221109)
              ·
                refine ⟨13784295210931701889520729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 147032482249938153488221109 13784295210931701889520729)
                ·
                  refine ⟨10338221408198776417140547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13784295210931701889520729 10338221408198776417140547)
                  ·
                    refine ⟨15507332112298164625710821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10338221408198776417140547 15507332112298164625710821)
                    ·
                      refine ⟨2907624771055905867320779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15507332112298164625710821 2907624771055905867320779)
                      ·
                        rfl

theorem cell23_5662579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 4].length) (baseStart_5662579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662579 prefixEnd_5662579 := by exact prefixLift 5662579
  have htrace : WordTrace (prefixWord ++ tailWord_5662579) baseStart_5662579 baseEnd_5662579 := by
    simpa [prefixWord, tailWord_5662579, baseEnd_5662579] using wordTrace_append hprefix tailTrace_5662579
  have hstable : (prefixWord ++ tailWord_5662579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662579).length < 2 ^ (prefixWord ++ tailWord_5662579).sum := by decide
  have hdescent : baseEnd_5662579 < baseStart_5662579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662593 : List Nat := [1, 2, 4, 4, 1, 1, 1, 2, 2, 5]
def baseStart_5662593 : Nat := 118140960795 + 5662593 * 2 ^ 59
def prefixEnd_5662593 : Nat := 4983230072969 + 3 ^ 40 * 5662593 * 2
def baseEnd_5662593 : Nat := 969210653261689604181905

theorem tailTrace_5662593 : CollatzResearch.WordTrace tailWord_5662593 prefixEnd_5662593 969210653261689604181905 := by
  unfold tailWord_5662593
  simp only [CollatzResearch.WordTrace]
  refine ⟨206531733974400129735232433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137687822649600086490154955 206531733974400129735232433)
  ·
    refine ⟨154898800480800097301424325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206531733974400129735232433 154898800480800097301424325)
    ·
      refine ⟨29043525090150018244017061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154898800480800097301424325 29043525090150018244017061)
      ·
        refine ⟨5445660954403128420753199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29043525090150018244017061 5445660954403128420753199)
        ·
          refine ⟨8168491431604692631129799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5445660954403128420753199 8168491431604692631129799)
          ·
            refine ⟨12252737147407038946694699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8168491431604692631129799 12252737147407038946694699)
            ·
              refine ⟨18379105721110558420042049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12252737147407038946694699 18379105721110558420042049)
              ·
                refine ⟨13784329290832918815031537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18379105721110558420042049 13784329290832918815031537)
                ·
                  refine ⟨10338246968124689111273653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13784329290832918815031537 10338246968124689111273653)
                  ·
                    refine ⟨969210653261689604181905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10338246968124689111273653 969210653261689604181905)
                    ·
                      rfl

theorem cell23_5662593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_5662593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662593 prefixEnd_5662593 := by exact prefixLift 5662593
  have htrace : WordTrace (prefixWord ++ tailWord_5662593) baseStart_5662593 baseEnd_5662593 := by
    simpa [prefixWord, tailWord_5662593, baseEnd_5662593] using wordTrace_append hprefix tailTrace_5662593
  have hstable : (prefixWord ++ tailWord_5662593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662593).length < 2 ^ (prefixWord ++ tailWord_5662593).sum := by decide
  have hdescent : baseEnd_5662593 < baseStart_5662593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662596 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 4, 4, 2]
def baseStart_5662596 : Nat := 118140960795 + 5662596 * 2 ^ 59
def prefixEnd_5662596 : Nat := 4983230072969 + 3 ^ 40 * 5662596 * 2
def baseEnd_5662596 : Nat := 2907633500227032300808201

theorem tailTrace_5662596 : CollatzResearch.WordTrace tailWord_5662596 prefixEnd_5662596 2907633500227032300808201 := by
  unfold tailWord_5662596
  simp only [CollatzResearch.WordTrace]
  refine ⟨103265921696694630623795821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137687895595592840831727761 103265921696694630623795821)
  ·
    refine ⟨38724720636260486483923433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103265921696694630623795821 38724720636260486483923433)
    ·
      refine ⟨29043540477195364862942575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38724720636260486483923433 29043540477195364862942575)
      ·
        refine ⟨43565310715793047294413863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29043540477195364862942575 43565310715793047294413863)
        ·
          refine ⟨65347966073689570941620795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43565310715793047294413863 65347966073689570941620795)
          ·
            refine ⟨98021949110534356412431193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65347966073689570941620795 98021949110534356412431193)
            ·
              refine ⟨73516461832900767309323395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98021949110534356412431193 73516461832900767309323395)
              ·
                refine ⟨110274692749351150963985093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73516461832900767309323395 110274692749351150963985093)
                ·
                  refine ⟨20676504890503340805747205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110274692749351150963985093 20676504890503340805747205)
                  ·
                    refine ⟨3876844666969376401077601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20676504890503340805747205 3876844666969376401077601)
                    ·
                      refine ⟨2907633500227032300808201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3876844666969376401077601 2907633500227032300808201)
                      ·
                        rfl

theorem cell23_5662596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_5662596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662596 prefixEnd_5662596 := by exact prefixLift 5662596
  have htrace : WordTrace (prefixWord ++ tailWord_5662596) baseStart_5662596 baseEnd_5662596 := by
    simpa [prefixWord, tailWord_5662596, baseEnd_5662596] using wordTrace_append hprefix tailTrace_5662596
  have hstable : (prefixWord ++ tailWord_5662596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662596).length < 2 ^ (prefixWord ++ tailWord_5662596).sum := by decide
  have hdescent : baseEnd_5662596 < baseStart_5662596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662629 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 2, 5, 3]
def baseStart_5662629 : Nat := 118140960795 + 5662629 * 2 ^ 59
def prefixEnd_5662629 : Nat := 4983230072969 + 3 ^ 40 * 5662629 * 2
def baseEnd_5662629 : Nat := 2907650445088630671695549

theorem tailTrace_5662629 : CollatzResearch.WordTrace tailWord_5662629 prefixEnd_5662629 2907650445088630671695549 := by
  unfold tailWord_5662629
  simp only [CollatzResearch.WordTrace]
  refine ⟨206533047002269707883542941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137688698001513138589028627 206533047002269707883542941)
  ·
    refine ⟨77449892625851140456328603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206533047002269707883542941 77449892625851140456328603)
    ·
      refine ⟨116174838938776710684492905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77449892625851140456328603 116174838938776710684492905)
      ·
        refine ⟨87131129204082533013369679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116174838938776710684492905 87131129204082533013369679)
        ·
          refine ⟨130696693806123799520054519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87131129204082533013369679 130696693806123799520054519)
          ·
            refine ⟨196045040709185699280081779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130696693806123799520054519 196045040709185699280081779)
            ·
              refine ⟨294067561063778548920122669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196045040709185699280081779 294067561063778548920122669)
              ·
                refine ⟨110275335398916955845046001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 294067561063778548920122669 110275335398916955845046001)
                ·
                  refine ⟨82706501549187716883784501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110275335398916955845046001 82706501549187716883784501)
                  ·
                    refine ⟨7753734520236348457854797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82706501549187716883784501 7753734520236348457854797)
                    ·
                      refine ⟨2907650445088630671695549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7753734520236348457854797 2907650445088630671695549)
                      ·
                        rfl

theorem cell23_5662629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_5662629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662629 prefixEnd_5662629 := by exact prefixLift 5662629
  have htrace : WordTrace (prefixWord ++ tailWord_5662629) baseStart_5662629 baseEnd_5662629 := by
    simpa [prefixWord, tailWord_5662629, baseEnd_5662629] using wordTrace_append hprefix tailTrace_5662629
  have hstable : (prefixWord ++ tailWord_5662629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662629).length < 2 ^ (prefixWord ++ tailWord_5662629).sum := by decide
  have hdescent : baseEnd_5662629 < baseStart_5662629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662684 : List Nat := [2, 2, 6, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_5662684 : Nat := 118140960795 + 5662684 * 2 ^ 59
def prefixEnd_5662684 : Nat := 4983230072969 + 3 ^ 40 * 5662684 * 2
def baseEnd_5662684 : Nat := 2907678686524627956507797

theorem tailTrace_5662684 : CollatzResearch.WordTrace tailWord_5662684 prefixEnd_5662684 2907678686524627956507797 := by
  unfold tailWord_5662684
  simp only [CollatzResearch.WordTrace]
  refine ⟨103267526508535226138397553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137690035344713634851196737 103267526508535226138397553)
  ·
    refine ⟨77450644881401419603798165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103267526508535226138397553 77450644881401419603798165)
    ·
      refine ⟨3630498978815691543928039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 77450644881401419603798165 3630498978815691543928039)
      ·
        refine ⟨5445748468223537315892059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3630498978815691543928039 5445748468223537315892059)
        ·
          refine ⟨8168622702335305973838089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5445748468223537315892059 8168622702335305973838089)
          ·
            refine ⟨6126467026751479480378567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8168622702335305973838089 6126467026751479480378567)
            ·
              refine ⟨9189700540127219220567851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6126467026751479480378567 9189700540127219220567851)
              ·
                refine ⟨13784550810190828830851777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9189700540127219220567851 13784550810190828830851777)
                ·
                  refine ⟨10338413107643121623138833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13784550810190828830851777 10338413107643121623138833)
                  ·
                    refine ⟨7753809830732341217354125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10338413107643121623138833 7753809830732341217354125)
                    ·
                      refine ⟨2907678686524627956507797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7753809830732341217354125 2907678686524627956507797)
                      ·
                        rfl

theorem cell23_5662684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_5662684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662684 prefixEnd_5662684 := by exact prefixLift 5662684
  have htrace : WordTrace (prefixWord ++ tailWord_5662684) baseStart_5662684 baseEnd_5662684 := by
    simpa [prefixWord, tailWord_5662684, baseEnd_5662684] using wordTrace_append hprefix tailTrace_5662684
  have hstable : (prefixWord ++ tailWord_5662684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662684).length < 2 ^ (prefixWord ++ tailWord_5662684).sum := by decide
  have hdescent : baseEnd_5662684 < baseStart_5662684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662696 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 4, 4]
def baseStart_5662696 : Nat := 118140960795 + 5662696 * 2 ^ 59
def prefixEnd_5662696 : Nat := 4983230072969 + 3 ^ 40 * 5662696 * 2
def baseEnd_5662696 : Nat := 969228282764160636519247

theorem tailTrace_5662696 : CollatzResearch.WordTrace tailWord_5662696 prefixEnd_5662696 969228282764160636519247 := by
  unfold tailWord_5662696
  simp only [CollatzResearch.WordTrace]
  refine ⟨103267745346513489163115971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137690327128684652217487961 103267745346513489163115971)
  ·
    refine ⟨154901618019770233744673957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103267745346513489163115971 154901618019770233744673957)
    ·
      refine ⟨29044053378706918827126367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154901618019770233744673957 29044053378706918827126367)
      ·
        refine ⟨43566080068060378240689551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29044053378706918827126367 43566080068060378240689551)
        ·
          refine ⟨65349120102090567361034327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43566080068060378240689551 65349120102090567361034327)
          ·
            refine ⟨98023680153135851041551491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65349120102090567361034327 98023680153135851041551491)
            ·
              refine ⟨147035520229703776562327237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98023680153135851041551491 147035520229703776562327237)
              ·
                refine ⟨27569160043069458105436357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147035520229703776562327237 27569160043069458105436357)
                ·
                  refine ⟨5169217508075523394769317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27569160043069458105436357 5169217508075523394769317)
                  ·
                    refine ⟨969228282764160636519247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5169217508075523394769317 969228282764160636519247)
                    ·
                      rfl

theorem cell23_5662696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_5662696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662696 prefixEnd_5662696 := by exact prefixLift 5662696
  have htrace : WordTrace (prefixWord ++ tailWord_5662696) baseStart_5662696 baseEnd_5662696 := by
    simpa [prefixWord, tailWord_5662696, baseEnd_5662696] using wordTrace_append hprefix tailTrace_5662696
  have hstable : (prefixWord ++ tailWord_5662696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662696).length < 2 ^ (prefixWord ++ tailWord_5662696).sum := by decide
  have hdescent : baseEnd_5662696 < baseStart_5662696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662703 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 5, 2, 2]
def baseStart_5662703 : Nat := 118140960795 + 5662703 * 2 ^ 59
def prefixEnd_5662703 : Nat := 4983230072969 + 3 ^ 40 * 5662703 * 2
def baseEnd_5662703 : Nat := 2907688442657063382170209

theorem tailTrace_5662703 : CollatzResearch.WordTrace tailWord_5662703 prefixEnd_5662703 2907688442657063382170209 := by
  unfold tailWord_5662703
  simp only [CollatzResearch.WordTrace]
  refine ⟨206535746004001618521736763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137690497336001079014491175 206535746004001618521736763)
  ·
    refine ⟨309803619006002427782605145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206535746004001618521736763 309803619006002427782605145)
    ·
      refine ⟨232352714254501820836953859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309803619006002427782605145 232352714254501820836953859)
      ·
        refine ⟨348529071381752731255430789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232352714254501820836953859 348529071381752731255430789)
        ·
          refine ⟨65349200884078637110393273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 348529071381752731255430789 65349200884078637110393273)
          ·
            refine ⟨49011900663058977832794955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65349200884078637110393273 49011900663058977832794955)
            ·
              refine ⟨73517850994588466749192433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49011900663058977832794955 73517850994588466749192433)
              ·
                refine ⟨55138388245941350061894325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73517850994588466749192433 55138388245941350061894325)
                ·
                  refine ⟨5169223898057001568302593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55138388245941350061894325 5169223898057001568302593)
                  ·
                    refine ⟨3876917923542751176226945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5169223898057001568302593 3876917923542751176226945)
                    ·
                      refine ⟨2907688442657063382170209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3876917923542751176226945 2907688442657063382170209)
                      ·
                        rfl

theorem cell23_5662703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 2, 2].length) (baseStart_5662703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662703 prefixEnd_5662703 := by exact prefixLift 5662703
  have htrace : WordTrace (prefixWord ++ tailWord_5662703) baseStart_5662703 baseEnd_5662703 := by
    simpa [prefixWord, tailWord_5662703, baseEnd_5662703] using wordTrace_append hprefix tailTrace_5662703
  have hstable : (prefixWord ++ tailWord_5662703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662703).length < 2 ^ (prefixWord ++ tailWord_5662703).sum := by decide
  have hdescent : baseEnd_5662703 < baseStart_5662703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662713 : List Nat := [1, 2, 1, 3, 1, 4, 3, 2, 2, 4]
def baseStart_5662713 : Nat := 118140960795 + 5662713 * 2 ^ 59
def prefixEnd_5662713 : Nat := 4983230072969 + 3 ^ 40 * 5662713 * 2
def baseEnd_5662713 : Nat := 969231192487869447681721

theorem tailTrace_5662713 : CollatzResearch.WordTrace tailWord_5662713 prefixEnd_5662713 969231192487869447681721 := by
  unfold tailWord_5662713
  simp only [CollatzResearch.WordTrace]
  refine ⟨206536110733965390229600793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137690740489310260153067195 206536110733965390229600793)
  ·
    refine ⟨154902083050474042672200595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206536110733965390229600793 154902083050474042672200595)
    ·
      refine ⟨232353124575711064008300893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154902083050474042672200595 232353124575711064008300893)
      ·
        refine ⟨87132421715891649003112835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232353124575711064008300893 87132421715891649003112835)
        ·
          refine ⟨130698632573837473504669253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87132421715891649003112835 130698632573837473504669253)
          ·
            refine ⟨24505993607594526282125485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130698632573837473504669253 24505993607594526282125485)
            ·
              refine ⟨9189747602847947355797057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24505993607594526282125485 9189747602847947355797057)
              ·
                refine ⟨6892310702135960516847793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9189747602847947355797057 6892310702135960516847793)
                ·
                  refine ⟨5169233026601970387635845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6892310702135960516847793 5169233026601970387635845)
                  ·
                    refine ⟨969231192487869447681721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5169233026601970387635845 969231192487869447681721)
                    ·
                      rfl

theorem cell23_5662713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 4].length) (baseStart_5662713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662713 prefixEnd_5662713 := by exact prefixLift 5662713
  have htrace : WordTrace (prefixWord ++ tailWord_5662713) baseStart_5662713 baseEnd_5662713 := by
    simpa [prefixWord, tailWord_5662713, baseEnd_5662713] using wordTrace_append hprefix tailTrace_5662713
  have hstable : (prefixWord ++ tailWord_5662713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662713).length < 2 ^ (prefixWord ++ tailWord_5662713).sum := by decide
  have hdescent : baseEnd_5662713 < baseStart_5662713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662730 : List Nat := [3, 1, 2, 2, 5, 1, 1, 1, 1, 6]
def baseStart_5662730 : Nat := 118140960795 + 5662730 * 2 ^ 59
def prefixEnd_5662730 : Nat := 4983230072969 + 3 ^ 40 * 5662730 * 2
def baseEnd_5662730 : Nat := 969234102211578258844195

theorem tailTrace_5662730 : CollatzResearch.WordTrace tailWord_5662730 prefixEnd_5662730 969234102211578258844195 := by
  unfold tailWord_5662730
  simp only [CollatzResearch.WordTrace]
  refine ⟨51634182693725950533242411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137691153849935868088646429 51634182693725950533242411)
  ·
    refine ⟨77451274040588925799863617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51634182693725950533242411 77451274040588925799863617)
    ·
      refine ⟨58088455530441694349897713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77451274040588925799863617 58088455530441694349897713)
      ·
        refine ⟨43566341647831270762423285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58088455530441694349897713 43566341647831270762423285)
        ·
          refine ⟨4084344529484181633977183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43566341647831270762423285 4084344529484181633977183)
          ·
            refine ⟨6126516794226272450965775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4084344529484181633977183 6126516794226272450965775)
            ·
              refine ⟨9189775191339408676448663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6126516794226272450965775 9189775191339408676448663)
              ·
                refine ⟨13784662787009113014672995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9189775191339408676448663 13784662787009113014672995)
                ·
                  refine ⟨20676994180513669522009493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13784662787009113014672995 20676994180513669522009493)
                  ·
                    refine ⟨969234102211578258844195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20676994180513669522009493 969234102211578258844195)
                    ·
                      rfl

theorem cell23_5662730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_5662730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662730 prefixEnd_5662730 := by exact prefixLift 5662730
  have htrace : WordTrace (prefixWord ++ tailWord_5662730) baseStart_5662730 baseEnd_5662730 := by
    simpa [prefixWord, tailWord_5662730, baseEnd_5662730] using wordTrace_append hprefix tailTrace_5662730
  have hstable : (prefixWord ++ tailWord_5662730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662730).length < 2 ^ (prefixWord ++ tailWord_5662730).sum := by decide
  have hdescent : baseEnd_5662730 < baseStart_5662730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662739 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 2, 7]
def baseStart_5662739 : Nat := 118140960795 + 5662739 * 2 ^ 59
def prefixEnd_5662739 : Nat := 4983230072969 + 3 ^ 40 * 5662739 * 2
def baseEnd_5662739 : Nat := 969235642653541747106681

theorem tailTrace_5662739 : CollatzResearch.WordTrace tailWord_5662739 prefixEnd_5662739 969235642653541747106681 := by
  unfold tailWord_5662739
  simp only [CollatzResearch.WordTrace]
  refine ⟨206537059031871196670047271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137691372687914131113364847 206537059031871196670047271)
  ·
    refine ⟨309805588547806795005070907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206537059031871196670047271 309805588547806795005070907)
    ·
      refine ⟨464708382821710192507606361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309805588547806795005070907 464708382821710192507606361)
      ·
        refine ⟨348531287116282644380704771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 464708382821710192507606361 348531287116282644380704771)
        ·
          refine ⟨522796930674423966571057157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348531287116282644380704771 522796930674423966571057157)
          ·
            refine ⟨98024424501454493732073217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 522796930674423966571057157 98024424501454493732073217)
            ·
              refine ⟨73518318376090870299054913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98024424501454493732073217 73518318376090870299054913)
              ·
                refine ⟨55138738782068152724291185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73518318376090870299054913 55138738782068152724291185)
                ·
                  refine ⟨41354054086551114543218389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55138738782068152724291185 41354054086551114543218389)
                  ·
                    refine ⟨969235642653541747106681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41354054086551114543218389 969235642653541747106681)
                    ·
                      rfl

theorem cell23_5662739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 7].length) (baseStart_5662739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662739 prefixEnd_5662739 := by exact prefixLift 5662739
  have htrace : WordTrace (prefixWord ++ tailWord_5662739) baseStart_5662739 baseEnd_5662739 := by
    simpa [prefixWord, tailWord_5662739, baseEnd_5662739] using wordTrace_append hprefix tailTrace_5662739
  have hstable : (prefixWord ++ tailWord_5662739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662739).length < 2 ^ (prefixWord ++ tailWord_5662739).sum := by decide
  have hdescent : baseEnd_5662739 < baseStart_5662739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662760 : List Nat := [2, 1, 5, 3, 2, 1, 9]
def baseStart_5662760 : Nat := 118140960795 + 5662760 * 2 ^ 59
def prefixEnd_5662760 : Nat := 4983230072969 + 3 ^ 40 * 5662760 * 2
def baseEnd_5662760 : Nat := 35897749519189748878487

theorem tailTrace_5662760 : CollatzResearch.WordTrace tailWord_5662760 prefixEnd_5662760 35897749519189748878487 := by
  unfold tailWord_5662760
  simp only [CollatzResearch.WordTrace]
  refine ⟨103268912482397558628280867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137691883309863411504374489 103268912482397558628280867)
  ·
    refine ⟨154903368723596337942421301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103268912482397558628280867 154903368723596337942421301)
    ·
      refine ⟨14522190817837156682101997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154903368723596337942421301 14522190817837156682101997)
      ·
        refine ⟨5445821556688933755788249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14522190817837156682101997 5445821556688933755788249)
        ·
          refine ⟨4084366167516700316841187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5445821556688933755788249 4084366167516700316841187)
          ·
            refine ⟨6126549251275050475261781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4084366167516700316841187 6126549251275050475261781)
            ·
              refine ⟨35897749519189748878487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6126549251275050475261781 35897749519189748878487)
              ·
                rfl

theorem cell23_5662760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 9].length) (baseStart_5662760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662760 prefixEnd_5662760 := by exact prefixLift 5662760
  have htrace : WordTrace (prefixWord ++ tailWord_5662760) baseStart_5662760 baseEnd_5662760 := by
    simpa [prefixWord, tailWord_5662760, baseEnd_5662760] using wordTrace_append hprefix tailTrace_5662760
  have hstable : (prefixWord ++ tailWord_5662760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662760).length < 2 ^ (prefixWord ++ tailWord_5662760).sum := by decide
  have hdescent : baseEnd_5662760 < baseStart_5662760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662793 : List Nat := [1, 2, 1, 1, 2, 2, 4, 3, 1, 4, 2]
def baseStart_5662793 : Nat := 118140960795 + 5662793 * 2 ^ 59
def prefixEnd_5662793 : Nat := 4983230072969 + 3 ^ 40 * 5662793 * 2
def baseEnd_5662793 : Nat := 2907734655915968030044795

theorem tailTrace_5662793 : CollatzResearch.WordTrace tailWord_5662793 prefixEnd_5662793 2907734655915968030044795 := by
  unfold tailWord_5662793
  simp only [CollatzResearch.WordTrace]
  refine ⟨206539028573675563892513033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137692685715783709261675355 206539028573675563892513033)
  ·
    refine ⟨154904271430256672919384775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206539028573675563892513033 154904271430256672919384775)
    ·
      refine ⟨232356407145385009379077163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154904271430256672919384775 232356407145385009379077163)
      ·
        refine ⟨348534610718077514068615745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232356407145385009379077163 348534610718077514068615745)
        ·
          refine ⟨261400958038558135551461809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348534610718077514068615745 261400958038558135551461809)
          ·
            refine ⟨196050718528918601663596357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261400958038558135551461809 196050718528918601663596357)
            ·
              refine ⟨36759509724172237811924317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196050718528918601663596357 36759509724172237811924317)
              ·
                refine ⟨13784816146564589179471619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36759509724172237811924317 13784816146564589179471619)
                ·
                  refine ⟨20677224219846883769207429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13784816146564589179471619 20677224219846883769207429)
                  ·
                    refine ⟨3876979541221290706726393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20677224219846883769207429 3876979541221290706726393)
                    ·
                      refine ⟨2907734655915968030044795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3876979541221290706726393 2907734655915968030044795)
                      ·
                        rfl

theorem cell23_5662793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 4, 2].length) (baseStart_5662793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662793 prefixEnd_5662793 := by exact prefixLift 5662793
  have htrace : WordTrace (prefixWord ++ tailWord_5662793) baseStart_5662793 baseEnd_5662793 := by
    simpa [prefixWord, tailWord_5662793, baseEnd_5662793] using wordTrace_append hprefix tailTrace_5662793
  have hstable : (prefixWord ++ tailWord_5662793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662793).length < 2 ^ (prefixWord ++ tailWord_5662793).sum := by decide
  have hdescent : baseEnd_5662793 < baseStart_5662793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662796 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 2, 1, 5]
def baseStart_5662796 : Nat := 118140960795 + 5662796 * 2 ^ 59
def prefixEnd_5662796 : Nat := 4983230072969 + 3 ^ 40 * 5662796 * 2
def baseEnd_5662796 : Nat := 2907736196357931518307281

theorem tailTrace_5662796 : CollatzResearch.WordTrace tailWord_5662796 prefixEnd_5662796 2907736196357931518307281 := by
  unfold tailWord_5662796
  simp only [CollatzResearch.WordTrace]
  refine ⟨103269568996332347702436121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137692758661776463603248161 103269568996332347702436121)
  ·
    refine ⟨77452176747249260776827091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103269568996332347702436121 77452176747249260776827091)
    ·
      refine ⟨116178265120873891165240637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77452176747249260776827091 116178265120873891165240637)
      ·
        refine ⟨43566849420327709186965239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116178265120873891165240637 43566849420327709186965239)
        ·
          refine ⟨65350274130491563780447859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43566849420327709186965239 65350274130491563780447859)
          ·
            refine ⟨98025411195737345670671789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65350274130491563780447859 98025411195737345670671789)
            ·
              refine ⟨36759529198401504626501921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98025411195737345670671789 36759529198401504626501921)
              ·
                refine ⟨27569646898801128469876441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36759529198401504626501921 27569646898801128469876441)
                ·
                  refine ⟨20677235174100846352407331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27569646898801128469876441 20677235174100846352407331)
                  ·
                    refine ⟨31015852761151269528610997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20677235174100846352407331 31015852761151269528610997)
                    ·
                      refine ⟨2907736196357931518307281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31015852761151269528610997 2907736196357931518307281)
                      ·
                        rfl

theorem cell23_5662796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_5662796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662796 prefixEnd_5662796 := by exact prefixLift 5662796
  have htrace : WordTrace (prefixWord ++ tailWord_5662796) baseStart_5662796 baseEnd_5662796 := by
    simpa [prefixWord, tailWord_5662796, baseEnd_5662796] using wordTrace_append hprefix tailTrace_5662796
  have hstable : (prefixWord ++ tailWord_5662796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662796).length < 2 ^ (prefixWord ++ tailWord_5662796).sum := by decide
  have hdescent : baseEnd_5662796 < baseStart_5662796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662833 : List Nat := [1, 2, 2, 2, 1, 1, 5, 4, 5]
def baseStart_5662833 : Nat := 118140960795 + 5662833 * 2 ^ 59
def prefixEnd_5662833 : Nat := 4983230072969 + 3 ^ 40 * 5662833 * 2
def baseEnd_5662833 : Nat := 323083910571349763727179

theorem tailTrace_5662833 : CollatzResearch.WordTrace tailWord_5662833 prefixEnd_5662833 323083910571349763727179 := by
  unfold tailWord_5662833
  simp only [CollatzResearch.WordTrace]
  refine ⟨206540487493530650723969153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137693658329020433815979435 206540487493530650723969153)
  ·
    refine ⟨154905365620147988042976865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206540487493530650723969153 154905365620147988042976865)
    ·
      refine ⟨116179024215110991032232649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154905365620147988042976865 116179024215110991032232649)
      ·
        refine ⟨87134268161333243274174487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116179024215110991032232649 87134268161333243274174487)
        ·
          refine ⟨130701402241999864911261731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87134268161333243274174487 130701402241999864911261731)
          ·
            refine ⟨196052103362999797366892597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130701402241999864911261731 196052103362999797366892597)
            ·
              refine ⟨18379884690281231003146181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 196052103362999797366892597 18379884690281231003146181)
              ·
                refine ⟨3446228379427730813089909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18379884690281231003146181 3446228379427730813089909)
                ·
                  refine ⟨323083910571349763727179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3446228379427730813089909 323083910571349763727179)
                  ·
                    rfl

theorem cell23_5662833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 5].length) (baseStart_5662833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662833 prefixEnd_5662833 := by exact prefixLift 5662833
  have htrace : WordTrace (prefixWord ++ tailWord_5662833) baseStart_5662833 baseEnd_5662833 := by
    simpa [prefixWord, tailWord_5662833, baseEnd_5662833] using wordTrace_append hprefix tailTrace_5662833
  have hstable : (prefixWord ++ tailWord_5662833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662833).length < 2 ^ (prefixWord ++ tailWord_5662833).sum := by decide
  have hdescent : baseEnd_5662833 < baseStart_5662833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662878 : List Nat := [4, 3, 1, 1, 4, 1, 1, 2, 2, 2, 2]
def baseStart_5662878 : Nat := 118140960795 + 5662878 * 2 ^ 59
def prefixEnd_5662878 : Nat := 4983230072969 + 3 ^ 40 * 5662878 * 2
def baseEnd_5662878 : Nat := 2907778301771600197481905

theorem tailTrace_5662878 : CollatzResearch.WordTrace tailWord_5662878 prefixEnd_5662878 2907778301771600197481905 := by
  unfold tailWord_5662878
  simp only [CollatzResearch.WordTrace]
  refine ⟨25817766097295952926169661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137694752518911748939571525 25817766097295952926169661)
  ·
    refine ⟨9681662286485982347313623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25817766097295952926169661 9681662286485982347313623)
    ·
      refine ⟨14522493429728973520970435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9681662286485982347313623 14522493429728973520970435)
      ·
        refine ⟨21783740144593460281455653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14522493429728973520970435 21783740144593460281455653)
        ·
          refine ⟨4084451277111273802772935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21783740144593460281455653 4084451277111273802772935)
          ·
            refine ⟨6126676915666910704159403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4084451277111273802772935 6126676915666910704159403)
            ·
              refine ⟨9190015373500366056239105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6126676915666910704159403 9190015373500366056239105)
              ·
                refine ⟨6892511530125274542179329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9190015373500366056239105 6892511530125274542179329)
                ·
                  refine ⟨5169383647593955906634497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6892511530125274542179329 5169383647593955906634497)
                  ·
                    refine ⟨3877037735695466929975873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5169383647593955906634497 3877037735695466929975873)
                    ·
                      refine ⟨2907778301771600197481905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3877037735695466929975873 2907778301771600197481905)
                      ·
                        rfl

theorem cell23_5662878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_5662878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662878 prefixEnd_5662878 := by exact prefixLift 5662878
  have htrace : WordTrace (prefixWord ++ tailWord_5662878) baseStart_5662878 baseEnd_5662878 := by
    simpa [prefixWord, tailWord_5662878, baseEnd_5662878] using wordTrace_append hprefix tailTrace_5662878
  have hstable : (prefixWord ++ tailWord_5662878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662878).length < 2 ^ (prefixWord ++ tailWord_5662878).sum := by decide
  have hdescent : baseEnd_5662878 < baseStart_5662878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662896 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 4]
def baseStart_5662896 : Nat := 118140960795 + 5662896 * 2 ^ 59
def prefixEnd_5662896 : Nat := 4983230072969 + 3 ^ 40 * 5662896 * 2
def baseEnd_5662896 : Nat := 2907787544423381127056821

theorem tailTrace_5662896 : CollatzResearch.WordTrace tailWord_5662896 prefixEnd_5662896 2907787544423381127056821 := by
  unfold tailWord_5662896
  simp only [CollatzResearch.WordTrace]
  refine ⟨103271392646151206241756271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137695190194868274989008361 103271392646151206241756271)
  ·
    refine ⟨154907088969226809362634407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103271392646151206241756271 154907088969226809362634407)
    ·
      refine ⟨232360633453840214043951611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154907088969226809362634407 232360633453840214043951611)
      ·
        refine ⟨348540950180760321065927417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232360633453840214043951611 348540950180760321065927417)
        ·
          refine ⟨261405712635570240799445563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348540950180760321065927417 261405712635570240799445563)
          ·
            refine ⟨392108568953355361199168345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261405712635570240799445563 392108568953355361199168345)
            ·
              refine ⟨294081426715016520899376259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 392108568953355361199168345 294081426715016520899376259)
              ·
                refine ⟨441122140072524781349064389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294081426715016520899376259 441122140072524781349064389)
                ·
                  refine ⟨82710401263598396502949573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 441122140072524781349064389 82710401263598396502949573)
                  ·
                    refine ⟨15508200236924699344303045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82710401263598396502949573 15508200236924699344303045)
                    ·
                      refine ⟨2907787544423381127056821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15508200236924699344303045 2907787544423381127056821)
                      ·
                        rfl

theorem cell23_5662896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 4].length) (baseStart_5662896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662896 prefixEnd_5662896 := by exact prefixLift 5662896
  have htrace : WordTrace (prefixWord ++ tailWord_5662896) baseStart_5662896 baseEnd_5662896 := by
    simpa [prefixWord, tailWord_5662896, baseEnd_5662896] using wordTrace_append hprefix tailTrace_5662896
  have hstable : (prefixWord ++ tailWord_5662896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662896).length < 2 ^ (prefixWord ++ tailWord_5662896).sum := by decide
  have hdescent : baseEnd_5662896 < baseStart_5662896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662903 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 3]
def baseStart_5662903 : Nat := 118140960795 + 5662903 * 2 ^ 59
def prefixEnd_5662903 : Nat := 4983230072969 + 3 ^ 40 * 5662903 * 2
def baseEnd_5662903 : Nat := 2907791138787962599669289

theorem tailTrace_5662903 : CollatzResearch.WordTrace tailWord_5662903 prefixEnd_5662903 2907791138787962599669289 := by
  unfold tailWord_5662903
  simp only [CollatzResearch.WordTrace]
  refine ⟨206543040603277052679017363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137695360402184701786011575 206543040603277052679017363)
  ·
    refine ⟨309814560904915579018526045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206543040603277052679017363 309814560904915579018526045)
    ·
      refine ⟨116180460339343342131947267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 309814560904915579018526045 116180460339343342131947267)
      ·
        refine ⟨174270690509015013197920901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116180460339343342131947267 174270690509015013197920901)
        ·
          refine ⟨32675754470440314974610169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174270690509015013197920901 32675754470440314974610169)
          ·
            refine ⟨24506815852830236230957627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32675754470440314974610169 24506815852830236230957627)
            ·
              refine ⟨36760223779245354346436441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24506815852830236230957627 36760223779245354346436441)
              ·
                refine ⟨27570167834434015759827331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36760223779245354346436441 27570167834434015759827331)
                ·
                  refine ⟨41355251751651023639740997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27570167834434015759827331 41355251751651023639740997)
                  ·
                    refine ⟨7754109703434566932451437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41355251751651023639740997 7754109703434566932451437)
                    ·
                      refine ⟨2907791138787962599669289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7754109703434566932451437 2907791138787962599669289)
                      ·
                        rfl

theorem cell23_5662903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 3].length) (baseStart_5662903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662903 prefixEnd_5662903 := by exact prefixLift 5662903
  have htrace : WordTrace (prefixWord ++ tailWord_5662903) baseStart_5662903 baseEnd_5662903 := by
    simpa [prefixWord, tailWord_5662903, baseEnd_5662903] using wordTrace_append hprefix tailTrace_5662903
  have hstable : (prefixWord ++ tailWord_5662903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662903).length < 2 ^ (prefixWord ++ tailWord_5662903).sum := by decide
  have hdescent : baseEnd_5662903 < baseStart_5662903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662970 : List Nat := [3, 1, 1, 1, 1, 5, 3, 2, 1, 5]
def baseStart_5662970 : Nat := 118140960795 + 5662970 * 2 ^ 59
def prefixEnd_5662970 : Nat := 4983230072969 + 3 ^ 40 * 5662970 * 2
def baseEnd_5662970 : Nat := 969275180663937945843827

theorem tailTrace_5662970 : CollatzResearch.WordTrace tailWord_5662970 prefixEnd_5662970 969275180663937945843827 := by
  unfold tailWord_5662970
  simp only [CollatzResearch.WordTrace]
  refine ⟨51636371073508580780426591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137696989529356215414470909 51636371073508580780426591)
  ·
    refine ⟨77454556610262871170639887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51636371073508580780426591 77454556610262871170639887)
    ·
      refine ⟨116181834915394306755959831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77454556610262871170639887 116181834915394306755959831)
      ·
        refine ⟨174272752373091460133939747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116181834915394306755959831 174272752373091460133939747)
        ·
          refine ⟨261409128559637190200909621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174272752373091460133939747 261409128559637190200909621)
          ·
            refine ⟨24507105802465986581335277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 261409128559637190200909621 24507105802465986581335277)
            ·
              refine ⟨9190164675924744968000729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24507105802465986581335277 9190164675924744968000729)
              ·
                refine ⟨6892623506943558726000547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9190164675924744968000729 6892623506943558726000547)
                ·
                  refine ⟨10338935260415338089000821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6892623506943558726000547 10338935260415338089000821)
                  ·
                    refine ⟨969275180663937945843827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10338935260415338089000821 969275180663937945843827)
                    ·
                      rfl

theorem cell23_5662970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 1, 5].length) (baseStart_5662970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662970 prefixEnd_5662970 := by exact prefixLift 5662970
  have htrace : WordTrace (prefixWord ++ tailWord_5662970) baseStart_5662970 baseEnd_5662970 := by
    simpa [prefixWord, tailWord_5662970, baseEnd_5662970] using wordTrace_append hprefix tailTrace_5662970
  have hstable : (prefixWord ++ tailWord_5662970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662970).length < 2 ^ (prefixWord ++ tailWord_5662970).sum := by decide
  have hdescent : baseEnd_5662970 < baseStart_5662970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5662977 : List Nat := [1, 2, 4, 1, 1, 2, 4, 1, 2, 3, 2]
def baseStart_5662977 : Nat := 118140960795 + 5662977 * 2 ^ 59
def prefixEnd_5662977 : Nat := 4983230072969 + 3 ^ 40 * 5662977 * 2
def baseEnd_5662977 : Nat := 2907829136356395310143949

theorem tailTrace_5662977 : CollatzResearch.WordTrace tailWord_5662977 prefixEnd_5662977 2907829136356395310143949 := by
  unfold tailWord_5662977
  simp only [CollatzResearch.WordTrace]
  refine ⟨206545739605008963317211185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137697159736672642211474123 206545739605008963317211185)
  ·
    refine ⟨154909304703756722487908389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206545739605008963317211185 154909304703756722487908389)
    ·
      refine ⟨29045494631954385466482823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154909304703756722487908389 29045494631954385466482823)
      ·
        refine ⟨43568241947931578199724235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29045494631954385466482823 43568241947931578199724235)
        ·
          refine ⟨65352362921897367299586353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43568241947931578199724235 65352362921897367299586353)
          ·
            refine ⟨49014272191423025474689765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65352362921897367299586353 49014272191423025474689765)
            ·
              refine ⟨9190176035891817276504331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49014272191423025474689765 9190176035891817276504331)
              ·
                refine ⟨13785264053837725914756497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9190176035891817276504331 13785264053837725914756497)
                ·
                  refine ⟨10338948040378294436067373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13785264053837725914756497 10338948040378294436067373)
                  ·
                    refine ⟨3877105515141860413525265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10338948040378294436067373 3877105515141860413525265)
                    ·
                      refine ⟨2907829136356395310143949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3877105515141860413525265 2907829136356395310143949)
                      ·
                        rfl

theorem cell23_5662977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_5662977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5662977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5662977 prefixEnd_5662977 := by exact prefixLift 5662977
  have htrace : WordTrace (prefixWord ++ tailWord_5662977) baseStart_5662977 baseEnd_5662977 := by
    simpa [prefixWord, tailWord_5662977, baseEnd_5662977] using wordTrace_append hprefix tailTrace_5662977
  have hstable : (prefixWord ++ tailWord_5662977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5662977).length < 2 ^ (prefixWord ++ tailWord_5662977).sum := by decide
  have hdescent : baseEnd_5662977 < baseStart_5662977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5662977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663041 : List Nat := [1, 2, 5, 2, 2, 2, 2, 1, 1, 1, 4]
def baseStart_5663041 : Nat := 118140960795 + 5663041 * 2 ^ 59
def prefixEnd_5663041 : Nat := 4983230072969 + 3 ^ 40 * 5663041 * 2
def baseEnd_5663041 : Nat := 2907861999118283059743655

theorem tailTrace_5663041 : CollatzResearch.WordTrace tailWord_5663041 prefixEnd_5663041 2907861999118283059743655 := by
  unfold tailWord_5663041
  simp only [CollatzResearch.WordTrace]
  refine ⟨206548073876777102247540977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137698715917851401498360651 206548073876777102247540977)
  ·
    refine ⟨154911055407582826685655733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206548073876777102247540977 154911055407582826685655733)
    ·
      refine ⟨14522911444460890001780225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154911055407582826685655733 14522911444460890001780225)
      ·
        refine ⟨10892183583345667501335169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14522911444460890001780225 10892183583345667501335169)
        ·
          refine ⟨8169137687509250626001377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10892183583345667501335169 8169137687509250626001377)
          ·
            refine ⟨6126853265631937969501033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8169137687509250626001377 6126853265631937969501033)
            ·
              refine ⟨4595139949223953477125775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6126853265631937969501033 4595139949223953477125775)
              ·
                refine ⟨6892709923835930215688663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4595139949223953477125775 6892709923835930215688663)
                ·
                  refine ⟨10339064885753895323532995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6892709923835930215688663 10339064885753895323532995)
                  ·
                    refine ⟨15508597328630842985299493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10339064885753895323532995 15508597328630842985299493)
                    ·
                      refine ⟨2907861999118283059743655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15508597328630842985299493 2907861999118283059743655)
                      ·
                        rfl

theorem cell23_5663041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_5663041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663041 prefixEnd_5663041 := by exact prefixLift 5663041
  have htrace : WordTrace (prefixWord ++ tailWord_5663041) baseStart_5663041 baseEnd_5663041 := by
    simpa [prefixWord, tailWord_5663041, baseEnd_5663041] using wordTrace_append hprefix tailTrace_5663041
  have hstable : (prefixWord ++ tailWord_5663041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663041).length < 2 ^ (prefixWord ++ tailWord_5663041).sum := by decide
  have hdescent : baseEnd_5663041 < baseStart_5663041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663057 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 4, 1, 3]
def baseStart_5663057 : Nat := 118140960795 + 5663057 * 2 ^ 59
def prefixEnd_5663057 : Nat := 4983230072969 + 3 ^ 40 * 5663057 * 2
def baseEnd_5663057 : Nat := 2907870214808754997143581

theorem tailTrace_5663057 : CollatzResearch.WordTrace tailWord_5663057 prefixEnd_5663057 2907870214808754997143581 := by
  unfold tailWord_5663057
  simp only [CollatzResearch.WordTrace]
  refine ⟨206548657444719136980123425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137699104963146091320082283 206548657444719136980123425)
  ·
    refine ⟨154911493083539352735092569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206548657444719136980123425 154911493083539352735092569)
    ·
      refine ⟨116183619812654514551319427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154911493083539352735092569 116183619812654514551319427)
      ·
        refine ⟨174275429718981771826979141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116183619812654514551319427 174275429718981771826979141)
        ·
          refine ⟨32676643072309082217558589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174275429718981771826979141 32676643072309082217558589)
          ·
            refine ⟨12253741152115905831584471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32676643072309082217558589 12253741152115905831584471)
            ·
              refine ⟨18380611728173858747376707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12253741152115905831584471 18380611728173858747376707)
              ·
                refine ⟨27570917592260788121065061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18380611728173858747376707 27570917592260788121065061)
                ·
                  refine ⟨5169547048548897772699699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27570917592260788121065061 5169547048548897772699699)
                  ·
                    refine ⟨7754320572823346659049549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5169547048548897772699699 7754320572823346659049549)
                    ·
                      refine ⟨2907870214808754997143581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7754320572823346659049549 2907870214808754997143581)
                      ·
                        rfl

theorem cell23_5663057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 1, 3].length) (baseStart_5663057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663057 prefixEnd_5663057 := by exact prefixLift 5663057
  have htrace : WordTrace (prefixWord ++ tailWord_5663057) baseStart_5663057 baseEnd_5663057 := by
    simpa [prefixWord, tailWord_5663057, baseEnd_5663057] using wordTrace_append hprefix tailTrace_5663057
  have hstable : (prefixWord ++ tailWord_5663057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663057).length < 2 ^ (prefixWord ++ tailWord_5663057).sum := by decide
  have hdescent : baseEnd_5663057 < baseStart_5663057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663074 : List Nat := [3, 3, 2, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_5663074 : Nat := 118140960795 + 5663074 * 2 ^ 59
def prefixEnd_5663074 : Nat := 4983230072969 + 3 ^ 40 * 5663074 * 2
def baseEnd_5663074 : Nat := 2907878943979881430631003

theorem tailTrace_5663074 : CollatzResearch.WordTrace tailWord_5663074 prefixEnd_5663074 2907878943979881430631003 := by
  unfold tailWord_5663074
  simp only [CollatzResearch.WordTrace]
  refine ⟨51637319371414387220873069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137699518323771699255661517 51637319371414387220873069)
  ·
    refine ⟨19363994764280395207827401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51637319371414387220873069 19363994764280395207827401)
    ·
      refine ⟨14522996073210296405870551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19363994764280395207827401 14522996073210296405870551)
      ·
        refine ⟨21784494109815444608805827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14522996073210296405870551 21784494109815444608805827)
        ·
          refine ⟨32676741164723166913208741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21784494109815444608805827 32676741164723166913208741)
          ·
            refine ⟨6126888968385593796226639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32676741164723166913208741 6126888968385593796226639)
            ·
              refine ⟨9190333452578390694339959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6126888968385593796226639 9190333452578390694339959)
              ·
                refine ⟨13785500178867586041509939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9190333452578390694339959 13785500178867586041509939)
                ·
                  refine ⟨20678250268301379062264909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13785500178867586041509939 20678250268301379062264909)
                  ·
                    refine ⟨7754343850613017148349341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20678250268301379062264909 7754343850613017148349341)
                    ·
                      refine ⟨2907878943979881430631003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7754343850613017148349341 2907878943979881430631003)
                      ·
                        rfl

theorem cell23_5663074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_5663074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663074 prefixEnd_5663074 := by exact prefixLift 5663074
  have htrace : WordTrace (prefixWord ++ tailWord_5663074) baseStart_5663074 baseEnd_5663074 := by
    simpa [prefixWord, tailWord_5663074, baseEnd_5663074] using wordTrace_append hprefix tailTrace_5663074
  have hstable : (prefixWord ++ tailWord_5663074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663074).length < 2 ^ (prefixWord ++ tailWord_5663074).sum := by decide
  have hdescent : baseEnd_5663074 < baseStart_5663074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663083 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 5]
def baseStart_5663083 : Nat := 118140960795 + 5663083 * 2 ^ 59
def prefixEnd_5663083 : Nat := 4983230072969 + 3 ^ 40 * 5663083 * 2
def baseEnd_5663083 : Nat := 2907883565305771895418461

theorem tailTrace_5663083 : CollatzResearch.WordTrace tailWord_5663083 prefixEnd_5663083 2907883565305771895418461 := by
  unfold tailWord_5663083
  simp only [CollatzResearch.WordTrace]
  refine ⟨206549605742624943420569903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137699737161749962280379935 206549605742624943420569903)
  ·
    refine ⟨309824408613937415130854855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206549605742624943420569903 309824408613937415130854855)
    ·
      refine ⟨464736612920906122696282283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309824408613937415130854855 464736612920906122696282283)
      ·
        refine ⟨697104919381359184044423425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464736612920906122696282283 697104919381359184044423425)
        ·
          refine ⟨522828689536019388033317569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 697104919381359184044423425 522828689536019388033317569)
          ·
            refine ⟨392121517152014541024988177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 522828689536019388033317569 392121517152014541024988177)
            ·
              refine ⟨294091137864010905768741133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 392121517152014541024988177 294091137864010905768741133)
              ·
                refine ⟨110284176699004089663277925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 294091137864010905768741133 110284176699004089663277925)
                ·
                  refine ⟨20678283131063266811864611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110284176699004089663277925 20678283131063266811864611)
                  ·
                    refine ⟨31017424696594900217796917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20678283131063266811864611 31017424696594900217796917)
                    ·
                      refine ⟨2907883565305771895418461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31017424696594900217796917 2907883565305771895418461)
                      ·
                        rfl

theorem cell23_5663083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 5].length) (baseStart_5663083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663083 prefixEnd_5663083 := by exact prefixLift 5663083
  have htrace : WordTrace (prefixWord ++ tailWord_5663083) baseStart_5663083 baseEnd_5663083 := by
    simpa [prefixWord, tailWord_5663083, baseEnd_5663083] using wordTrace_append hprefix tailTrace_5663083
  have hstable : (prefixWord ++ tailWord_5663083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663083).length < 2 ^ (prefixWord ++ tailWord_5663083).sum := by decide
  have hdescent : baseEnd_5663083 < baseStart_5663083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663163 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 3, 10]
def baseStart_5663163 : Nat := 118140960795 + 5663163 * 2 ^ 59
def prefixEnd_5663163 : Nat := 4983230072969 + 3 ^ 40 * 5663163 * 2
def baseEnd_5663163 : Nat := 969308214586043860806031

theorem tailTrace_5663163 : CollatzResearch.WordTrace tailWord_5663163 prefixEnd_5663163 969308214586043860806031 := by
  unfold tailWord_5663163
  simp only [CollatzResearch.WordTrace]
  refine ⟨206552523582335117083482143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137701682388223411388988095 206552523582335117083482143)
  ·
    refine ⟨309828785373502675625223215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206552523582335117083482143 309828785373502675625223215)
    ·
      refine ⟨464743178060254013437834823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309828785373502675625223215 464743178060254013437834823)
      ·
        refine ⟨697114767090381020156752235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464743178060254013437834823 697114767090381020156752235)
        ·
          refine ⟨1045672150635571530235128353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697114767090381020156752235 1045672150635571530235128353)
          ·
            refine ⟨784254112976678647676346265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1045672150635571530235128353 784254112976678647676346265)
            ·
              refine ⟨588190584732508985757259699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 784254112976678647676346265 588190584732508985757259699)
              ·
                refine ⟨882285877098763478635889549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 588190584732508985757259699 882285877098763478635889549)
                ·
                  refine ⟨330857203912036304488458581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 882285877098763478635889549 330857203912036304488458581)
                  ·
                    refine ⟨969308214586043860806031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 330857203912036304488458581 969308214586043860806031)
                    ·
                      rfl

theorem cell23_5663163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 10].length) (baseStart_5663163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663163 prefixEnd_5663163 := by exact prefixLift 5663163
  have htrace : WordTrace (prefixWord ++ tailWord_5663163) baseStart_5663163 baseEnd_5663163 := by
    simpa [prefixWord, tailWord_5663163, baseEnd_5663163] using wordTrace_append hprefix tailTrace_5663163
  have hstable : (prefixWord ++ tailWord_5663163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663163).length < 2 ^ (prefixWord ++ tailWord_5663163).sum := by decide
  have hdescent : baseEnd_5663163 < baseStart_5663163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663207 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 3]
def baseStart_5663207 : Nat := 118140960795 + 5663207 * 2 ^ 59
def prefixEnd_5663207 : Nat := 4983230072969 + 3 ^ 40 * 5663207 * 2
def baseEnd_5663207 : Nat := 2907947236906929410267891

theorem tailTrace_5663207 : CollatzResearch.WordTrace tailWord_5663207 prefixEnd_5663207 2907947236906929410267891 := by
  unfold tailWord_5663207
  simp only [CollatzResearch.WordTrace]
  refine ⟨206554128394175712598083875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137702752262783808398722583 206554128394175712598083875)
  ·
    refine ⟨309831192591263568897125813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206554128394175712598083875 309831192591263568897125813)
    ·
      refine ⟨29046674305430959584105545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 309831192591263568897125813 29046674305430959584105545)
      ·
        refine ⟨21785005729073219688079159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29046674305430959584105545 21785005729073219688079159)
        ·
          refine ⟨32677508593609829532118739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21785005729073219688079159 32677508593609829532118739)
          ·
            refine ⟨49016262890414744298178109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32677508593609829532118739 49016262890414744298178109)
            ·
              refine ⟨18381098583905529111816791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49016262890414744298178109 18381098583905529111816791)
              ·
                refine ⟨27571647875858293667725187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18381098583905529111816791 27571647875858293667725187)
                ·
                  refine ⟨41357471813787440501587781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27571647875858293667725187 41357471813787440501587781)
                  ·
                    refine ⟨7754525965085145094047709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41357471813787440501587781 7754525965085145094047709)
                    ·
                      refine ⟨2907947236906929410267891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7754525965085145094047709 2907947236906929410267891)
                      ·
                        rfl

theorem cell23_5663207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_5663207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663207 prefixEnd_5663207 := by exact prefixLift 5663207
  have htrace : WordTrace (prefixWord ++ tailWord_5663207) baseStart_5663207 baseEnd_5663207 := by
    simpa [prefixWord, tailWord_5663207, baseEnd_5663207] using wordTrace_append hprefix tailTrace_5663207
  have hstable : (prefixWord ++ tailWord_5663207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663207).length < 2 ^ (prefixWord ++ tailWord_5663207).sum := by decide
  have hdescent : baseEnd_5663207 < baseStart_5663207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663244 : List Nat := [2, 2, 1, 2, 4, 2, 3, 1, 6]
def baseStart_5663244 : Nat := 118140960795 + 5663244 * 2 ^ 59
def prefixEnd_5663244 : Nat := 4983230072969 + 3 ^ 40 * 5663244 * 2
def baseEnd_5663244 : Nat := 323107359521238418389469

theorem tailTrace_5663244 : CollatzResearch.WordTrace tailWord_5663244 prefixEnd_5663244 323107359521238418389469 := by
  unfold tailWord_5663244
  simp only [CollatzResearch.WordTrace]
  refine ⟨103277738947520833958590393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137703651930027778611453857 103277738947520833958590393)
  ·
    refine ⟨77458304210640625468942795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103277738947520833958590393 77458304210640625468942795)
    ·
      refine ⟨116187456315960938203414193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77458304210640625468942795 116187456315960938203414193)
      ·
        refine ⟨87140592236970703652560645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116187456315960938203414193 87140592236970703652560645)
        ·
          refine ⟨16338861044432006934855121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87140592236970703652560645 16338861044432006934855121)
          ·
            refine ⟨12254145783324005201141341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16338861044432006934855121 12254145783324005201141341)
            ·
              refine ⟨4595304668746501950428003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12254145783324005201141341 4595304668746501950428003)
              ·
                refine ⟨6892957003119752925642005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4595304668746501950428003 6892957003119752925642005)
                ·
                  refine ⟨323107359521238418389469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6892957003119752925642005 323107359521238418389469)
                  ·
                    rfl

theorem cell23_5663244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 6].length) (baseStart_5663244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663244 prefixEnd_5663244 := by exact prefixLift 5663244
  have htrace : WordTrace (prefixWord ++ tailWord_5663244) baseStart_5663244 baseEnd_5663244 := by
    simpa [prefixWord, tailWord_5663244, baseEnd_5663244] using wordTrace_append hprefix tailTrace_5663244
  have hstable : (prefixWord ++ tailWord_5663244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663244).length < 2 ^ (prefixWord ++ tailWord_5663244).sum := by decide
  have hdescent : baseEnd_5663244 < baseStart_5663244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663247 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 1, 5, 2]
def baseStart_5663247 : Nat := 118140960795 + 5663247 * 2 ^ 59
def prefixEnd_5663247 : Nat := 4983230072969 + 3 ^ 40 * 5663247 * 2
def baseEnd_5663247 : Nat := 2907967776133109253767707

theorem tailTrace_5663247 : CollatzResearch.WordTrace tailWord_5663247 prefixEnd_5663247 2907967776133109253767707 := by
  unfold tailWord_5663247
  simp only [CollatzResearch.WordTrace]
  refine ⟨206555587314030799429539995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137703724876020532953026663 206555587314030799429539995)
  ·
    refine ⟨309833380971046199144309993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206555587314030799429539995 309833380971046199144309993)
    ·
      refine ⟨232375035728284649358232495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309833380971046199144309993 232375035728284649358232495)
      ·
        refine ⟨348562553592426974037348743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232375035728284649358232495 348562553592426974037348743)
        ·
          refine ⟨522843830388640461056023115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348562553592426974037348743 522843830388640461056023115)
          ·
            refine ⟨784265745582960691584034673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522843830388640461056023115 784265745582960691584034673)
            ·
              refine ⟨588199309187220518688026005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 784265745582960691584034673 588199309187220518688026005)
              ·
                refine ⟨27571842618150961813501219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 588199309187220518688026005 27571842618150961813501219)
                ·
                  refine ⟨41357763927226442720251829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27571842618150961813501219 41357763927226442720251829)
                  ·
                    refine ⟨3877290368177479005023609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41357763927226442720251829 3877290368177479005023609)
                    ·
                      refine ⟨2907967776133109253767707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3877290368177479005023609 2907967776133109253767707)
                      ·
                        rfl

theorem cell23_5663247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 5, 2].length) (baseStart_5663247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663247 prefixEnd_5663247 := by exact prefixLift 5663247
  have htrace : WordTrace (prefixWord ++ tailWord_5663247) baseStart_5663247 baseEnd_5663247 := by
    simpa [prefixWord, tailWord_5663247, baseEnd_5663247] using wordTrace_append hprefix tailTrace_5663247
  have hstable : (prefixWord ++ tailWord_5663247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663247).length < 2 ^ (prefixWord ++ tailWord_5663247).sum := by decide
  have hdescent : baseEnd_5663247 < baseStart_5663247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663274 : List Nat := [3, 1, 4, 1, 1, 2, 2, 3, 1, 5]
def baseStart_5663274 : Nat := 118140960795 + 5663274 * 2 ^ 59
def prefixEnd_5663274 : Nat := 4983230072969 + 3 ^ 40 * 5663274 * 2
def baseEnd_5663274 : Nat := 969327213370260216043361

theorem tailTrace_5663274 : CollatzResearch.WordTrace tailWord_5663274 prefixEnd_5663274 969327213370260216043361 := by
  unfold tailWord_5663274
  simp only [CollatzResearch.WordTrace]
  refine ⟨51639143021233245760193219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137704381389955322027181917 51639143021233245760193219)
  ·
    refine ⟨77458714531849868640289829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51639143021233245760193219 77458714531849868640289829)
    ·
      refine ⟨14523508974721850370054343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77458714531849868640289829 14523508974721850370054343)
      ·
        refine ⟨21785263462082775555081515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14523508974721850370054343 21785263462082775555081515)
        ·
          refine ⟨32677895193124163332622273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21785263462082775555081515 32677895193124163332622273)
          ·
            refine ⟨24508421394843122499466705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32677895193124163332622273 24508421394843122499466705)
            ·
              refine ⟨18381316046132341874600029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24508421394843122499466705 18381316046132341874600029)
              ·
                refine ⟨6892993517299628202975011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18381316046132341874600029 6892993517299628202975011)
                ·
                  refine ⟨10339490275949442304462517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6892993517299628202975011 10339490275949442304462517)
                  ·
                    refine ⟨969327213370260216043361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10339490275949442304462517 969327213370260216043361)
                    ·
                      rfl

theorem cell23_5663274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_5663274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663274 prefixEnd_5663274 := by exact prefixLift 5663274
  have htrace : WordTrace (prefixWord ++ tailWord_5663274) baseStart_5663274 baseEnd_5663274 := by
    simpa [prefixWord, tailWord_5663274, baseEnd_5663274] using wordTrace_append hprefix tailTrace_5663274
  have hstable : (prefixWord ++ tailWord_5663274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663274).length < 2 ^ (prefixWord ++ tailWord_5663274).sum := by decide
  have hdescent : baseEnd_5663274 < baseStart_5663274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663287 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 4, 4]
def baseStart_5663287 : Nat := 118140960795 + 5663287 * 2 ^ 59
def prefixEnd_5663287 : Nat := 4983230072969 + 3 ^ 40 * 5663287 * 2
def baseEnd_5663287 : Nat := 969329438453096365755841

theorem tailTrace_5663287 : CollatzResearch.WordTrace tailWord_5663287 prefixEnd_5663287 969329438453096365755841 := by
  unfold tailWord_5663287
  simp only [CollatzResearch.WordTrace]
  refine ⟨206557046233885886260996115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137704697489257257507330743 206557046233885886260996115)
  ·
    refine ⟨309835569350828829391494173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206557046233885886260996115 309835569350828829391494173)
    ·
      refine ⟨116188338506560811021810315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 309835569350828829391494173 116188338506560811021810315)
      ·
        refine ⟨174282507759841216532715473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116188338506560811021810315 174282507759841216532715473)
        ·
          refine ⟨130711880819880912399536605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174282507759841216532715473 130711880819880912399536605)
          ·
            refine ⟨49016955307455342149826227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130711880819880912399536605 49016955307455342149826227)
            ·
              refine ⟨73525432961183013224739341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49016955307455342149826227 73525432961183013224739341)
              ·
                refine ⟨27572037360443629959277253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73525432961183013224739341 27572037360443629959277253)
                ·
                  refine ⟨5169757005083180617364485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27572037360443629959277253 5169757005083180617364485)
                  ·
                    refine ⟨969329438453096365755841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5169757005083180617364485 969329438453096365755841)
                    ·
                      rfl

theorem cell23_5663287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 4].length) (baseStart_5663287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663287 prefixEnd_5663287 := by exact prefixLift 5663287
  have htrace : WordTrace (prefixWord ++ tailWord_5663287) baseStart_5663287 baseEnd_5663287 := by
    simpa [prefixWord, tailWord_5663287, baseEnd_5663287] using wordTrace_append hprefix tailTrace_5663287
  have hstable : (prefixWord ++ tailWord_5663287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663287).length < 2 ^ (prefixWord ++ tailWord_5663287).sum := by decide
  have hdescent : baseEnd_5663287 < baseStart_5663287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663288 : List Nat := [2, 1, 2, 1, 4, 1, 5, 2, 1, 1, 3]
def baseStart_5663288 : Nat := 118140960795 + 5663288 * 2 ^ 59
def prefixEnd_5663288 : Nat := 4983230072969 + 3 ^ 40 * 5663288 * 2
def baseEnd_5663288 : Nat := 2907988828839943593355019

theorem tailTrace_5663288 : CollatzResearch.WordTrace tailWord_5663288 prefixEnd_5663288 2907988828839943593355019 := by
  unfold tailWord_5663288
  simp only [CollatzResearch.WordTrace]
  refine ⟨103278541353441131715891259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137704721804588175621188345 103278541353441131715891259)
  ·
    refine ⟨154917812030161697573836889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103278541353441131715891259 154917812030161697573836889)
    ·
      refine ⟨116188359022621273180377667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154917812030161697573836889 116188359022621273180377667)
      ·
        refine ⟨174282538533931909770566501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116188359022621273180377667 174282538533931909770566501)
        ·
          refine ⟨32677975975112233081981219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174282538533931909770566501 32677975975112233081981219)
          ·
            refine ⟨49016963962668349622971829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32677975975112233081981219 49016963962668349622971829)
            ·
              refine ⟨4595340371500157777153609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49016963962668349622971829 4595340371500157777153609)
              ·
                refine ⟨3446505278625118332865207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4595340371500157777153609 3446505278625118332865207)
                ·
                  refine ⟨5169757917937677499297811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3446505278625118332865207 5169757917937677499297811)
                  ·
                    refine ⟨7754636876906516248946717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5169757917937677499297811 7754636876906516248946717)
                    ·
                      refine ⟨2907988828839943593355019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7754636876906516248946717 2907988828839943593355019)
                      ·
                        rfl

theorem cell23_5663288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 1, 1, 3].length) (baseStart_5663288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663288 prefixEnd_5663288 := by exact prefixLift 5663288
  have htrace : WordTrace (prefixWord ++ tailWord_5663288) baseStart_5663288 baseEnd_5663288 := by
    simpa [prefixWord, tailWord_5663288, baseEnd_5663288] using wordTrace_append hprefix tailTrace_5663288
  have hstable : (prefixWord ++ tailWord_5663288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663288).length < 2 ^ (prefixWord ++ tailWord_5663288).sum := by decide
  have hdescent : baseEnd_5663288 < baseStart_5663288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663314 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 3, 2, 3]
def baseStart_5663314 : Nat := 118140960795 + 5663314 * 2 ^ 59
def prefixEnd_5663314 : Nat := 4983230072969 + 3 ^ 40 * 5663314 * 2
def baseEnd_5663314 : Nat := 2908002179336960491629899

theorem tailTrace_5663314 : CollatzResearch.WordTrace tailWord_5663314 prefixEnd_5663314 2908002179336960491629899 := by
  unfold tailWord_5663314
  simp only [CollatzResearch.WordTrace]
  refine ⟨51639507751197017468057249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137705354003192046581485997 51639507751197017468057249)
  ·
    refine ⟨38729630813397763101042937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51639507751197017468057249 38729630813397763101042937)
    ·
      refine ⟨29047223110048322325782203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38729630813397763101042937 29047223110048322325782203)
      ·
        refine ⟨43570834665072483488673305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29047223110048322325782203 43570834665072483488673305)
        ·
          refine ⟨32678125998804362616504979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43570834665072483488673305 32678125998804362616504979)
          ·
            refine ⟨49017188998206543924757469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32678125998804362616504979 49017188998206543924757469)
            ·
              refine ⟨18381445874327453971784051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49017188998206543924757469 18381445874327453971784051)
              ·
                refine ⟨27572168811491180957676077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18381445874327453971784051 27572168811491180957676077)
                ·
                  refine ⟨10339563304309192859128529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27572168811491180957676077 10339563304309192859128529)
                  ·
                    refine ⟨7754672478231894644346397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10339563304309192859128529 7754672478231894644346397)
                    ·
                      refine ⟨2908002179336960491629899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7754672478231894644346397 2908002179336960491629899)
                      ·
                        rfl

theorem cell23_5663314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_5663314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663314 prefixEnd_5663314 := by exact prefixLift 5663314
  have htrace : WordTrace (prefixWord ++ tailWord_5663314) baseStart_5663314 baseEnd_5663314 := by
    simpa [prefixWord, tailWord_5663314, baseEnd_5663314] using wordTrace_append hprefix tailTrace_5663314
  have hstable : (prefixWord ++ tailWord_5663314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663314).length < 2 ^ (prefixWord ++ tailWord_5663314).sum := by decide
  have hdescent : baseEnd_5663314 < baseStart_5663314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663331 : List Nat := [1, 1, 1, 5, 1, 2, 5, 1, 1, 2, 3]
def baseStart_5663331 : Nat := 118140960795 + 5663331 * 2 ^ 59
def prefixEnd_5663331 : Nat := 4983230072969 + 3 ^ 40 * 5663331 * 2
def baseEnd_5663331 : Nat := 2908010908508086925117321

theorem tailTrace_5663331 : CollatzResearch.WordTrace tailWord_5663331 prefixEnd_5663331 2908010908508086925117321 := by
  unfold tailWord_5663331
  simp only [CollatzResearch.WordTrace]
  refine ⟨206558651045726481775597847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137705767363817654517065231 206558651045726481775597847)
  ·
    refine ⟨309837976568589722663396771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206558651045726481775597847 309837976568589722663396771)
    ·
      refine ⟨464756964852884583995095157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309837976568589722663396771 464756964852884583995095157)
      ·
        refine ⟨43570965454957929749540171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 464756964852884583995095157 43570965454957929749540171)
        ·
          refine ⟨65356448182436894624310257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43570965454957929749540171 65356448182436894624310257)
          ·
            refine ⟨49017336136827670968232693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65356448182436894624310257 49017336136827670968232693)
            ·
              refine ⟨4595375262827594153271815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49017336136827670968232693 4595375262827594153271815)
              ·
                refine ⟨6893062894241391229907723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4595375262827594153271815 6893062894241391229907723)
                ·
                  refine ⟨10339594341362086844861585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6893062894241391229907723 10339594341362086844861585)
                  ·
                    refine ⟨7754695756021565133646189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10339594341362086844861585 7754695756021565133646189)
                    ·
                      refine ⟨2908010908508086925117321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7754695756021565133646189 2908010908508086925117321)
                      ·
                        rfl

theorem cell23_5663331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_5663331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663331 prefixEnd_5663331 := by exact prefixLift 5663331
  have htrace : WordTrace (prefixWord ++ tailWord_5663331) baseStart_5663331 baseEnd_5663331 := by
    simpa [prefixWord, tailWord_5663331, baseEnd_5663331] using wordTrace_append hprefix tailTrace_5663331
  have hstable : (prefixWord ++ tailWord_5663331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663331).length < 2 ^ (prefixWord ++ tailWord_5663331).sum := by decide
  have hdescent : baseEnd_5663331 < baseStart_5663331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663361 : List Nat := [1, 2, 4, 2, 1, 1, 1, 5, 2, 1, 3]
def baseStart_5663361 : Nat := 118140960795 + 5663361 * 2 ^ 59
def prefixEnd_5663361 : Nat := 4983230072969 + 3 ^ 40 * 5663361 * 2
def baseEnd_5663361 : Nat := 2908026312927721807742183

theorem tailTrace_5663361 : CollatzResearch.WordTrace tailWord_5663361 prefixEnd_5663361 2908026312927721807742183 := by
  unfold tailWord_5663361
  simp only [CollatzResearch.WordTrace]
  refine ⟨206559745235617796899189937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137706496823745197932793291 206559745235617796899189937)
  ·
    refine ⟨154919808926713347674392453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206559745235617796899189937 154919808926713347674392453)
    ·
      refine ⟨29047464173758752688948585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154919808926713347674392453 29047464173758752688948585)
      ·
        refine ⟨21785598130319064516711439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29047464173758752688948585 21785598130319064516711439)
        ·
          refine ⟨32678397195478596775067159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21785598130319064516711439 32678397195478596775067159)
          ·
            refine ⟨49017595793217895162600739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32678397195478596775067159 49017595793217895162600739)
            ·
              refine ⟨73526393689826842743901109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49017595793217895162600739 73526393689826842743901109)
              ·
                refine ⟨6893099408421266507240729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73526393689826842743901109 6893099408421266507240729)
                ·
                  refine ⟨5169824556315949880430547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6893099408421266507240729 5169824556315949880430547)
                  ·
                    refine ⟨7754736834473924820645821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5169824556315949880430547 7754736834473924820645821)
                    ·
                      refine ⟨2908026312927721807742183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7754736834473924820645821 2908026312927721807742183)
                      ·
                        rfl

theorem cell23_5663361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_5663361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663361 prefixEnd_5663361 := by exact prefixLift 5663361
  have htrace : WordTrace (prefixWord ++ tailWord_5663361) baseStart_5663361 baseEnd_5663361 := by
    simpa [prefixWord, tailWord_5663361, baseEnd_5663361] using wordTrace_append hprefix tailTrace_5663361
  have hstable : (prefixWord ++ tailWord_5663361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663361).length < 2 ^ (prefixWord ++ tailWord_5663361).sum := by decide
  have hdescent : baseEnd_5663361 < baseStart_5663361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663367 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 4]
def baseStart_5663367 : Nat := 118140960795 + 5663367 * 2 ^ 59
def prefixEnd_5663367 : Nat := 4983230072969 + 3 ^ 40 * 5663367 * 2
def baseEnd_5663367 : Nat := 2908029393811648784267155

theorem tailTrace_5663367 : CollatzResearch.WordTrace tailWord_5663367 prefixEnd_5663367 2908029393811648784267155 := by
  unfold tailWord_5663367
  simp only [CollatzResearch.WordTrace]
  refine ⟨206559964073596059923908355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137706642715730706615938903 206559964073596059923908355)
  ·
    refine ⟨309839946110394089885862533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206559964073596059923908355 309839946110394089885862533)
    ·
      refine ⟨58094989895698891853599225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 309839946110394089885862533 58094989895698891853599225)
      ·
        refine ⟨43571242421774168890199419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58094989895698891853599225 43571242421774168890199419)
        ·
          refine ⟨65356863632661253335299129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43571242421774168890199419 65356863632661253335299129)
          ·
            refine ⟨49017647724495940001474347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65356863632661253335299129 49017647724495940001474347)
            ·
              refine ⟨73526471586743910002211521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49017647724495940001474347 73526471586743910002211521)
              ·
                refine ⟨55144853690057932501658641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73526471586743910002211521 55144853690057932501658641)
                ·
                  refine ⟨41358640267543449376243981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55144853690057932501658641 41358640267543449376243981)
                  ·
                    refine ⟨15509490100328793516091493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41358640267543449376243981 15509490100328793516091493)
                    ·
                      refine ⟨2908029393811648784267155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15509490100328793516091493 2908029393811648784267155)
                      ·
                        rfl

theorem cell23_5663367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_5663367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663367 prefixEnd_5663367 := by exact prefixLift 5663367
  have htrace : WordTrace (prefixWord ++ tailWord_5663367) baseStart_5663367 baseEnd_5663367 := by
    simpa [prefixWord, tailWord_5663367, baseEnd_5663367] using wordTrace_append hprefix tailTrace_5663367
  have hstable : (prefixWord ++ tailWord_5663367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663367).length < 2 ^ (prefixWord ++ tailWord_5663367).sum := by decide
  have hdescent : baseEnd_5663367 < baseStart_5663367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663388 : List Nat := [2, 2, 3, 2, 2, 2, 1, 3, 1, 3, 2]
def baseStart_5663388 : Nat := 118140960795 + 5663388 * 2 ^ 59
def prefixEnd_5663388 : Nat := 4983230072969 + 3 ^ 40 * 5663388 * 2
def baseEnd_5663388 : Nat := 2908040176905393202104559

theorem tailTrace_5663388 : CollatzResearch.WordTrace tailWord_5663388 prefixEnd_5663388 2908040176905393202104559 := by
  unfold tailWord_5663388
  simp only [CollatzResearch.WordTrace]
  refine ⟨103280365003259990255211409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137707153337679987006948545 103280365003259990255211409)
  ·
    refine ⟨77460273752444992691408557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103280365003259990255211409 77460273752444992691408557)
    ·
      refine ⟨29047602657166872259278209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77460273752444992691408557 29047602657166872259278209)
      ·
        refine ⟨21785701992875154194458657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29047602657166872259278209 21785701992875154194458657)
        ·
          refine ⟨16339276494656365645843993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21785701992875154194458657 16339276494656365645843993)
          ·
            refine ⟨12254457370992274234382995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16339276494656365645843993 12254457370992274234382995)
            ·
              refine ⟨18381686056488411351574493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12254457370992274234382995 18381686056488411351574493)
              ·
                refine ⟨6893132271183154256840435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18381686056488411351574493 6893132271183154256840435)
                ·
                  refine ⟨10339698406774731385260653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6893132271183154256840435 10339698406774731385260653)
                  ·
                    refine ⟨3877386902540524269472745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10339698406774731385260653 3877386902540524269472745)
                    ·
                      refine ⟨2908040176905393202104559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3877386902540524269472745 2908040176905393202104559)
                      ·
                        rfl

theorem cell23_5663388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_5663388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663388 prefixEnd_5663388 := by exact prefixLift 5663388
  have htrace : WordTrace (prefixWord ++ tailWord_5663388) baseStart_5663388 baseEnd_5663388 := by
    simpa [prefixWord, tailWord_5663388, baseEnd_5663388] using wordTrace_append hprefix tailTrace_5663388
  have hstable : (prefixWord ++ tailWord_5663388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663388).length < 2 ^ (prefixWord ++ tailWord_5663388).sum := by decide
  have hdescent : baseEnd_5663388 < baseStart_5663388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663407 : List Nat := [1, 1, 2, 1, 2, 5, 1, 3, 7]
def baseStart_5663407 : Nat := 118140960795 + 5663407 * 2 ^ 59
def prefixEnd_5663407 : Nat := 4983230072969 + 3 ^ 40 * 5663407 * 2
def baseEnd_5663407 : Nat := 323116659226425403085219

theorem tailTrace_5663407 : CollatzResearch.WordTrace tailWord_5663407 prefixEnd_5663407 323116659226425403085219 := by
  unfold tailWord_5663407
  simp only [CollatzResearch.WordTrace]
  refine ⟨206561422993451146755364475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137707615328967431170242983 206561422993451146755364475)
  ·
    refine ⟨309842134490176720133046713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206561422993451146755364475 309842134490176720133046713)
    ·
      refine ⟨232381600867632540099785035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309842134490176720133046713 232381600867632540099785035)
      ·
        refine ⟨348572401301448810149677553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232381600867632540099785035 348572401301448810149677553)
        ·
          refine ⟨261429300976086607612258165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348572401301448810149677553 261429300976086607612258165)
          ·
            refine ⟨24508996966508119463649203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 261429300976086607612258165 24508996966508119463649203)
            ·
              refine ⟨36763495449762179195473805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24508996966508119463649203 36763495449762179195473805)
              ·
                refine ⟨13786310793660817198302677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36763495449762179195473805 13786310793660817198302677)
                ·
                  refine ⟨323116659226425403085219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13786310793660817198302677 323116659226425403085219)
                  ·
                    rfl

theorem cell23_5663407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 7].length) (baseStart_5663407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663407 prefixEnd_5663407 := by exact prefixLift 5663407
  have htrace : WordTrace (prefixWord ++ tailWord_5663407) baseStart_5663407 baseEnd_5663407 := by
    simpa [prefixWord, tailWord_5663407, baseEnd_5663407] using wordTrace_append hprefix tailTrace_5663407
  have hstable : (prefixWord ++ tailWord_5663407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663407).length < 2 ^ (prefixWord ++ tailWord_5663407).sum := by decide
  have hdescent : baseEnd_5663407 < baseStart_5663407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663487 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 6]
def baseStart_5663487 : Nat := 118140960795 + 5663487 * 2 ^ 59
def prefixEnd_5663487 : Nat := 4983230072969 + 3 ^ 40 * 5663487 * 2
def baseEnd_5663487 : Nat := 2908091011490188314766603

theorem tailTrace_5663487 : CollatzResearch.WordTrace tailWord_5663487 prefixEnd_5663487 2908091011490188314766603 := by
  unfold tailWord_5663487
  simp only [CollatzResearch.WordTrace]
  refine ⟨206564340833161320418276715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137709560555440880278851143 206564340833161320418276715)
  ·
    refine ⟨309846511249741980627415073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206564340833161320418276715 309846511249741980627415073)
    ·
      refine ⟨232384883437306485470561305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309846511249741980627415073 232384883437306485470561305)
      ·
        refine ⟨174288662577979864102920979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232384883437306485470561305 174288662577979864102920979)
        ·
          refine ⟨261432993866969796154381469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174288662577979864102920979 261432993866969796154381469)
          ·
            refine ⟨98037372700113673557893051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261432993866969796154381469 98037372700113673557893051)
            ·
              refine ⟨147056059050170510336839577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98037372700113673557893051 147056059050170510336839577)
              ·
                refine ⟨110292044287627882752629683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147056059050170510336839577 110292044287627882752629683)
                ·
                  refine ⟨165438066431441824128944525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110292044287627882752629683 165438066431441824128944525)
                  ·
                    refine ⟨62039274911790684048354197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165438066431441824128944525 62039274911790684048354197)
                    ·
                      refine ⟨2908091011490188314766603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62039274911790684048354197 2908091011490188314766603)
                      ·
                        rfl

theorem cell23_5663487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_5663487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663487 prefixEnd_5663487 := by exact prefixLift 5663487
  have htrace : WordTrace (prefixWord ++ tailWord_5663487) baseStart_5663487 baseEnd_5663487 := by
    simpa [prefixWord, tailWord_5663487, baseEnd_5663487] using wordTrace_append hprefix tailTrace_5663487
  have hstable : (prefixWord ++ tailWord_5663487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663487).length < 2 ^ (prefixWord ++ tailWord_5663487).sum := by decide
  have hdescent : baseEnd_5663487 < baseStart_5663487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663497 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 10]
def baseStart_5663497 : Nat := 118140960795 + 5663497 * 2 ^ 59
def prefixEnd_5663497 : Nat := 4983230072969 + 3 ^ 40 * 5663497 * 2
def baseEnd_5663497 : Nat := 323121794032970363960173

theorem tailTrace_5663497 : CollatzResearch.WordTrace tailWord_5663497 prefixEnd_5663497 323121794032970363960173 := by
  unfold tailWord_5663497
  simp only [CollatzResearch.WordTrace]
  refine ⟨206564705563125092126140745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137709803708750061417427163 206564705563125092126140745)
  ·
    refine ⟨154923529172343819094605559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206564705563125092126140745 154923529172343819094605559)
    ·
      refine ⟨232385293758515728641908339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154923529172343819094605559 232385293758515728641908339)
      ·
        refine ⟨348577940637773592962862509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232385293758515728641908339 348577940637773592962862509)
        ·
          refine ⟨130716727739165097361073441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 348577940637773592962862509 130716727739165097361073441)
          ·
            refine ⟨98037545804373823020805081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130716727739165097361073441 98037545804373823020805081)
            ·
              refine ⟨73528159353280367265603811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98037545804373823020805081 73528159353280367265603811)
              ·
                refine ⟨110292239029920550898405717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73528159353280367265603811 110292239029920550898405717)
                ·
                  refine ⟨323121794032970363960173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 110292239029920550898405717 323121794032970363960173)
                  ·
                    rfl

theorem cell23_5663497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 10].length) (baseStart_5663497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663497 prefixEnd_5663497 := by exact prefixLift 5663497
  have htrace : WordTrace (prefixWord ++ tailWord_5663497) baseStart_5663497 baseEnd_5663497 := by
    simpa [prefixWord, tailWord_5663497, baseEnd_5663497] using wordTrace_append hprefix tailTrace_5663497
  have hstable : (prefixWord ++ tailWord_5663497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663497).length < 2 ^ (prefixWord ++ tailWord_5663497).sum := by decide
  have hdescent : baseEnd_5663497 < baseStart_5663497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663542 : List Nat := [5, 1, 2, 2, 3, 1, 1, 1, 2, 1, 4]
def baseStart_5663542 : Nat := 118140960795 + 5663542 * 2 ^ 59
def prefixEnd_5663542 : Nat := 4983230072969 + 3 ^ 40 * 5663542 * 2
def baseEnd_5663542 : Nat := 2908119252926185599578851

theorem tailTrace_5663542 : CollatzResearch.WordTrace tailWord_5663542 prefixEnd_5663542 2908119252926185599578851 := by
  unfold tailWord_5663542
  simp only [CollatzResearch.WordTrace]
  refine ⟨12910396677997629050720555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137710897898641376541019253 12910396677997629050720555)
  ·
    refine ⟨19365595016996443576080833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12910396677997629050720555 19365595016996443576080833)
    ·
      refine ⟨14524196262747332682060625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19365595016996443576080833 14524196262747332682060625)
      ·
        refine ⟨10893147197060499511545469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14524196262747332682060625 10893147197060499511545469)
        ·
          refine ⟨4084930198897687316829551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10893147197060499511545469 4084930198897687316829551)
          ·
            refine ⟨6127395298346530975244327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4084930198897687316829551 6127395298346530975244327)
            ·
              refine ⟨9191092947519796462866491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6127395298346530975244327 9191092947519796462866491)
              ·
                refine ⟨13786639421279694694299737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9191092947519796462866491 13786639421279694694299737)
                ·
                  refine ⟨10339979565959771020724803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13786639421279694694299737 10339979565959771020724803)
                  ·
                    refine ⟨15509969348939656531087205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10339979565959771020724803 15509969348939656531087205)
                    ·
                      refine ⟨2908119252926185599578851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15509969348939656531087205 2908119252926185599578851)
                      ·
                        rfl

theorem cell23_5663542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_5663542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663542 prefixEnd_5663542 := by exact prefixLift 5663542
  have htrace : WordTrace (prefixWord ++ tailWord_5663542) baseStart_5663542 baseEnd_5663542 := by
    simpa [prefixWord, tailWord_5663542, baseEnd_5663542] using wordTrace_append hprefix tailTrace_5663542
  have hstable : (prefixWord ++ tailWord_5663542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663542).length < 2 ^ (prefixWord ++ tailWord_5663542).sum := by decide
  have hdescent : baseEnd_5663542 < baseStart_5663542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663544 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 3, 5]
def baseStart_5663544 : Nat := 118140960795 + 5663544 * 2 ^ 59
def prefixEnd_5663544 : Nat := 4983230072969 + 3 ^ 40 * 5663544 * 2
def baseEnd_5663544 : Nat := 969373426629164863917947

theorem tailTrace_5663544 : CollatzResearch.WordTrace tailWord_5663544 prefixEnd_5663544 969373426629164863917947 := by
  unfold tailWord_5663544
  simp only [CollatzResearch.WordTrace]
  refine ⟨103283209896977409576550843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137710946529303212768734457 103283209896977409576550843)
  ·
    refine ⟨154924814845466114364826265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103283209896977409576550843 154924814845466114364826265)
    ·
      refine ⟨116193611134099585773619699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154924814845466114364826265 116193611134099585773619699)
      ·
        refine ⟨174290416701149378660429549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116193611134099585773619699 174290416701149378660429549)
        ·
          refine ⟨65358906262931016997661081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174290416701149378660429549 65358906262931016997661081)
          ·
            refine ⟨49019179697198262748245811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65358906262931016997661081 49019179697198262748245811)
            ·
              refine ⟨73528769545797394122368717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49019179697198262748245811 73528769545797394122368717)
              ·
                refine ⟨27573288579674022795888269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73528769545797394122368717 27573288579674022795888269)
                ·
                  refine ⟨10339983217377758548458101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27573288579674022795888269 10339983217377758548458101)
                  ·
                    refine ⟨969373426629164863917947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10339983217377758548458101 969373426629164863917947)
                    ·
                      rfl

theorem cell23_5663544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_5663544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663544 prefixEnd_5663544 := by exact prefixLift 5663544
  have htrace : WordTrace (prefixWord ++ tailWord_5663544) baseStart_5663544 baseEnd_5663544 := by
    simpa [prefixWord, tailWord_5663544, baseEnd_5663544] using wordTrace_append hprefix tailTrace_5663544
  have hstable : (prefixWord ++ tailWord_5663544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663544).length < 2 ^ (prefixWord ++ tailWord_5663544).sum := by decide
  have hdescent : baseEnd_5663544 < baseStart_5663544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663561 : List Nat := [1, 2, 1, 1, 2, 6, 1, 3, 1, 5]
def baseStart_5663561 : Nat := 118140960795 + 5663561 * 2 ^ 59
def prefixEnd_5663561 : Nat := 4983230072969 + 3 ^ 40 * 5663561 * 2
def baseEnd_5663561 : Nat := 969376336352873675080421

theorem tailTrace_5663561 : CollatzResearch.WordTrace tailWord_5663561 prefixEnd_5663561 969376336352873675080421 := by
  unfold tailWord_5663561
  simp only [CollatzResearch.WordTrace]
  refine ⟨206567039834893231056470537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137711359889928820704313691 206567039834893231056470537)
  ·
    refine ⟨154925279876169923292352903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206567039834893231056470537 154925279876169923292352903)
    ·
      refine ⟨232387919814254884938529355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154925279876169923292352903 232387919814254884938529355)
      ·
        refine ⟨348581879721382327407794033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232387919814254884938529355 348581879721382327407794033)
        ·
          refine ⟨261436409791036745555845525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348581879721382327407794033 261436409791036745555845525)
          ·
            refine ⟨12254831708954847447930259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 261436409791036745555845525 12254831708954847447930259)
            ·
              refine ⟨18382247563432271171895389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12254831708954847447930259 18382247563432271171895389)
              ·
                refine ⟨6893342836287101689460771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18382247563432271171895389 6893342836287101689460771)
                ·
                  refine ⟨10340014254430652534191157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6893342836287101689460771 10340014254430652534191157)
                  ·
                    refine ⟨969376336352873675080421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10340014254430652534191157 969376336352873675080421)
                    ·
                      rfl

theorem cell23_5663561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 5].length) (baseStart_5663561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663561 prefixEnd_5663561 := by exact prefixLift 5663561
  have htrace : WordTrace (prefixWord ++ tailWord_5663561) baseStart_5663561 baseEnd_5663561 := by
    simpa [prefixWord, tailWord_5663561, baseEnd_5663561] using wordTrace_append hprefix tailTrace_5663561
  have hstable : (prefixWord ++ tailWord_5663561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663561).length < 2 ^ (prefixWord ++ tailWord_5663561).sum := by decide
  have hdescent : baseEnd_5663561 < baseStart_5663561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663565 : List Nat := [1, 6, 1, 2, 2, 2, 1, 2, 6]
def baseStart_5663565 : Nat := 118140960795 + 5663565 * 2 ^ 59
def prefixEnd_5663565 : Nat := 4983230072969 + 3 ^ 40 * 5663565 * 2
def baseEnd_5663565 : Nat := 323125673664582112176805

theorem tailTrace_5663565 : CollatzResearch.WordTrace tailWord_5663565 prefixEnd_5663565 323125673664582112176805 := by
  unfold tailWord_5663565
  simp only [CollatzResearch.WordTrace]
  refine ⟨206567185726878739739616149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137711457151252493159744099 206567185726878739739616149)
  ·
    refine ⟨9682836830947440925294507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 206567185726878739739616149 9682836830947440925294507)
    ·
      refine ⟨14524255246421161387941761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9682836830947440925294507 14524255246421161387941761)
      ·
        refine ⟨10893191434815871040956321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14524255246421161387941761 10893191434815871040956321)
        ·
          refine ⟨8169893576111903280717241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10893191434815871040956321 8169893576111903280717241)
          ·
            refine ⟨6127420182083927460537931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8169893576111903280717241 6127420182083927460537931)
            ·
              refine ⟨9191130273125891190806897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6127420182083927460537931 9191130273125891190806897)
              ·
                refine ⟨6893347704844418393105173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9191130273125891190806897 6893347704844418393105173)
                ·
                  refine ⟨323125673664582112176805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6893347704844418393105173 323125673664582112176805)
                  ·
                    rfl

theorem cell23_5663565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_5663565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663565 prefixEnd_5663565 := by exact prefixLift 5663565
  have htrace : WordTrace (prefixWord ++ tailWord_5663565) baseStart_5663565 baseEnd_5663565 := by
    simpa [prefixWord, tailWord_5663565, baseEnd_5663565] using wordTrace_append hprefix tailTrace_5663565
  have hstable : (prefixWord ++ tailWord_5663565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663565).length < 2 ^ (prefixWord ++ tailWord_5663565).sum := by decide
  have hdescent : baseEnd_5663565 < baseStart_5663565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663575 : List Nat := [1, 1, 3, 2, 4, 1, 2, 4, 1, 1, 3]
def baseStart_5663575 : Nat := 118140960795 + 5663575 * 2 ^ 59
def prefixEnd_5663575 : Nat := 4983230072969 + 3 ^ 40 * 5663575 * 2
def baseEnd_5663575 : Nat := 2908136197787783970466199

theorem tailTrace_5663575 : CollatzResearch.WordTrace tailWord_5663575 prefixEnd_5663575 2908136197787783970466199 := by
  unfold tailWord_5663575
  simp only [CollatzResearch.WordTrace]
  refine ⟨206567550456842511447480179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137711700304561674298320119 206567550456842511447480179)
  ·
    refine ⟨309851325685263767171220269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206567550456842511447480179 309851325685263767171220269)
    ·
      refine ⟨116194247131973912689207601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 309851325685263767171220269 116194247131973912689207601)
      ·
        refine ⟨87145685348980434516905701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116194247131973912689207601 87145685348980434516905701)
        ·
          refine ⟨16339816002933831471919819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87145685348980434516905701 16339816002933831471919819)
          ·
            refine ⟨24509724004400747207879729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16339816002933831471919819 24509724004400747207879729)
            ·
              refine ⟨18382293003300560405909797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24509724004400747207879729 18382293003300560405909797)
              ·
                refine ⟨3446679938118855076108087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18382293003300560405909797 3446679938118855076108087)
                ·
                  refine ⟨5170019907178282614162131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3446679938118855076108087 5170019907178282614162131)
                  ·
                    refine ⟨7755029860767423921243197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5170019907178282614162131 7755029860767423921243197)
                    ·
                      refine ⟨2908136197787783970466199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7755029860767423921243197 2908136197787783970466199)
                      ·
                        rfl

theorem cell23_5663575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 1, 1, 3].length) (baseStart_5663575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663575 prefixEnd_5663575 := by exact prefixLift 5663575
  have htrace : WordTrace (prefixWord ++ tailWord_5663575) baseStart_5663575 baseEnd_5663575 := by
    simpa [prefixWord, tailWord_5663575, baseEnd_5663575] using wordTrace_append hprefix tailTrace_5663575
  have hstable : (prefixWord ++ tailWord_5663575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663575).length < 2 ^ (prefixWord ++ tailWord_5663575).sum := by decide
  have hdescent : baseEnd_5663575 < baseStart_5663575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663591 : List Nat := [1, 1, 5, 1, 2, 2, 3, 1, 1, 6]
def baseStart_5663591 : Nat := 118140960795 + 5663591 * 2 ^ 59
def prefixEnd_5663591 : Nat := 4983230072969 + 3 ^ 40 * 5663591 * 2
def baseEnd_5663591 : Nat := 969381471159418635955375

theorem tailTrace_5663591 : CollatzResearch.WordTrace tailWord_5663591 prefixEnd_5663591 969381471159418635955375 := by
  unfold tailWord_5663591
  simp only [CollatzResearch.WordTrace]
  refine ⟨206568134024784546180062627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137712089349856364120041751 206568134024784546180062627)
  ·
    refine ⟨309852201037176819270093941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206568134024784546180062627 309852201037176819270093941)
    ·
      refine ⟨29048643847235326806571307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 309852201037176819270093941 29048643847235326806571307)
      ·
        refine ⟨43572965770852990209856961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29048643847235326806571307 43572965770852990209856961)
        ·
          refine ⟨32679724328139742657392721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43572965770852990209856961 32679724328139742657392721)
          ·
            refine ⟨24509793246104806993044541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32679724328139742657392721 24509793246104806993044541)
            ·
              refine ⟨9191172467289302622391703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24509793246104806993044541 9191172467289302622391703)
              ·
                refine ⟨13786758700933953933587555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9191172467289302622391703 13786758700933953933587555)
                ·
                  refine ⟨20680138051400930900381333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13786758700933953933587555 20680138051400930900381333)
                  ·
                    refine ⟨969381471159418635955375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20680138051400930900381333 969381471159418635955375)
                    ·
                      rfl

theorem cell23_5663591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_5663591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663591 prefixEnd_5663591 := by exact prefixLift 5663591
  have htrace : WordTrace (prefixWord ++ tailWord_5663591) baseStart_5663591 baseEnd_5663591 := by
    simpa [prefixWord, tailWord_5663591, baseEnd_5663591] using wordTrace_append hprefix tailTrace_5663591
  have hstable : (prefixWord ++ tailWord_5663591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663591).length < 2 ^ (prefixWord ++ tailWord_5663591).sum := by decide
  have hdescent : baseEnd_5663591 < baseStart_5663591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663641 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 2, 7, 2]
def baseStart_5663641 : Nat := 118140960795 + 5663641 * 2 ^ 59
def prefixEnd_5663641 : Nat := 4983230072969 + 3 ^ 40 * 5663641 * 2
def baseEnd_5663641 : Nat := 2908170087510980712240895

theorem tailTrace_5663641 : CollatzResearch.WordTrace tailWord_5663641 prefixEnd_5663641 2908170087510980712240895 := by
  unfold tailWord_5663641
  simp only [CollatzResearch.WordTrace]
  refine ⟨206569957674603404719382777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137713305116402269812921851 206569957674603404719382777)
  ·
    refine ⟨154927468255952553539537083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206569957674603404719382777 154927468255952553539537083)
    ·
      refine ⟨232391202383928830309305625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154927468255952553539537083 232391202383928830309305625)
      ·
        refine ⟨174293401787946622731979219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232391202383928830309305625 174293401787946622731979219)
        ·
          refine ⟨261440102681919934097968829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174293401787946622731979219 261440102681919934097968829)
          ·
            refine ⟨98040038505719975286738311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261440102681919934097968829 98040038505719975286738311)
            ·
              refine ⟨147060057758579962930107467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98040038505719975286738311 147060057758579962930107467)
              ·
                refine ⟨220590086637869944395161201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147060057758579962930107467 220590086637869944395161201)
                ·
                  refine ⟨165442564978402458296370901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220590086637869944395161201 165442564978402458296370901)
                  ·
                    refine ⟨3877560116681307616321193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 165442564978402458296370901 3877560116681307616321193)
                    ·
                      refine ⟨2908170087510980712240895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3877560116681307616321193 2908170087510980712240895)
                      ·
                        rfl

theorem cell23_5663641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 7, 2].length) (baseStart_5663641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663641 prefixEnd_5663641 := by exact prefixLift 5663641
  have htrace : WordTrace (prefixWord ++ tailWord_5663641) baseStart_5663641 baseEnd_5663641 := by
    simpa [prefixWord, tailWord_5663641, baseEnd_5663641] using wordTrace_append hprefix tailTrace_5663641
  have hstable : (prefixWord ++ tailWord_5663641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663641).length < 2 ^ (prefixWord ++ tailWord_5663641).sum := by decide
  have hdescent : baseEnd_5663641 < baseStart_5663641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663642 : List Nat := [3, 1, 1, 4, 3, 2, 2, 1, 2, 4]
def baseStart_5663642 : Nat := 118140960795 + 5663642 * 2 ^ 59
def prefixEnd_5663642 : Nat := 4983230072969 + 3 ^ 40 * 5663642 * 2
def baseEnd_5663642 : Nat := 969390200330545069442797

theorem tailTrace_5663642 : CollatzResearch.WordTrace tailWord_5663642 prefixEnd_5663642 969390200330545069442797 := by
  unfold tailWord_5663642
  simp only [CollatzResearch.WordTrace]
  refine ⟨51642498536899945472542295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137713329431733187926779453 51642498536899945472542295)
  ·
    refine ⟨77463747805349918208813443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51642498536899945472542295 77463747805349918208813443)
    ·
      refine ⟨116195621708024877313220165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77463747805349918208813443 116195621708024877313220165)
      ·
        refine ⟨21786679070254664496228781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116195621708024877313220165 21786679070254664496228781)
        ·
          refine ⟨8170004651345499186085793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21786679070254664496228781 8170004651345499186085793)
          ·
            refine ⟨6127503488509124389564345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8170004651345499186085793 6127503488509124389564345)
            ·
              refine ⟨4595627616381843292173259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6127503488509124389564345 4595627616381843292173259)
              ·
                refine ⟨6893441424572764938259889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4595627616381843292173259 6893441424572764938259889)
                ·
                  refine ⟨5170081068429573703694917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6893441424572764938259889 5170081068429573703694917)
                  ·
                    refine ⟨969390200330545069442797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5170081068429573703694917 969390200330545069442797)
                    ·
                      rfl

theorem cell23_5663642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 2, 4].length) (baseStart_5663642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663642 prefixEnd_5663642 := by exact prefixLift 5663642
  have htrace : WordTrace (prefixWord ++ tailWord_5663642) baseStart_5663642 baseEnd_5663642 := by
    simpa [prefixWord, tailWord_5663642, baseEnd_5663642] using wordTrace_append hprefix tailTrace_5663642
  have hstable : (prefixWord ++ tailWord_5663642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663642).length < 2 ^ (prefixWord ++ tailWord_5663642).sum := by decide
  have hdescent : baseEnd_5663642 < baseStart_5663642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663691 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 3]
def baseStart_5663691 : Nat := 118140960795 + 5663691 * 2 ^ 59
def prefixEnd_5663691 : Nat := 4983230072969 + 3 ^ 40 * 5663691 * 2
def baseEnd_5663691 : Nat := 2908195761543705516615665

theorem tailTrace_5663691 : CollatzResearch.WordTrace tailWord_5663691 prefixEnd_5663691 2908195761543705516615665 := by
  unfold tailWord_5663691
  simp only [CollatzResearch.WordTrace]
  refine ⟨206571781324422263258702927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137714520882948175505801951 206571781324422263258702927)
  ·
    refine ⟨309857671986633394888054391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206571781324422263258702927 309857671986633394888054391)
    ·
      refine ⟨464786507979950092332081587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309857671986633394888054391 464786507979950092332081587)
      ·
        refine ⟨697179761969925138498122381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464786507979950092332081587 697179761969925138498122381)
        ·
          refine ⟨261442410738721926936795893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 697179761969925138498122381 261442410738721926936795893)
          ·
            refine ⟨24510226006755180650324615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 261442410738721926936795893 24510226006755180650324615)
            ·
              refine ⟨36765339010132770975486923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24510226006755180650324615 36765339010132770975486923)
              ·
                refine ⟨55148008515199156463230385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36765339010132770975486923 55148008515199156463230385)
                ·
                  refine ⟨41361006386399367347422789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55148008515199156463230385 41361006386399367347422789)
                  ·
                    refine ⟨7755188697449881377641773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41361006386399367347422789 7755188697449881377641773)
                    ·
                      refine ⟨2908195761543705516615665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7755188697449881377641773 2908195761543705516615665)
                      ·
                        rfl

theorem cell23_5663691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 3].length) (baseStart_5663691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663691 prefixEnd_5663691 := by exact prefixLift 5663691
  have htrace : WordTrace (prefixWord ++ tailWord_5663691) baseStart_5663691 baseEnd_5663691 := by
    simpa [prefixWord, tailWord_5663691, baseEnd_5663691] using wordTrace_append hprefix tailTrace_5663691
  have hstable : (prefixWord ++ tailWord_5663691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663691).length < 2 ^ (prefixWord ++ tailWord_5663691).sum := by decide
  have hdescent : baseEnd_5663691 < baseStart_5663691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663698 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 2, 6]
def baseStart_5663698 : Nat := 118140960795 + 5663698 * 2 ^ 59
def prefixEnd_5663698 : Nat := 4983230072969 + 3 ^ 40 * 5663698 * 2
def baseEnd_5663698 : Nat := 969399785302762329742711

theorem tailTrace_5663698 : CollatzResearch.WordTrace tailWord_5663698 prefixEnd_5663698 969399785302762329742711 := by
  unfold tailWord_5663698
  simp only [CollatzResearch.WordTrace]
  refine ⟨51643009158849225863551937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137714691090264602302805165 51643009158849225863551937)
  ·
    refine ⟨38732256869136919397663953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51643009158849225863551937 38732256869136919397663953)
    ·
      refine ⟨29049192651852689548247965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38732256869136919397663953 29049192651852689548247965)
      ·
        refine ⟨10893447244444758580592987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29049192651852689548247965 10893447244444758580592987)
        ·
          refine ⟨16340170866667137870889481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10893447244444758580592987 16340170866667137870889481)
          ·
            refine ⟨12255128150000353403167111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16340170866667137870889481 12255128150000353403167111)
            ·
              refine ⟨18382692225000530104750667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12255128150000353403167111 18382692225000530104750667)
              ·
                refine ⟨27574038337500795157126001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18382692225000530104750667 27574038337500795157126001)
                ·
                  refine ⟨20680528753125596367844501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27574038337500795157126001 20680528753125596367844501)
                  ·
                    refine ⟨969399785302762329742711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20680528753125596367844501 969399785302762329742711)
                    ·
                      rfl

theorem cell23_5663698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_5663698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663698 prefixEnd_5663698 := by exact prefixLift 5663698
  have htrace : WordTrace (prefixWord ++ tailWord_5663698) baseStart_5663698 baseEnd_5663698 := by
    simpa [prefixWord, tailWord_5663698, baseEnd_5663698] using wordTrace_append hprefix tailTrace_5663698
  have hstable : (prefixWord ++ tailWord_5663698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663698).length < 2 ^ (prefixWord ++ tailWord_5663698).sum := by decide
  have hdescent : baseEnd_5663698 < baseStart_5663698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663705 : List Nat := [1, 2, 1, 2, 5, 2, 2, 1, 1, 4, 2]
def baseStart_5663705 : Nat := 118140960795 + 5663705 * 2 ^ 59
def prefixEnd_5663705 : Nat := 4983230072969 + 3 ^ 40 * 5663705 * 2
def baseEnd_5663705 : Nat := 2908202950272868461840601

theorem tailTrace_5663705 : CollatzResearch.WordTrace tailWord_5663705 prefixEnd_5663705 2908202950272868461840601 := by
  unfold tailWord_5663705
  simp only [CollatzResearch.WordTrace]
  refine ⟨206572291946371543649712569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137714861297581029099808379 206572291946371543649712569)
  ·
    refine ⟨154929218959778657737284427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206572291946371543649712569 154929218959778657737284427)
    ·
      refine ⟨232393828439667986605926641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154929218959778657737284427 232393828439667986605926641)
      ·
        refine ⟨174295371329750989954444981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232393828439667986605926641 174295371329750989954444981)
        ·
          refine ⟨16340191062164155308229217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174295371329750989954444981 16340191062164155308229217)
          ·
            refine ⟨12255143296623116481171913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16340191062164155308229217 12255143296623116481171913)
            ·
              refine ⟨9191357472467337360878935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12255143296623116481171913 9191357472467337360878935)
              ·
                refine ⟨13787036208701006041318403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9191357472467337360878935 13787036208701006041318403)
                ·
                  refine ⟨20680554313051509061977605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13787036208701006041318403 20680554313051509061977605)
                  ·
                    refine ⟨3877603933697157949120801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20680554313051509061977605 3877603933697157949120801)
                    ·
                      refine ⟨2908202950272868461840601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3877603933697157949120801 2908202950272868461840601)
                      ·
                        rfl

theorem cell23_5663705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 4, 2].length) (baseStart_5663705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663705 prefixEnd_5663705 := by exact prefixLift 5663705
  have htrace : WordTrace (prefixWord ++ tailWord_5663705) baseStart_5663705 baseEnd_5663705 := by
    simpa [prefixWord, tailWord_5663705, baseEnd_5663705] using wordTrace_append hprefix tailTrace_5663705
  have hstable : (prefixWord ++ tailWord_5663705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663705).length < 2 ^ (prefixWord ++ tailWord_5663705).sum := by decide
  have hdescent : baseEnd_5663705 < baseStart_5663705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663726 : List Nat := [4, 1, 2, 1, 5, 1, 2, 1, 1, 3, 2]
def baseStart_5663726 : Nat := 118140960795 + 5663726 * 2 ^ 59
def prefixEnd_5663726 : Nat := 4983230072969 + 3 ^ 40 * 5663726 * 2
def baseEnd_5663726 : Nat := 2908213733366612879678005

theorem tailTrace_5663726 : CollatzResearch.WordTrace tailWord_5663726 prefixEnd_5663726 2908213733366612879678005 := by
  unfold tailWord_5663726
  simp only [CollatzResearch.WordTrace]
  refine ⟨25821632234911933029528379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137715371919530309490818021 25821632234911933029528379)
  ·
    refine ⟨38732448352367899544292569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25821632234911933029528379 38732448352367899544292569)
    ·
      refine ⟨29049336264275924658219427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38732448352367899544292569 29049336264275924658219427)
      ·
        refine ⟨43574004396413886987329141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29049336264275924658219427 43574004396413886987329141)
        ·
          refine ⟨4085062912163801905062107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43574004396413886987329141 4085062912163801905062107)
          ·
            refine ⟨6127594368245702857593161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4085062912163801905062107 6127594368245702857593161)
            ·
              refine ⟨4595695776184277143194871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6127594368245702857593161 4595695776184277143194871)
              ·
                refine ⟨6893543664276415714792307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4595695776184277143194871 6893543664276415714792307)
                ·
                  refine ⟨10340315496414623572188461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6893543664276415714792307 10340315496414623572188461)
                  ·
                    refine ⟨3877618311155483839570673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10340315496414623572188461 3877618311155483839570673)
                    ·
                      refine ⟨2908213733366612879678005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3877618311155483839570673 2908213733366612879678005)
                      ·
                        rfl

theorem cell23_5663726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_5663726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663726 prefixEnd_5663726 := by exact prefixLift 5663726
  have htrace : WordTrace (prefixWord ++ tailWord_5663726) baseStart_5663726 baseEnd_5663726 := by
    simpa [prefixWord, tailWord_5663726, baseEnd_5663726] using wordTrace_append hprefix tailTrace_5663726
  have hstable : (prefixWord ++ tailWord_5663726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663726).length < 2 ^ (prefixWord ++ tailWord_5663726).sum := by decide
  have hdescent : baseEnd_5663726 < baseStart_5663726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663741 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 4, 5]
def baseStart_5663741 : Nat := 118140960795 + 5663741 * 2 ^ 59
def prefixEnd_5663741 : Nat := 4983230072969 + 3 ^ 40 * 5663741 * 2
def baseEnd_5663741 : Nat := 969407145192143440330145

theorem tailTrace_5663741 : CollatzResearch.WordTrace tailWord_5663741 prefixEnd_5663741 969407145192143440330145 := by
  unfold tailWord_5663741
  simp only [CollatzResearch.WordTrace]
  refine ⟨206573604974241121798023077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137715736649494081198682051 206573604974241121798023077)
  ·
    refine ⟨38732550932670210337129327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206573604974241121798023077 38732550932670210337129327)
    ·
      refine ⟨58098826399005315505693991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38732550932670210337129327 58098826399005315505693991)
      ·
        refine ⟨87148239598507973258540987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58098826399005315505693991 87148239598507973258540987)
        ·
          refine ⟨130722359397761959887811481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87148239598507973258540987 130722359397761959887811481)
          ·
            refine ⟨98041769548321469915858611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130722359397761959887811481 98041769548321469915858611)
            ·
              refine ⟨147062654322482204873787917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98041769548321469915858611 147062654322482204873787917)
              ·
                refine ⟨55148495370930826827670469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147062654322482204873787917 55148495370930826827670469)
                ·
                  refine ⟨10340342882049530030188213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55148495370930826827670469 10340342882049530030188213)
                  ·
                    refine ⟨969407145192143440330145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10340342882049530030188213 969407145192143440330145)
                    ·
                      rfl

theorem cell23_5663741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_5663741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663741 prefixEnd_5663741 := by exact prefixLift 5663741
  have htrace : WordTrace (prefixWord ++ tailWord_5663741) baseStart_5663741 baseEnd_5663741 := by
    simpa [prefixWord, tailWord_5663741, baseEnd_5663741] using wordTrace_append hprefix tailTrace_5663741
  have hstable : (prefixWord ++ tailWord_5663741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663741).length < 2 ^ (prefixWord ++ tailWord_5663741).sum := by decide
  have hdescent : baseEnd_5663741 < baseStart_5663741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663751 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 7]
def baseStart_5663751 : Nat := 118140960795 + 5663751 * 2 ^ 59
def prefixEnd_5663751 : Nat := 4983230072969 + 3 ^ 40 * 5663751 * 2
def baseEnd_5663751 : Nat := 2908226570382975281865389

theorem tailTrace_5663751 : CollatzResearch.WordTrace tailWord_5663751 prefixEnd_5663751 2908226570382975281865389 := by
  unfold tailWord_5663751
  simp only [CollatzResearch.WordTrace]
  refine ⟨206573969704204893505887107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137715979802803262337258071 206573969704204893505887107)
  ·
    refine ⟨309860954556307340258830661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206573969704204893505887107 309860954556307340258830661)
    ·
      refine ⟨58098928979307626298530749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 309860954556307340258830661 58098928979307626298530749)
      ·
        refine ⟨21787098367240359861949031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58098928979307626298530749 21787098367240359861949031)
        ·
          refine ⟨32680647550860539792923547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21787098367240359861949031 32680647550860539792923547)
          ·
            refine ⟨49020971326290809689385321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32680647550860539792923547 49020971326290809689385321)
            ·
              refine ⟨36765728494718107267038991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49020971326290809689385321 36765728494718107267038991)
              ·
                refine ⟨55148592742077160900558487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36765728494718107267038991 55148592742077160900558487)
                ·
                  refine ⟨82722889113115741350837731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55148592742077160900558487 82722889113115741350837731)
                  ·
                    refine ⟨124084333669673612026256597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82722889113115741350837731 124084333669673612026256597)
                    ·
                      refine ⟨2908226570382975281865389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124084333669673612026256597 2908226570382975281865389)
                      ·
                        rfl

theorem cell23_5663751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_5663751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663751 prefixEnd_5663751 := by exact prefixLift 5663751
  have htrace : WordTrace (prefixWord ++ tailWord_5663751) baseStart_5663751 baseEnd_5663751 := by
    simpa [prefixWord, tailWord_5663751, baseEnd_5663751] using wordTrace_append hprefix tailTrace_5663751
  have hstable : (prefixWord ++ tailWord_5663751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663751).length < 2 ^ (prefixWord ++ tailWord_5663751).sum := by decide
  have hdescent : baseEnd_5663751 < baseStart_5663751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663778 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_5663778 : Nat := 118140960795 + 5663778 * 2 ^ 59
def prefixEnd_5663778 : Nat := 4983230072969 + 3 ^ 40 * 5663778 * 2
def baseEnd_5663778 : Nat := 2908240434360646676227765

theorem tailTrace_5663778 : CollatzResearch.WordTrace tailWord_5663778 prefixEnd_5663778 2908240434360646676227765 := by
  unfold tailWord_5663778
  simp only [CollatzResearch.WordTrace]
  refine ⟨51643738618776769279279997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137716636316738051411413325 51643738618776769279279997)
  ·
    refine ⟨19366401982041288479729999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51643738618776769279279997 19366401982041288479729999)
    ·
      refine ⟨29049602973061932719594999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19366401982041288479729999 29049602973061932719594999)
      ·
        refine ⟨43574404459592899079392499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29049602973061932719594999 43574404459592899079392499)
        ·
          refine ⟨65361606689389348619088749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43574404459592899079392499 65361606689389348619088749)
          ·
            refine ⟨24510602508521005732158281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65361606689389348619088749 24510602508521005732158281)
            ·
              refine ⟨18382951881390754299118711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24510602508521005732158281 18382951881390754299118711)
              ·
                refine ⟨27574427822086131448678067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18382951881390754299118711 27574427822086131448678067)
                ·
                  refine ⟨41361641733129197173017101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27574427822086131448678067 41361641733129197173017101)
                  ·
                    refine ⟨15510615649923448939881413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41361641733129197173017101 15510615649923448939881413)
                    ·
                      refine ⟨2908240434360646676227765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15510615649923448939881413 2908240434360646676227765)
                      ·
                        rfl

theorem cell23_5663778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_5663778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663778 prefixEnd_5663778 := by exact prefixLift 5663778
  have htrace : WordTrace (prefixWord ++ tailWord_5663778) baseStart_5663778 baseEnd_5663778 := by
    simpa [prefixWord, tailWord_5663778, baseEnd_5663778] using wordTrace_append hprefix tailTrace_5663778
  have hstable : (prefixWord ++ tailWord_5663778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663778).length < 2 ^ (prefixWord ++ tailWord_5663778).sum := by decide
  have hdescent : baseEnd_5663778 < baseStart_5663778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663805 : List Nat := [1, 4, 1, 3, 1, 2, 3, 1, 3, 4]
def baseStart_5663805 : Nat := 118140960795 + 5663805 * 2 ^ 59
def prefixEnd_5663805 : Nat := 4983230072969 + 3 ^ 40 * 5663805 * 2
def baseEnd_5663805 : Nat := 969418099446106023530047

theorem tailTrace_5663805 : CollatzResearch.WordTrace tailWord_5663805 prefixEnd_5663805 969418099446106023530047 := by
  unfold tailWord_5663805
  simp only [CollatzResearch.WordTrace]
  refine ⟨206575939246009260728352869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137717292830672840485568579 206575939246009260728352869)
  ·
    refine ⟨38732988608626736386566163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206575939246009260728352869 38732988608626736386566163)
    ·
      refine ⟨58099482912940104579849245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38732988608626736386566163 58099482912940104579849245)
      ·
        refine ⟨21787306092352539217443467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58099482912940104579849245 21787306092352539217443467)
        ·
          refine ⟨32680959138528808826165201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21787306092352539217443467 32680959138528808826165201)
          ·
            refine ⟨24510719353896606619623901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32680959138528808826165201 24510719353896606619623901)
            ·
              refine ⟨9191519757711227482358963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24510719353896606619623901 9191519757711227482358963)
              ·
                refine ⟨13787279636566841223538445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9191519757711227482358963 13787279636566841223538445)
                ·
                  refine ⟨5170229863712565458826917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13787279636566841223538445 5170229863712565458826917)
                  ·
                    refine ⟨969418099446106023530047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5170229863712565458826917 969418099446106023530047)
                    ·
                      rfl

theorem cell23_5663805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_5663805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663805 prefixEnd_5663805 := by exact prefixLift 5663805
  have htrace : WordTrace (prefixWord ++ tailWord_5663805) baseStart_5663805 baseEnd_5663805 := by
    simpa [prefixWord, tailWord_5663805, baseEnd_5663805] using wordTrace_append hprefix tailTrace_5663805
  have hstable : (prefixWord ++ tailWord_5663805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663805).length < 2 ^ (prefixWord ++ tailWord_5663805).sum := by decide
  have hdescent : baseEnd_5663805 < baseStart_5663805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663828 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 2, 5, 3]
def baseStart_5663828 : Nat := 118140960795 + 5663828 * 2 ^ 59
def prefixEnd_5663828 : Nat := 4983230072969 + 3 ^ 40 * 5663828 * 2
def baseEnd_5663828 : Nat := 2908266108393371480602535

theorem tailTrace_5663828 : CollatzResearch.WordTrace tailWord_5663828 prefixEnd_5663828 2908266108393371480602535 := by
  unfold tailWord_5663828
  simp only [CollatzResearch.WordTrace]
  refine ⟨103288389062462967828220069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137717852083283957104293425 103288389062462967828220069)
  ·
    refine ⟨19366572949211806467791263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103288389062462967828220069 19366572949211806467791263)
    ·
      refine ⟨29049859423817709701686895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19366572949211806467791263 29049859423817709701686895)
      ·
        refine ⟨43574789135726564552530343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29049859423817709701686895 43574789135726564552530343)
        ·
          refine ⟨65362183703589846828795515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43574789135726564552530343 65362183703589846828795515)
          ·
            refine ⟨98043275555384770243193273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65362183703589846828795515 98043275555384770243193273)
            ·
              refine ⟨73532456666538577682394955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98043275555384770243193273 73532456666538577682394955)
              ·
                refine ⟨110298684999807866523592433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73532456666538577682394955 110298684999807866523592433)
                ·
                  refine ⟨82724013749855899892694325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110298684999807866523592433 82724013749855899892694325)
                  ·
                    refine ⟨7755376289048990614940093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82724013749855899892694325 7755376289048990614940093)
                    ·
                      refine ⟨2908266108393371480602535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7755376289048990614940093 2908266108393371480602535)
                      ·
                        rfl

theorem cell23_5663828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_5663828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663828 prefixEnd_5663828 := by exact prefixLift 5663828
  have htrace : WordTrace (prefixWord ++ tailWord_5663828) baseStart_5663828 baseEnd_5663828 := by
    simpa [prefixWord, tailWord_5663828, baseEnd_5663828] using wordTrace_append hprefix tailTrace_5663828
  have hstable : (prefixWord ++ tailWord_5663828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663828).length < 2 ^ (prefixWord ++ tailWord_5663828).sum := by decide
  have hdescent : baseEnd_5663828 < baseStart_5663828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663855 : List Nat := [1, 1, 2, 1, 3, 3, 1, 4, 2, 3, 2]
def baseStart_5663855 : Nat := 118140960795 + 5663855 * 2 ^ 59
def prefixEnd_5663855 : Nat := 4983230072969 + 3 ^ 40 * 5663855 * 2
def baseEnd_5663855 : Nat := 2908279972371042874964911

theorem tailTrace_5663855 : CollatzResearch.WordTrace tailWord_5663855 prefixEnd_5663855 2908279972371042874964911 := by
  unfold tailWord_5663855
  simp only [CollatzResearch.WordTrace]
  refine ⟨206577762895828119267673019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137718508597218746178448679 206577762895828119267673019)
  ·
    refine ⟨309866644343742178901509529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206577762895828119267673019 309866644343742178901509529)
    ·
      refine ⟨232399983257806634176132147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309866644343742178901509529 232399983257806634176132147)
      ·
        refine ⟨348599974886709951264198221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232399983257806634176132147 348599974886709951264198221)
        ·
          refine ⟨130724990582516231724074333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 348599974886709951264198221 130724990582516231724074333)
          ·
            refine ⟨49021871468443586896527875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130724990582516231724074333 49021871468443586896527875)
            ·
              refine ⟨73532807202665380344791813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49021871468443586896527875 73532807202665380344791813)
              ·
                refine ⟨13787401350499758814648465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73532807202665380344791813 13787401350499758814648465)
                ·
                  refine ⟨10340551012874819110986349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13787401350499758814648465 10340551012874819110986349)
                  ·
                    refine ⟨3877706629828057166619881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10340551012874819110986349 3877706629828057166619881)
                    ·
                      refine ⟨2908279972371042874964911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3877706629828057166619881 2908279972371042874964911)
                      ·
                        rfl

theorem cell23_5663855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 3, 2].length) (baseStart_5663855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663855 prefixEnd_5663855 := by exact prefixLift 5663855
  have htrace : WordTrace (prefixWord ++ tailWord_5663855) baseStart_5663855 baseEnd_5663855 := by
    simpa [prefixWord, tailWord_5663855, baseEnd_5663855] using wordTrace_append hprefix tailTrace_5663855
  have hstable : (prefixWord ++ tailWord_5663855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663855).length < 2 ^ (prefixWord ++ tailWord_5663855).sum := by decide
  have hdescent : baseEnd_5663855 < baseStart_5663855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663862 : List Nat := [5, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3]
def baseStart_5663862 : Nat := 118140960795 + 5663862 * 2 ^ 59
def prefixEnd_5663862 : Nat := 4983230072969 + 3 ^ 40 * 5663862 * 2
def baseEnd_5663862 : Nat := 2908283566735624347577379

theorem tailTrace_5663862 : CollatzResearch.WordTrace tailWord_5663862 prefixEnd_5663862 2908283566735624347577379 := by
  unfold tailWord_5663862
  simp only [CollatzResearch.WordTrace]
  refine ⟨12911126137925172466448615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137718678804535172975451893 12911126137925172466448615)
  ·
    refine ⟨19366689206887758699672923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12911126137925172466448615 19366689206887758699672923)
    ·
      refine ⟨29050033810331638049509385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19366689206887758699672923 29050033810331638049509385)
      ·
        refine ⟨21787525357748728537132039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29050033810331638049509385 21787525357748728537132039)
        ·
          refine ⟨32681288036623092805698059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21787525357748728537132039 32681288036623092805698059)
          ·
            refine ⟨49021932054934639208547089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32681288036623092805698059 49021932054934639208547089)
            ·
              refine ⟨36766449041200979406410317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49021932054934639208547089 36766449041200979406410317)
              ·
                refine ⟨13787418390450367277403869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36766449041200979406410317 13787418390450367277403869)
                ·
                  refine ⟨5170281896418887729026451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13787418390450367277403869 5170281896418887729026451)
                  ·
                    refine ⟨7755422844628331593539677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5170281896418887729026451 7755422844628331593539677)
                    ·
                      refine ⟨2908283566735624347577379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7755422844628331593539677 2908283566735624347577379)
                      ·
                        rfl

theorem cell23_5663862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_5663862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663862 prefixEnd_5663862 := by exact prefixLift 5663862
  have htrace : WordTrace (prefixWord ++ tailWord_5663862) baseStart_5663862 baseEnd_5663862 := by
    simpa [prefixWord, tailWord_5663862, baseEnd_5663862] using wordTrace_append hprefix tailTrace_5663862
  have hstable : (prefixWord ++ tailWord_5663862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663862).length < 2 ^ (prefixWord ++ tailWord_5663862).sum := by decide
  have hdescent : baseEnd_5663862 < baseStart_5663862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663868 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 5, 1, 4]
def baseStart_5663868 : Nat := 118140960795 + 5663868 * 2 ^ 59
def prefixEnd_5663868 : Nat := 4983230072969 + 3 ^ 40 * 5663868 * 2
def baseEnd_5663868 : Nat := 2908286647619551324102351

theorem tailTrace_5663868 : CollatzResearch.WordTrace tailWord_5663868 prefixEnd_5663868 2908286647619551324102351 := by
  unfold tailWord_5663868
  simp only [CollatzResearch.WordTrace]
  refine ⟨103289118522390511243948129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137718824696520681658597505 103289118522390511243948129)
  ·
    refine ⟨77466838891792883432961097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103289118522390511243948129 77466838891792883432961097)
    ·
      refine ⟨58100129168844662574720823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77466838891792883432961097 58100129168844662574720823)
      ·
        refine ⟨87150193753266993862081235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58100129168844662574720823 87150193753266993862081235)
        ·
          refine ⟨130725290629900490793121853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87150193753266993862081235 130725290629900490793121853)
          ·
            refine ⟨49021983986212684047420695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130725290629900490793121853 49021983986212684047420695)
            ·
              refine ⟨73532975979319026071131043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49021983986212684047420695 73532975979319026071131043)
              ·
                refine ⟨110299463968978539106696565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73532975979319026071131043 110299463968978539106696565)
                ·
                  refine ⟨10340574747091738041252803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110299463968978539106696565 10340574747091738041252803)
                  ·
                    refine ⟨15510862120637607061879205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10340574747091738041252803 15510862120637607061879205)
                    ·
                      refine ⟨2908286647619551324102351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15510862120637607061879205 2908286647619551324102351)
                      ·
                        rfl

theorem cell23_5663868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_5663868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663868 prefixEnd_5663868 := by exact prefixLift 5663868
  have htrace : WordTrace (prefixWord ++ tailWord_5663868) baseStart_5663868 baseEnd_5663868 := by
    simpa [prefixWord, tailWord_5663868, baseEnd_5663868] using wordTrace_append hprefix tailTrace_5663868
  have hstable : (prefixWord ++ tailWord_5663868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663868).length < 2 ^ (prefixWord ++ tailWord_5663868).sum := by decide
  have hdescent : baseEnd_5663868 < baseStart_5663868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663891 : List Nat := [1, 1, 1, 2, 1, 2, 4, 11]
def baseStart_5663891 : Nat := 118140960795 + 5663891 * 2 ^ 59
def prefixEnd_5663891 : Nat := 4983230072969 + 3 ^ 40 * 5663891 * 2
def baseEnd_5663891 : Nat := 107714757691652027189435

theorem tailTrace_5663891 : CollatzResearch.WordTrace tailWord_5663891 prefixEnd_5663891 107714757691652027189435 := by
  unfold tailWord_5663891
  simp only [CollatzResearch.WordTrace]
  refine ⟨206579075923697697415983527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137719383949131798277322351 206579075923697697415983527)
  ·
    refine ⟨309868613885546546123975291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206579075923697697415983527 309868613885546546123975291)
    ·
      refine ⟨464802920828319819185962937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309868613885546546123975291 464802920828319819185962937)
      ·
        refine ⟨348602190621239864389472203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 464802920828319819185962937 348602190621239864389472203)
        ·
          refine ⟨522903285931859796584208305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348602190621239864389472203 522903285931859796584208305)
          ·
            refine ⟨392177464448894847438156229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 522903285931859796584208305 392177464448894847438156229)
            ·
              refine ⟨73533274584167783894654293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 392177464448894847438156229 73533274584167783894654293)
              ·
                refine ⟨107714757691652027189435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 73533274584167783894654293 107714757691652027189435)
                ·
                  rfl

theorem cell23_5663891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 11].length) (baseStart_5663891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663891 prefixEnd_5663891 := by exact prefixLift 5663891
  have htrace : WordTrace (prefixWord ++ tailWord_5663891) baseStart_5663891 baseEnd_5663891 := by
    simpa [prefixWord, tailWord_5663891, baseEnd_5663891] using wordTrace_append hprefix tailTrace_5663891
  have hstable : (prefixWord ++ tailWord_5663891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663891).length < 2 ^ (prefixWord ++ tailWord_5663891).sum := by decide
  have hdescent : baseEnd_5663891 < baseStart_5663891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663908 : List Nat := [2, 3, 1, 2, 3, 2, 10]
def baseStart_5663908 : Nat := 118140960795 + 5663908 * 2 ^ 59
def prefixEnd_5663908 : Nat := 4983230072969 + 3 ^ 40 * 5663908 * 2
def baseEnd_5663908 : Nat := 35905026998095446513607

theorem tailTrace_5663908 : CollatzResearch.WordTrace tailWord_5663908 prefixEnd_5663908 35905026998095446513607 := by
  unfold tailWord_5663908
  simp only [CollatzResearch.WordTrace]
  refine ⟨103289847982318054659676189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137719797309757406212901585 103289847982318054659676189)
  ·
    refine ⟨38733692993369270497378571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103289847982318054659676189 38733692993369270497378571)
    ·
      refine ⟨58100539490053905746067857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38733692993369270497378571 58100539490053905746067857)
      ·
        refine ⟨43575404617540429309550893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58100539490053905746067857 43575404617540429309550893)
        ·
          refine ⟨16340776731577660991081585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43575404617540429309550893 16340776731577660991081585)
          ·
            refine ⟨12255582548683245743311189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16340776731577660991081585 12255582548683245743311189)
            ·
              refine ⟨35905026998095446513607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12255582548683245743311189 35905026998095446513607)
              ·
                rfl

theorem cell23_5663908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 10].length) (baseStart_5663908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663908 prefixEnd_5663908 := by exact prefixLift 5663908
  have htrace : WordTrace (prefixWord ++ tailWord_5663908) baseStart_5663908 baseEnd_5663908 := by
    simpa [prefixWord, tailWord_5663908, baseEnd_5663908] using wordTrace_append hprefix tailTrace_5663908
  have hstable : (prefixWord ++ tailWord_5663908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663908).length < 2 ^ (prefixWord ++ tailWord_5663908).sum := by decide
  have hdescent : baseEnd_5663908 < baseStart_5663908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663919 : List Nat := [1, 1, 2, 1, 2, 3, 4, 4, 1, 2, 2]
def baseStart_5663919 : Nat := 118140960795 + 5663919 * 2 ^ 59
def prefixEnd_5663919 : Nat := 4983230072969 + 3 ^ 40 * 5663919 * 2
def baseEnd_5663919 : Nat := 2908312835132930624564617

theorem tailTrace_5663919 : CollatzResearch.WordTrace tailWord_5663919 prefixEnd_5663919 2908312835132930624564617 := by
  unfold tailWord_5663919
  simp only [CollatzResearch.WordTrace]
  refine ⟨206580097167596258198002811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137720064778397505465335207 206580097167596258198002811)
  ·
    refine ⟨309870145751394387297004217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206580097167596258198002811 309870145751394387297004217)
    ·
      refine ⟨232402609313545790472753163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309870145751394387297004217 232402609313545790472753163)
      ·
        refine ⟨348603913970318685709129745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232402609313545790472753163 348603913970318685709129745)
        ·
          refine ⟨261452935477739014281847309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348603913970318685709129745 261452935477739014281847309)
          ·
            refine ⟨98044850804152130355692741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261452935477739014281847309 98044850804152130355692741)
            ·
              refine ⟨18383409525778524441692389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98044850804152130355692741 18383409525778524441692389)
              ·
                refine ⟨3446889286083473332817323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18383409525778524441692389 3446889286083473332817323)
                ·
                  refine ⟨5170333929125209999225985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3446889286083473332817323 5170333929125209999225985)
                  ·
                    refine ⟨3877750446843907499419489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5170333929125209999225985 3877750446843907499419489)
                    ·
                      refine ⟨2908312835132930624564617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3877750446843907499419489 2908312835132930624564617)
                      ·
                        rfl

theorem cell23_5663919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 1, 2, 2].length) (baseStart_5663919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663919 prefixEnd_5663919 := by exact prefixLift 5663919
  have htrace : WordTrace (prefixWord ++ tailWord_5663919) baseStart_5663919 baseEnd_5663919 := by
    simpa [prefixWord, tailWord_5663919, baseEnd_5663919] using wordTrace_append hprefix tailTrace_5663919
  have hstable : (prefixWord ++ tailWord_5663919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663919).length < 2 ^ (prefixWord ++ tailWord_5663919).sum := by decide
  have hdescent : baseEnd_5663919 < baseStart_5663919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663932 : List Nat := [2, 2, 2, 3, 2, 3, 1, 1, 1, 2, 4]
def baseStart_5663932 : Nat := 118140960795 + 5663932 * 2 ^ 59
def prefixEnd_5663932 : Nat := 4983230072969 + 3 ^ 40 * 5663932 * 2
def baseEnd_5663932 : Nat := 2908319510381439073702057

theorem tailTrace_5663932 : CollatzResearch.WordTrace tailWord_5663932 prefixEnd_5663932 2908319510381439073702057 := by
  unfold tailWord_5663932
  simp only [CollatzResearch.WordTrace]
  refine ⟨103290285658274580709113025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137720380877699440945484033 103290285658274580709113025)
  ·
    refine ⟨77467714243705935531834769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103290285658274580709113025 77467714243705935531834769)
    ·
      refine ⟨58100785682779451648876077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77467714243705935531834769 58100785682779451648876077)
      ·
        refine ⟨21787794631042294368328529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58100785682779451648876077 21787794631042294368328529)
        ·
          refine ⟨16340845973281720776246397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21787794631042294368328529 16340845973281720776246397)
          ·
            refine ⟨6127817239980645291092399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16340845973281720776246397 6127817239980645291092399)
            ·
              refine ⟨9191725859970967936638599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6127817239980645291092399 9191725859970967936638599)
              ·
                refine ⟨13787588789956451904957899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9191725859970967936638599 13787588789956451904957899)
                ·
                  refine ⟨20681383184934677857436849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13787588789956451904957899 20681383184934677857436849)
                  ·
                    refine ⟨15511037388701008393077637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20681383184934677857436849 15511037388701008393077637)
                    ·
                      refine ⟨2908319510381439073702057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15511037388701008393077637 2908319510381439073702057)
                      ·
                        rfl

theorem cell23_5663932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_5663932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663932 prefixEnd_5663932 := by exact prefixLift 5663932
  have htrace : WordTrace (prefixWord ++ tailWord_5663932) baseStart_5663932 baseEnd_5663932 := by
    simpa [prefixWord, tailWord_5663932, baseEnd_5663932] using wordTrace_append hprefix tailTrace_5663932
  have hstable : (prefixWord ++ tailWord_5663932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663932).length < 2 ^ (prefixWord ++ tailWord_5663932).sum := by decide
  have hdescent : baseEnd_5663932 < baseStart_5663932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663935 : List Nat := [1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 3]
def baseStart_5663935 : Nat := 118140960795 + 5663935 * 2 ^ 59
def prefixEnd_5663935 : Nat := 4983230072969 + 3 ^ 40 * 5663935 * 2
def baseEnd_5663935 : Nat := 2908321050823402561964543

theorem tailTrace_5663935 : CollatzResearch.WordTrace tailWord_5663935 prefixEnd_5663935 2908321050823402561964543 := by
  unfold tailWord_5663935
  simp only [CollatzResearch.WordTrace]
  refine ⟨206580680735538292930585259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137720453823692195287056839 206580680735538292930585259)
  ·
    refine ⟨309871021103307439395877889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206580680735538292930585259 309871021103307439395877889)
    ·
      refine ⟨232403265827480579546908417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309871021103307439395877889 232403265827480579546908417)
      ·
        refine ⟨174302449370610434660181313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232403265827480579546908417 174302449370610434660181313)
        ·
          refine ⟨130726837027957825995135985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174302449370610434660181313 130726837027957825995135985)
          ·
            refine ⟨98045127770968369496351989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130726837027957825995135985 98045127770968369496351989)
            ·
              refine ⟨9191730728528284640282999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98045127770968369496351989 9191730728528284640282999)
              ·
                refine ⟨13787596092792426960424499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9191730728528284640282999 13787596092792426960424499)
                ·
                  refine ⟨20681394139188640440636749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13787596092792426960424499 20681394139188640440636749)
                  ·
                    refine ⟨7755522802195740165238781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20681394139188640440636749 7755522802195740165238781)
                    ·
                      refine ⟨2908321050823402561964543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7755522802195740165238781 2908321050823402561964543)
                      ·
                        rfl

theorem cell23_5663935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 3].length) (baseStart_5663935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663935 prefixEnd_5663935 := by exact prefixLift 5663935
  have htrace : WordTrace (prefixWord ++ tailWord_5663935) baseStart_5663935 baseEnd_5663935 := by
    simpa [prefixWord, tailWord_5663935, baseEnd_5663935] using wordTrace_append hprefix tailTrace_5663935
  have hstable : (prefixWord ++ tailWord_5663935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663935).length < 2 ^ (prefixWord ++ tailWord_5663935).sum := by decide
  have hdescent : baseEnd_5663935 < baseStart_5663935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663945 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 7, 3, 2]
def baseStart_5663945 : Nat := 118140960795 + 5663945 * 2 ^ 59
def prefixEnd_5663945 : Nat := 4983230072969 + 3 ^ 40 * 5663945 * 2
def baseEnd_5663945 : Nat := 2908326185629947522839497

theorem tailTrace_5663945 : CollatzResearch.WordTrace tailWord_5663945 prefixEnd_5663945 2908326185629947522839497 := by
  unfold tailWord_5663945
  simp only [CollatzResearch.WordTrace]
  refine ⟨206581045465502064638449289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137720696977001376425632859 206581045465502064638449289)
  ·
    refine ⟨154935784099126548478836967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206581045465502064638449289 154935784099126548478836967)
    ·
      refine ⟨232403676148689822718255451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154935784099126548478836967 232403676148689822718255451)
      ·
        refine ⟨348605514223034734077383177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232403676148689822718255451 348605514223034734077383177)
        ·
          refine ⟨261454135667276050558037383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348605514223034734077383177 261454135667276050558037383)
          ·
            refine ⟨392181203500914075837056075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261454135667276050558037383 392181203500914075837056075)
            ·
              refine ⟨588271805251371113755584113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392181203500914075837056075 588271805251371113755584113)
              ·
                refine ⟨441203853938528335316688085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588271805251371113755584113 441203853938528335316688085)
                ·
                  refine ⟨10340715326684257858984877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 441203853938528335316688085 10340715326684257858984877)
                  ·
                    refine ⟨3877768247506596697119329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10340715326684257858984877 3877768247506596697119329)
                    ·
                      refine ⟨2908326185629947522839497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3877768247506596697119329 2908326185629947522839497)
                      ·
                        rfl

theorem cell23_5663945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 3, 2].length) (baseStart_5663945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663945 prefixEnd_5663945 := by exact prefixLift 5663945
  have htrace : WordTrace (prefixWord ++ tailWord_5663945) baseStart_5663945 baseEnd_5663945 := by
    simpa [prefixWord, tailWord_5663945, baseEnd_5663945] using wordTrace_append hprefix tailTrace_5663945
  have hstable : (prefixWord ++ tailWord_5663945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663945).length < 2 ^ (prefixWord ++ tailWord_5663945).sum := by decide
  have hdescent : baseEnd_5663945 < baseStart_5663945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5663996 : List Nat := [2, 2, 2, 1, 5, 2, 1, 2, 1, 3, 2]
def baseStart_5663996 : Nat := 118140960795 + 5663996 * 2 ^ 59
def prefixEnd_5663996 : Nat := 4983230072969 + 3 ^ 40 * 5663996 * 2
def baseEnd_5663996 : Nat := 2908352373143326823301763

theorem tailTrace_5663996 : CollatzResearch.WordTrace tailWord_5663996 prefixEnd_5663996 2908352373143326823301763 := by
  unfold tailWord_5663996
  simp only [CollatzResearch.WordTrace]
  refine ⟨103291452794158650174277921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137721937058878200232370561 103291452794158650174277921)
  ·
    refine ⟨77468589595618987630708441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103291452794158650174277921 77468589595618987630708441)
    ·
      refine ⟨58101442196714240723031331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77468589595618987630708441 58101442196714240723031331)
      ·
        refine ⟨87152163295071361084546997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58101442196714240723031331 87152163295071361084546997)
        ·
          refine ⟨8170515308912940101676281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87152163295071361084546997 8170515308912940101676281)
          ·
            refine ⟨6127886481684705076257211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8170515308912940101676281 6127886481684705076257211)
            ·
              refine ⟨9191829722527057614385817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6127886481684705076257211 9191829722527057614385817)
              ·
                refine ⟨6893872291895293210789363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9191829722527057614385817 6893872291895293210789363)
                ·
                  refine ⟨10340808437842939816184045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6893872291895293210789363 10340808437842939816184045)
                  ·
                    refine ⟨3877803164191102431069017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10340808437842939816184045 3877803164191102431069017)
                    ·
                      refine ⟨2908352373143326823301763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3877803164191102431069017 2908352373143326823301763)
                      ·
                        rfl

theorem cell23_5663996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 1, 3, 2].length) (baseStart_5663996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5663996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5663996 prefixEnd_5663996 := by exact prefixLift 5663996
  have htrace : WordTrace (prefixWord ++ tailWord_5663996) baseStart_5663996 baseEnd_5663996 := by
    simpa [prefixWord, tailWord_5663996, baseEnd_5663996] using wordTrace_append hprefix tailTrace_5663996
  have hstable : (prefixWord ++ tailWord_5663996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5663996).length < 2 ^ (prefixWord ++ tailWord_5663996).sum := by decide
  have hdescent : baseEnd_5663996 < baseStart_5663996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5663996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664026 : List Nat := [3, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2]
def baseStart_5664026 : Nat := 118140960795 + 5664026 * 2 ^ 59
def prefixEnd_5664026 : Nat := 4983230072969 + 3 ^ 40 * 5664026 * 2
def baseEnd_5664026 : Nat := 2908367777562961705926625

theorem tailTrace_5664026 : CollatzResearch.WordTrace tailWord_5664026 prefixEnd_5664026 2908367777562961705926625 := by
  unfold tailWord_5664026
  simp only [CollatzResearch.WordTrace]
  refine ⟨51645999944552153868036983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137722666518805743648098621 51645999944552153868036983)
  ·
    refine ⟨77468999916828230802055475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51645999944552153868036983 77468999916828230802055475)
    ·
      refine ⟨116203499875242346203083213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77468999916828230802055475 116203499875242346203083213)
      ·
        refine ⟨43576312453215879826156205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116203499875242346203083213 43576312453215879826156205)
        ·
          refine ⟨16341117169955954934808577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43576312453215879826156205 16341117169955954934808577)
          ·
            refine ⟨12255837877466966201106433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16341117169955954934808577 12255837877466966201106433)
            ·
              refine ⟨9191878408100224650829825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12255837877466966201106433 9191878408100224650829825)
              ·
                refine ⟨6893908806075168488122369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9191878408100224650829825 6893908806075168488122369)
                ·
                  refine ⟨5170431604556376366091777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6893908806075168488122369 5170431604556376366091777)
                  ·
                    refine ⟨3877823703417282274568833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5170431604556376366091777 3877823703417282274568833)
                    ·
                      refine ⟨2908367777562961705926625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3877823703417282274568833 2908367777562961705926625)
                      ·
                        rfl

theorem cell23_5664026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_5664026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664026 prefixEnd_5664026 := by exact prefixLift 5664026
  have htrace : WordTrace (prefixWord ++ tailWord_5664026) baseStart_5664026 baseEnd_5664026 := by
    simpa [prefixWord, tailWord_5664026, baseEnd_5664026] using wordTrace_append hprefix tailTrace_5664026
  have hstable : (prefixWord ++ tailWord_5664026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664026).length < 2 ^ (prefixWord ++ tailWord_5664026).sum := by decide
  have hdescent : baseEnd_5664026 < baseStart_5664026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664042 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_5664042 : Nat := 118140960795 + 5664042 * 2 ^ 59
def prefixEnd_5664042 : Nat := 4983230072969 + 3 ^ 40 * 5664042 * 2
def baseEnd_5664042 : Nat := 2908375993253433643326551

theorem tailTrace_5664042 : CollatzResearch.WordTrace tailWord_5664042 prefixEnd_5664042 2908375993253433643326551 := by
  unfold tailWord_5664042
  simp only [CollatzResearch.WordTrace]
  refine ⟨51646145836537662551182595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137723055564100433469820253 51646145836537662551182595)
  ·
    refine ⟨77469218754806493826773893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51646145836537662551182595 77469218754806493826773893)
    ·
      refine ⟨14525478516526217592520105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77469218754806493826773893 14525478516526217592520105)
      ·
        refine ⟨10894108887394663194390079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14525478516526217592520105 10894108887394663194390079)
        ·
          refine ⟨16341163331091994791585119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10894108887394663194390079 16341163331091994791585119)
          ·
            refine ⟨24511744996637992187377679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16341163331091994791585119 24511744996637992187377679)
            ·
              refine ⟨36767617494956988281066519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24511744996637992187377679 36767617494956988281066519)
              ·
                refine ⟨55151426242435482421599779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36767617494956988281066519 55151426242435482421599779)
                ·
                  refine ⟨82727139363653223632399669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55151426242435482421599779 82727139363653223632399669)
                  ·
                    refine ⟨7755669315342489715537469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82727139363653223632399669 7755669315342489715537469)
                    ·
                      refine ⟨2908375993253433643326551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7755669315342489715537469 2908375993253433643326551)
                      ·
                        rfl

theorem cell23_5664042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_5664042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664042 prefixEnd_5664042 := by exact prefixLift 5664042
  have htrace : WordTrace (prefixWord ++ tailWord_5664042) baseStart_5664042 baseEnd_5664042 := by
    simpa [prefixWord, tailWord_5664042, baseEnd_5664042] using wordTrace_append hprefix tailTrace_5664042
  have hstable : (prefixWord ++ tailWord_5664042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664042).length < 2 ^ (prefixWord ++ tailWord_5664042).sum := by decide
  have hdescent : baseEnd_5664042 < baseStart_5664042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664077 : List Nat := [1, 6, 1, 3, 2, 1, 1, 2, 2, 2, 2]
def baseStart_5664077 : Nat := 118140960795 + 5664077 * 2 ^ 59
def prefixEnd_5664077 : Nat := 4983230072969 + 3 ^ 40 * 5664077 * 2
def baseEnd_5664077 : Nat := 2908393965076341006388891

theorem tailTrace_5664077 : CollatzResearch.WordTrace tailWord_5664077 prefixEnd_5664077 2908393965076341006388891 := by
  unfold tailWord_5664077
  simp only [CollatzResearch.WordTrace]
  refine ⟨206585859901023851182254485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137723906600682567454836323 206585859901023851182254485)
  ·
    refine ⟨9683712182860493024168179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 206585859901023851182254485 9683712182860493024168179)
    ·
      refine ⟨14525568274290739536252269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9683712182860493024168179 14525568274290739536252269)
      ·
        refine ⟨5447088102859027326094601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14525568274290739536252269 5447088102859027326094601)
        ·
          refine ⟨4085316077144270494570951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5447088102859027326094601 4085316077144270494570951)
          ·
            refine ⟨6127974115716405741856427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4085316077144270494570951 6127974115716405741856427)
            ·
              refine ⟨9191961173574608612784641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6127974115716405741856427 9191961173574608612784641)
              ·
                refine ⟨6893970880180956459588481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9191961173574608612784641 6893970880180956459588481)
                ·
                  refine ⟨5170478160135717344691361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6893970880180956459588481 5170478160135717344691361)
                  ·
                    refine ⟨3877858620101788008518521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5170478160135717344691361 3877858620101788008518521)
                    ·
                      refine ⟨2908393965076341006388891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3877858620101788008518521 2908393965076341006388891)
                      ·
                        rfl

theorem cell23_5664077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_5664077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664077 prefixEnd_5664077 := by exact prefixLift 5664077
  have htrace : WordTrace (prefixWord ++ tailWord_5664077) baseStart_5664077 baseEnd_5664077 := by
    simpa [prefixWord, tailWord_5664077, baseEnd_5664077] using wordTrace_append hprefix tailTrace_5664077
  have hstable : (prefixWord ++ tailWord_5664077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664077).length < 2 ^ (prefixWord ++ tailWord_5664077).sum := by decide
  have hdescent : baseEnd_5664077 < baseStart_5664077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664149 : List Nat := [1, 3, 2, 1, 1, 2, 5, 1, 3, 1, 3]
def baseStart_5664149 : Nat := 118140960795 + 5664149 * 2 ^ 59
def prefixEnd_5664149 : Nat := 4983230072969 + 3 ^ 40 * 5664149 * 2
def baseEnd_5664149 : Nat := 2908430935683464724688559

theorem tailTrace_5664149 : CollatzResearch.WordTrace tailWord_5664149 prefixEnd_5664149 2908430935683464724688559 := by
  unfold tailWord_5664149
  simp only [CollatzResearch.WordTrace]
  refine ⟨206588485956763007478875501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137725657304508671652583667 206588485956763007478875501)
  ·
    refine ⟨77470682233786127804578313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206588485956763007478875501 77470682233786127804578313)
    ·
      refine ⟨58103011675339595853433735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77470682233786127804578313 58103011675339595853433735)
      ·
        refine ⟨87154517513009393780150603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58103011675339595853433735 87154517513009393780150603)
        ·
          refine ⟨130731776269514090670225905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87154517513009393780150603 130731776269514090670225905)
          ·
            refine ⟨98048832202135568002669429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130731776269514090670225905 98048832202135568002669429)
            ·
              refine ⟨9192078018950209500250259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98048832202135568002669429 9192078018950209500250259)
              ·
                refine ⟨13788117028425314250375389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9192078018950209500250259 13788117028425314250375389)
                ·
                  refine ⟨5170543885659492843890771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13788117028425314250375389 5170543885659492843890771)
                  ·
                    refine ⟨7755815828489239265836157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5170543885659492843890771 7755815828489239265836157)
                    ·
                      refine ⟨2908430935683464724688559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7755815828489239265836157 2908430935683464724688559)
                      ·
                        rfl

theorem cell23_5664149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_5664149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664149 prefixEnd_5664149 := by exact prefixLift 5664149
  have htrace : WordTrace (prefixWord ++ tailWord_5664149) baseStart_5664149 baseEnd_5664149 := by
    simpa [prefixWord, tailWord_5664149, baseEnd_5664149] using wordTrace_append hprefix tailTrace_5664149
  have hstable : (prefixWord ++ tailWord_5664149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664149).length < 2 ^ (prefixWord ++ tailWord_5664149).sum := by decide
  have hdescent : baseEnd_5664149 < baseStart_5664149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664172 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 2, 6, 2]
def baseStart_5664172 : Nat := 118140960795 + 5664172 * 2 ^ 59
def prefixEnd_5664172 : Nat := 4983230072969 + 3 ^ 40 * 5664172 * 2
def baseEnd_5664172 : Nat := 2908442745738518134700953

theorem tailTrace_5664172 : CollatzResearch.WordTrace tailWord_5664172 prefixEnd_5664172 2908442745738518134700953 := by
  unfold tailWord_5664172
  simp only [CollatzResearch.WordTrace]
  refine ⟨103294662417839841203481385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137726216557119788271308513 103294662417839841203481385)
  ·
    refine ⟨77470996813379880902611039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103294662417839841203481385 77470996813379880902611039)
    ·
      refine ⟨116206495220069821353916559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77470996813379880902611039 116206495220069821353916559)
      ·
        refine ⟨174309742830104732030874839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116206495220069821353916559 174309742830104732030874839)
        ·
          refine ⟨261464614245157098046312259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174309742830104732030874839 261464614245157098046312259)
          ·
            refine ⟨392196921367735647069468389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261464614245157098046312259 392196921367735647069468389)
            ·
              refine ⟨73536922756450433825525323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 392196921367735647069468389 73536922756450433825525323)
              ·
                refine ⟨110305384134675650738287985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73536922756450433825525323 110305384134675650738287985)
                ·
                  refine ⟨82729038101006738053715989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110305384134675650738287985 82729038101006738053715989)
                  ·
                    refine ⟨3877923660984690846267937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82729038101006738053715989 3877923660984690846267937)
                    ·
                      refine ⟨2908442745738518134700953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3877923660984690846267937 2908442745738518134700953)
                      ·
                        rfl

theorem cell23_5664172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 6, 2].length) (baseStart_5664172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664172 prefixEnd_5664172 := by exact prefixLift 5664172
  have htrace : WordTrace (prefixWord ++ tailWord_5664172) baseStart_5664172 baseEnd_5664172 := by
    simpa [prefixWord, tailWord_5664172, baseEnd_5664172] using wordTrace_append hprefix tailTrace_5664172
  have hstable : (prefixWord ++ tailWord_5664172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664172).length < 2 ^ (prefixWord ++ tailWord_5664172).sum := by decide
  have hdescent : baseEnd_5664172 < baseStart_5664172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664175 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 5]
def baseStart_5664175 : Nat := 118140960795 + 5664175 * 2 ^ 59
def prefixEnd_5664175 : Nat := 4983230072969 + 3 ^ 40 * 5664175 * 2
def baseEnd_5664175 : Nat := 2908444286180481622963439

theorem tailTrace_5664175 : CollatzResearch.WordTrace tailWord_5664175 prefixEnd_5664175 2908444286180481622963439 := by
  unfold tailWord_5664175
  simp only [CollatzResearch.WordTrace]
  refine ⟨206589434254668813919321979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137726289503112542612881319 206589434254668813919321979)
  ·
    refine ⟨309884151382003220878982969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206589434254668813919321979 309884151382003220878982969)
    ·
      refine ⟨232413113536502415659237227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309884151382003220878982969 232413113536502415659237227)
      ·
        refine ⟨348619670304753623488855841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232413113536502415659237227 348619670304753623488855841)
        ·
          refine ⟨261464752728565217616641881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348619670304753623488855841 261464752728565217616641881)
          ·
            refine ⟨196098564546423913212481411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261464752728565217616641881 196098564546423913212481411)
            ·
              refine ⟨294147846819635869818722117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196098564546423913212481411 294147846819635869818722117)
              ·
                refine ⟨55152721278681725591010397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 294147846819635869818722117 55152721278681725591010397)
                ·
                  refine ⟨20682270479505647096628899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55152721278681725591010397 20682270479505647096628899)
                  ·
                    refine ⟨31023405719258470644943349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20682270479505647096628899 31023405719258470644943349)
                    ·
                      refine ⟨2908444286180481622963439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31023405719258470644943349 2908444286180481622963439)
                      ·
                        rfl

theorem cell23_5664175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 5].length) (baseStart_5664175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664175 prefixEnd_5664175 := by exact prefixLift 5664175
  have htrace : WordTrace (prefixWord ++ tailWord_5664175) baseStart_5664175 baseEnd_5664175 := by
    simpa [prefixWord, tailWord_5664175, baseEnd_5664175] using wordTrace_append hprefix tailTrace_5664175
  have hstable : (prefixWord ++ tailWord_5664175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664175).length < 2 ^ (prefixWord ++ tailWord_5664175).sum := by decide
  have hdescent : baseEnd_5664175 < baseStart_5664175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664192 : List Nat := [2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 5]
def baseStart_5664192 : Nat := 118140960795 + 5664192 * 2 ^ 59
def prefixEnd_5664192 : Nat := 4983230072969 + 3 ^ 40 * 5664192 * 2
def baseEnd_5664192 : Nat := 2908453015351608056450861

theorem tailTrace_5664192 : CollatzResearch.WordTrace tailWord_5664192 prefixEnd_5664192 2908453015351608056450861 := by
  unfold tailWord_5664192
  simp only [CollatzResearch.WordTrace]
  refine ⟨103295027147803612911345415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137726702863738150548460553 103295027147803612911345415)
  ·
    refine ⟨154942540721705419367018123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103295027147803612911345415 154942540721705419367018123)
    ·
      refine ⟨232413811082558129050527185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154942540721705419367018123 232413811082558129050527185)
      ·
        refine ⟨174310358311918596787895389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232413811082558129050527185 174310358311918596787895389)
        ·
          refine ⟨65366384366969473795460771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174310358311918596787895389 65366384366969473795460771)
          ·
            refine ⟨98049576550454210693191157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65366384366969473795460771 98049576550454210693191157)
            ·
              refine ⟨9192147801605082252486671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98049576550454210693191157 9192147801605082252486671)
              ·
                refine ⟨13788221702407623378730007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9192147801605082252486671 13788221702407623378730007)
                ·
                  refine ⟨20682332553611435068095011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13788221702407623378730007 20682332553611435068095011)
                  ·
                    refine ⟨31023498830417152602142517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20682332553611435068095011 31023498830417152602142517)
                    ·
                      refine ⟨2908453015351608056450861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31023498830417152602142517 2908453015351608056450861)
                      ·
                        rfl

theorem cell23_5664192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 5].length) (baseStart_5664192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664192 prefixEnd_5664192 := by exact prefixLift 5664192
  have htrace : WordTrace (prefixWord ++ tailWord_5664192) baseStart_5664192 baseEnd_5664192 := by
    simpa [prefixWord, tailWord_5664192, baseEnd_5664192] using wordTrace_append hprefix tailTrace_5664192
  have hstable : (prefixWord ++ tailWord_5664192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664192).length < 2 ^ (prefixWord ++ tailWord_5664192).sum := by decide
  have hdescent : baseEnd_5664192 < baseStart_5664192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664199 : List Nat := [1, 1, 4, 1, 1, 3, 4, 2, 2, 4]
def baseStart_5664199 : Nat := 118140960795 + 5664199 * 2 ^ 59
def prefixEnd_5664199 : Nat := 4983230072969 + 3 ^ 40 * 5664199 * 2
def baseEnd_5664199 : Nat := 969485536572063176354443

theorem tailTrace_5664199 : CollatzResearch.WordTrace tailWord_5664199 prefixEnd_5664199 969485536572063176354443 := by
  unfold tailWord_5664199
  simp only [CollatzResearch.WordTrace]
  refine ⟨206590309606581866018195651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137726873071054577345463767 206590309606581866018195651)
  ·
    refine ⟨309885464409872799027293477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206590309606581866018195651 309885464409872799027293477)
    ·
      refine ⟨58103524576851149817617527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 309885464409872799027293477 58103524576851149817617527)
      ·
        refine ⟨87155286865276724726426291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58103524576851149817617527 87155286865276724726426291)
        ·
          refine ⟨130732930297915087089639437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87155286865276724726426291 130732930297915087089639437)
          ·
            refine ⟨49024848861718157658614789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130732930297915087089639437 49024848861718157658614789)
            ·
              refine ⟨9192159161572154560990273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49024848861718157658614789 9192159161572154560990273)
              ·
                refine ⟨6894119371179115920742705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9192159161572154560990273 6894119371179115920742705)
                ·
                  refine ⟨5170589528384336940557029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6894119371179115920742705 5170589528384336940557029)
                  ·
                    refine ⟨969485536572063176354443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5170589528384336940557029 969485536572063176354443)
                    ·
                      rfl

theorem cell23_5664199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_5664199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664199 prefixEnd_5664199 := by exact prefixLift 5664199
  have htrace : WordTrace (prefixWord ++ tailWord_5664199) baseStart_5664199 baseEnd_5664199 := by
    simpa [prefixWord, tailWord_5664199, baseEnd_5664199] using wordTrace_append hprefix tailTrace_5664199
  have hstable : (prefixWord ++ tailWord_5664199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664199).length < 2 ^ (prefixWord ++ tailWord_5664199).sum := by decide
  have hdescent : baseEnd_5664199 < baseStart_5664199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664215 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 6]
def baseStart_5664215 : Nat := 118140960795 + 5664215 * 2 ^ 59
def prefixEnd_5664215 : Nat := 4983230072969 + 3 ^ 40 * 5664215 * 2
def baseEnd_5664215 : Nat := 2908464825406661466463255

theorem tailTrace_5664215 : CollatzResearch.WordTrace tailWord_5664215 prefixEnd_5664215 2908464825406661466463255 := by
  unfold tailWord_5664215
  simp only [CollatzResearch.WordTrace]
  refine ⟨206590893174523900750778099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137727262116349267167185399 206590893174523900750778099)
  ·
    refine ⟨309886339761785851126167149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206590893174523900750778099 309886339761785851126167149)
    ·
      refine ⟨116207377410669694172312681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 309886339761785851126167149 116207377410669694172312681)
      ·
        refine ⟨87155533058002270629234511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116207377410669694172312681 87155533058002270629234511)
        ·
          refine ⟨130733299587003405943851767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87155533058002270629234511 130733299587003405943851767)
          ·
            refine ⟨196099949380505108915777651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130733299587003405943851767 196099949380505108915777651)
            ·
              refine ⟨294149924070757663373666477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196099949380505108915777651 294149924070757663373666477)
              ·
                refine ⟨110306221526534123765124929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 294149924070757663373666477 110306221526534123765124929)
                ·
                  refine ⟨82729666144900592823843697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110306221526534123765124929 82729666144900592823843697)
                  ·
                    refine ⟨62047249608675444617882773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82729666144900592823843697 62047249608675444617882773)
                    ·
                      refine ⟨2908464825406661466463255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62047249608675444617882773 2908464825406661466463255)
                      ·
                        rfl

theorem cell23_5664215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_5664215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664215 prefixEnd_5664215 := by exact prefixLift 5664215
  have htrace : WordTrace (prefixWord ++ tailWord_5664215) baseStart_5664215 baseEnd_5664215 := by
    simpa [prefixWord, tailWord_5664215, baseEnd_5664215] using wordTrace_append hprefix tailTrace_5664215
  have hstable : (prefixWord ++ tailWord_5664215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664215).length < 2 ^ (prefixWord ++ tailWord_5664215).sum := by decide
  have hdescent : baseEnd_5664215 < baseStart_5664215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664229 : List Nat := [1, 3, 1, 5, 1, 2, 3, 7]
def baseStart_5664229 : Nat := 118140960795 + 5664229 * 2 ^ 59
def prefixEnd_5664229 : Nat := 4983230072969 + 3 ^ 40 * 5664229 * 2
def baseEnd_5664229 : Nat := 107721185708734237469933

theorem tailTrace_5664229 : CollatzResearch.WordTrace tailWord_5664229 prefixEnd_5664229 107721185708734237469933 := by
  unfold tailWord_5664229
  simp only [CollatzResearch.WordTrace]
  refine ⟨206591403796473181141787741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137727602530982120761191827 206591403796473181141787741)
  ·
    refine ⟨77471776423677442928170403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206591403796473181141787741 77471776423677442928170403)
    ·
      refine ⟨116207664635516164392255605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77471776423677442928170403 116207664635516164392255605)
      ·
        refine ⟨10894468559579640411773963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116207664635516164392255605 10894468559579640411773963)
        ·
          refine ⟨16341702839369460617660945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10894468559579640411773963 16341702839369460617660945)
          ·
            refine ⟨12256277129527095463245709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16341702839369460617660945 12256277129527095463245709)
            ·
              refine ⟨4596103923572660798717141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12256277129527095463245709 4596103923572660798717141)
              ·
                refine ⟨107721185708734237469933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4596103923572660798717141 107721185708734237469933)
                ·
                  rfl

theorem cell23_5664229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 7].length) (baseStart_5664229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664229 prefixEnd_5664229 := by exact prefixLift 5664229
  have htrace : WordTrace (prefixWord ++ tailWord_5664229) baseStart_5664229 baseEnd_5664229 := by
    simpa [prefixWord, tailWord_5664229, baseEnd_5664229] using wordTrace_append hprefix tailTrace_5664229
  have hstable : (prefixWord ++ tailWord_5664229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664229).length < 2 ^ (prefixWord ++ tailWord_5664229).sum := by decide
  have hdescent : baseEnd_5664229 < baseStart_5664229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664282 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5]
def baseStart_5664282 : Nat := 118140960795 + 5664282 * 2 ^ 59
def prefixEnd_5664282 : Nat := 4983230072969 + 3 ^ 40 * 5664282 * 2
def baseEnd_5664282 : Nat := 2908499228610512704325447

theorem tailTrace_5664282 : CollatzResearch.WordTrace tailWord_5664282 prefixEnd_5664282 2908499228610512704325447 := by
  unfold tailWord_5664282
  simp only [CollatzResearch.WordTrace]
  refine ⟨51648334216320292798366775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137728891243520780795644733 51648334216320292798366775)
  ·
    refine ⟨77472501324480439197550163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51648334216320292798366775 77472501324480439197550163)
    ·
      refine ⟨116208751986720658796325245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77472501324480439197550163 116208751986720658796325245)
      ·
        refine ⟨43578281995020247048621967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116208751986720658796325245 43578281995020247048621967)
        ·
          refine ⟨65367422992530370572932951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43578281995020247048621967 65367422992530370572932951)
          ·
            refine ⟨98051134488795555859399427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65367422992530370572932951 98051134488795555859399427)
            ·
              refine ⟨147076701733193333789099141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98051134488795555859399427 147076701733193333789099141)
              ·
                refine ⟨27576881574973750085456089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147076701733193333789099141 27576881574973750085456089)
                ·
                  refine ⟨20682661181230312564092067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27576881574973750085456089 20682661181230312564092067)
                  ·
                    refine ⟨31023991771845468846138101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20682661181230312564092067 31023991771845468846138101)
                    ·
                      refine ⟨2908499228610512704325447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31023991771845468846138101 2908499228610512704325447)
                      ·
                        rfl

theorem cell23_5664282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_5664282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664282 prefixEnd_5664282 := by exact prefixLift 5664282
  have htrace : WordTrace (prefixWord ++ tailWord_5664282) baseStart_5664282 baseEnd_5664282 := by
    simpa [prefixWord, tailWord_5664282, baseEnd_5664282] using wordTrace_append hprefix tailTrace_5664282
  have hstable : (prefixWord ++ tailWord_5664282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664282).length < 2 ^ (prefixWord ++ tailWord_5664282).sum := by decide
  have hdescent : baseEnd_5664282 < baseStart_5664282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664319 : List Nat := [1, 1, 2, 2, 3, 5, 1, 1, 7]
def baseStart_5664319 : Nat := 118140960795 + 5664319 * 2 ^ 59
def prefixEnd_5664319 : Nat := 4983230072969 + 3 ^ 40 * 5664319 * 2
def baseEnd_5664319 : Nat := 323168691932747673284753

theorem tailTrace_5664319 : CollatzResearch.WordTrace tailWord_5664319 prefixEnd_5664319 323168691932747673284753 := by
  unfold tailWord_5664319
  simp only [CollatzResearch.WordTrace]
  refine ⟨206594686366147126512564011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137729790910764751008376007 206594686366147126512564011)
  ·
    refine ⟨309892029549220689768846017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206594686366147126512564011 309892029549220689768846017)
    ·
      refine ⟨232419022161915517326634513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309892029549220689768846017 232419022161915517326634513)
      ·
        refine ⟨174314266621436637994975885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232419022161915517326634513 174314266621436637994975885)
        ·
          refine ⟨65367849983038739248115957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174314266621436637994975885 65367849983038739248115957)
          ·
            refine ⟨6128235935909881804510871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65367849983038739248115957 6128235935909881804510871)
            ·
              refine ⟨9192353903864822706766307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6128235935909881804510871 9192353903864822706766307)
              ·
                refine ⟨13788530855797234060149461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9192353903864822706766307 13788530855797234060149461)
                ·
                  refine ⟨323168691932747673284753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13788530855797234060149461 323168691932747673284753)
                  ·
                    rfl

theorem cell23_5664319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 7].length) (baseStart_5664319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664319 prefixEnd_5664319 := by exact prefixLift 5664319
  have htrace : WordTrace (prefixWord ++ tailWord_5664319) baseStart_5664319 baseEnd_5664319 := by
    simpa [prefixWord, tailWord_5664319, baseEnd_5664319] using wordTrace_append hprefix tailTrace_5664319
  have hstable : (prefixWord ++ tailWord_5664319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664319).length < 2 ^ (prefixWord ++ tailWord_5664319).sum := by decide
  have hdescent : baseEnd_5664319 < baseStart_5664319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664369 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 3, 6, 2]
def baseStart_5664369 : Nat := 118140960795 + 5664369 * 2 ^ 59
def prefixEnd_5664369 : Nat := 4983230072969 + 3 ^ 40 * 5664369 * 2
def baseEnd_5664369 : Nat := 2908543901427453863937547

theorem tailTrace_5664369 : CollatzResearch.WordTrace tailWord_5664369 prefixEnd_5664369 2908543901427453863937547 := by
  unfold tailWord_5664369
  simp only [CollatzResearch.WordTrace]
  refine ⟨206596510015965985051884161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137731006677310656701256107 206596510015965985051884161)
  ·
    refine ⟨154947382511974488788913121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206596510015965985051884161 154947382511974488788913121)
    ·
      refine ⟨116210536883980866591684841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154947382511974488788913121 116210536883980866591684841)
      ·
        refine ⟨87157902662985649943763631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116210536883980866591684841 87157902662985649943763631)
        ·
          refine ⟨130736853994478474915645447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87157902662985649943763631 130736853994478474915645447)
          ·
            refine ⟨196105280991717712373468171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130736853994478474915645447 196105280991717712373468171)
            ·
              refine ⟨294157921487576568560202257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196105280991717712373468171 294157921487576568560202257)
              ·
                refine ⟨220618441115682426420151693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294157921487576568560202257 220618441115682426420151693)
                ·
                  refine ⟨82731915418380909907556885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 220618441115682426420151693 82731915418380909907556885)
                  ·
                    refine ⟨3878058535236605151916729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82731915418380909907556885 3878058535236605151916729)
                    ·
                      refine ⟨2908543901427453863937547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3878058535236605151916729 2908543901427453863937547)
                      ·
                        rfl

theorem cell23_5664369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 6, 2].length) (baseStart_5664369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664369 prefixEnd_5664369 := by exact prefixLift 5664369
  have htrace : WordTrace (prefixWord ++ tailWord_5664369) baseStart_5664369 baseEnd_5664369 := by
    simpa [prefixWord, tailWord_5664369, baseEnd_5664369] using wordTrace_append hprefix tailTrace_5664369
  have hstable : (prefixWord ++ tailWord_5664369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664369).length < 2 ^ (prefixWord ++ tailWord_5664369).sum := by decide
  have hdescent : baseEnd_5664369 < baseStart_5664369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664379 : List Nat := [1, 1, 1, 1, 1, 4, 4, 3, 3, 4]
def baseStart_5664379 : Nat := 118140960795 + 5664379 * 2 ^ 59
def prefixEnd_5664379 : Nat := 4983230072969 + 3 ^ 40 * 5664379 * 2
def baseEnd_5664379 : Nat := 969516345411332941604167

theorem tailTrace_5664379 : CollatzResearch.WordTrace tailWord_5664379 prefixEnd_5664379 969516345411332941604167 := by
  unfold tailWord_5664379
  simp only [CollatzResearch.WordTrace]
  refine ⟨206596874745929756759748191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137731249830619837839832127 206596874745929756759748191)
  ·
    refine ⟨309895312118894635139622287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206596874745929756759748191 309895312118894635139622287)
    ·
      refine ⟨464842968178341952709433431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309895312118894635139622287 464842968178341952709433431)
      ·
        refine ⟨697264452267512929064150147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464842968178341952709433431 697264452267512929064150147)
        ·
          refine ⟨1045896678401269393596225221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697264452267512929064150147 1045896678401269393596225221)
          ·
            refine ⟨196105627200238011299292229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1045896678401269393596225221 196105627200238011299292229)
            ·
              refine ⟨36769805100044627118617293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196105627200238011299292229 36769805100044627118617293)
              ·
                refine ⟨13788676912516735169481485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36769805100044627118617293 13788676912516735169481485)
                ·
                  refine ⟨5170753842193775688555557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13788676912516735169481485 5170753842193775688555557)
                  ·
                    refine ⟨969516345411332941604167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5170753842193775688555557 969516345411332941604167)
                    ·
                      rfl

theorem cell23_5664379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 4].length) (baseStart_5664379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664379 prefixEnd_5664379 := by exact prefixLift 5664379
  have htrace : WordTrace (prefixWord ++ tailWord_5664379) baseStart_5664379 baseEnd_5664379 := by
    simpa [prefixWord, tailWord_5664379, baseEnd_5664379] using wordTrace_append hprefix tailTrace_5664379
  have hstable : (prefixWord ++ tailWord_5664379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664379).length < 2 ^ (prefixWord ++ tailWord_5664379).sum := by decide
  have hdescent : baseEnd_5664379 < baseStart_5664379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664389 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 1, 4, 3]
def baseStart_5664389 : Nat := 118140960795 + 5664389 * 2 ^ 59
def prefixEnd_5664389 : Nat := 4983230072969 + 3 ^ 40 * 5664389 * 2
def baseEnd_5664389 : Nat := 2908554171040543785687455

theorem tailTrace_5664389 : CollatzResearch.WordTrace tailWord_5664389 prefixEnd_5664389 2908554171040543785687455 := by
  unfold tailWord_5664389
  simp only [CollatzResearch.WordTrace]
  refine ⟨206597239475893528467612221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137731492983929018978408147 206597239475893528467612221)
  ·
    refine ⟨77473964803460073175354583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206597239475893528467612221 77473964803460073175354583)
    ·
      refine ⟨116210947205190109763031875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77473964803460073175354583 116210947205190109763031875)
      ·
        refine ⟨174316420807785164644547813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116210947205190109763031875 174316420807785164644547813)
        ·
          refine ⟨32684328901459718370852715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174316420807785164644547813 32684328901459718370852715)
          ·
            refine ⟨49026493352189577556279073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32684328901459718370852715 49026493352189577556279073)
            ·
              refine ⟨36769870014142183167209305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49026493352189577556279073 36769870014142183167209305)
              ·
                refine ⟨27577402510606637375406979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36769870014142183167209305 27577402510606637375406979)
                ·
                  refine ⟨41366103765909956063110469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27577402510606637375406979 41366103765909956063110469)
                  ·
                    refine ⟨7756144456108116761833213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41366103765909956063110469 7756144456108116761833213)
                    ·
                      refine ⟨2908554171040543785687455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7756144456108116761833213 2908554171040543785687455)
                      ·
                        rfl

theorem cell23_5664389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 4, 3].length) (baseStart_5664389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664389 prefixEnd_5664389 := by exact prefixLift 5664389
  have htrace : WordTrace (prefixWord ++ tailWord_5664389) baseStart_5664389 baseEnd_5664389 := by
    simpa [prefixWord, tailWord_5664389, baseEnd_5664389] using wordTrace_append hprefix tailTrace_5664389
  have hstable : (prefixWord ++ tailWord_5664389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664389).length < 2 ^ (prefixWord ++ tailWord_5664389).sum := by decide
  have hdescent : baseEnd_5664389 < baseStart_5664389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664429 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_5664429 : Nat := 118140960795 + 5664429 * 2 ^ 59
def prefixEnd_5664429 : Nat := 4983230072969 + 3 ^ 40 * 5664429 * 2
def baseEnd_5664429 : Nat := 2908574710266723629187271

theorem tailTrace_5664429 : CollatzResearch.WordTrace tailWord_5664429 prefixEnd_5664429 2908574710266723629187271 := by
  unfold tailWord_5664429
  simp only [CollatzResearch.WordTrace]
  refine ⟨206598698395748615299068341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137732465597165743532712227 206598698395748615299068341)
  ·
    refine ⟨19368627974601432684287657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 206598698395748615299068341 19368627974601432684287657)
    ·
      refine ⟨14526470980951074513215743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19368627974601432684287657 14526470980951074513215743)
      ·
        refine ⟨21789706471426611769823615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14526470980951074513215743 21789706471426611769823615)
        ·
          refine ⟨32684559707139917654735423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21789706471426611769823615 32684559707139917654735423)
          ·
            refine ⟨49026839560709876482103135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32684559707139917654735423 49026839560709876482103135)
            ·
              refine ⟨73540259341064814723154703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49026839560709876482103135 73540259341064814723154703)
              ·
                refine ⟨110310389011597222084732055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73540259341064814723154703 110310389011597222084732055)
                ·
                  refine ⟨165465583517395833127098083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110310389011597222084732055 165465583517395833127098083)
                  ·
                    refine ⟨248198375276093749690647125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 165465583517395833127098083 248198375276093749690647125)
                    ·
                      refine ⟨2908574710266723629187271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 248198375276093749690647125 2908574710266723629187271)
                      ·
                        rfl

theorem cell23_5664429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_5664429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664429 prefixEnd_5664429 := by exact prefixLift 5664429
  have htrace : WordTrace (prefixWord ++ tailWord_5664429) baseStart_5664429 baseEnd_5664429 := by
    simpa [prefixWord, tailWord_5664429, baseEnd_5664429] using wordTrace_append hprefix tailTrace_5664429
  have hstable : (prefixWord ++ tailWord_5664429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664429).length < 2 ^ (prefixWord ++ tailWord_5664429).sum := by decide
  have hdescent : baseEnd_5664429 < baseStart_5664429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664430 : List Nat := [4, 1, 4, 1, 2, 1, 2, 1, 3, 4]
def baseStart_5664430 : Nat := 118140960795 + 5664430 * 2 ^ 59
def prefixEnd_5664430 : Nat := 4983230072969 + 3 ^ 40 * 5664430 * 2
def baseEnd_5664430 : Nat := 969525074582459375091589

theorem tailTrace_5664430 : CollatzResearch.WordTrace tailWord_5664430 prefixEnd_5664430 969525074582459375091589 := by
  unfold tailWord_5664430
  simp only [CollatzResearch.WordTrace]
  refine ⟨25824841858593124058731843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137732489912496661646569829 25824841858593124058731843)
  ·
    refine ⟨38737262787889686088097765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25824841858593124058731843 38737262787889686088097765)
    ·
      refine ⟨7263236772729316141518331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38737262787889686088097765 7263236772729316141518331)
      ·
        refine ⟨10894855159093974212277497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7263236772729316141518331 10894855159093974212277497)
        ·
          refine ⟨8171141369320480659208123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10894855159093974212277497 8171141369320480659208123)
          ·
            refine ⟨12256712053980720988812185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8171141369320480659208123 12256712053980720988812185)
            ·
              refine ⟨9192534040485540741609139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12256712053980720988812185 9192534040485540741609139)
              ·
                refine ⟨13788801060728311112413709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9192534040485540741609139 13788801060728311112413709)
                ·
                  refine ⟨5170800397773116667155141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13788801060728311112413709 5170800397773116667155141)
                  ·
                    refine ⟨969525074582459375091589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5170800397773116667155141 969525074582459375091589)
                    ·
                      rfl

theorem cell23_5664430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_5664430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664430 prefixEnd_5664430 := by exact prefixLift 5664430
  have htrace : WordTrace (prefixWord ++ tailWord_5664430) baseStart_5664430 baseEnd_5664430 := by
    simpa [prefixWord, tailWord_5664430, baseEnd_5664430] using wordTrace_append hprefix tailTrace_5664430
  have hstable : (prefixWord ++ tailWord_5664430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664430).length < 2 ^ (prefixWord ++ tailWord_5664430).sum := by decide
  have hdescent : baseEnd_5664430 < baseStart_5664430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664456 : List Nat := [2, 1, 3, 1, 2, 2, 4, 2, 1, 5]
def baseStart_5664456 : Nat := 118140960795 + 5664456 * 2 ^ 59
def prefixEnd_5664456 : Nat := 4983230072969 + 3 ^ 40 * 5664456 * 2
def baseEnd_5664456 : Nat := 969529524748131674516549

theorem tailTrace_5664456 : CollatzResearch.WordTrace tailWord_5664456 prefixEnd_5664456 969529524748131674516549 := by
  unfold tailWord_5664456
  simp only [CollatzResearch.WordTrace]
  refine ⟨103299841583325399455150611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137733122111100532606867481 103299841583325399455150611)
  ·
    refine ⟨154949762374988099182725917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103299841583325399455150611 154949762374988099182725917)
    ·
      refine ⟨58106160890620537193522219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154949762374988099182725917 58106160890620537193522219)
      ·
        refine ⟨87159241335930805790283329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58106160890620537193522219 87159241335930805790283329)
        ·
          refine ⟨65369431001948104342712497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87159241335930805790283329 65369431001948104342712497)
          ·
            refine ⟨49027073251461078257034373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65369431001948104342712497 49027073251461078257034373)
            ·
              refine ⟨9192576234648952173193945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49027073251461078257034373 9192576234648952173193945)
              ·
                refine ⟨6894432175986714129895459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9192576234648952173193945 6894432175986714129895459)
                ·
                  refine ⟨10341648263980071194843189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6894432175986714129895459 10341648263980071194843189)
                  ·
                    refine ⟨969529524748131674516549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10341648263980071194843189 969529524748131674516549)
                    ·
                      rfl

theorem cell23_5664456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_5664456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664456 prefixEnd_5664456 := by exact prefixLift 5664456
  have htrace : WordTrace (prefixWord ++ tailWord_5664456) baseStart_5664456 baseEnd_5664456 := by
    simpa [prefixWord, tailWord_5664456, baseEnd_5664456] using wordTrace_append hprefix tailTrace_5664456
  have hstable : (prefixWord ++ tailWord_5664456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664456).length < 2 ^ (prefixWord ++ tailWord_5664456).sum := by decide
  have hdescent : baseEnd_5664456 < baseStart_5664456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664459 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 4]
def baseStart_5664459 : Nat := 118140960795 + 5664459 * 2 ^ 59
def prefixEnd_5664459 : Nat := 4983230072969 + 3 ^ 40 * 5664459 * 2
def baseEnd_5664459 : Nat := 2908590114686358511812133

theorem tailTrace_5664459 : CollatzResearch.WordTrace tailWord_5664459 prefixEnd_5664459 2908590114686358511812133 := by
  unfold tailWord_5664459
  simp only [CollatzResearch.WordTrace]
  refine ⟨206599792585639930422660431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137733195057093286948440287 206599792585639930422660431)
  ·
    refine ⟨309899688878459895633990647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206599792585639930422660431 309899688878459895633990647)
    ·
      refine ⟨464849533317689843450985971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309899688878459895633990647 464849533317689843450985971)
      ·
        refine ⟨697274299976534765176478957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464849533317689843450985971 697274299976534765176478957)
        ·
          refine ⟨261477862491200536941179609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 697274299976534765176478957 261477862491200536941179609)
          ·
            refine ⟨196108396868400402705884707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261477862491200536941179609 196108396868400402705884707)
            ·
              refine ⟨294162595302600604058827061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196108396868400402705884707 294162595302600604058827061)
              ·
                refine ⟨27577743309618806630515037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 294162595302600604058827061 27577743309618806630515037)
                ·
                  refine ⟨10341653741107052486443139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27577743309618806630515037 10341653741107052486443139)
                  ·
                    refine ⟨15512480611660578729664709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10341653741107052486443139 15512480611660578729664709)
                    ·
                      refine ⟨2908590114686358511812133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15512480611660578729664709 2908590114686358511812133)
                      ·
                        rfl

theorem cell23_5664459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 4].length) (baseStart_5664459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664459 prefixEnd_5664459 := by exact prefixLift 5664459
  have htrace : WordTrace (prefixWord ++ tailWord_5664459) baseStart_5664459 baseEnd_5664459 := by
    simpa [prefixWord, tailWord_5664459, baseEnd_5664459] using wordTrace_append hprefix tailTrace_5664459
  have hstable : (prefixWord ++ tailWord_5664459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664459).length < 2 ^ (prefixWord ++ tailWord_5664459).sum := by decide
  have hdescent : baseEnd_5664459 < baseStart_5664459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664487 : List Nat := [1, 1, 5, 4, 1, 2, 1, 1, 3, 1, 3]
def baseStart_5664487 : Nat := 118140960795 + 5664487 * 2 ^ 59
def prefixEnd_5664487 : Nat := 4983230072969 + 3 ^ 40 * 5664487 * 2
def baseEnd_5664487 : Nat := 2908604492144684402262005

theorem tailTrace_5664487 : CollatzResearch.WordTrace tailWord_5664487 prefixEnd_5664487 2908604492144684402262005 := by
  unfold tailWord_5664487
  simp only [CollatzResearch.WordTrace]
  refine ⟨206600813829538491204679715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137733875886358994136453143 206600813829538491204679715)
  ·
    refine ⟨309901220744307736807019573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206600813829538491204679715 309901220744307736807019573)
    ·
      refine ⟨29053239444778850325658085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 309901220744307736807019573 29053239444778850325658085)
      ·
        refine ⟨5447482395896034436060891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29053239444778850325658085 5447482395896034436060891)
        ·
          refine ⟨8171223593844051654091337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5447482395896034436060891 8171223593844051654091337)
          ·
            refine ⟨6128417695383038740568503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8171223593844051654091337 6128417695383038740568503)
            ·
              refine ⟨9192626543074558110852755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6128417695383038740568503 9192626543074558110852755)
              ·
                refine ⟨13788939814611837166279133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9192626543074558110852755 13788939814611837166279133)
                ·
                  refine ⟨5170852430479438937354675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13788939814611837166279133 5170852430479438937354675)
                  ·
                    refine ⟨7756278645719158406032013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5170852430479438937354675 7756278645719158406032013)
                    ·
                      refine ⟨2908604492144684402262005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7756278645719158406032013 2908604492144684402262005)
                      ·
                        rfl

theorem cell23_5664487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_5664487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664487 prefixEnd_5664487 := by exact prefixLift 5664487
  have htrace : WordTrace (prefixWord ++ tailWord_5664487) baseStart_5664487 baseEnd_5664487 := by
    simpa [prefixWord, tailWord_5664487, baseEnd_5664487] using wordTrace_append hprefix tailTrace_5664487
  have hstable : (prefixWord ++ tailWord_5664487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664487).length < 2 ^ (prefixWord ++ tailWord_5664487).sum := by decide
  have hdescent : baseEnd_5664487 < baseStart_5664487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664503 : List Nat := [1, 1, 3, 1, 1, 1, 8, 1, 2, 4]
def baseStart_5664503 : Nat := 118140960795 + 5664503 * 2 ^ 59
def prefixEnd_5664503 : Nat := 4983230072969 + 3 ^ 40 * 5664503 * 2
def baseEnd_5664503 : Nat := 969537569278385446553977

theorem tailTrace_5664503 : CollatzResearch.WordTrace tailWord_5664503 prefixEnd_5664503 969537569278385446553977 := by
  unfold tailWord_5664503
  simp only [CollatzResearch.WordTrace]
  refine ⟨206601397397480525937262163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137734264931653683958174775 206601397397480525937262163)
  ·
    refine ⟨309902096096220788905893245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206601397397480525937262163 309902096096220788905893245)
    ·
      refine ⟨116213286036082795839709967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 309902096096220788905893245 116213286036082795839709967)
      ·
        refine ⟨174319929054124193759564951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116213286036082795839709967 174319929054124193759564951)
        ·
          refine ⟨261479893581186290639347427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174319929054124193759564951 261479893581186290639347427)
          ·
            refine ⟨392219840371779435959021141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261479893581186290639347427 392219840371779435959021141)
            ·
              refine ⟨4596326254356790265144779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 392219840371779435959021141 4596326254356790265144779)
              ·
                refine ⟨6894489381535185397717169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4596326254356790265144779 6894489381535185397717169)
                ·
                  refine ⟨5170867036151389048287877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6894489381535185397717169 5170867036151389048287877)
                  ·
                    refine ⟨969537569278385446553977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5170867036151389048287877 969537569278385446553977)
                    ·
                      rfl

theorem cell23_5664503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 2, 4].length) (baseStart_5664503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664503 prefixEnd_5664503 := by exact prefixLift 5664503
  have htrace : WordTrace (prefixWord ++ tailWord_5664503) baseStart_5664503 baseEnd_5664503 := by
    simpa [prefixWord, tailWord_5664503, baseEnd_5664503] using wordTrace_append hprefix tailTrace_5664503
  have hstable : (prefixWord ++ tailWord_5664503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664503).length < 2 ^ (prefixWord ++ tailWord_5664503).sum := by decide
  have hdescent : baseEnd_5664503 < baseStart_5664503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664513 : List Nat := [1, 2, 4, 1, 1, 1, 5, 2, 1, 2, 3]
def baseStart_5664513 : Nat := 118140960795 + 5664513 * 2 ^ 59
def prefixEnd_5664513 : Nat := 4983230072969 + 3 ^ 40 * 5664513 * 2
def baseEnd_5664513 : Nat := 2908617842641701300536885

theorem tailTrace_5664513 : CollatzResearch.WordTrace tailWord_5664513 prefixEnd_5664513 2908617842641701300536885 := by
  unfold tailWord_5664513
  simp only [CollatzResearch.WordTrace]
  refine ⟨206601762127444297645126193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137734508084962865096750795 206601762127444297645126193)
  ·
    refine ⟨154951321595583223233844645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206601762127444297645126193 154951321595583223233844645)
    ·
      refine ⟨29053372799171854356345871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154951321595583223233844645 29053372799171854356345871)
      ·
        refine ⟨43580059198757781534518807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29053372799171854356345871 43580059198757781534518807)
        ·
          refine ⟨65370088798136672301778211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43580059198757781534518807 65370088798136672301778211)
          ·
            refine ⟨98055133197205008452667317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65370088798136672301778211 98055133197205008452667317)
            ·
              refine ⟨9192668737237969542437561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98055133197205008452667317 9192668737237969542437561)
              ·
                refine ⟨6894501552928477156828171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9192668737237969542437561 6894501552928477156828171)
                ·
                  refine ⟨10341752329392715735242257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6894501552928477156828171 10341752329392715735242257)
                  ·
                    refine ⟨7756314247044536801431693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10341752329392715735242257 7756314247044536801431693)
                    ·
                      refine ⟨2908617842641701300536885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7756314247044536801431693 2908617842641701300536885)
                      ·
                        rfl

theorem cell23_5664513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_5664513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664513 prefixEnd_5664513 := by exact prefixLift 5664513
  have htrace : WordTrace (prefixWord ++ tailWord_5664513) baseStart_5664513 baseEnd_5664513 := by
    simpa [prefixWord, tailWord_5664513, baseEnd_5664513] using wordTrace_append hprefix tailTrace_5664513
  have hstable : (prefixWord ++ tailWord_5664513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664513).length < 2 ^ (prefixWord ++ tailWord_5664513).sum := by decide
  have hdescent : baseEnd_5664513 < baseStart_5664513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664526 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3]
def baseStart_5664526 : Nat := 118140960795 + 5664526 * 2 ^ 59
def prefixEnd_5664526 : Nat := 4983230072969 + 3 ^ 40 * 5664526 * 2
def baseEnd_5664526 : Nat := 2908624517890209749674325

theorem tailTrace_5664526 : CollatzResearch.WordTrace tailWord_5664526 prefixEnd_5664526 2908624517890209749674325 := by
  unfold tailWord_5664526
  simp only [CollatzResearch.WordTrace]
  refine ⟨25825279534549650108168679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137734824184264800576899621 25825279534549650108168679)
  ·
    refine ⟨38737919301824475162253019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25825279534549650108168679 38737919301824475162253019)
    ·
      refine ⟨58106878952736712743379529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38737919301824475162253019 58106878952736712743379529)
      ·
        refine ⟨43580159214552534557534647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58106878952736712743379529 43580159214552534557534647)
        ·
          refine ⟨65370238821828801836301971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43580159214552534557534647 65370238821828801836301971)
          ·
            refine ⟨98055358232743202754452957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65370238821828801836301971 98055358232743202754452957)
            ·
              refine ⟨36770759337278701032919859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98055358232743202754452957 36770759337278701032919859)
              ·
                refine ⟨55156139005918051549379789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36770759337278701032919859 55156139005918051549379789)
                ·
                  refine ⟨20683552127219269331017421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55156139005918051549379789 20683552127219269331017421)
                  ·
                    refine ⟨7756332047707225999131533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20683552127219269331017421 7756332047707225999131533)
                    ·
                      refine ⟨2908624517890209749674325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7756332047707225999131533 2908624517890209749674325)
                      ·
                        rfl

theorem cell23_5664526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_5664526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664526 prefixEnd_5664526 := by exact prefixLift 5664526
  have htrace : WordTrace (prefixWord ++ tailWord_5664526) baseStart_5664526 baseEnd_5664526 := by
    simpa [prefixWord, tailWord_5664526, baseEnd_5664526] using wordTrace_append hprefix tailTrace_5664526
  have hstable : (prefixWord ++ tailWord_5664526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664526).length < 2 ^ (prefixWord ++ tailWord_5664526).sum := by decide
  have hdescent : baseEnd_5664526 < baseStart_5664526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664530 : List Nat := [3, 2, 4, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_5664530 : Nat := 118140960795 + 5664530 * 2 ^ 59
def prefixEnd_5664530 : Nat := 4983230072969 + 3 ^ 40 * 5664530 * 2
def baseEnd_5664530 : Nat := 2908626571812827734024307

theorem tailTrace_5664530 : CollatzResearch.WordTrace tailWord_5664530 prefixEnd_5664530 2908626571812827734024307 := by
  unfold tailWord_5664530
  simp only [CollatzResearch.WordTrace]
  refine ⟨51650595542095677387123761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137734921445588473032330029 51650595542095677387123761)
  ·
    refine ⟨38737946656571758040342821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51650595542095677387123761 38737946656571758040342821)
    ·
      refine ⟨7263364998107204632564279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38737946656571758040342821 7263364998107204632564279)
      ·
        refine ⟨10895047497160806948846419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7263364998107204632564279 10895047497160806948846419)
        ·
          refine ⟨16342571245741210423269629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10895047497160806948846419 16342571245741210423269629)
          ·
            refine ⟨6128464217152953908726111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16342571245741210423269629 6128464217152953908726111)
            ·
              refine ⟨9192696325729430863089167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6128464217152953908726111 9192696325729430863089167)
              ·
                refine ⟨13789044488594146294633751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9192696325729430863089167 13789044488594146294633751)
                ·
                  refine ⟨20683566732891219441950627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13789044488594146294633751 20683566732891219441950627)
                  ·
                    refine ⟨31025350099336829162925941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20683566732891219441950627 31025350099336829162925941)
                    ·
                      refine ⟨2908626571812827734024307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31025350099336829162925941 2908626571812827734024307)
                      ·
                        rfl

theorem cell23_5664530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_5664530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664530 prefixEnd_5664530 := by exact prefixLift 5664530
  have htrace : WordTrace (prefixWord ++ tailWord_5664530) baseStart_5664530 baseEnd_5664530 := by
    simpa [prefixWord, tailWord_5664530, baseEnd_5664530] using wordTrace_append hprefix tailTrace_5664530
  have hstable : (prefixWord ++ tailWord_5664530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664530).length < 2 ^ (prefixWord ++ tailWord_5664530).sum := by decide
  have hdescent : baseEnd_5664530 < baseStart_5664530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664559 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 2, 6]
def baseStart_5664559 : Nat := 118140960795 + 5664559 * 2 ^ 59
def prefixEnd_5664559 : Nat := 4983230072969 + 3 ^ 40 * 5664559 * 2
def baseEnd_5664559 : Nat := 969547154250602706853891

theorem tailTrace_5664559 : CollatzResearch.WordTrace tailWord_5664559 prefixEnd_5664559 969547154250602706853891 := by
  unfold tailWord_5664559
  simp only [CollatzResearch.WordTrace]
  refine ⟨206603439885277647501300731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137735626590185098334200487 206603439885277647501300731)
  ·
    refine ⟨309905159827916471251951097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206603439885277647501300731 309905159827916471251951097)
    ·
      refine ⟨232428869870937353438963323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309905159827916471251951097 232428869870937353438963323)
      ·
        refine ⟨348643304806406030158444985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232428869870937353438963323 348643304806406030158444985)
        ·
          refine ⟨261482478604804522618833739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348643304806406030158444985 261482478604804522618833739)
          ·
            refine ⟨392223717907206783928250609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261482478604804522618833739 392223717907206783928250609)
            ·
              refine ⟨294167788430405087946187957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 392223717907206783928250609 294167788430405087946187957)
              ·
                refine ⟨27578230165350476994955121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 294167788430405087946187957 27578230165350476994955121)
                ·
                  refine ⟨20683672624012857746216341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27578230165350476994955121 20683672624012857746216341)
                  ·
                    refine ⟨969547154250602706853891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20683672624012857746216341 969547154250602706853891)
                    ·
                      rfl

theorem cell23_5664559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 6].length) (baseStart_5664559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664559 prefixEnd_5664559 := by exact prefixLift 5664559
  have htrace : WordTrace (prefixWord ++ tailWord_5664559) baseStart_5664559 baseEnd_5664559 := by
    simpa [prefixWord, tailWord_5664559, baseEnd_5664559] using wordTrace_append hprefix tailTrace_5664559
  have hstable : (prefixWord ++ tailWord_5664559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664559).length < 2 ^ (prefixWord ++ tailWord_5664559).sum := by decide
  have hdescent : baseEnd_5664559 < baseStart_5664559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664583 : List Nat := [1, 1, 4, 1, 2, 1, 4, 2, 1, 4, 2]
def baseStart_5664583 : Nat := 118140960795 + 5664583 * 2 ^ 59
def prefixEnd_5664583 : Nat := 4983230072969 + 3 ^ 40 * 5664583 * 2
def baseEnd_5664583 : Nat := 2908653786287516026661563

theorem tailTrace_5664583 : CollatzResearch.WordTrace tailWord_5664583 prefixEnd_5664583 2908653786287516026661563 := by
  unfold tailWord_5664583
  simp only [CollatzResearch.WordTrace]
  refine ⟨206604315237190699600174403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137736210158127133066782935 206604315237190699600174403)
  ·
    refine ⟨309906472855786049400261605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206604315237190699600174403 309906472855786049400261605)
    ·
      refine ⟨58107463660459884262549051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 309906472855786049400261605 58107463660459884262549051)
      ·
        refine ⟨87161195490689826393823577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58107463660459884262549051 87161195490689826393823577)
        ·
          refine ⟨65370896618017369795367683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87161195490689826393823577 65370896618017369795367683)
          ·
            refine ⟨98056344927026054693051525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65370896618017369795367683 98056344927026054693051525)
            ·
              refine ⟨18385564673817385254947161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98056344927026054693051525 18385564673817385254947161)
              ·
                refine ⟨13789173505363038941210371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18385564673817385254947161 13789173505363038941210371)
                ·
                  refine ⟨20683760258044558411815557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13789173505363038941210371 20683760258044558411815557)
                  ·
                    refine ⟨3878205048383354702215417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20683760258044558411815557 3878205048383354702215417)
                    ·
                      refine ⟨2908653786287516026661563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3878205048383354702215417 2908653786287516026661563)
                      ·
                        rfl

theorem cell23_5664583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 4, 2].length) (baseStart_5664583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664583 prefixEnd_5664583 := by exact prefixLift 5664583
  have htrace : WordTrace (prefixWord ++ tailWord_5664583) baseStart_5664583 baseEnd_5664583 := by
    simpa [prefixWord, tailWord_5664583, baseEnd_5664583] using wordTrace_append hprefix tailTrace_5664583
  have hstable : (prefixWord ++ tailWord_5664583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664583).length < 2 ^ (prefixWord ++ tailWord_5664583).sum := by decide
  have hdescent : baseEnd_5664583 < baseStart_5664583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664656 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 4]
def baseStart_5664656 : Nat := 118140960795 + 5664656 * 2 ^ 59
def prefixEnd_5664656 : Nat := 4983230072969 + 3 ^ 40 * 5664656 * 2
def baseEnd_5664656 : Nat := 2908691270375294241048727

theorem tailTrace_5664656 : CollatzResearch.WordTrace tailWord_5664656 prefixEnd_5664656 2908691270375294241048727 := by
  unfold tailWord_5664656
  simp only [CollatzResearch.WordTrace]
  refine ⟨103303488882963116533790911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137737985177284155378387881 103303488882963116533790911)
  ·
    refine ⟨154955233324444674800686367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103303488882963116533790911 154955233324444674800686367)
    ·
      refine ⟨232432849986667012201029551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154955233324444674800686367 232432849986667012201029551)
      ·
        refine ⟨348649274980000518301544327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232432849986667012201029551 348649274980000518301544327)
        ·
          refine ⟨522973912470000777452316491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348649274980000518301544327 522973912470000777452316491)
          ·
            refine ⟨784460868705001166178474737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522973912470000777452316491 784460868705001166178474737)
            ·
              refine ⟨588345651528750874633856053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 784460868705001166178474737 588345651528750874633856053)
              ·
                refine ⟨55157404830820394496924005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 588345651528750874633856053 55157404830820394496924005)
                ·
                  refine ⟨10342013405778823968173251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55157404830820394496924005 10342013405778823968173251)
                  ·
                    refine ⟨15513020108668235952259877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10342013405778823968173251 15513020108668235952259877)
                    ·
                      refine ⟨2908691270375294241048727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15513020108668235952259877 2908691270375294241048727)
                      ·
                        rfl

theorem cell23_5664656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 4].length) (baseStart_5664656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664656 prefixEnd_5664656 := by exact prefixLift 5664656
  have htrace : WordTrace (prefixWord ++ tailWord_5664656) baseStart_5664656 baseEnd_5664656 := by
    simpa [prefixWord, tailWord_5664656, baseEnd_5664656] using wordTrace_append hprefix tailTrace_5664656
  have hstable : (prefixWord ++ tailWord_5664656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664656).length < 2 ^ (prefixWord ++ tailWord_5664656).sum := by decide
  have hdescent : baseEnd_5664656 < baseStart_5664656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664740 : List Nat := [2, 3, 1, 1, 1, 1, 5, 2, 3, 1, 3]
def baseStart_5664740 : Nat := 118140960795 + 5664740 * 2 ^ 59
def prefixEnd_5664740 : Nat := 4983230072969 + 3 ^ 40 * 5664740 * 2
def baseEnd_5664740 : Nat := 2908734402750271912398341

theorem tailTrace_5664740 : CollatzResearch.WordTrace tailWord_5664740 prefixEnd_5664740 2908734402750271912398341 := by
  unfold tailWord_5664740
  simp only [CollatzResearch.WordTrace]
  refine ⟨103305020748810957706819837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137740027665081276942426449 103305020748810957706819837)
  ·
    refine ⟨38739382780804109140057439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103305020748810957706819837 38739382780804109140057439)
    ·
      refine ⟨58109074171206163710086159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38739382780804109140057439 58109074171206163710086159)
      ·
        refine ⟨87163611256809245565129239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58109074171206163710086159 87163611256809245565129239)
        ·
          refine ⟨130745416885213868347693859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87163611256809245565129239 130745416885213868347693859)
          ·
            refine ⟨196118125327820802521540789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130745416885213868347693859 196118125327820802521540789)
            ·
              refine ⟨18386074249483200236394449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 196118125327820802521540789 18386074249483200236394449)
              ·
                refine ⟨13789555687112400177295837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18386074249483200236394449 13789555687112400177295837)
                ·
                  refine ⟨5171083382667150066485939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13789555687112400177295837 5171083382667150066485939)
                  ·
                    refine ⟨7756625074000725099728909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5171083382667150066485939 7756625074000725099728909)
                    ·
                      refine ⟨2908734402750271912398341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7756625074000725099728909 2908734402750271912398341)
                      ·
                        rfl

theorem cell23_5664740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_5664740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664740 prefixEnd_5664740 := by exact prefixLift 5664740
  have htrace : WordTrace (prefixWord ++ tailWord_5664740) baseStart_5664740 baseEnd_5664740 := by
    simpa [prefixWord, tailWord_5664740, baseEnd_5664740] using wordTrace_append hprefix tailTrace_5664740
  have hstable : (prefixWord ++ tailWord_5664740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664740).length < 2 ^ (prefixWord ++ tailWord_5664740).sum := by decide
  have hdescent : baseEnd_5664740 < baseStart_5664740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664760 : List Nat := [2, 1, 2, 1, 1, 3, 6, 1, 1, 5]
def baseStart_5664760 : Nat := 118140960795 + 5664760 * 2 ^ 59
def prefixEnd_5664760 : Nat := 4983230072969 + 3 ^ 40 * 5664760 * 2
def baseEnd_5664760 : Nat := 969581557454453944716083

theorem tailTrace_5664760 : CollatzResearch.WordTrace tailWord_5664760 prefixEnd_5664760 969581557454453944716083 := by
  unfold tailWord_5664760
  simp only [CollatzResearch.WordTrace]
  refine ⟨103305385478774729414683867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137740513971699639219578489 103305385478774729414683867)
  ·
    refine ⟨154958078218162094122025801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103305385478774729414683867 154958078218162094122025801)
    ·
      refine ⟨116218558663621570591519351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154958078218162094122025801 116218558663621570591519351)
      ·
        refine ⟨174327837995432355887279027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116218558663621570591519351 174327837995432355887279027)
        ·
          refine ⟨261491756993148533830918541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174327837995432355887279027 261491756993148533830918541)
          ·
            refine ⟨98059408872430700186594453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261491756993148533830918541 98059408872430700186594453)
            ·
              refine ⟨4596534790895189071246615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98059408872430700186594453 4596534790895189071246615)
              ·
                refine ⟨6894802186342783606869923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4596534790895189071246615 6894802186342783606869923)
                ·
                  refine ⟨10342203279514175410304885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6894802186342783606869923 10342203279514175410304885)
                  ·
                    refine ⟨969581557454453944716083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10342203279514175410304885 969581557454453944716083)
                    ·
                      rfl

theorem cell23_5664760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 1, 5].length) (baseStart_5664760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664760 prefixEnd_5664760 := by exact prefixLift 5664760
  have htrace : WordTrace (prefixWord ++ tailWord_5664760) baseStart_5664760 baseEnd_5664760 := by
    simpa [prefixWord, tailWord_5664760, baseEnd_5664760] using wordTrace_append hprefix tailTrace_5664760
  have hstable : (prefixWord ++ tailWord_5664760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664760).length < 2 ^ (prefixWord ++ tailWord_5664760).sum := by decide
  have hdescent : baseEnd_5664760 < baseStart_5664760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664781 : List Nat := [1, 7, 1, 2, 1, 1, 3, 1, 6]
def baseStart_5664781 : Nat := 118140960795 + 5664781 * 2 ^ 59
def prefixEnd_5664781 : Nat := 4983230072969 + 3 ^ 40 * 5664781 * 2
def baseEnd_5664781 : Nat := 323195050606345139109517

theorem tailTrace_5664781 : CollatzResearch.WordTrace tailWord_5664781 prefixEnd_5664781 323195050606345139109517 := by
  unfold tailWord_5664781
  simp only [CollatzResearch.WordTrace]
  refine ⟨206611536890473379415882197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137741024593648919610588131 206611536890473379415882197)
  ·
    refine ⟨4842457895870469830059739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 206611536890473379415882197 4842457895870469830059739)
    ·
      refine ⟨7263686843805704745089609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4842457895870469830059739 7263686843805704745089609)
      ·
        refine ⟨5447765132854278558817207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7263686843805704745089609 5447765132854278558817207)
        ·
          refine ⟨8171647699281417838225811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5447765132854278558817207 8171647699281417838225811)
          ·
            refine ⟨12257471548922126757338717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8171647699281417838225811 12257471548922126757338717)
            ·
              refine ⟨4596551830845797534002019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12257471548922126757338717 4596551830845797534002019)
              ·
                refine ⟨6894827746268696301003029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4596551830845797534002019 6894827746268696301003029)
                ·
                  refine ⟨323195050606345139109517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6894827746268696301003029 323195050606345139109517)
                  ·
                    rfl

theorem cell23_5664781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_5664781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664781 prefixEnd_5664781 := by exact prefixLift 5664781
  have htrace : WordTrace (prefixWord ++ tailWord_5664781) baseStart_5664781 baseEnd_5664781 := by
    simpa [prefixWord, tailWord_5664781, baseEnd_5664781] using wordTrace_append hprefix tailTrace_5664781
  have hstable : (prefixWord ++ tailWord_5664781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664781).length < 2 ^ (prefixWord ++ tailWord_5664781).sum := by decide
  have hdescent : baseEnd_5664781 < baseStart_5664781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664797 : List Nat := [1, 4, 2, 2, 2, 2, 2, 2, 1, 1, 4]
def baseStart_5664797 : Nat := 118140960795 + 5664797 * 2 ^ 59
def prefixEnd_5664797 : Nat := 4983230072969 + 3 ^ 40 * 5664797 * 2
def baseEnd_5664797 : Nat := 2908763671147578189385579

theorem tailTrace_5664797 : CollatzResearch.WordTrace tailWord_5664797 prefixEnd_5664797 2908763671147578189385579 := by
  unfold tailWord_5664797
  simp only [CollatzResearch.WordTrace]
  refine ⟨206612120458415414148464645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137741413638943609432309763 206612120458415414148464645)
  ·
    refine ⟨38739772585952890152837121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206612120458415414148464645 38739772585952890152837121)
    ·
      refine ⟨29054829439464667614627841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38739772585952890152837121 29054829439464667614627841)
      ·
        refine ⟨21791122079598500710970881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29054829439464667614627841 21791122079598500710970881)
        ·
          refine ⟨16343341559698875533228161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21791122079598500710970881 16343341559698875533228161)
          ·
            refine ⟨12257506169774156649921121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16343341559698875533228161 12257506169774156649921121)
            ·
              refine ⟨9193129627330617487440841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12257506169774156649921121 9193129627330617487440841)
              ·
                refine ⟨6894847220497963115580631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9193129627330617487440841 6894847220497963115580631)
                ·
                  refine ⟨10342270830746944673370947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6894847220497963115580631 10342270830746944673370947)
                  ·
                    refine ⟨15513406246120417010056421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10342270830746944673370947 15513406246120417010056421)
                    ·
                      refine ⟨2908763671147578189385579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15513406246120417010056421 2908763671147578189385579)
                      ·
                        rfl

theorem cell23_5664797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_5664797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664797 prefixEnd_5664797 := by exact prefixLift 5664797
  have htrace : WordTrace (prefixWord ++ tailWord_5664797) baseStart_5664797 baseEnd_5664797 := by
    simpa [prefixWord, tailWord_5664797, baseEnd_5664797] using wordTrace_append hprefix tailTrace_5664797
  have hstable : (prefixWord ++ tailWord_5664797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664797).length < 2 ^ (prefixWord ++ tailWord_5664797).sum := by decide
  have hdescent : baseEnd_5664797 < baseStart_5664797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664808 : List Nat := [2, 1, 5, 3, 1, 2, 1, 3, 1, 1, 3]
def baseStart_5664808 : Nat := 118140960795 + 5664808 * 2 ^ 59
def prefixEnd_5664808 : Nat := 4983230072969 + 3 ^ 40 * 5664808 * 2
def baseEnd_5664808 : Nat := 2908769319434777646348029

theorem tailTrace_5664808 : CollatzResearch.WordTrace tailWord_5664808 prefixEnd_5664808 2908769319434777646348029 := by
  unfold tailWord_5664808
  simp only [CollatzResearch.WordTrace]
  refine ⟨103306260830687781513557539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137741681107583708684743385 103306260830687781513557539)
  ·
    refine ⟨154959391246031672270336309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103306260830687781513557539 154959391246031672270336309)
    ·
      refine ⟨14527442929315469275344029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154959391246031672270336309 14527442929315469275344029)
      ·
        refine ⟨5447791098493300978254011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14527442929315469275344029 5447791098493300978254011)
        ·
          refine ⟨8171686647739951467381017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5447791098493300978254011 8171686647739951467381017)
          ·
            refine ⟨6128764985804963600535763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8171686647739951467381017 6128764985804963600535763)
            ·
              refine ⟨9193147478707445400803645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6128764985804963600535763 9193147478707445400803645)
              ·
                refine ⟨3447430304515292025301367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9193147478707445400803645 3447430304515292025301367)
                ·
                  refine ⟨5171145456772938037952051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3447430304515292025301367 5171145456772938037952051)
                  ·
                    refine ⟨7756718185159407056928077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5171145456772938037952051 7756718185159407056928077)
                    ·
                      refine ⟨2908769319434777646348029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7756718185159407056928077 2908769319434777646348029)
                      ·
                        rfl

theorem cell23_5664808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_5664808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664808 prefixEnd_5664808 := by exact prefixLift 5664808
  have htrace : WordTrace (prefixWord ++ tailWord_5664808) baseStart_5664808 baseEnd_5664808 := by
    simpa [prefixWord, tailWord_5664808, baseEnd_5664808] using wordTrace_append hprefix tailTrace_5664808
  have hstable : (prefixWord ++ tailWord_5664808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664808).length < 2 ^ (prefixWord ++ tailWord_5664808).sum := by decide
  have hdescent : baseEnd_5664808 < baseStart_5664808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664873 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 2, 1, 5]
def baseStart_5664873 : Nat := 118140960795 + 5664873 * 2 ^ 59
def prefixEnd_5664873 : Nat := 4983230072969 + 3 ^ 40 * 5664873 * 2
def baseEnd_5664873 : Nat := 2908802695677319892035229

theorem tailTrace_5664873 : CollatzResearch.WordTrace tailWord_5664873 prefixEnd_5664873 2908802695677319892035229 := by
  unfold tailWord_5664873
  simp only [CollatzResearch.WordTrace]
  refine ⟨206614892406140079128231273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137743261604093386085487515 206614892406140079128231273)
  ·
    refine ⟨154961169304605059346173455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206614892406140079128231273 154961169304605059346173455)
    ·
      refine ⟨232441753956907589019260183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154961169304605059346173455 232441753956907589019260183)
      ·
        refine ⟨348662630935361383528890275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232441753956907589019260183 348662630935361383528890275)
        ·
          refine ⟨522993946403042075293335413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348662630935361383528890275 522993946403042075293335413)
          ·
            refine ⟨49030682475285194558750195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 522993946403042075293335413 49030682475285194558750195)
            ·
              refine ⟨73546023712927791838125293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49030682475285194558750195 73546023712927791838125293)
              ·
                refine ⟨27579758892347921939296985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73546023712927791838125293 27579758892347921939296985)
                ·
                  refine ⟨20684819169260941454472739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27579758892347921939296985 20684819169260941454472739)
                  ·
                    refine ⟨31027228753891412181709109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20684819169260941454472739 31027228753891412181709109)
                    ·
                      refine ⟨2908802695677319892035229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31027228753891412181709109 2908802695677319892035229)
                      ·
                        rfl

theorem cell23_5664873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 1, 5].length) (baseStart_5664873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664873 prefixEnd_5664873 := by exact prefixLift 5664873
  have htrace : WordTrace (prefixWord ++ tailWord_5664873) baseStart_5664873 baseEnd_5664873 := by
    simpa [prefixWord, tailWord_5664873, baseEnd_5664873] using wordTrace_append hprefix tailTrace_5664873
  have hstable : (prefixWord ++ tailWord_5664873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664873).length < 2 ^ (prefixWord ++ tailWord_5664873).sum := by decide
  have hdescent : baseEnd_5664873 < baseStart_5664873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664900 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_5664900 : Nat := 118140960795 + 5664900 * 2 ^ 59
def prefixEnd_5664900 : Nat := 4983230072969 + 3 ^ 40 * 5664900 * 2
def baseEnd_5664900 : Nat := 2908816559654991286397605

theorem tailTrace_5664900 : CollatzResearch.WordTrace tailWord_5664900 prefixEnd_5664900 2908816559654991286397605 := by
  unfold tailWord_5664900
  simp only [CollatzResearch.WordTrace]
  refine ⟨103307938588521131369732077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137743918118028175159642769 103307938588521131369732077)
  ·
    refine ⟨38740476970695424263649529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103307938588521131369732077 38740476970695424263649529)
    ·
      refine ⟨29055357728021568197737147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38740476970695424263649529 29055357728021568197737147)
      ·
        refine ⟨43583036592032352296605721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29055357728021568197737147 43583036592032352296605721)
        ·
          refine ⟨32687277444024264222454291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43583036592032352296605721 32687277444024264222454291)
          ·
            refine ⟨49030916166036396333681437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32687277444024264222454291 49030916166036396333681437)
            ·
              refine ⟨18386593562263648625130539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49030916166036396333681437 18386593562263648625130539)
              ·
                refine ⟨27579890343395472937695809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18386593562263648625130539 27579890343395472937695809)
                ·
                  refine ⟨20684917757546604703271857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27579890343395472937695809 20684917757546604703271857)
                  ·
                    refine ⟨15513688318159953527453893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20684917757546604703271857 15513688318159953527453893)
                    ·
                      refine ⟨2908816559654991286397605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15513688318159953527453893 2908816559654991286397605)
                      ·
                        rfl

theorem cell23_5664900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_5664900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664900 prefixEnd_5664900 := by exact prefixLift 5664900
  have htrace : WordTrace (prefixWord ++ tailWord_5664900) baseStart_5664900 baseEnd_5664900 := by
    simpa [prefixWord, tailWord_5664900, baseEnd_5664900] using wordTrace_append hprefix tailTrace_5664900
  have hstable : (prefixWord ++ tailWord_5664900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664900).length < 2 ^ (prefixWord ++ tailWord_5664900).sum := by decide
  have hdescent : baseEnd_5664900 < baseStart_5664900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664904 : List Nat := [2, 1, 3, 4, 1, 2, 2, 1, 1, 4, 2]
def baseStart_5664904 : Nat := 118140960795 + 5664904 * 2 ^ 59
def prefixEnd_5664904 : Nat := 4983230072969 + 3 ^ 40 * 5664904 * 2
def baseEnd_5664904 : Nat := 2908818613577609270747587

theorem tailTrace_5664904 : CollatzResearch.WordTrace tailWord_5664904 prefixEnd_5664904 2908818613577609270747587 := by
  unfold tailWord_5664904
  simp only [CollatzResearch.WordTrace]
  refine ⟨103308011534513885711304883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137744015379351847615073177 103308011534513885711304883)
  ·
    refine ⟨154962017301770828566957325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103308011534513885711304883 154962017301770828566957325)
    ·
      refine ⟨58110756488164060712608997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154962017301770828566957325 58110756488164060712608997)
      ·
        refine ⟨10895766841530761383614187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58110756488164060712608997 10895766841530761383614187)
        ·
          refine ⟨16343650262296142075421281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10895766841530761383614187 16343650262296142075421281)
          ·
            refine ⟨12257737696722106556565961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16343650262296142075421281 12257737696722106556565961)
            ·
              refine ⟨9193303272541579917424471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12257737696722106556565961 9193303272541579917424471)
              ·
                refine ⟨13789954908812369876136707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9193303272541579917424471 13789954908812369876136707)
                ·
                  refine ⟨20684932363218554814205061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13789954908812369876136707 20684932363218554814205061)
                  ·
                    refine ⟨3878424818103479027663449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20684932363218554814205061 3878424818103479027663449)
                    ·
                      refine ⟨2908818613577609270747587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3878424818103479027663449 2908818613577609270747587)
                      ·
                        rfl

theorem cell23_5664904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_5664904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664904 prefixEnd_5664904 := by exact prefixLift 5664904
  have htrace : WordTrace (prefixWord ++ tailWord_5664904) baseStart_5664904 baseEnd_5664904 := by
    simpa [prefixWord, tailWord_5664904, baseEnd_5664904] using wordTrace_append hprefix tailTrace_5664904
  have hstable : (prefixWord ++ tailWord_5664904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664904).length < 2 ^ (prefixWord ++ tailWord_5664904).sum := by decide
  have hdescent : baseEnd_5664904 < baseStart_5664904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664923 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 6, 5]
def baseStart_5664923 : Nat := 118140960795 + 5664923 * 2 ^ 59
def prefixEnd_5664923 : Nat := 4983230072969 + 3 ^ 40 * 5664923 * 2
def baseEnd_5664923 : Nat := 969609456570014898803333

theorem tailTrace_5664923 : CollatzResearch.WordTrace tailWord_5664923 prefixEnd_5664923 969609456570014898803333 := by
  unfold tailWord_5664923
  simp only [CollatzResearch.WordTrace]
  refine ⟨206616716055958937667551423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137744477370639291778367615 206616716055958937667551423)
  ·
    refine ⟨309925074083938406501327135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206616716055958937667551423 309925074083938406501327135)
    ·
      refine ⟨464887611125907609751990703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309925074083938406501327135 464887611125907609751990703)
      ·
        refine ⟨697331416688861414627986055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464887611125907609751990703 697331416688861414627986055)
        ·
          refine ⟨1045997125033292121941979083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697331416688861414627986055 1045997125033292121941979083)
          ·
            refine ⟨1568995687549938182912968625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045997125033292121941979083 1568995687549938182912968625)
            ·
              refine ⟨1176746765662453637184726469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1568995687549938182912968625 1176746765662453637184726469)
              ·
                refine ⟨220640018561710056972136213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1176746765662453637184726469 220640018561710056972136213)
                ·
                  refine ⟨10342500870080158920568885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 220640018561710056972136213 10342500870080158920568885)
                  ·
                    refine ⟨969609456570014898803333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10342500870080158920568885 969609456570014898803333)
                    ·
                      rfl

theorem cell23_5664923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 5].length) (baseStart_5664923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664923 prefixEnd_5664923 := by exact prefixLift 5664923
  have htrace : WordTrace (prefixWord ++ tailWord_5664923) baseStart_5664923 baseEnd_5664923 := by
    simpa [prefixWord, tailWord_5664923, baseEnd_5664923] using wordTrace_append hprefix tailTrace_5664923
  have hstable : (prefixWord ++ tailWord_5664923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664923).length < 2 ^ (prefixWord ++ tailWord_5664923).sum := by decide
  have hdescent : baseEnd_5664923 < baseStart_5664923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664927 : List Nat := [1, 1, 2, 6, 1, 1, 1, 5, 5]
def baseStart_5664927 : Nat := 118140960795 + 5664927 * 2 ^ 59
def prefixEnd_5664927 : Nat := 4983230072969 + 3 ^ 40 * 5664927 * 2
def baseEnd_5664927 : Nat := 323203380403629186751109

theorem tailTrace_5664927 : CollatzResearch.WordTrace tailWord_5664927 prefixEnd_5664927 323203380403629186751109 := by
  unfold tailWord_5664927
  simp only [CollatzResearch.WordTrace]
  refine ⟨206616861947944446350697035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137744574631962964233798023 206616861947944446350697035)
  ·
    refine ⟨309925292921916669526045553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206616861947944446350697035 309925292921916669526045553)
    ·
      refine ⟨232443969691437502144534165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309925292921916669526045553 232443969691437502144534165)
      ·
        refine ⟨10895811079286132913025039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 232443969691437502144534165 10895811079286132913025039)
        ·
          refine ⟨16343716618929199369537559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10895811079286132913025039 16343716618929199369537559)
          ·
            refine ⟨24515574928393799054306339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16343716618929199369537559 24515574928393799054306339)
            ·
              refine ⟨36773362392590698581459509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24515574928393799054306339 36773362392590698581459509)
              ·
                refine ⟨3447502724305377992011829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36773362392590698581459509 3447502724305377992011829)
                ·
                  refine ⟨323203380403629186751109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3447502724305377992011829 323203380403629186751109)
                  ·
                    rfl

theorem cell23_5664927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 5].length) (baseStart_5664927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664927 prefixEnd_5664927 := by exact prefixLift 5664927
  have htrace : WordTrace (prefixWord ++ tailWord_5664927) baseStart_5664927 baseEnd_5664927 := by
    simpa [prefixWord, tailWord_5664927, baseEnd_5664927] using wordTrace_append hprefix tailTrace_5664927
  have hstable : (prefixWord ++ tailWord_5664927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664927).length < 2 ^ (prefixWord ++ tailWord_5664927).sum := by decide
  have hdescent : baseEnd_5664927 < baseStart_5664927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664960 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 4]
def baseStart_5664960 : Nat := 118140960795 + 5664960 * 2 ^ 59
def prefixEnd_5664960 : Nat := 4983230072969 + 3 ^ 40 * 5664960 * 2
def baseEnd_5664960 : Nat := 2908847368494261051647329

theorem tailTrace_5664960 : CollatzResearch.WordTrace tailWord_5664960 prefixEnd_5664960 2908847368494261051647329 := by
  unfold tailWord_5664960
  simp only [CollatzResearch.WordTrace]
  refine ⟨103309032778412446493324167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137745377037883261991098889 103309032778412446493324167)
  ·
    refine ⟨154963549167618669739986251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103309032778412446493324167 154963549167618669739986251)
    ·
      refine ⟨232445323751428004609979377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154963549167618669739986251 232445323751428004609979377)
      ·
        refine ⟨174333992813571003457484533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232445323751428004609979377 174333992813571003457484533)
        ·
          refine ⟨16343811826272281574139175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174333992813571003457484533 16343811826272281574139175)
          ·
            refine ⟨24515717739408422361208763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16343811826272281574139175 24515717739408422361208763)
            ·
              refine ⟨36773576609112633541813145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24515717739408422361208763 36773576609112633541813145)
              ·
                refine ⟨27580182456834475156359859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36773576609112633541813145 27580182456834475156359859)
                ·
                  refine ⟨41370273685251712734539789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27580182456834475156359859 41370273685251712734539789)
                  ·
                    refine ⟨15513852631969392275452421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41370273685251712734539789 15513852631969392275452421)
                    ·
                      refine ⟨2908847368494261051647329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15513852631969392275452421 2908847368494261051647329)
                      ·
                        rfl

theorem cell23_5664960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_5664960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664960 prefixEnd_5664960 := by exact prefixLift 5664960
  have htrace : WordTrace (prefixWord ++ tailWord_5664960) baseStart_5664960 baseEnd_5664960 := by
    simpa [prefixWord, tailWord_5664960, baseEnd_5664960] using wordTrace_append hprefix tailTrace_5664960
  have hstable : (prefixWord ++ tailWord_5664960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664960).length < 2 ^ (prefixWord ++ tailWord_5664960).sum := by decide
  have hdescent : baseEnd_5664960 < baseStart_5664960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664963 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 5]
def baseStart_5664963 : Nat := 118140960795 + 5664963 * 2 ^ 59
def prefixEnd_5664963 : Nat := 4983230072969 + 3 ^ 40 * 5664963 * 2
def baseEnd_5664963 : Nat := 2908848908936224539909815

theorem tailTrace_5664963 : CollatzResearch.WordTrace tailWord_5664963 prefixEnd_5664963 2908848908936224539909815 := by
  unfold tailWord_5664963
  simp only [CollatzResearch.WordTrace]
  refine ⟨206618174975814024499007543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137745449983876016332671695 206618174975814024499007543)
  ·
    refine ⟨309927262463721036748511315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206618174975814024499007543 309927262463721036748511315)
    ·
      refine ⟨464890893695581555122766973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309927262463721036748511315 464890893695581555122766973)
      ·
        refine ⟨174334085135843083171037615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 464890893695581555122766973 174334085135843083171037615)
        ·
          refine ⟨261501127703764624756556423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174334085135843083171037615 261501127703764624756556423)
          ·
            refine ⟨392251691555646937134834635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261501127703764624756556423 392251691555646937134834635)
            ·
              refine ⟨588377537333470405702251953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392251691555646937134834635 588377537333470405702251953)
              ·
                refine ⟨441283153000102804276688965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588377537333470405702251953 441283153000102804276688965)
                ·
                  refine ⟨82740591187519275801879181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 441283153000102804276688965 82740591187519275801879181)
                  ·
                    refine ⟨31027721695319728425704693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82740591187519275801879181 31027721695319728425704693)
                    ·
                      refine ⟨2908848908936224539909815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31027721695319728425704693 2908848908936224539909815)
                      ·
                        rfl

theorem cell23_5664963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_5664963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664963 prefixEnd_5664963 := by exact prefixLift 5664963
  have htrace : WordTrace (prefixWord ++ tailWord_5664963) baseStart_5664963 baseEnd_5664963 := by
    simpa [prefixWord, tailWord_5664963, baseEnd_5664963] using wordTrace_append hprefix tailTrace_5664963
  have hstable : (prefixWord ++ tailWord_5664963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664963).length < 2 ^ (prefixWord ++ tailWord_5664963).sum := by decide
  have hdescent : baseEnd_5664963 < baseStart_5664963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5664997 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 4, 2, 3]
def baseStart_5664997 : Nat := 118140960795 + 5664997 * 2 ^ 59
def prefixEnd_5664997 : Nat := 4983230072969 + 3 ^ 40 * 5664997 * 2
def baseEnd_5664997 : Nat := 2908866367278477406884659

theorem tailTrace_5664997 : CollatzResearch.WordTrace tailWord_5664997 prefixEnd_5664997 2908866367278477406884659 := by
  unfold tailWord_5664997
  simp only [CollatzResearch.WordTrace]
  refine ⟨206619415057690848305745245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137746276705127232203830163 206619415057690848305745245)
  ·
    refine ⟨77482280646634068114654467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206619415057690848305745245 77482280646634068114654467)
    ·
      refine ⟨116223420969951102171981701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77482280646634068114654467 116223420969951102171981701)
      ·
        refine ⟨21791891431865831657246569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116223420969951102171981701 21791891431865831657246569)
        ·
          refine ⟨16343918573899373742934927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21791891431865831657246569 16343918573899373742934927)
          ·
            refine ⟨24515877860849060614402391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16343918573899373742934927 24515877860849060614402391)
            ·
              refine ⟨36773816791273590921603587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24515877860849060614402391 36773816791273590921603587)
              ·
                refine ⟨55160725186910386382405381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36773816791273590921603587 55160725186910386382405381)
                ·
                  refine ⟨10342635972545697446701009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55160725186910386382405381 10342635972545697446701009)
                  ·
                    refine ⟨7756976979409273085025757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10342635972545697446701009 7756976979409273085025757)
                    ·
                      refine ⟨2908866367278477406884659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7756976979409273085025757 2908866367278477406884659)
                      ·
                        rfl

theorem cell23_5664997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_5664997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5664997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5664997 prefixEnd_5664997 := by exact prefixLift 5664997
  have htrace : WordTrace (prefixWord ++ tailWord_5664997) baseStart_5664997 baseEnd_5664997 := by
    simpa [prefixWord, tailWord_5664997, baseEnd_5664997] using wordTrace_append hprefix tailTrace_5664997
  have hstable : (prefixWord ++ tailWord_5664997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5664997).length < 2 ^ (prefixWord ++ tailWord_5664997).sum := by decide
  have hdescent : baseEnd_5664997 < baseStart_5664997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5664997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665000 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 8]
def baseStart_5665000 : Nat := 118140960795 + 5665000 * 2 ^ 59
def prefixEnd_5665000 : Nat := 4983230072969 + 3 ^ 40 * 5665000 * 2
def baseEnd_5665000 : Nat := 323207545302271210571905

theorem tailTrace_5665000 : CollatzResearch.WordTrace tailWord_5665000 prefixEnd_5665000 323207545302271210571905 := by
  unfold tailWord_5665000
  simp only [CollatzResearch.WordTrace]
  refine ⟨103309762238339989909052227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137746349651119986545402969 103309762238339989909052227)
  ·
    refine ⟨154964643357509984863578341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103309762238339989909052227 154964643357509984863578341)
    ·
      refine ⟨29055870629533122161920939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154964643357509984863578341 29055870629533122161920939)
      ·
        refine ⟨43583805944299683242881409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29055870629533122161920939 43583805944299683242881409)
        ·
          refine ⟨32687854458224762432161057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43583805944299683242881409 32687854458224762432161057)
          ·
            refine ⟨24515890843668571824120793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32687854458224762432161057 24515890843668571824120793)
            ·
              refine ⟨18386918132751428868090595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24515890843668571824120793 18386918132751428868090595)
              ·
                refine ⟨27580377199127143302135893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18386918132751428868090595 27580377199127143302135893)
                ·
                  refine ⟨323207545302271210571905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27580377199127143302135893 323207545302271210571905)
                  ·
                    rfl

theorem cell23_5665000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 8].length) (baseStart_5665000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665000 prefixEnd_5665000 := by exact prefixLift 5665000
  have htrace : WordTrace (prefixWord ++ tailWord_5665000) baseStart_5665000 baseEnd_5665000 := by
    simpa [prefixWord, tailWord_5665000, baseEnd_5665000] using wordTrace_append hprefix tailTrace_5665000
  have hstable : (prefixWord ++ tailWord_5665000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665000).length < 2 ^ (prefixWord ++ tailWord_5665000).sum := by decide
  have hdescent : baseEnd_5665000 < baseStart_5665000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665027 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 5, 1, 3]
def baseStart_5665027 : Nat := 118140960795 + 5665027 * 2 ^ 59
def prefixEnd_5665027 : Nat := 4983230072969 + 3 ^ 40 * 5665027 * 2
def baseEnd_5665027 : Nat := 2908881771698112289509521

theorem tailTrace_5665027 : CollatzResearch.WordTrace tailWord_5665027 prefixEnd_5665027 2908881771698112289509521 := by
  unfold tailWord_5665027
  simp only [CollatzResearch.WordTrace]
  refine ⟨206620509247582163429337335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137747006165054775619558223 206620509247582163429337335)
  ·
    refine ⟨309930763871373245144006003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206620509247582163429337335 309930763871373245144006003)
    ·
      refine ⟨464896145807059867716009005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309930763871373245144006003 464896145807059867716009005)
      ·
        refine ⟨174336054677647450393503377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 464896145807059867716009005 174336054677647450393503377)
        ·
          refine ⟨130752041008235587795127533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174336054677647450393503377 130752041008235587795127533)
          ·
            refine ⟨49032015378088345423172825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130752041008235587795127533 49032015378088345423172825)
            ·
              refine ⟨36774011533566259067379619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49032015378088345423172825 36774011533566259067379619)
              ·
                refine ⟨55161017300349388601069429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36774011533566259067379619 55161017300349388601069429)
                ·
                  refine ⟨5171345371907755181350259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55161017300349388601069429 5171345371907755181350259)
                  ·
                    refine ⟨7757018057861632772025389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5171345371907755181350259 7757018057861632772025389)
                    ·
                      refine ⟨2908881771698112289509521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7757018057861632772025389 2908881771698112289509521)
                      ·
                        rfl

theorem cell23_5665027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 1, 3].length) (baseStart_5665027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665027 prefixEnd_5665027 := by exact prefixLift 5665027
  have htrace : WordTrace (prefixWord ++ tailWord_5665027) baseStart_5665027 baseEnd_5665027 := by
    simpa [prefixWord, tailWord_5665027, baseEnd_5665027] using wordTrace_append hprefix tailTrace_5665027
  have hstable : (prefixWord ++ tailWord_5665027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665027).length < 2 ^ (prefixWord ++ tailWord_5665027).sum := by decide
  have hdescent : baseEnd_5665027 < baseStart_5665027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665031 : List Nat := [1, 1, 4, 5, 1, 1, 2, 1, 2, 2, 3]
def baseStart_5665031 : Nat := 118140960795 + 5665031 * 2 ^ 59
def prefixEnd_5665031 : Nat := 4983230072969 + 3 ^ 40 * 5665031 * 2
def baseEnd_5665031 : Nat := 2908883825620730273859503

theorem tailTrace_5665031 : CollatzResearch.WordTrace tailWord_5665031 prefixEnd_5665031 2908883825620730273859503 := by
  unfold tailWord_5665031
  simp only [CollatzResearch.WordTrace]
  refine ⟨206620655139567672112482947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137747103426378448074988631 206620655139567672112482947)
  ·
    refine ⟨309930982709351508168724421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206620655139567672112482947 309930982709351508168724421)
    ·
      refine ⟨58112059258003407781635829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 309930982709351508168724421 58112059258003407781635829)
      ·
        refine ⟨5448005555437819479528359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58112059258003407781635829 5448005555437819479528359)
        ·
          refine ⟨8172008333156729219292539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5448005555437819479528359 8172008333156729219292539)
          ·
            refine ⟨12258012499735093828938809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8172008333156729219292539 12258012499735093828938809)
            ·
              refine ⟨9193509374801320371704107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12258012499735093828938809 9193509374801320371704107)
              ·
                refine ⟨13790264062201980557556161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9193509374801320371704107 13790264062201980557556161)
                ·
                  refine ⟨10342698046651485418167121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13790264062201980557556161 10342698046651485418167121)
                  ·
                    refine ⟨7757023534988614063625341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10342698046651485418167121 7757023534988614063625341)
                    ·
                      refine ⟨2908883825620730273859503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7757023534988614063625341 2908883825620730273859503)
                      ·
                        rfl

theorem cell23_5665031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_5665031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665031 prefixEnd_5665031 := by exact prefixLift 5665031
  have htrace : WordTrace (prefixWord ++ tailWord_5665031) baseStart_5665031 baseEnd_5665031 := by
    simpa [prefixWord, tailWord_5665031, baseEnd_5665031] using wordTrace_append hprefix tailTrace_5665031
  have hstable : (prefixWord ++ tailWord_5665031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665031).length < 2 ^ (prefixWord ++ tailWord_5665031).sum := by decide
  have hdescent : baseEnd_5665031 < baseStart_5665031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665077 : List Nat := [1, 3, 3, 1, 2, 1, 4, 1, 1, 6]
def baseStart_5665077 : Nat := 118140960795 + 5665077 * 2 ^ 59
def prefixEnd_5665077 : Nat := 4983230072969 + 3 ^ 40 * 5665077 * 2
def baseEnd_5665077 : Nat := 969635815243612364628097

theorem tailTrace_5665077 : CollatzResearch.WordTrace tailWord_5665077 prefixEnd_5665077 969635815243612364628097 := by
  unfold tailWord_5665077
  simp only [CollatzResearch.WordTrace]
  refine ⟨206622332897401021968657485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137748221931600681312438323 206622332897401021968657485)
  ·
    refine ⟨77483374836525383238246557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206622332897401021968657485 77483374836525383238246557)
    ·
      refine ⟨29056265563697018714342459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77483374836525383238246557 29056265563697018714342459)
      ·
        refine ⟨43584398345545528071513689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29056265563697018714342459 43584398345545528071513689)
        ·
          refine ⟨32688298759159146053635267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43584398345545528071513689 32688298759159146053635267)
          ·
            refine ⟨49032448138738719080452901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32688298759159146053635267 49032448138738719080452901)
            ·
              refine ⟨9193584026013509827584919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49032448138738719080452901 9193584026013509827584919)
              ·
                refine ⟨13790376039020264741377379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9193584026013509827584919 13790376039020264741377379)
                ·
                  refine ⟨20685564058530397112066069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13790376039020264741377379 20685564058530397112066069)
                  ·
                    refine ⟨969635815243612364628097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20685564058530397112066069 969635815243612364628097)
                    ·
                      rfl

theorem cell23_5665077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_5665077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665077 prefixEnd_5665077 := by exact prefixLift 5665077
  have htrace : WordTrace (prefixWord ++ tailWord_5665077) baseStart_5665077 baseEnd_5665077 := by
    simpa [prefixWord, tailWord_5665077, baseEnd_5665077] using wordTrace_append hprefix tailTrace_5665077
  have hstable : (prefixWord ++ tailWord_5665077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665077).length < 2 ^ (prefixWord ++ tailWord_5665077).sum := by decide
  have hdescent : baseEnd_5665077 < baseStart_5665077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665080 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 1, 1, 6]
def baseStart_5665080 : Nat := 118140960795 + 5665080 * 2 ^ 59
def prefixEnd_5665080 : Nat := 4983230072969 + 3 ^ 40 * 5665080 * 2
def baseEnd_5665080 : Nat := 2908908986172800582146777

theorem tailTrace_5665080 : CollatzResearch.WordTrace tailWord_5665080 prefixEnd_5665080 2908908986172800582146777 := by
  unfold tailWord_5665080
  simp only [CollatzResearch.WordTrace]
  refine ⟨103311221158195076740508347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137748294877593435654011129 103311221158195076740508347)
  ·
    refine ⟨154966831737292615110762521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103311221158195076740508347 154966831737292615110762521)
    ·
      refine ⟨116225123802969461333071891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154966831737292615110762521 116225123802969461333071891)
      ·
        refine ⟨174337685704454191999607837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116225123802969461333071891 174337685704454191999607837)
        ·
          refine ⟨65376632139170321999852939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174337685704454191999607837 65376632139170321999852939)
          ·
            refine ⟨98064948208755482999779409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65376632139170321999852939 98064948208755482999779409)
            ·
              refine ⟨73548711156566612249834557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98064948208755482999779409 73548711156566612249834557)
              ·
                refine ⟨27580766683712479593687959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73548711156566612249834557 27580766683712479593687959)
                ·
                  refine ⟨41371150025568719390531939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27580766683712479593687959 41371150025568719390531939)
                  ·
                    refine ⟨62056725038353079085797909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41371150025568719390531939 62056725038353079085797909)
                    ·
                      refine ⟨2908908986172800582146777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62056725038353079085797909 2908908986172800582146777)
                      ·
                        rfl

theorem cell23_5665080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_5665080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665080 prefixEnd_5665080 := by exact prefixLift 5665080
  have htrace : WordTrace (prefixWord ++ tailWord_5665080) baseStart_5665080 baseEnd_5665080 := by
    simpa [prefixWord, tailWord_5665080, baseEnd_5665080] using wordTrace_append hprefix tailTrace_5665080
  have hstable : (prefixWord ++ tailWord_5665080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665080).length < 2 ^ (prefixWord ++ tailWord_5665080).sum := by decide
  have hdescent : baseEnd_5665080 < baseStart_5665080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665087 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 3]
def baseStart_5665087 : Nat := 118140960795 + 5665087 * 2 ^ 59
def prefixEnd_5665087 : Nat := 4983230072969 + 3 ^ 40 * 5665087 * 2
def baseEnd_5665087 : Nat := 2908912580537382054759245

theorem tailTrace_5665087 : CollatzResearch.WordTrace tailWord_5665087 prefixEnd_5665087 2908912580537382054759245 := by
  unfold tailWord_5665087
  simp only [CollatzResearch.WordTrace]
  refine ⟨206622697627364793676521515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137748465084909862451014343 206622697627364793676521515)
  ·
    refine ⟨309934046441047190514782273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206622697627364793676521515 309934046441047190514782273)
    ·
      refine ⟨232450534830785392886086705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309934046441047190514782273 232450534830785392886086705)
      ·
        refine ⟨174337901123089044664565029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232450534830785392886086705 174337901123089044664565029)
        ·
          refine ⟨32688356460579195874605943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174337901123089044664565029 32688356460579195874605943)
          ·
            refine ⟨49032534690868793811908915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32688356460579195874605943 49032534690868793811908915)
            ·
              refine ⟨73548802036303190717863373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49032534690868793811908915 73548802036303190717863373)
              ·
                refine ⟨27580800763613696519198765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73548802036303190717863373 27580800763613696519198765)
                ·
                  refine ⟨10342800286355136194699537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27580800763613696519198765 10342800286355136194699537)
                  ·
                    refine ⟨7757100214766352146024653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10342800286355136194699537 7757100214766352146024653)
                    ·
                      refine ⟨2908912580537382054759245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7757100214766352146024653 2908912580537382054759245)
                      ·
                        rfl

theorem cell23_5665087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 3].length) (baseStart_5665087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665087 prefixEnd_5665087 := by exact prefixLift 5665087
  have htrace : WordTrace (prefixWord ++ tailWord_5665087) baseStart_5665087 baseEnd_5665087 := by
    simpa [prefixWord, tailWord_5665087, baseEnd_5665087] using wordTrace_append hprefix tailTrace_5665087
  have hstable : (prefixWord ++ tailWord_5665087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665087).length < 2 ^ (prefixWord ++ tailWord_5665087).sum := by decide
  have hdescent : baseEnd_5665087 < baseStart_5665087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665104 : List Nat := [2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 3]
def baseStart_5665104 : Nat := 118140960795 + 5665104 * 2 ^ 59
def prefixEnd_5665104 : Nat := 4983230072969 + 3 ^ 40 * 5665104 * 2
def baseEnd_5665104 : Nat := 2908921309708508488246667

theorem tailTrace_5665104 : CollatzResearch.WordTrace tailWord_5665104 prefixEnd_5665104 2908921309708508488246667 := by
  unfold tailWord_5665104
  simp only [CollatzResearch.WordTrace]
  refine ⟨103311658834151602789945183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137748878445535470386593577 103311658834151602789945183)
  ·
    refine ⟨154967488251227404184917775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103311658834151602789945183 154967488251227404184917775)
    ·
      refine ⟨232451232376841106277376663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154967488251227404184917775 232451232376841106277376663)
      ·
        refine ⟨348676848565261659416064995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232451232376841106277376663 348676848565261659416064995)
        ·
          refine ⟨523015272847892489124097493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348676848565261659416064995 523015272847892489124097493)
          ·
            refine ⟨12258170457372480213846035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 523015272847892489124097493 12258170457372480213846035)
            ·
              refine ⟨18387255686058720320769053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12258170457372480213846035 18387255686058720320769053)
              ·
                refine ⟨6895220882272020120288395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18387255686058720320769053 6895220882272020120288395)
                ·
                  refine ⟨10342831323408030180432593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6895220882272020120288395 10342831323408030180432593)
                  ·
                    refine ⟨7757123492556022635324445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10342831323408030180432593 7757123492556022635324445)
                    ·
                      refine ⟨2908921309708508488246667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7757123492556022635324445 2908921309708508488246667)
                      ·
                        rfl

theorem cell23_5665104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 3].length) (baseStart_5665104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665104 prefixEnd_5665104 := by exact prefixLift 5665104
  have htrace : WordTrace (prefixWord ++ tailWord_5665104) baseStart_5665104 baseEnd_5665104 := by
    simpa [prefixWord, tailWord_5665104, baseEnd_5665104] using wordTrace_append hprefix tailTrace_5665104
  have hstable : (prefixWord ++ tailWord_5665104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665104).length < 2 ^ (prefixWord ++ tailWord_5665104).sum := by decide
  have hdescent : baseEnd_5665104 < baseStart_5665104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665161 : List Nat := [1, 2, 1, 1, 6, 1, 2, 3, 1, 3, 2]
def baseStart_5665161 : Nat := 118140960795 + 5665161 * 2 ^ 59
def prefixEnd_5665161 : Nat := 4983230072969 + 3 ^ 40 * 5665161 * 2
def baseEnd_5665161 : Nat := 2908950578105814765233905

theorem tailTrace_5665161 : CollatzResearch.WordTrace tailWord_5665161 prefixEnd_5665161 2908950578105814765233905 := by
  unfold tailWord_5665161
  simp only [CollatzResearch.WordTrace]
  refine ⟨206625396629096704314715337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137750264419397802876476891 206625396629096704314715337)
  ·
    refine ⟨154969047471822528236036503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206625396629096704314715337 154969047471822528236036503)
    ·
      refine ⟨232453571207733792354054755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154969047471822528236036503 232453571207733792354054755)
      ·
        refine ⟨348680356811600688531082133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232453571207733792354054755 348680356811600688531082133)
        ·
          refine ⟨16344391725543782274894475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 348680356811600688531082133 16344391725543782274894475)
          ·
            refine ⟨24516587588315673412341713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16344391725543782274894475 24516587588315673412341713)
            ·
              refine ⟨18387440691236755059256285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24516587588315673412341713 18387440691236755059256285)
              ·
                refine ⟨6895290259213783147221107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18387440691236755059256285 6895290259213783147221107)
                ·
                  refine ⟨10342935388820674720831661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6895290259213783147221107 10342935388820674720831661)
                  ·
                    refine ⟨3878600770807753020311873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10342935388820674720831661 3878600770807753020311873)
                    ·
                      refine ⟨2908950578105814765233905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3878600770807753020311873 2908950578105814765233905)
                      ·
                        rfl

theorem cell23_5665161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 3, 2].length) (baseStart_5665161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665161 prefixEnd_5665161 := by exact prefixLift 5665161
  have htrace : WordTrace (prefixWord ++ tailWord_5665161) baseStart_5665161 baseEnd_5665161 := by
    simpa [prefixWord, tailWord_5665161, baseEnd_5665161] using wordTrace_append hprefix tailTrace_5665161
  have hstable : (prefixWord ++ tailWord_5665161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665161).length < 2 ^ (prefixWord ++ tailWord_5665161).sum := by decide
  have hdescent : baseEnd_5665161 < baseStart_5665161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665177 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 2, 4, 3]
def baseStart_5665177 : Nat := 118140960795 + 5665177 * 2 ^ 59
def prefixEnd_5665177 : Nat := 4983230072969 + 3 ^ 40 * 5665177 * 2
def baseEnd_5665177 : Nat := 2908958793796286702633831

theorem tailTrace_5665177 : CollatzResearch.WordTrace tailWord_5665177 prefixEnd_5665177 2908958793796286702633831 := by
  unfold tailWord_5665177
  simp only [CollatzResearch.WordTrace]
  refine ⟨206625980197038739047297785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137750653464692492698198523 206625980197038739047297785)
  ·
    refine ⟨154969485147779054285473339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206625980197038739047297785 154969485147779054285473339)
    ·
      refine ⟨232454227721668581428210009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154969485147779054285473339 232454227721668581428210009)
      ·
        refine ⟨174340670791251436071157507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232454227721668581428210009 174340670791251436071157507)
        ·
          refine ⟨261511006186877154106736261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174340670791251436071157507 261511006186877154106736261)
          ·
            refine ⟨49033313660039466395013049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 261511006186877154106736261 49033313660039466395013049)
            ·
              refine ⟨36774985245029599796259787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49033313660039466395013049 36774985245029599796259787)
              ·
                refine ⟨55162477867544399694389681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36774985245029599796259787 55162477867544399694389681)
                ·
                  refine ⟨41371858400658299770792261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55162477867544399694389681 41371858400658299770792261)
                  ·
                    refine ⟨7757223450123431207023549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41371858400658299770792261 7757223450123431207023549)
                    ·
                      refine ⟨2908958793796286702633831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7757223450123431207023549 2908958793796286702633831)
                      ·
                        rfl

theorem cell23_5665177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 4, 3].length) (baseStart_5665177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665177 prefixEnd_5665177 := by exact prefixLift 5665177
  have htrace : WordTrace (prefixWord ++ tailWord_5665177) baseStart_5665177 baseEnd_5665177 := by
    simpa [prefixWord, tailWord_5665177, baseEnd_5665177] using wordTrace_append hprefix tailTrace_5665177
  have hstable : (prefixWord ++ tailWord_5665177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665177).length < 2 ^ (prefixWord ++ tailWord_5665177).sum := by decide
  have hdescent : baseEnd_5665177 < baseStart_5665177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665261 : List Nat := [1, 5, 1, 3, 1, 1, 3, 1, 2, 5]
def baseStart_5665261 : Nat := 118140960795 + 5665261 * 2 ^ 59
def prefixEnd_5665261 : Nat := 4983230072969 + 3 ^ 40 * 5665261 * 2
def baseEnd_5665261 : Nat := 969667308723754791327815

theorem tailTrace_5665261 : CollatzResearch.WordTrace tailWord_5665261 prefixEnd_5665261 969667308723754791327815 := by
  unfold tailWord_5665261
  simp only [CollatzResearch.WordTrace]
  refine ⟨206629043928734421393355637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137752695952489614262237091 206629043928734421393355637)
  ·
    refine ⟨19371472868318852005627091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 206629043928734421393355637 19371472868318852005627091)
    ·
      refine ⟨29057209302478278008440637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19371472868318852005627091 29057209302478278008440637)
      ·
        refine ⟨10896453488429354253165239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29057209302478278008440637 10896453488429354253165239)
        ·
          refine ⟨16344680232644031379747859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10896453488429354253165239 16344680232644031379747859)
          ·
            refine ⟨24517020348966047069621789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16344680232644031379747859 24517020348966047069621789)
            ·
              refine ⟨9193882630862267651108171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24517020348966047069621789 9193882630862267651108171)
              ·
                refine ⟨13790823946293401476662257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9193882630862267651108171 13790823946293401476662257)
                ·
                  refine ⟨10343117959720051107496693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13790823946293401476662257 10343117959720051107496693)
                  ·
                    refine ⟨969667308723754791327815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10343117959720051107496693 969667308723754791327815)
                    ·
                      rfl

theorem cell23_5665261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_5665261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665261 prefixEnd_5665261 := by exact prefixLift 5665261
  have htrace : WordTrace (prefixWord ++ tailWord_5665261) baseStart_5665261 baseEnd_5665261 := by
    simpa [prefixWord, tailWord_5665261, baseEnd_5665261] using wordTrace_append hprefix tailTrace_5665261
  have hstable : (prefixWord ++ tailWord_5665261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665261).length < 2 ^ (prefixWord ++ tailWord_5665261).sum := by decide
  have hdescent : baseEnd_5665261 < baseStart_5665261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665264 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 1, 6, 2]
def baseStart_5665264 : Nat := 118140960795 + 5665264 * 2 ^ 59
def prefixEnd_5665264 : Nat := 4983230072969 + 3 ^ 40 * 5665264 * 2
def baseEnd_5665264 : Nat := 2909003466613227862245931

theorem tailTrace_5665264 : CollatzResearch.WordTrace tailWord_5665264 prefixEnd_5665264 2909003466613227862245931 := by
  unfold tailWord_5665264
  simp only [CollatzResearch.WordTrace]
  refine ⟨103314576673861776452857423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137752768898482368603809897 103314576673861776452857423)
  ·
    refine ⟨154971865010792664679286135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103314576673861776452857423 154971865010792664679286135)
    ·
      refine ⟨232457797516188997018929203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154971865010792664679286135 232457797516188997018929203)
      ·
        refine ⟨348686696274283495528393805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232457797516188997018929203 348686696274283495528393805)
        ·
          refine ⟨130757511102856310823147677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 348686696274283495528393805 130757511102856310823147677)
          ·
            refine ⟨49034066663571116558680379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130757511102856310823147677 49034066663571116558680379)
            ·
              refine ⟨73551099995356674838020569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49034066663571116558680379 73551099995356674838020569)
              ·
                refine ⟨55163324996517506128515427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73551099995356674838020569 55163324996517506128515427)
                ·
                  refine ⟨82744987494776259192773141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55163324996517506128515427 82744987494776259192773141)
                  ·
                    refine ⟨3878671288817637149661241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82744987494776259192773141 3878671288817637149661241)
                    ·
                      refine ⟨2909003466613227862245931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3878671288817637149661241 2909003466613227862245931)
                      ·
                        rfl

theorem cell23_5665264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 1, 6, 2].length) (baseStart_5665264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665264 prefixEnd_5665264 := by exact prefixLift 5665264
  have htrace : WordTrace (prefixWord ++ tailWord_5665264) baseStart_5665264 baseEnd_5665264 := by
    simpa [prefixWord, tailWord_5665264, baseEnd_5665264] using wordTrace_append hprefix tailTrace_5665264
  have hstable : (prefixWord ++ tailWord_5665264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665264).length < 2 ^ (prefixWord ++ tailWord_5665264).sum := by decide
  have hdescent : baseEnd_5665264 < baseStart_5665264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665277 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 1, 3, 6]
def baseStart_5665277 : Nat := 118140960795 + 5665277 * 2 ^ 59
def prefixEnd_5665277 : Nat := 4983230072969 + 3 ^ 40 * 5665277 * 2
def baseEnd_5665277 : Nat := 2909010141861736311383371

theorem tailTrace_5665277 : CollatzResearch.WordTrace tailWord_5665277 prefixEnd_5665277 2909010141861736311383371 := by
  unfold tailWord_5665277
  simp only [CollatzResearch.WordTrace]
  refine ⟨206629627496676456125938085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137753084997784304083958723 206629627496676456125938085)
  ·
    refine ⟨38743055155626835523613391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206629627496676456125938085 38743055155626835523613391)
    ·
      refine ⟨58114582733440253285420087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38743055155626835523613391 58114582733440253285420087)
      ·
        refine ⟨87171874100160379928130131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58114582733440253285420087 87171874100160379928130131)
        ·
          refine ⟨130757811150240569892195197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87171874100160379928130131 130757811150240569892195197)
          ·
            refine ⟨49034179181340213709573199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130757811150240569892195197 49034179181340213709573199)
            ·
              refine ⟨73551268772010320564359799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49034179181340213709573199 73551268772010320564359799)
              ·
                refine ⟨110326903158015480846539699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73551268772010320564359799 110326903158015480846539699)
                ·
                  refine ⟨165490354737023221269809549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110326903158015480846539699 165490354737023221269809549)
                  ·
                    refine ⟨62058883026383707976178581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165490354737023221269809549 62058883026383707976178581)
                    ·
                      refine ⟨2909010141861736311383371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62058883026383707976178581 2909010141861736311383371)
                      ·
                        rfl

theorem cell23_5665277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_5665277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665277 prefixEnd_5665277 := by exact prefixLift 5665277
  have htrace : WordTrace (prefixWord ++ tailWord_5665277) baseStart_5665277 baseEnd_5665277 := by
    simpa [prefixWord, tailWord_5665277, baseEnd_5665277] using wordTrace_append hprefix tailTrace_5665277
  have hstable : (prefixWord ++ tailWord_5665277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665277).length < 2 ^ (prefixWord ++ tailWord_5665277).sum := by decide
  have hdescent : baseEnd_5665277 < baseStart_5665277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665281 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 2, 4, 2]
def baseStart_5665281 : Nat := 118140960795 + 5665281 * 2 ^ 59
def prefixEnd_5665281 : Nat := 4983230072969 + 3 ^ 40 * 5665281 * 2
def baseEnd_5665281 : Nat := 2909012195784354295733353

theorem tailTrace_5665281 : CollatzResearch.WordTrace tailWord_5665281 prefixEnd_5665281 2909012195784354295733353 := by
  unfold tailWord_5665281
  simp only [CollatzResearch.WordTrace]
  refine ⟨206629773388661964809083697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137753182259107976539389131 206629773388661964809083697)
  ·
    refine ⟨154972330041496473606812773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206629773388661964809083697 154972330041496473606812773)
    ·
      refine ⟨29057311882780588801277395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154972330041496473606812773 29057311882780588801277395)
      ·
        refine ⟨43585967824170883201916093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29057311882780588801277395 43585967824170883201916093)
        ·
          refine ⟨16344737934064081200718535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43585967824170883201916093 16344737934064081200718535)
          ·
            refine ⟨24517106901096121801077803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16344737934064081200718535 24517106901096121801077803)
            ·
              refine ⟨36775660351644182701616705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24517106901096121801077803 36775660351644182701616705)
              ·
                refine ⟨27581745263733137026212529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36775660351644182701616705 27581745263733137026212529)
                ·
                  refine ⟨20686308947799852769659397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27581745263733137026212529 20686308947799852769659397)
                  ·
                    refine ⟨3878682927712472394311137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20686308947799852769659397 3878682927712472394311137)
                    ·
                      refine ⟨2909012195784354295733353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3878682927712472394311137 2909012195784354295733353)
                      ·
                        rfl

theorem cell23_5665281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_5665281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665281 prefixEnd_5665281 := by exact prefixLift 5665281
  have htrace : WordTrace (prefixWord ++ tailWord_5665281) baseStart_5665281 baseEnd_5665281 := by
    simpa [prefixWord, tailWord_5665281, baseEnd_5665281] using wordTrace_append hprefix tailTrace_5665281
  have hstable : (prefixWord ++ tailWord_5665281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665281).length < 2 ^ (prefixWord ++ tailWord_5665281).sum := by decide
  have hdescent : baseEnd_5665281 < baseStart_5665281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665291 : List Nat := [1, 1, 1, 1, 7, 2, 2, 1, 3, 4]
def baseStart_5665291 : Nat := 118140960795 + 5665291 * 2 ^ 59
def prefixEnd_5665291 : Nat := 4983230072969 + 3 ^ 40 * 5665291 * 2
def baseEnd_5665291 : Nat := 969672443530299752202769

theorem tailTrace_5665291 : CollatzResearch.WordTrace tailWord_5665291 prefixEnd_5665291 969672443530299752202769 := by
  unfold tailWord_5665291
  simp only [CollatzResearch.WordTrace]
  refine ⟨206630138118625736516947727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137753425412417157677965151 206630138118625736516947727)
  ·
    refine ⟨309945207177938604775421591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206630138118625736516947727 309945207177938604775421591)
    ·
      refine ⟨464917810766907907163132387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309945207177938604775421591 464917810766907907163132387)
      ·
        refine ⟨697376716150361860744698581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464917810766907907163132387 697376716150361860744698581)
        ·
          refine ⟨16344766784774106111203873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 697376716150361860744698581 16344766784774106111203873)
          ·
            refine ⟨12258575088580579583402905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16344766784774106111203873 12258575088580579583402905)
            ·
              refine ⟨9193931316435434687552179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12258575088580579583402905 9193931316435434687552179)
              ·
                refine ⟨13790896974653152031328269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9193931316435434687552179 13790896974653152031328269)
                ·
                  refine ⟨5171586365494932011748101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13790896974653152031328269 5171586365494932011748101)
                  ·
                    refine ⟨969672443530299752202769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5171586365494932011748101 969672443530299752202769)
                    ·
                      rfl

theorem cell23_5665291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 4].length) (baseStart_5665291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665291 prefixEnd_5665291 := by exact prefixLift 5665291
  have htrace : WordTrace (prefixWord ++ tailWord_5665291) baseStart_5665291 baseEnd_5665291 := by
    simpa [prefixWord, tailWord_5665291, baseEnd_5665291] using wordTrace_append hprefix tailTrace_5665291
  have hstable : (prefixWord ++ tailWord_5665291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665291).length < 2 ^ (prefixWord ++ tailWord_5665291).sum := by decide
  have hdescent : baseEnd_5665291 < baseStart_5665291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665314 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 1, 7, 3]
def baseStart_5665314 : Nat := 118140960795 + 5665314 * 2 ^ 59
def prefixEnd_5665314 : Nat := 4983230072969 + 3 ^ 40 * 5665314 * 2
def baseEnd_5665314 : Nat := 2909029140645952666620701

theorem tailTrace_5665314 : CollatzResearch.WordTrace tailWord_5665314 prefixEnd_5665314 2909029140645952666620701 := by
  unfold tailWord_5665314
  simp only [CollatzResearch.WordTrace]
  refine ⟨51657744249385602861258749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137753984665028274296689997 51657744249385602861258749)
  ·
    refine ⟨19371654093519601072972031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51657744249385602861258749 19371654093519601072972031)
    ·
      refine ⟨29057481140279401609458047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19371654093519601072972031 29057481140279401609458047)
      ·
        refine ⟨43586221710419102414187071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29057481140279401609458047 43586221710419102414187071)
        ·
          refine ⟨65379332565628653621280607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43586221710419102414187071 65379332565628653621280607)
          ·
            refine ⟨98068998848442980431920911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65379332565628653621280607 98068998848442980431920911)
            ·
              refine ⟨147103498272664470647881367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98068998848442980431920911 147103498272664470647881367)
              ·
                refine ⟨220655247408996705971822051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147103498272664470647881367 220655247408996705971822051)
                ·
                  refine ⟨330982871113495058957733077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220655247408996705971822051 330982871113495058957733077)
                  ·
                    refine ⟨7757411041722540444321869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 330982871113495058957733077 7757411041722540444321869)
                    ·
                      refine ⟨2909029140645952666620701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7757411041722540444321869 2909029140645952666620701)
                      ·
                        rfl

theorem cell23_5665314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_5665314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665314 prefixEnd_5665314 := by exact prefixLift 5665314
  have htrace : WordTrace (prefixWord ++ tailWord_5665314) baseStart_5665314 baseEnd_5665314 := by
    simpa [prefixWord, tailWord_5665314, baseEnd_5665314] using wordTrace_append hprefix tailTrace_5665314
  have hstable : (prefixWord ++ tailWord_5665314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665314).length < 2 ^ (prefixWord ++ tailWord_5665314).sum := by decide
  have hdescent : baseEnd_5665314 < baseStart_5665314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665342 : List Nat := [4, 2, 1, 4, 2, 1, 1, 1, 3, 4]
def baseStart_5665342 : Nat := 118140960795 + 5665342 * 2 ^ 59
def prefixEnd_5665342 : Nat := 4983230072969 + 3 ^ 40 * 5665342 * 2
def baseEnd_5665342 : Nat := 969681172701426185690191

theorem tailTrace_5665342 : CollatzResearch.WordTrace tailWord_5665342 prefixEnd_5665342 969681172701426185690191 := by
  unfold tailWord_5665342
  simp only [CollatzResearch.WordTrace]
  refine ⟨25828999780180121528381785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137754665494293981484702853 25828999780180121528381785)
  ·
    refine ⟨19371749835135091146286339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25828999780180121528381785 19371749835135091146286339)
    ·
      refine ⟨29057624752702636719429509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19371749835135091146286339 29057624752702636719429509)
      ·
        refine ⟨5448304641131744384893033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29057624752702636719429509 5448304641131744384893033)
        ·
          refine ⟨4086228480848808288669775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5448304641131744384893033 4086228480848808288669775)
          ·
            refine ⟨6129342721273212433004663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4086228480848808288669775 6129342721273212433004663)
            ·
              refine ⟨9194014081909818649506995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6129342721273212433004663 9194014081909818649506995)
              ·
                refine ⟨13791021122864727974260493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9194014081909818649506995 13791021122864727974260493)
                ·
                  refine ⟨5171632921074272990347685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13791021122864727974260493 5171632921074272990347685)
                  ·
                    refine ⟨969681172701426185690191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5171632921074272990347685 969681172701426185690191)
                    ·
                      rfl

theorem cell23_5665342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_5665342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665342 prefixEnd_5665342 := by exact prefixLift 5665342
  have htrace : WordTrace (prefixWord ++ tailWord_5665342) baseStart_5665342 baseEnd_5665342 := by
    simpa [prefixWord, tailWord_5665342, baseEnd_5665342] using wordTrace_append hprefix tailTrace_5665342
  have hstable : (prefixWord ++ tailWord_5665342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665342).length < 2 ^ (prefixWord ++ tailWord_5665342).sum := by decide
  have hdescent : baseEnd_5665342 < baseStart_5665342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665381 : List Nat := [1, 3, 1, 3, 4, 1, 1, 2, 1, 6]
def baseStart_5665381 : Nat := 118140960795 + 5665381 * 2 ^ 59
def prefixEnd_5665381 : Nat := 4983230072969 + 3 ^ 40 * 5665381 * 2
def baseEnd_5665381 : Nat := 969687847949934634827631

theorem tailTrace_5665381 : CollatzResearch.WordTrace tailWord_5665381 prefixEnd_5665381 969687847949934634827631 := by
  unfold tailWord_5665381
  simp only [CollatzResearch.WordTrace]
  refine ⟨206633420688299681887723997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137755613792199787925149331 206633420688299681887723997)
  ·
    refine ⟨77487532758112380707896499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206633420688299681887723997 77487532758112380707896499)
    ·
      refine ⟨116231299137168571061844749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77487532758112380707896499 116231299137168571061844749)
      ·
        refine ⟨43586737176438214148191781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116231299137168571061844749 43586737176438214148191781)
        ·
          refine ⟨8172513220582165152785959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43586737176438214148191781 8172513220582165152785959)
          ·
            refine ⟨12258769830873247729178939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8172513220582165152785959 12258769830873247729178939)
            ·
              refine ⟨18388154746309871593768409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12258769830873247729178939 18388154746309871593768409)
              ·
                refine ⟨13791116059732403695326307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18388154746309871593768409 13791116059732403695326307)
                ·
                  refine ⟨20686674089598605542989461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13791116059732403695326307 20686674089598605542989461)
                  ·
                    refine ⟨969687847949934634827631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20686674089598605542989461 969687847949934634827631)
                    ·
                      rfl

theorem cell23_5665381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 6].length) (baseStart_5665381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665381 prefixEnd_5665381 := by exact prefixLift 5665381
  have htrace : WordTrace (prefixWord ++ tailWord_5665381) baseStart_5665381 baseEnd_5665381 := by
    simpa [prefixWord, tailWord_5665381, baseEnd_5665381] using wordTrace_append hprefix tailTrace_5665381
  have hstable : (prefixWord ++ tailWord_5665381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665381).length < 2 ^ (prefixWord ++ tailWord_5665381).sum := by decide
  have hdescent : baseEnd_5665381 < baseStart_5665381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665391 : List Nat := [1, 1, 2, 1, 3, 2, 2, 5, 1, 2, 3]
def baseStart_5665391 : Nat := 118140960795 + 5665391 * 2 ^ 59
def prefixEnd_5665391 : Nat := 4983230072969 + 3 ^ 40 * 5665391 * 2
def baseEnd_5665391 : Nat := 2909068678656348865357847

theorem tailTrace_5665391 : CollatzResearch.WordTrace tailWord_5665391 prefixEnd_5665391 2909068678656348865357847 := by
  unfold tailWord_5665391
  simp only [CollatzResearch.WordTrace]
  refine ⟨206633785418263453595588027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137755856945508969063725351 206633785418263453595588027)
  ·
    refine ⟨309950678127395180393382041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206633785418263453595588027 309950678127395180393382041)
    ·
      refine ⟨232463008595546385295036531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309950678127395180393382041 232463008595546385295036531)
      ·
        refine ⟨348694512893319577942554797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232463008595546385295036531 348694512893319577942554797)
        ·
          refine ⟨130760442334994841728458049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 348694512893319577942554797 130760442334994841728458049)
          ·
            refine ⟨98070331751246131296343537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130760442334994841728458049 98070331751246131296343537)
            ·
              refine ⟨73552748813434598472257653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98070331751246131296343537 73552748813434598472257653)
              ·
                refine ⟨6895570201259493606774155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73552748813434598472257653 6895570201259493606774155)
                ·
                  refine ⟨10343355301889240410161233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6895570201259493606774155 10343355301889240410161233)
                  ·
                    refine ⟨7757516476416930307620925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10343355301889240410161233 7757516476416930307620925)
                    ·
                      refine ⟨2909068678656348865357847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7757516476416930307620925 2909068678656348865357847)
                      ·
                        rfl

theorem cell23_5665391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 2, 3].length) (baseStart_5665391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665391 prefixEnd_5665391 := by exact prefixLift 5665391
  have htrace : WordTrace (prefixWord ++ tailWord_5665391) baseStart_5665391 baseEnd_5665391 := by
    simpa [prefixWord, tailWord_5665391, baseEnd_5665391] using wordTrace_append hprefix tailTrace_5665391
  have hstable : (prefixWord ++ tailWord_5665391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665391).length < 2 ^ (prefixWord ++ tailWord_5665391).sum := by decide
  have hdescent : baseEnd_5665391 < baseStart_5665391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665394 : List Nat := [3, 2, 1, 2, 4, 11]
def baseStart_5665394 : Nat := 118140960795 + 5665394 * 2 ^ 59
def prefixEnd_5665394 : Nat := 4983230072969 + 3 ^ 40 * 5665394 * 2
def baseEnd_5665394 : Nat := 11971482383120626969631

theorem tailTrace_5665394 : CollatzResearch.WordTrace tailWord_5665394 prefixEnd_5665394 11971482383120626969631 := by
  unfold tailWord_5665394
  simp only [CollatzResearch.WordTrace]
  refine ⟨51658473709313146276986809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137755929891501723405298157 51658473709313146276986809)
  ·
    refine ⟨38743855281984859707740107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51658473709313146276986809 38743855281984859707740107)
    ·
      refine ⟨58115782922977289561610161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38743855281984859707740107 58115782922977289561610161)
      ·
        refine ⟨43586837192232967171207621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58115782922977289561610161 43586837192232967171207621)
        ·
          refine ⟨8172531973543681344601429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43586837192232967171207621 8172531973543681344601429)
          ·
            refine ⟨11971482383120626969631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8172531973543681344601429 11971482383120626969631)
            ·
              rfl

theorem cell23_5665394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 11].length) (baseStart_5665394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665394 prefixEnd_5665394 := by exact prefixLift 5665394
  have htrace : WordTrace (prefixWord ++ tailWord_5665394) baseStart_5665394 baseEnd_5665394 := by
    simpa [prefixWord, tailWord_5665394, baseEnd_5665394] using wordTrace_append hprefix tailTrace_5665394
  have hstable : (prefixWord ++ tailWord_5665394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665394).length < 2 ^ (prefixWord ++ tailWord_5665394).sum := by decide
  have hdescent : baseEnd_5665394 < baseStart_5665394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665418 : List Nat := [3, 1, 2, 3, 3, 1, 2, 1, 1, 2, 4]
def baseStart_5665418 : Nat := 118140960795 + 5665418 * 2 ^ 59
def prefixEnd_5665418 : Nat := 4983230072969 + 3 ^ 40 * 5665418 * 2
def baseEnd_5665418 : Nat := 2909082542634020259720223

theorem tailTrace_5665418 : CollatzResearch.WordTrace tailWord_5665418 prefixEnd_5665418 2909082542634020259720223 := by
  unfold tailWord_5665418
  simp only [CollatzResearch.WordTrace]
  refine ⟨51658692547291409301705227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137756513459443758137880605 51658692547291409301705227)
  ·
    refine ⟨77488038820937113952557841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51658692547291409301705227 77488038820937113952557841)
    ·
      refine ⟨58116029115702835464418381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77488038820937113952557841 58116029115702835464418381)
      ·
        refine ⟨21793510918388563299156893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58116029115702835464418381 21793510918388563299156893)
        ·
          refine ⟨8172566594395711237183835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21793510918388563299156893 8172566594395711237183835)
          ·
            refine ⟨12258849891593566855775753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8172566594395711237183835 12258849891593566855775753)
            ·
              refine ⟨9194137418695175141831815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12258849891593566855775753 9194137418695175141831815)
              ·
                refine ⟨13791206128042762712747723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9194137418695175141831815 13791206128042762712747723)
                ·
                  refine ⟨20686809192064144069121585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13791206128042762712747723 20686809192064144069121585)
                  ·
                    refine ⟨15515106894048108051841189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20686809192064144069121585 15515106894048108051841189)
                    ·
                      refine ⟨2909082542634020259720223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15515106894048108051841189 2909082542634020259720223)
                      ·
                        rfl

theorem cell23_5665418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_5665418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665418 prefixEnd_5665418 := by exact prefixLift 5665418
  have htrace : WordTrace (prefixWord ++ tailWord_5665418) baseStart_5665418 baseEnd_5665418 := by
    simpa [prefixWord, tailWord_5665418, baseEnd_5665418] using wordTrace_append hprefix tailTrace_5665418
  have hstable : (prefixWord ++ tailWord_5665418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665418).length < 2 ^ (prefixWord ++ tailWord_5665418).sum := by decide
  have hdescent : baseEnd_5665418 < baseStart_5665418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665428 : List Nat := [2, 4, 2, 2, 1, 2, 3, 7]
def baseStart_5665428 : Nat := 118140960795 + 5665428 * 2 ^ 59
def prefixEnd_5665428 : Nat := 4983230072969 + 3 ^ 40 * 5665428 * 2
def baseEnd_5665428 : Nat := 107743988053354267429451

theorem tailTrace_5665428 : CollatzResearch.WordTrace tailWord_5665428 prefixEnd_5665428 107743988053354267429451 := by
  unfold tailWord_5665428
  simp only [CollatzResearch.WordTrace]
  refine ⟨103317567459564704457342469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137756756612752939276456625 103317567459564704457342469)
  ·
    refine ⟨19372043898668382085751713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103317567459564704457342469 19372043898668382085751713)
    ·
      refine ⟨14529032924001286564313785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19372043898668382085751713 14529032924001286564313785)
      ·
        refine ⟨10896774693000964923235339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14529032924001286564313785 10896774693000964923235339)
        ·
          refine ⟨16345162039501447384853009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10896774693000964923235339 16345162039501447384853009)
          ·
            refine ⟨12258871529626085538639757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16345162039501447384853009 12258871529626085538639757)
            ·
              refine ⟨4597076823609782076989909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12258871529626085538639757 4597076823609782076989909)
              ·
                refine ⟨107743988053354267429451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4597076823609782076989909 107743988053354267429451)
                ·
                  rfl

theorem cell23_5665428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 7].length) (baseStart_5665428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665428 prefixEnd_5665428 := by exact prefixLift 5665428
  have htrace : WordTrace (prefixWord ++ tailWord_5665428) baseStart_5665428 baseEnd_5665428 := by
    simpa [prefixWord, tailWord_5665428, baseEnd_5665428] using wordTrace_append hprefix tailTrace_5665428
  have hstable : (prefixWord ++ tailWord_5665428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665428).length < 2 ^ (prefixWord ++ tailWord_5665428).sum := by decide
  have hdescent : baseEnd_5665428 < baseStart_5665428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665438 : List Nat := [4, 3, 1, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_5665438 : Nat := 118140960795 + 5665438 * 2 ^ 59
def prefixEnd_5665438 : Nat := 4983230072969 + 3 ^ 40 * 5665438 * 2
def baseEnd_5665438 : Nat := 2909092812247110181470131

theorem tailTrace_5665438 : CollatzResearch.WordTrace tailWord_5665438 prefixEnd_5665438 2909092812247110181470131 := by
  unfold tailWord_5665438
  simp only [CollatzResearch.WordTrace]
  refine ⟨25829437456136647577818621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137756999766062120415032645 25829437456136647577818621)
  ·
    refine ⟨9686039046051242841681983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25829437456136647577818621 9686039046051242841681983)
    ·
      refine ⟨14529058569076864262522975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9686039046051242841681983 14529058569076864262522975)
      ·
        refine ⟨21793587853615296393784463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14529058569076864262522975 21793587853615296393784463)
        ·
          refine ⟨32690381780422944590676695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21793587853615296393784463 32690381780422944590676695)
          ·
            refine ⟨49035572670634416886015043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32690381780422944590676695 49035572670634416886015043)
            ·
              refine ⟨73553359005951625329022565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49035572670634416886015043 73553359005951625329022565)
              ·
                refine ⟨13791254813615929749191731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73553359005951625329022565 13791254813615929749191731)
                ·
                  refine ⟨20686882220423894623787597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13791254813615929749191731 20686882220423894623787597)
                  ·
                    refine ⟨7757580832658960483920349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20686882220423894623787597 7757580832658960483920349)
                    ·
                      refine ⟨2909092812247110181470131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7757580832658960483920349 2909092812247110181470131)
                      ·
                        rfl

theorem cell23_5665438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_5665438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665438 prefixEnd_5665438 := by exact prefixLift 5665438
  have htrace : WordTrace (prefixWord ++ tailWord_5665438) baseStart_5665438 baseEnd_5665438 := by
    simpa [prefixWord, tailWord_5665438, baseEnd_5665438] using wordTrace_append hprefix tailTrace_5665438
  have hstable : (prefixWord ++ tailWord_5665438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665438).length < 2 ^ (prefixWord ++ tailWord_5665438).sum := by decide
  have hdescent : baseEnd_5665438 < baseStart_5665438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665455 : List Nat := [1, 1, 2, 1, 2, 7, 1, 2, 2, 1, 3]
def baseStart_5665455 : Nat := 118140960795 + 5665455 * 2 ^ 59
def prefixEnd_5665455 : Nat := 4983230072969 + 3 ^ 40 * 5665455 * 2
def baseEnd_5665455 : Nat := 2909101541418236614957553

theorem tailTrace_5665455 : CollatzResearch.WordTrace tailWord_5665455 prefixEnd_5665455 2909101541418236614957553 := by
  unfold tailWord_5665455
  simp only [CollatzResearch.WordTrace]
  refine ⟨206636119690031592525917819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137757413126687728350611879 206636119690031592525917819)
  ·
    refine ⟨309954179535047388788876729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206636119690031592525917819 309954179535047388788876729)
    ·
      refine ⟨232465634651285541591657547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309954179535047388788876729 232465634651285541591657547)
      ·
        refine ⟨348698451976928312387486321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232465634651285541591657547 348698451976928312387486321)
        ·
          refine ⟨261523838982696234290614741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348698451976928312387486321 261523838982696234290614741)
          ·
            refine ⟨6129464976156942991186283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 261523838982696234290614741 6129464976156942991186283)
            ·
              refine ⟨9194197464235414486779425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6129464976156942991186283 9194197464235414486779425)
              ·
                refine ⟨6895648098176560865084569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9194197464235414486779425 6895648098176560865084569)
                ·
                  refine ⟨5171736073632420648813427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6895648098176560865084569 5171736073632420648813427)
                  ·
                    refine ⟨7757604110448630973220141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5171736073632420648813427 7757604110448630973220141)
                    ·
                      refine ⟨2909101541418236614957553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7757604110448630973220141 2909101541418236614957553)
                      ·
                        rfl

theorem cell23_5665455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 1, 3].length) (baseStart_5665455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665455 prefixEnd_5665455 := by exact prefixLift 5665455
  have htrace : WordTrace (prefixWord ++ tailWord_5665455) baseStart_5665455 baseEnd_5665455 := by
    simpa [prefixWord, tailWord_5665455, baseEnd_5665455] using wordTrace_append hprefix tailTrace_5665455
  have hstable : (prefixWord ++ tailWord_5665455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665455).length < 2 ^ (prefixWord ++ tailWord_5665455).sum := by decide
  have hdescent : baseEnd_5665455 < baseStart_5665455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665464 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 6, 1, 5]
def baseStart_5665464 : Nat := 118140960795 + 5665464 * 2 ^ 59
def prefixEnd_5665464 : Nat := 4983230072969 + 3 ^ 40 * 5665464 * 2
def baseEnd_5665464 : Nat := 2909106162744127079745011

theorem tailTrace_5665464 : CollatzResearch.WordTrace tailWord_5665464 prefixEnd_5665464 2909106162744127079745011 := by
  unfold tailWord_5665464
  simp only [CollatzResearch.WordTrace]
  refine ⟨103318223973499493531497723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137757631964665991375330297 103318223973499493531497723)
  ·
    refine ⟨154977335960249240297246585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103318223973499493531497723 154977335960249240297246585)
    ·
      refine ⟨116233001970186930222934939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154977335960249240297246585 116233001970186930222934939)
      ·
        refine ⟨174349502955280395334402409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116233001970186930222934939 174349502955280395334402409)
        ·
          refine ⟨130762127216460296500801807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174349502955280395334402409 130762127216460296500801807)
          ·
            refine ⟨196143190824690444751202711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130762127216460296500801807 196143190824690444751202711)
            ·
              refine ⟨294214786237035667126804067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196143190824690444751202711 294214786237035667126804067)
              ·
                refine ⟨441322179355553500690206101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294214786237035667126804067 441322179355553500690206101)
                ·
                  refine ⟨20686977157291570344853411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 441322179355553500690206101 20686977157291570344853411)
                  ·
                    refine ⟨31030465735937355517280117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20686977157291570344853411 31030465735937355517280117)
                    ·
                      refine ⟨2909106162744127079745011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31030465735937355517280117 2909106162744127079745011)
                      ·
                        rfl

theorem cell23_5665464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_5665464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665464 prefixEnd_5665464 := by exact prefixLift 5665464
  have htrace : WordTrace (prefixWord ++ tailWord_5665464) baseStart_5665464 baseEnd_5665464 := by
    simpa [prefixWord, tailWord_5665464, baseEnd_5665464] using wordTrace_append hprefix tailTrace_5665464
  have hstable : (prefixWord ++ tailWord_5665464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665464).length < 2 ^ (prefixWord ++ tailWord_5665464).sum := by decide
  have hdescent : baseEnd_5665464 < baseStart_5665464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665518 : List Nat := [4, 1, 2, 1, 1, 5, 1, 1, 7]
def baseStart_5665518 : Nat := 118140960795 + 5665518 * 2 ^ 59
def prefixEnd_5665518 : Nat := 4983230072969 + 3 ^ 40 * 5665518 * 2
def baseEnd_5665518 : Nat := 323237098966607763163307

theorem tailTrace_5665518 : CollatzResearch.WordTrace tailWord_5665518 prefixEnd_5665518 323237098966607763163307 := by
  unfold tailWord_5665518
  simp only [CollatzResearch.WordTrace]
  refine ⟨25829802186100419285682651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137758944992535569523640805 25829802186100419285682651)
  ·
    refine ⟨38744703279150628928523977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25829802186100419285682651 38744703279150628928523977)
    ·
      refine ⟨29058527459362971696392983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38744703279150628928523977 29058527459362971696392983)
      ·
        refine ⟨43587791189044457544589475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29058527459362971696392983 43587791189044457544589475)
        ·
          refine ⟨65381686783566686316884213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43587791189044457544589475 65381686783566686316884213)
          ·
            refine ⟨6129533135959376842207895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65381686783566686316884213 6129533135959376842207895)
            ·
              refine ⟨9194299703939065263311843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6129533135959376842207895 9194299703939065263311843)
              ·
                refine ⟨13791449555908597894967765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9194299703939065263311843 13791449555908597894967765)
                ·
                  refine ⟨323237098966607763163307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13791449555908597894967765 323237098966607763163307)
                  ·
                    rfl

theorem cell23_5665518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_5665518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665518 prefixEnd_5665518 := by exact prefixLift 5665518
  have htrace : WordTrace (prefixWord ++ tailWord_5665518) baseStart_5665518 baseEnd_5665518 := by
    simpa [prefixWord, tailWord_5665518, baseEnd_5665518] using wordTrace_append hprefix tailTrace_5665518
  have hstable : (prefixWord ++ tailWord_5665518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665518).length < 2 ^ (prefixWord ++ tailWord_5665518).sum := by decide
  have hdescent : baseEnd_5665518 < baseStart_5665518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665561 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 7, 4]
def baseStart_5665561 : Nat := 118140960795 + 5665561 * 2 ^ 59
def prefixEnd_5665561 : Nat := 4983230072969 + 3 ^ 40 * 5665561 * 2
def baseEnd_5665561 : Nat := 969718656789204400077355

theorem tailTrace_5665561 : CollatzResearch.WordTrace tailWord_5665561 prefixEnd_5665561 969718656789204400077355 := by
  unfold tailWord_5665561
  simp only [CollatzResearch.WordTrace]
  refine ⟨206639985827647572629276537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137759990551765048419517691 206639985827647572629276537)
  ·
    refine ⟨154979989370735679471957403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206639985827647572629276537 154979989370735679471957403)
    ·
      refine ⟨232469984056103519207936105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154979989370735679471957403 232469984056103519207936105)
      ·
        refine ⟨174352488042077639405952079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232469984056103519207936105 174352488042077639405952079)
        ·
          refine ⟨261528732063116459108928119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174352488042077639405952079 261528732063116459108928119)
          ·
            refine ⟨392293098094674688663392179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261528732063116459108928119 392293098094674688663392179)
            ·
              refine ⟨588439647142012032995088269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392293098094674688663392179 588439647142012032995088269)
              ·
                refine ⟨220664867678254512373158101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 588439647142012032995088269 220664867678254512373158101)
                ·
                  refine ⟨5171832836209090133745893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 220664867678254512373158101 5171832836209090133745893)
                  ·
                    refine ⟨969718656789204400077355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5171832836209090133745893 969718656789204400077355)
                    ·
                      rfl

theorem cell23_5665561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 4].length) (baseStart_5665561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665561 prefixEnd_5665561 := by exact prefixLift 5665561
  have htrace : WordTrace (prefixWord ++ tailWord_5665561) baseStart_5665561 baseEnd_5665561 := by
    simpa [prefixWord, tailWord_5665561, baseEnd_5665561] using wordTrace_append hprefix tailTrace_5665561
  have hstable : (prefixWord ++ tailWord_5665561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665561).length < 2 ^ (prefixWord ++ tailWord_5665561).sum := by decide
  have hdescent : baseEnd_5665561 < baseStart_5665561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665568 : List Nat := [2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 4]
def baseStart_5665568 : Nat := 118140960795 + 5665568 * 2 ^ 59
def prefixEnd_5665568 : Nat := 4983230072969 + 3 ^ 40 * 5665568 * 2
def baseEnd_5665568 : Nat := 2909159564732194672844533

theorem tailTrace_5665568 : CollatzResearch.WordTrace tailWord_5665568 prefixEnd_5665568 2909159564732194672844533 := by
  unfold tailWord_5665568
  simp only [CollatzResearch.WordTrace]
  refine ⟨103320120569311106412390679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137760160759081475216520905 103320120569311106412390679)
  ·
    refine ⟨154980180853966659618586019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103320120569311106412390679 154980180853966659618586019)
    ·
      refine ⟨232470271280949989427879029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154980180853966659618586019 232470271280949989427879029)
      ·
        refine ⟨21794087932589061508863659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 232470271280949989427879029 21794087932589061508863659)
        ·
          refine ⟨32691131898883592263295489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21794087932589061508863659 32691131898883592263295489)
          ·
            refine ⟨24518348924162694197471617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32691131898883592263295489 24518348924162694197471617)
            ·
              refine ⟨18388761693122020648103713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24518348924162694197471617 18388761693122020648103713)
              ·
                refine ⟨13791571269841515486077785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18388761693122020648103713 13791571269841515486077785)
                ·
                  refine ⟨10343678452381136614558339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13791571269841515486077785 10343678452381136614558339)
                  ·
                    refine ⟨15515517678571704921837509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10343678452381136614558339 15515517678571704921837509)
                    ·
                      refine ⟨2909159564732194672844533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15515517678571704921837509 2909159564732194672844533)
                      ·
                        rfl

theorem cell23_5665568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_5665568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665568 prefixEnd_5665568 := by exact prefixLift 5665568
  have htrace : WordTrace (prefixWord ++ tailWord_5665568) baseStart_5665568 baseEnd_5665568 := by
    simpa [prefixWord, tailWord_5665568, baseEnd_5665568] using wordTrace_append hprefix tailTrace_5665568
  have hstable : (prefixWord ++ tailWord_5665568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665568).length < 2 ^ (prefixWord ++ tailWord_5665568).sum := by decide
  have hdescent : baseEnd_5665568 < baseStart_5665568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665571 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 3]
def baseStart_5665571 : Nat := 118140960795 + 5665571 * 2 ^ 59
def prefixEnd_5665571 : Nat := 4983230072969 + 3 ^ 40 * 5665571 * 2
def baseEnd_5665571 : Nat := 2909161105174158161107019

theorem tailTrace_5665571 : CollatzResearch.WordTrace tailWord_5665571 prefixEnd_5665571 2909161105174158161107019 := by
  unfold tailWord_5665571
  simp only [CollatzResearch.WordTrace]
  refine ⟨206640350557611344337140567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137760233705074229558093711 206640350557611344337140567)
  ·
    refine ⟨309960525836417016505710851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206640350557611344337140567 309960525836417016505710851)
    ·
      refine ⟨464940788754625524758566277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309960525836417016505710851 464940788754625524758566277)
      ·
        refine ⟨87176397891492285892231177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 464940788754625524758566277 87176397891492285892231177)
        ·
          refine ⟨65382298418619214419173383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87176397891492285892231177 65382298418619214419173383)
          ·
            refine ⟨98073447627928821628760075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65382298418619214419173383 98073447627928821628760075)
            ·
              refine ⟨147110171441893232443140113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98073447627928821628760075 147110171441893232443140113)
              ·
                refine ⟨110332628581419924332355085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147110171441893232443140113 110332628581419924332355085)
                ·
                  refine ⟨41374735718032471624633157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110332628581419924332355085 41374735718032471624633157)
                  ·
                    refine ⟨7757762947131088429618717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41374735718032471624633157 7757762947131088429618717)
                    ·
                      refine ⟨2909161105174158161107019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7757762947131088429618717 2909161105174158161107019)
                      ·
                        rfl

theorem cell23_5665571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_5665571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665571 prefixEnd_5665571 := by exact prefixLift 5665571
  have htrace : WordTrace (prefixWord ++ tailWord_5665571) baseStart_5665571 baseEnd_5665571 := by
    simpa [prefixWord, tailWord_5665571, baseEnd_5665571] using wordTrace_append hprefix tailTrace_5665571
  have hstable : (prefixWord ++ tailWord_5665571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665571).length < 2 ^ (prefixWord ++ tailWord_5665571).sum := by decide
  have hdescent : baseEnd_5665571 < baseStart_5665571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665591 : List Nat := [1, 1, 3, 1, 2, 1, 3, 5, 6]
def baseStart_5665591 : Nat := 118140960795 + 5665591 * 2 ^ 59
def prefixEnd_5665591 : Nat := 4983230072969 + 3 ^ 40 * 5665591 * 2
def baseEnd_5665591 : Nat := 323241263865249786984103

theorem tailTrace_5665591 : CollatzResearch.WordTrace tailWord_5665591 prefixEnd_5665591 323241263865249786984103 := by
  unfold tailWord_5665591
  simp only [CollatzResearch.WordTrace]
  refine ⟨206641080017538887752868627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137760720011692591835245751 206641080017538887752868627)
  ·
    refine ⟨309961620026308331629302941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206641080017538887752868627 309961620026308331629302941)
    ·
      refine ⟨116235607509865624360988603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 309961620026308331629302941 116235607509865624360988603)
      ·
        refine ⟨174353411264798436541482905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116235607509865624360988603 174353411264798436541482905)
        ·
          refine ⟨130765058448598827406112179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174353411264798436541482905 130765058448598827406112179)
          ·
            refine ⟨196147587672898241109168269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130765058448598827406112179 196147587672898241109168269)
            ·
              refine ⟨73555345377336840415938101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196147587672898241109168269 73555345377336840415938101)
              ·
                refine ⟨6895813629125328788994197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73555345377336840415938101 6895813629125328788994197)
                ·
                  refine ⟨323241263865249786984103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6895813629125328788994197 323241263865249786984103)
                  ·
                    rfl

theorem cell23_5665591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 6].length) (baseStart_5665591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665591 prefixEnd_5665591 := by exact prefixLift 5665591
  have htrace : WordTrace (prefixWord ++ tailWord_5665591) baseStart_5665591 baseEnd_5665591 := by
    simpa [prefixWord, tailWord_5665591, baseEnd_5665591] using wordTrace_append hprefix tailTrace_5665591
  have hstable : (prefixWord ++ tailWord_5665591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665591).length < 2 ^ (prefixWord ++ tailWord_5665591).sum := by decide
  have hdescent : baseEnd_5665591 < baseStart_5665591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665612 : List Nat := [2, 2, 1, 3, 3, 2, 2, 3, 1, 4]
def baseStart_5665612 : Nat := 118140960795 + 5665612 * 2 ^ 59
def prefixEnd_5665612 : Nat := 4983230072969 + 3 ^ 40 * 5665612 * 2
def baseEnd_5665612 : Nat := 969727385960330833564777

theorem tailTrace_5665612 : CollatzResearch.WordTrace tailWord_5665612 prefixEnd_5665612 969727385960330833564777 := by
  unfold tailWord_5665612
  simp only [CollatzResearch.WordTrace]
  refine ⟨103320922975231404169691545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137761230633641872226255393 103320922975231404169691545)
  ·
    refine ⟨77490692231423553127268659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103320922975231404169691545 77490692231423553127268659)
    ·
      refine ⟨116236038347135329690902989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77490692231423553127268659 116236038347135329690902989)
      ·
        refine ⟨43588514380175748634088621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116236038347135329690902989 43588514380175748634088621)
        ·
          refine ⟨16345692892565905737783233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43588514380175748634088621 16345692892565905737783233)
          ·
            refine ⟨12259269669424429303337425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16345692892565905737783233 12259269669424429303337425)
            ·
              refine ⟨9194452252068321977503069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12259269669424429303337425 9194452252068321977503069)
              ·
                refine ⟨3447919594525620741563651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9194452252068321977503069 3447919594525620741563651)
                ·
                  refine ⟨5171879391788431112345477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3447919594525620741563651 5171879391788431112345477)
                  ·
                    refine ⟨969727385960330833564777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5171879391788431112345477 969727385960330833564777)
                    ·
                      rfl

theorem cell23_5665612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 1, 4].length) (baseStart_5665612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665612 prefixEnd_5665612 := by exact prefixLift 5665612
  have htrace : WordTrace (prefixWord ++ tailWord_5665612) baseStart_5665612 baseEnd_5665612 := by
    simpa [prefixWord, tailWord_5665612, baseEnd_5665612] using wordTrace_append hprefix tailTrace_5665612
  have hstable : (prefixWord ++ tailWord_5665612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665612).length < 2 ^ (prefixWord ++ tailWord_5665612).sum := by decide
  have hdescent : baseEnd_5665612 < baseStart_5665612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665628 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_5665628 : Nat := 118140960795 + 5665628 * 2 ^ 59
def prefixEnd_5665628 : Nat := 4983230072969 + 3 ^ 40 * 5665628 * 2
def baseEnd_5665628 : Nat := 2909190373571464438094257

theorem tailTrace_5665628 : CollatzResearch.WordTrace tailWord_5665628 prefixEnd_5665628 2909190373571464438094257 := by
  unfold tailWord_5665628
  simp only [CollatzResearch.WordTrace]
  refine ⟨103321214759202421535982769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137761619678936562047977025 103321214759202421535982769)
  ·
    refine ⟨77490911069401816151987077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103321214759202421535982769 77490911069401816151987077)
    ·
      refine ⟨14529545825512840528497577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77490911069401816151987077 14529545825512840528497577)
      ·
        refine ⟨10897159369134630396373183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14529545825512840528497577 10897159369134630396373183)
        ·
          refine ⟨16345739053701945594559775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10897159369134630396373183 16345739053701945594559775)
          ·
            refine ⟨24518608580552918391839663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16345739053701945594559775 24518608580552918391839663)
            ·
              refine ⟨36777912870829377587759495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24518608580552918391839663 36777912870829377587759495)
              ·
                refine ⟨55166869306244066381639243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36777912870829377587759495 55166869306244066381639243)
                ·
                  refine ⟨82750303959366099572458865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55166869306244066381639243 82750303959366099572458865)
                  ·
                    refine ⟨62062727969524574679344149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82750303959366099572458865 62062727969524574679344149)
                    ·
                      refine ⟨2909190373571464438094257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62062727969524574679344149 2909190373571464438094257)
                      ·
                        rfl

theorem cell23_5665628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_5665628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665628 prefixEnd_5665628 := by exact prefixLift 5665628
  have htrace : WordTrace (prefixWord ++ tailWord_5665628) baseStart_5665628 baseEnd_5665628 := by
    simpa [prefixWord, tailWord_5665628, baseEnd_5665628] using wordTrace_append hprefix tailTrace_5665628
  have hstable : (prefixWord ++ tailWord_5665628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665628).length < 2 ^ (prefixWord ++ tailWord_5665628).sum := by decide
  have hdescent : baseEnd_5665628 < baseStart_5665628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665635 : List Nat := [1, 1, 1, 5, 3, 1, 1, 3, 3, 1, 3]
def baseStart_5665635 : Nat := 118140960795 + 5665635 * 2 ^ 59
def prefixEnd_5665635 : Nat := 4983230072969 + 3 ^ 40 * 5665635 * 2
def baseEnd_5665635 : Nat := 2909193967936045910706725

theorem tailTrace_5665635 : CollatzResearch.WordTrace tailWord_5665635 prefixEnd_5665635 2909193967936045910706725 := by
  unfold tailWord_5665635
  simp only [CollatzResearch.WordTrace]
  refine ⟨206642684829379483267470359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137761789886252988844980239 206642684829379483267470359)
  ·
    refine ⟨309964027244069224901205539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206642684829379483267470359 309964027244069224901205539)
    ·
      refine ⟨464946040866103837351808309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309964027244069224901205539 464946040866103837351808309)
      ·
        refine ⟨43588691331197234751732029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 464946040866103837351808309 43588691331197234751732029)
        ·
          refine ⟨16345759249198963031899511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43588691331197234751732029 16345759249198963031899511)
          ·
            refine ⟨24518638873798444547849267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16345759249198963031899511 24518638873798444547849267)
            ·
              refine ⟨36777958310697666821773901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24518638873798444547849267 36777958310697666821773901)
              ·
                refine ⟨13791734366511625058165213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36777958310697666821773901 13791734366511625058165213)
                ·
                  refine ⟨5171900387441859396811955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13791734366511625058165213 5171900387441859396811955)
                  ·
                    refine ⟨7757850581162789095217933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5171900387441859396811955 7757850581162789095217933)
                    ·
                      refine ⟨2909193967936045910706725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7757850581162789095217933 2909193967936045910706725)
                      ·
                        rfl

theorem cell23_5665635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_5665635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665635 prefixEnd_5665635 := by exact prefixLift 5665635
  have htrace : WordTrace (prefixWord ++ tailWord_5665635) baseStart_5665635 baseEnd_5665635 := by
    simpa [prefixWord, tailWord_5665635, baseEnd_5665635] using wordTrace_append hprefix tailTrace_5665635
  have hstable : (prefixWord ++ tailWord_5665635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665635).length < 2 ^ (prefixWord ++ tailWord_5665635).sum := by decide
  have hdescent : baseEnd_5665635 < baseStart_5665635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665658 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2]
def baseStart_5665658 : Nat := 118140960795 + 5665658 * 2 ^ 59
def prefixEnd_5665658 : Nat := 4983230072969 + 3 ^ 40 * 5665658 * 2
def baseEnd_5665658 : Nat := 2909205777991099320719119

theorem tailTrace_5665658 : CollatzResearch.WordTrace tailWord_5665658 prefixEnd_5665658 2909205777991099320719119 := by
  unfold tailWord_5665658
  simp only [CollatzResearch.WordTrace]
  refine ⟨51660880927074039548889407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137762349138864105463705085 51660880927074039548889407)
  ·
    refine ⟨77491321390611059323334111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51660880927074039548889407 77491321390611059323334111)
    ·
      refine ⟨116236982085916588985001167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77491321390611059323334111 116236982085916588985001167)
      ·
        refine ⟨174355473128874883477501751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116236982085916588985001167 174355473128874883477501751)
        ·
          refine ⟨261533209693312325216252627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174355473128874883477501751 261533209693312325216252627)
          ·
            refine ⟨392299814539968487824378941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261533209693312325216252627 392299814539968487824378941)
            ·
              refine ⟨147112430452488182934142103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 392299814539968487824378941 147112430452488182934142103)
              ·
                refine ⟨220668645678732274401213155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147112430452488182934142103 220668645678732274401213155)
                ·
                  refine ⟨331002968518098411601819733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220668645678732274401213155 331002968518098411601819733)
                  ·
                    refine ⟨3878941037321465760958825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 331002968518098411601819733 3878941037321465760958825)
                    ·
                      refine ⟨2909205777991099320719119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3878941037321465760958825 2909205777991099320719119)
                      ·
                        rfl

theorem cell23_5665658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2].length) (baseStart_5665658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665658 prefixEnd_5665658 := by exact prefixLift 5665658
  have htrace : WordTrace (prefixWord ++ tailWord_5665658) baseStart_5665658 baseEnd_5665658 := by
    simpa [prefixWord, tailWord_5665658, baseEnd_5665658] using wordTrace_append hprefix tailTrace_5665658
  have hstable : (prefixWord ++ tailWord_5665658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665658).length < 2 ^ (prefixWord ++ tailWord_5665658).sum := by decide
  have hdescent : baseEnd_5665658 < baseStart_5665658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665669 : List Nat := [1, 3, 1, 1, 3, 5, 1, 3, 1, 1, 3]
def baseStart_5665669 : Nat := 118140960795 + 5665669 * 2 ^ 59
def prefixEnd_5665669 : Nat := 4983230072969 + 3 ^ 40 * 5665669 * 2
def baseEnd_5665669 : Nat := 2909211426278298777681569

theorem tailTrace_5665669 : CollatzResearch.WordTrace tailWord_5665669 prefixEnd_5665669 2909211426278298777681569 := by
  unfold tailWord_5665669
  simp only [CollatzResearch.WordTrace]
  refine ⟨206643924911256307074208061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137762616607504204716138707 206643924911256307074208061)
  ·
    refine ⟨77491471841721115152828023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206643924911256307074208061 77491471841721115152828023)
    ·
      refine ⟨116237207762581672729242035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77491471841721115152828023 116237207762581672729242035)
      ·
        refine ⟨174355811643872509093863053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116237207762581672729242035 174355811643872509093863053)
        ·
          refine ⟨65383429366452190910198645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174355811643872509093863053 65383429366452190910198645)
          ·
            refine ⟨6129696503104892897831123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65383429366452190910198645 6129696503104892897831123)
            ·
              refine ⟨9194544754657339346746685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6129696503104892897831123 9194544754657339346746685)
              ·
                refine ⟨3447954282996502255030007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9194544754657339346746685 3447954282996502255030007)
                ·
                  refine ⟨5171931424494753382545011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3447954282996502255030007 5171931424494753382545011)
                  ·
                    refine ⟨7757897136742130073817517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5171931424494753382545011 7757897136742130073817517)
                    ·
                      refine ⟨2909211426278298777681569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7757897136742130073817517 2909211426278298777681569)
                      ·
                        rfl

theorem cell23_5665669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 1, 1, 3].length) (baseStart_5665669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665669 prefixEnd_5665669 := by exact prefixLift 5665669
  have htrace : WordTrace (prefixWord ++ tailWord_5665669) baseStart_5665669 baseEnd_5665669 := by
    simpa [prefixWord, tailWord_5665669, baseEnd_5665669] using wordTrace_append hprefix tailTrace_5665669
  have hstable : (prefixWord ++ tailWord_5665669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665669).length < 2 ^ (prefixWord ++ tailWord_5665669).sum := by decide
  have hdescent : baseEnd_5665669 < baseStart_5665669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665675 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 5, 2, 2]
def baseStart_5665675 : Nat := 118140960795 + 5665675 * 2 ^ 59
def prefixEnd_5665675 : Nat := 4983230072969 + 3 ^ 40 * 5665675 * 2
def baseEnd_5665675 : Nat := 2909214507162225754206541

theorem tailTrace_5665675 : CollatzResearch.WordTrace tailWord_5665675 prefixEnd_5665675 2909214507162225754206541 := by
  unfold tailWord_5665675
  simp only [CollatzResearch.WordTrace]
  refine ⟨206644143749234570098926479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137762762499489713399284319 206644143749234570098926479)
  ·
    refine ⟨309966215623851855148389719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206644143749234570098926479 309966215623851855148389719)
    ·
      refine ⟨464949323435777782722584579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309966215623851855148389719 464949323435777782722584579)
      ·
        refine ⟨697423985153666674083876869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464949323435777782722584579 697423985153666674083876869)
        ·
          refine ⟨130766997216312501390726913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 697423985153666674083876869 130766997216312501390726913)
          ·
            refine ⟨98075247912234376043045185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130766997216312501390726913 98075247912234376043045185)
            ·
              refine ⟨73556435934175782032283889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98075247912234376043045185 73556435934175782032283889)
              ·
                refine ⟨55167326950631836524212917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73556435934175782032283889 55167326950631836524212917)
                ·
                  refine ⟨5171936901621734674144961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55167326950631836524212917 5171936901621734674144961)
                  ·
                    refine ⟨3878952676216301005608721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5171936901621734674144961 3878952676216301005608721)
                    ·
                      refine ⟨2909214507162225754206541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3878952676216301005608721 2909214507162225754206541)
                      ·
                        rfl

theorem cell23_5665675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 2, 2].length) (baseStart_5665675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665675 prefixEnd_5665675 := by exact prefixLift 5665675
  have htrace : WordTrace (prefixWord ++ tailWord_5665675) baseStart_5665675 baseEnd_5665675 := by
    simpa [prefixWord, tailWord_5665675, baseEnd_5665675] using wordTrace_append hprefix tailTrace_5665675
  have hstable : (prefixWord ++ tailWord_5665675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665675).length < 2 ^ (prefixWord ++ tailWord_5665675).sum := by decide
  have hdescent : baseEnd_5665675 < baseStart_5665675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665686 : List Nat := [5, 3, 1, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_5665686 : Nat := 118140960795 + 5665686 * 2 ^ 59
def prefixEnd_5665686 : Nat := 4983230072969 + 3 ^ 40 * 5665686 * 2
def baseEnd_5665686 : Nat := 2909220155449425211168991

theorem tailTrace_5665686 : CollatzResearch.WordTrace tailWord_5665686 prefixEnd_5665686 2909220155449425211168991 := by
  unfold tailWord_5665686
  simp only [CollatzResearch.WordTrace]
  refine ⟨12915284059512169936098557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137763029968129812651717941 12915284059512169936098557)
  ·
    refine ⟨4843231522317063726036959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12915284059512169936098557 4843231522317063726036959)
    ·
      refine ⟨7264847283475595589055439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4843231522317063726036959 7264847283475595589055439)
      ·
        refine ⟨10897270925213393383583159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7264847283475595589055439 10897270925213393383583159)
        ·
          refine ⟨16345906387820090075374739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10897270925213393383583159 16345906387820090075374739)
          ·
            refine ⟨24518859581730135113062109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16345906387820090075374739 24518859581730135113062109)
            ·
              refine ⟨9194572343148800667398291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24518859581730135113062109 9194572343148800667398291)
              ·
                refine ⟨13791858514723201001097437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9194572343148800667398291 13791858514723201001097437)
                ·
                  refine ⟨5171946943021200375411539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13791858514723201001097437 5171946943021200375411539)
                  ·
                    refine ⟨7757920414531800563117309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5171946943021200375411539 7757920414531800563117309)
                    ·
                      refine ⟨2909220155449425211168991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7757920414531800563117309 2909220155449425211168991)
                      ·
                        rfl

theorem cell23_5665686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_5665686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665686 prefixEnd_5665686 := by exact prefixLift 5665686
  have htrace : WordTrace (prefixWord ++ tailWord_5665686) baseStart_5665686 baseEnd_5665686 := by
    simpa [prefixWord, tailWord_5665686, baseEnd_5665686] using wordTrace_append hprefix tailTrace_5665686
  have hstable : (prefixWord ++ tailWord_5665686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665686).length < 2 ^ (prefixWord ++ tailWord_5665686).sum := by decide
  have hdescent : baseEnd_5665686 < baseStart_5665686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665698 : List Nat := [3, 3, 1, 2, 2, 1, 1, 10]
def baseStart_5665698 : Nat := 118140960795 + 5665698 * 2 ^ 59
def prefixEnd_5665698 : Nat := 4983230072969 + 3 ^ 40 * 5665698 * 2
def baseEnd_5665698 : Nat := 107749122859899228304405

theorem tailTrace_5665698 : CollatzResearch.WordTrace tailWord_5665698 prefixEnd_5665698 107749122859899228304405 := by
  unfold tailWord_5665698
  simp only [CollatzResearch.WordTrace]
  refine ⟨51661245657037811256753437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137763321752100830018009165 51661245657037811256753437)
  ·
    refine ⟨19372967121389179221282539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51661245657037811256753437 19372967121389179221282539)
    ·
      refine ⟨29059450682083768831923809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19372967121389179221282539 29059450682083768831923809)
      ·
        refine ⟨21794588011562826623942857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29059450682083768831923809 21794588011562826623942857)
        ·
          refine ⟨16345941008672119967957143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21794588011562826623942857 16345941008672119967957143)
          ·
            refine ⟨24518911513008179951935715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16345941008672119967957143 24518911513008179951935715)
            ·
              refine ⟨36778367269512269927903573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24518911513008179951935715 36778367269512269927903573)
              ·
                refine ⟨107749122859899228304405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36778367269512269927903573 107749122859899228304405)
                ·
                  rfl

theorem cell23_5665698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 10].length) (baseStart_5665698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665698 prefixEnd_5665698 := by exact prefixLift 5665698
  have htrace : WordTrace (prefixWord ++ tailWord_5665698) baseStart_5665698 baseEnd_5665698 := by
    simpa [prefixWord, tailWord_5665698, baseEnd_5665698] using wordTrace_append hprefix tailTrace_5665698
  have hstable : (prefixWord ++ tailWord_5665698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665698).length < 2 ^ (prefixWord ++ tailWord_5665698).sum := by decide
  have hdescent : baseEnd_5665698 < baseStart_5665698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665711 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 4, 7]
def baseStart_5665711 : Nat := 118140960795 + 5665711 * 2 ^ 59
def prefixEnd_5665711 : Nat := 4983230072969 + 3 ^ 40 * 5665711 * 2
def baseEnd_5665711 : Nat := 969744330821929204452125

theorem tailTrace_5665711 : CollatzResearch.WordTrace tailWord_5665711 prefixEnd_5665711 969744330821929204452125 := by
  unfold tailWord_5665711
  simp only [CollatzResearch.WordTrace]
  refine ⟨206645456777104148247236987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137763637851402765498157991 206645456777104148247236987)
  ·
    refine ⟨309968185165656222370855481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206645456777104148247236987 309968185165656222370855481)
    ·
      refine ⟨232476138874242166778141611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309968185165656222370855481 232476138874242166778141611)
      ·
        refine ⟨348714208311363250167212417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232476138874242166778141611 348714208311363250167212417)
        ·
          refine ⟨261535656233522437625409313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348714208311363250167212417 261535656233522437625409313)
          ·
            refine ⟨196151742175141828219056985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261535656233522437625409313 196151742175141828219056985)
            ·
              refine ⟨147113806631356371164292739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196151742175141828219056985 147113806631356371164292739)
              ·
                refine ⟨220670709947034556746439109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147113806631356371164292739 220670709947034556746439109)
                ·
                  refine ⟨41375758115068979389957333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 220670709947034556746439109 41375758115068979389957333)
                  ·
                    refine ⟨969744330821929204452125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41375758115068979389957333 969744330821929204452125)
                    ·
                      rfl

theorem cell23_5665711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 7].length) (baseStart_5665711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665711 prefixEnd_5665711 := by exact prefixLift 5665711
  have htrace : WordTrace (prefixWord ++ tailWord_5665711) baseStart_5665711 baseEnd_5665711 := by
    simpa [prefixWord, tailWord_5665711, baseEnd_5665711] using wordTrace_append hprefix tailTrace_5665711
  have hstable : (prefixWord ++ tailWord_5665711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665711).length < 2 ^ (prefixWord ++ tailWord_5665711).sum := by decide
  have hdescent : baseEnd_5665711 < baseStart_5665711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665731 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 8]
def baseStart_5665731 : Nat := 118140960795 + 5665731 * 2 ^ 59
def prefixEnd_5665731 : Nat := 4983230072969 + 3 ^ 40 * 5665731 * 2
def baseEnd_5665731 : Nat := 2909243262078877535106283

theorem tailTrace_5665731 : CollatzResearch.WordTrace tailWord_5665731 prefixEnd_5665731 2909243262078877535106283 := by
  unfold tailWord_5665731
  simp only [CollatzResearch.WordTrace]
  refine ⟨206646186237031691662965047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137764124158021127775310031 206646186237031691662965047)
  ·
    refine ⟨309969279355547537494447571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206646186237031691662965047 309969279355547537494447571)
    ·
      refine ⟨464953919033321306241671357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309969279355547537494447571 464953919033321306241671357)
      ·
        refine ⟨174357719637495489840626759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 464953919033321306241671357 174357719637495489840626759)
        ·
          refine ⟨261536579456243234760940139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174357719637495489840626759 261536579456243234760940139)
          ·
            refine ⟨392304869184364852141410209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261536579456243234760940139 392304869184364852141410209)
            ·
              refine ⟨294228651888273639106057657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 392304869184364852141410209 294228651888273639106057657)
              ·
                refine ⟨220671488916205229329543243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294228651888273639106057657 220671488916205229329543243)
                ·
                  refine ⟨331007233374307843994314865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220671488916205229329543243 331007233374307843994314865)
                  ·
                    refine ⟨248255425030730882995736149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 331007233374307843994314865 248255425030730882995736149)
                    ·
                      refine ⟨2909243262078877535106283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 248255425030730882995736149 2909243262078877535106283)
                      ·
                        rfl

theorem cell23_5665731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_5665731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665731 prefixEnd_5665731 := by exact prefixLift 5665731
  have htrace : WordTrace (prefixWord ++ tailWord_5665731) baseStart_5665731 baseEnd_5665731 := by
    simpa [prefixWord, tailWord_5665731, baseEnd_5665731] using wordTrace_append hprefix tailTrace_5665731
  have hstable : (prefixWord ++ tailWord_5665731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665731).length < 2 ^ (prefixWord ++ tailWord_5665731).sum := by decide
  have hdescent : baseEnd_5665731 < baseStart_5665731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665742 : List Nat := [4, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3]
def baseStart_5665742 : Nat := 118140960795 + 5665742 * 2 ^ 59
def prefixEnd_5665742 : Nat := 4983230072969 + 3 ^ 40 * 5665742 * 2
def baseEnd_5665742 : Nat := 2909248910366076992068733

theorem tailTrace_5665742 : CollatzResearch.WordTrace tailWord_5665742 prefixEnd_5665742 2909248910366076992068733 := by
  unfold tailWord_5665742
  simp only [CollatzResearch.WordTrace]
  refine ⟨25830823429998980067701935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137764391626661227027743653 25830823429998980067701935)
  ·
    refine ⟨38746235144998470101552903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25830823429998980067701935 38746235144998470101552903)
    ·
      refine ⟨58119352717497705152329355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38746235144998470101552903 58119352717497705152329355)
      ·
        refine ⟨87179029076246557728494033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58119352717497705152329355 87179029076246557728494033)
        ·
          refine ⟨65384271807184918296370525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87179029076246557728494033 65384271807184918296370525)
          ·
            refine ⟨24519101927694344361138947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65384271807184918296370525 24519101927694344361138947)
            ·
              refine ⟨36778652891541516541708421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24519101927694344361138947 36778652891541516541708421)
              ·
                refine ⟨6895997417164034351570329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36778652891541516541708421 6895997417164034351570329)
                ·
                  refine ⟨5171998062873025763677747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6895997417164034351570329 5171998062873025763677747)
                  ·
                    refine ⟨7757997094309538645516621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5171998062873025763677747 7757997094309538645516621)
                    ·
                      refine ⟨2909248910366076992068733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7757997094309538645516621 2909248910366076992068733)
                      ·
                        rfl

theorem cell23_5665742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_5665742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665742 prefixEnd_5665742 := by exact prefixLift 5665742
  have htrace : WordTrace (prefixWord ++ tailWord_5665742) baseStart_5665742 baseEnd_5665742 := by
    simpa [prefixWord, tailWord_5665742, baseEnd_5665742] using wordTrace_append hprefix tailTrace_5665742
  have hstable : (prefixWord ++ tailWord_5665742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665742).length < 2 ^ (prefixWord ++ tailWord_5665742).sum := by decide
  have hdescent : baseEnd_5665742 < baseStart_5665742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665768 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_5665768 : Nat := 118140960795 + 5665768 * 2 ^ 59
def prefixEnd_5665768 : Nat := 4983230072969 + 3 ^ 40 * 5665768 * 2
def baseEnd_5665768 : Nat := 2909262260863093890343613

theorem tailTrace_5665768 : CollatzResearch.WordTrace tailWord_5665768 prefixEnd_5665768 2909262260863093890343613 := by
  unfold tailWord_5665768
  simp only [CollatzResearch.WordTrace]
  refine ⟨103323767868948823491030979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137765023825265097988041305 103323767868948823491030979)
  ·
    refine ⟨154985651803423235236546469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103323767868948823491030979 154985651803423235236546469)
    ·
      refine ⟨29059809713141856606852463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154985651803423235236546469 29059809713141856606852463)
      ·
        refine ⟨43589714569712784910278695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29059809713141856606852463 43589714569712784910278695)
        ·
          refine ⟨65384571854569177365418043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43589714569712784910278695 65384571854569177365418043)
          ·
            refine ⟨98076857781853766048127065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65384571854569177365418043 98076857781853766048127065)
            ·
              refine ⟨73557643336390324536095299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98076857781853766048127065 73557643336390324536095299)
              ·
                refine ⟨110336465004585486804142949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73557643336390324536095299 110336465004585486804142949)
                ·
                  refine ⟨20688087188359778775776803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110336465004585486804142949 20688087188359778775776803)
                  ·
                    refine ⟨31032130782539668163665205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20688087188359778775776803 31032130782539668163665205)
                    ·
                      refine ⟨2909262260863093890343613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31032130782539668163665205 2909262260863093890343613)
                      ·
                        rfl

theorem cell23_5665768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_5665768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665768 prefixEnd_5665768 := by exact prefixLift 5665768
  have htrace : WordTrace (prefixWord ++ tailWord_5665768) baseStart_5665768 baseEnd_5665768 := by
    simpa [prefixWord, tailWord_5665768, baseEnd_5665768] using wordTrace_append hprefix tailTrace_5665768
  have hstable : (prefixWord ++ tailWord_5665768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665768).length < 2 ^ (prefixWord ++ tailWord_5665768).sum := by decide
  have hdescent : baseEnd_5665768 < baseStart_5665768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665810 : List Nat := [3, 2, 5, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_5665810 : Nat := 118140960795 + 5665810 * 2 ^ 59
def prefixEnd_5665810 : Nat := 4983230072969 + 3 ^ 40 * 5665810 * 2
def baseEnd_5665810 : Nat := 2909283827050582726018421

theorem tailTrace_5665810 : CollatzResearch.WordTrace tailWord_5665810 prefixEnd_5665810 2909283827050582726018421 := by
  unfold tailWord_5665810
  simp only [CollatzResearch.WordTrace]
  refine ⟨51662266900936372038772721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137766045069163658770060589 51662266900936372038772721)
  ·
    refine ⟨38746700175702279029079541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51662266900936372038772721 38746700175702279029079541)
    ·
      refine ⟨3632503141472088658976207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38746700175702279029079541 3632503141472088658976207)
      ·
        refine ⟨5448754712208132988464311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3632503141472088658976207 5448754712208132988464311)
        ·
          refine ⟨8173132068312199482696467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5448754712208132988464311 8173132068312199482696467)
          ·
            refine ⟨12259698102468299224044701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8173132068312199482696467 12259698102468299224044701)
            ·
              refine ⟨4597386788425612209016763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12259698102468299224044701 4597386788425612209016763)
              ·
                refine ⟨6896080182638418313525145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4597386788425612209016763 6896080182638418313525145)
                ·
                  refine ⟨5172060136978813735143859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6896080182638418313525145 5172060136978813735143859)
                  ·
                    refine ⟨7758090205468220602715789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5172060136978813735143859 7758090205468220602715789)
                    ·
                      refine ⟨2909283827050582726018421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7758090205468220602715789 2909283827050582726018421)
                      ·
                        rfl

theorem cell23_5665810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_5665810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665810 prefixEnd_5665810 := by exact prefixLift 5665810
  have htrace : WordTrace (prefixWord ++ tailWord_5665810) baseStart_5665810 baseEnd_5665810 := by
    simpa [prefixWord, tailWord_5665810, baseEnd_5665810] using wordTrace_append hprefix tailTrace_5665810
  have hstable : (prefixWord ++ tailWord_5665810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665810).length < 2 ^ (prefixWord ++ tailWord_5665810).sum := by decide
  have hdescent : baseEnd_5665810 < baseStart_5665810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665816 : List Nat := [2, 1, 2, 3, 2, 3, 3, 1, 2, 2, 2]
def baseStart_5665816 : Nat := 118140960795 + 5665816 * 2 ^ 59
def prefixEnd_5665816 : Nat := 4983230072969 + 3 ^ 40 * 5665816 * 2
def baseEnd_5665816 : Nat := 2909286907934509702543393

theorem tailTrace_5665816 : CollatzResearch.WordTrace tailWord_5665816 prefixEnd_5665816 2909286907934509702543393 := by
  unfold tailWord_5665816
  simp only [CollatzResearch.WordTrace]
  refine ⟨103324643220861875589904651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137766190961149167453206201 103324643220861875589904651)
  ·
    refine ⟨154986964831292813384856977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103324643220861875589904651 154986964831292813384856977)
    ·
      refine ⟨116240223623469610038642733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154986964831292813384856977 116240223623469610038642733)
      ·
        refine ⟨43590083858801103764491025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116240223623469610038642733 43590083858801103764491025)
        ·
          refine ⟨32692562894100827823368269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43590083858801103764491025 32692562894100827823368269)
          ·
            refine ⟨12259711085287810433763101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32692562894100827823368269 12259711085287810433763101)
            ·
              refine ⟨4597391656982928912661163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12259711085287810433763101 4597391656982928912661163)
              ·
                refine ⟨6896087485474393368991745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4597391656982928912661163 6896087485474393368991745)
                ·
                  refine ⟨5172065614105795026743809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6896087485474393368991745 5172065614105795026743809)
                  ·
                    refine ⟨3879049210579346270057857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5172065614105795026743809 3879049210579346270057857)
                    ·
                      refine ⟨2909286907934509702543393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3879049210579346270057857 2909286907934509702543393)
                      ·
                        rfl

theorem cell23_5665816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_5665816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665816 prefixEnd_5665816 := by exact prefixLift 5665816
  have htrace : WordTrace (prefixWord ++ tailWord_5665816) baseStart_5665816 baseEnd_5665816 := by
    simpa [prefixWord, tailWord_5665816, baseEnd_5665816] using wordTrace_append hprefix tailTrace_5665816
  have hstable : (prefixWord ++ tailWord_5665816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665816).length < 2 ^ (prefixWord ++ tailWord_5665816).sum := by decide
  have hdescent : baseEnd_5665816 < baseStart_5665816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665818 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 3, 7]
def baseStart_5665818 : Nat := 118140960795 + 5665818 * 2 ^ 59
def prefixEnd_5665818 : Nat := 4983230072969 + 3 ^ 40 * 5665818 * 2
def baseEnd_5665818 : Nat := 969762644965272898239461

theorem tailTrace_5665818 : CollatzResearch.WordTrace tailWord_5665818 prefixEnd_5665818 969762644965272898239461 := by
  unfold tailWord_5665818
  simp only [CollatzResearch.WordTrace]
  refine ⟨51662339846929126380345527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137766239591811003680921405 51662339846929126380345527)
  ·
    refine ⟨77493509770393689570518291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51662339846929126380345527 77493509770393689570518291)
    ·
      refine ⟨116240264655590534355777437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77493509770393689570518291 116240264655590534355777437)
      ·
        refine ⟨43590099245846450383416539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116240264655590534355777437 43590099245846450383416539)
        ·
          refine ⟨65385148868769675575124809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43590099245846450383416539 65385148868769675575124809)
          ·
            refine ⟨49038861651577256681343607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65385148868769675575124809 49038861651577256681343607)
            ·
              refine ⟨73558292477365885022015411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49038861651577256681343607 73558292477365885022015411)
              ·
                refine ⟨110337438716048827533023117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73558292477365885022015411 110337438716048827533023117)
                ·
                  refine ⟨41376539518518310324883669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110337438716048827533023117 41376539518518310324883669)
                  ·
                    refine ⟨969762644965272898239461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41376539518518310324883669 969762644965272898239461)
                    ·
                      rfl

theorem cell23_5665818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_5665818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665818 prefixEnd_5665818 := by exact prefixLift 5665818
  have htrace : WordTrace (prefixWord ++ tailWord_5665818) baseStart_5665818 baseEnd_5665818 := by
    simpa [prefixWord, tailWord_5665818, baseEnd_5665818] using wordTrace_append hprefix tailTrace_5665818
  have hstable : (prefixWord ++ tailWord_5665818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665818).length < 2 ^ (prefixWord ++ tailWord_5665818).sum := by decide
  have hdescent : baseEnd_5665818 < baseStart_5665818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665862 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_5665862 : Nat := 118140960795 + 5665862 * 2 ^ 59
def prefixEnd_5665862 : Nat := 4983230072969 + 3 ^ 40 * 5665862 * 2
def baseEnd_5665862 : Nat := 2909310528044616522568181

theorem tailTrace_5665862 : CollatzResearch.WordTrace tailWord_5665862 prefixEnd_5665862 2909310528044616522568181 := by
  unfold tailWord_5665862
  simp only [CollatzResearch.WordTrace]
  refine ⟨6457842631236159407374495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 137767309466371400690655893 6457842631236159407374495)
  ·
    refine ⟨9686763946854239111061743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6457842631236159407374495 9686763946854239111061743)
    ·
      refine ⟨14530145920281358666592615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9686763946854239111061743 14530145920281358666592615)
      ·
        refine ⟨21795218880422037999888923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14530145920281358666592615 21795218880422037999888923)
        ·
          refine ⟨32692828320633056999833385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21795218880422037999888923 32692828320633056999833385)
          ·
            refine ⟨24519621240474792749875039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32692828320633056999833385 24519621240474792749875039)
            ·
              refine ⟨36779431860712189124812559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24519621240474792749875039 36779431860712189124812559)
              ·
                refine ⟨55169147791068283687218839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36779431860712189124812559 55169147791068283687218839)
                ·
                  refine ⟨82753721686602425530828259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55169147791068283687218839 82753721686602425530828259)
                  ·
                    refine ⟨124130582529903638296242389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82753721686602425530828259 124130582529903638296242389)
                    ·
                      refine ⟨2909310528044616522568181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124130582529903638296242389 2909310528044616522568181)
                      ·
                        rfl

theorem cell23_5665862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_5665862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665862 prefixEnd_5665862 := by exact prefixLift 5665862
  have htrace : WordTrace (prefixWord ++ tailWord_5665862) baseStart_5665862 baseEnd_5665862 := by
    simpa [prefixWord, tailWord_5665862, baseEnd_5665862] using wordTrace_append hprefix tailTrace_5665862
  have hstable : (prefixWord ++ tailWord_5665862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665862).length < 2 ^ (prefixWord ++ tailWord_5665862).sum := by decide
  have hdescent : baseEnd_5665862 < baseStart_5665862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665865 : List Nat := [1, 2, 1, 1, 2, 2, 2, 5, 3, 4]
def baseStart_5665865 : Nat := 118140960795 + 5665865 * 2 ^ 59
def prefixEnd_5665865 : Nat := 4983230072969 + 3 ^ 40 * 5665865 * 2
def baseEnd_5665865 : Nat := 969770689495526670276889

theorem tailTrace_5665865 : CollatzResearch.WordTrace tailWord_5665865 prefixEnd_5665865 969770689495526670276889 := by
  unfold tailWord_5665865
  simp only [CollatzResearch.WordTrace]
  refine ⟨206651073618546232548343049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137767382412364155032228699 206651073618546232548343049)
  ·
    refine ⟨154988305213909674411257287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206651073618546232548343049 154988305213909674411257287)
    ·
      refine ⟨232482457820864511616885931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154988305213909674411257287 232482457820864511616885931)
      ·
        refine ⟨348723686731296767425328897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232482457820864511616885931 348723686731296767425328897)
        ·
          refine ⟨261542765048472575568996673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348723686731296767425328897 261542765048472575568996673)
          ·
            refine ⟨196157073786354431676747505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261542765048472575568996673 196157073786354431676747505)
            ·
              refine ⟨147117805339765823757560629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196157073786354431676747505 147117805339765823757560629)
              ·
                refine ⟨13792294250603045977271309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 147117805339765823757560629 13792294250603045977271309)
                ·
                  refine ⟨5172110343976142241476741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13792294250603045977271309 5172110343976142241476741)
                  ·
                    refine ⟨969770689495526670276889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5172110343976142241476741 969770689495526670276889)
                    ·
                      rfl

theorem cell23_5665865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 4].length) (baseStart_5665865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665865 prefixEnd_5665865 := by exact prefixLift 5665865
  have htrace : WordTrace (prefixWord ++ tailWord_5665865) baseStart_5665865 baseEnd_5665865 := by
    simpa [prefixWord, tailWord_5665865, baseEnd_5665865] using wordTrace_append hprefix tailTrace_5665865
  have hstable : (prefixWord ++ tailWord_5665865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665865).length < 2 ^ (prefixWord ++ tailWord_5665865).sum := by decide
  have hdescent : baseEnd_5665865 < baseStart_5665865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665886 : List Nat := [4, 4, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_5665886 : Nat := 118140960795 + 5665886 * 2 ^ 59
def prefixEnd_5665886 : Nat := 4983230072969 + 3 ^ 40 * 5665886 * 2
def baseEnd_5665886 : Nat := 969774283860108142889357

theorem tailTrace_5665886 : CollatzResearch.WordTrace tailWord_5665886 prefixEnd_5665886 969774283860108142889357 := by
  unfold tailWord_5665886
  simp only [CollatzResearch.WordTrace]
  refine ⟨25831479943933769141857189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137767893034313435423238341 25831479943933769141857189)
  ·
    refine ⟨4843402489487581714098223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25831479943933769141857189 4843402489487581714098223)
    ·
      refine ⟨7265103734231372571147335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4843402489487581714098223 7265103734231372571147335)
      ·
        refine ⟨10897655601347058856721003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7265103734231372571147335 10897655601347058856721003)
        ·
          refine ⟨16346483402020588285081505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10897655601347058856721003 16346483402020588285081505)
          ·
            refine ⟨12259862551515441213811129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16346483402020588285081505 12259862551515441213811129)
            ·
              refine ⟨9194896913636580910358347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12259862551515441213811129 9194896913636580910358347)
              ·
                refine ⟨13792345370454871365537521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9194896913636580910358347 13792345370454871365537521)
                ·
                  refine ⟨10344259027841153524153141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13792345370454871365537521 10344259027841153524153141)
                  ·
                    refine ⟨969774283860108142889357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10344259027841153524153141 969774283860108142889357)
                    ·
                      rfl

theorem cell23_5665886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_5665886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665886 prefixEnd_5665886 := by exact prefixLift 5665886
  have htrace : WordTrace (prefixWord ++ tailWord_5665886) baseStart_5665886 baseEnd_5665886 := by
    simpa [prefixWord, tailWord_5665886, baseEnd_5665886] using wordTrace_append hprefix tailTrace_5665886
  have hstable : (prefixWord ++ tailWord_5665886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665886).length < 2 ^ (prefixWord ++ tailWord_5665886).sum := by decide
  have hdescent : baseEnd_5665886 < baseStart_5665886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665932 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 4, 3, 2]
def baseStart_5665932 : Nat := 118140960795 + 5665932 * 2 ^ 59
def prefixEnd_5665932 : Nat := 4983230072969 + 3 ^ 40 * 5665932 * 2
def baseEnd_5665932 : Nat := 2909346471690431248692859

theorem tailTrace_5665932 : CollatzResearch.WordTrace tailWord_5665932 prefixEnd_5665932 2909346471690431248692859 := by
  unfold tailWord_5665932
  simp only [CollatzResearch.WordTrace]
  refine ⟨103326758654651751495516025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137769011539535668660688033 103326758654651751495516025)
  ·
    refine ⟨77495068990988813621637019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103326758654651751495516025 77495068990988813621637019)
    ·
      refine ⟨116242603486483220432455529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77495068990988813621637019 116242603486483220432455529)
      ·
        refine ⟨87181952614862415324341647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116242603486483220432455529 87181952614862415324341647)
        ·
          refine ⟨130772928922293622986512471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87181952614862415324341647 130772928922293622986512471)
          ·
            refine ⟨196159393383440434479768707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130772928922293622986512471 196159393383440434479768707)
            ·
              refine ⟨294239090075160651719653061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196159393383440434479768707 294239090075160651719653061)
              ·
                refine ⟨55169829389092622197434949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 294239090075160651719653061 55169829389092622197434949)
                ·
                  refine ⟨10344343010454866662019053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55169829389092622197434949 10344343010454866662019053)
                  ·
                    refine ⟨3879128628920574998257145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10344343010454866662019053 3879128628920574998257145)
                    ·
                      refine ⟨2909346471690431248692859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3879128628920574998257145 2909346471690431248692859)
                      ·
                        rfl

theorem cell23_5665932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 4, 3, 2].length) (baseStart_5665932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665932 prefixEnd_5665932 := by exact prefixLift 5665932
  have htrace : WordTrace (prefixWord ++ tailWord_5665932) baseStart_5665932 baseEnd_5665932 := by
    simpa [prefixWord, tailWord_5665932, baseEnd_5665932] using wordTrace_append hprefix tailTrace_5665932
  have hstable : (prefixWord ++ tailWord_5665932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665932).length < 2 ^ (prefixWord ++ tailWord_5665932).sum := by decide
  have hdescent : baseEnd_5665932 < baseStart_5665932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665956 : List Nat := [2, 3, 1, 2, 3, 1, 1, 5, 1, 1, 3]
def baseStart_5665956 : Nat := 118140960795 + 5665956 * 2 ^ 59
def prefixEnd_5665956 : Nat := 4983230072969 + 3 ^ 40 * 5665956 * 2
def baseEnd_5665956 : Nat := 2909358795226139154792749

theorem tailTrace_5665956 : CollatzResearch.WordTrace tailWord_5665956 prefixEnd_5665956 2909358795226139154792749 := by
  unfold tailWord_5665956
  simp only [CollatzResearch.WordTrace]
  refine ⟨103327196330608277544952861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137769595107477703393270481 103327196330608277544952861)
  ·
    refine ⟨38747698623978104079357323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103327196330608277544952861 38747698623978104079357323)
    ·
      refine ⟨58121547935967156119035985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38747698623978104079357323 58121547935967156119035985)
      ·
        refine ⟨43591160951975367089276989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58121547935967156119035985 43591160951975367089276989)
        ·
          refine ⟨16346685356990762658478871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43591160951975367089276989 16346685356990762658478871)
          ·
            refine ⟨24520028035486143987718307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16346685356990762658478871 24520028035486143987718307)
            ·
              refine ⟨36780042053229215981577461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24520028035486143987718307 36780042053229215981577461)
              ·
                refine ⟨3448128942490238998272887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36780042053229215981577461 3448128942490238998272887)
                ·
                  refine ⟨5172193413735358497409331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3448128942490238998272887 5172193413735358497409331)
                  ·
                    refine ⟨7758290120603037746113997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5172193413735358497409331 7758290120603037746113997)
                    ·
                      refine ⟨2909358795226139154792749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7758290120603037746113997 2909358795226139154792749)
                      ·
                        rfl

theorem cell23_5665956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_5665956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665956 prefixEnd_5665956 := by exact prefixLift 5665956
  have htrace : WordTrace (prefixWord ++ tailWord_5665956) baseStart_5665956 baseEnd_5665956 := by
    simpa [prefixWord, tailWord_5665956, baseEnd_5665956] using wordTrace_append hprefix tailTrace_5665956
  have hstable : (prefixWord ++ tailWord_5665956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665956).length < 2 ^ (prefixWord ++ tailWord_5665956).sum := by decide
  have hdescent : baseEnd_5665956 < baseStart_5665956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665959 : List Nat := [1, 1, 6, 2, 1, 2, 1, 3, 1, 5]
def baseStart_5665959 : Nat := 118140960795 + 5665959 * 2 ^ 59
def prefixEnd_5665959 : Nat := 4983230072969 + 3 ^ 40 * 5665959 * 2
def baseEnd_5665959 : Nat := 969786778556034214351745

theorem tailTrace_5665959 : CollatzResearch.WordTrace tailWord_5665959 prefixEnd_5665959 969786778556034214351745 := by
  unfold tailWord_5665959
  simp only [CollatzResearch.WordTrace]
  refine ⟨206654502080205686602264931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137769668053470457734843287 206654502080205686602264931)
  ·
    refine ⟨309981753120308529903397397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206654502080205686602264931 309981753120308529903397397)
    ·
      refine ⟨14530394677514462339221753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 309981753120308529903397397 14530394677514462339221753)
      ·
        refine ⟨10897796008135846754416315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14530394677514462339221753 10897796008135846754416315)
        ·
          refine ⟨16346694012203770131624473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10897796008135846754416315 16346694012203770131624473)
          ·
            refine ⟨12260020509152827598718355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16346694012203770131624473 12260020509152827598718355)
            ·
              refine ⟨18390030763729241398077533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12260020509152827598718355 18390030763729241398077533)
              ·
                refine ⟨6896261536398465524279075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18390030763729241398077533 6896261536398465524279075)
                ·
                  refine ⟨10344392304597698286418613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6896261536398465524279075 10344392304597698286418613)
                  ·
                    refine ⟨969786778556034214351745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10344392304597698286418613 969786778556034214351745)
                    ·
                      rfl

theorem cell23_5665959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_5665959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665959 prefixEnd_5665959 := by exact prefixLift 5665959
  have htrace : WordTrace (prefixWord ++ tailWord_5665959) baseStart_5665959 baseEnd_5665959 := by
    simpa [prefixWord, tailWord_5665959, baseEnd_5665959] using wordTrace_append hprefix tailTrace_5665959
  have hstable : (prefixWord ++ tailWord_5665959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665959).length < 2 ^ (prefixWord ++ tailWord_5665959).sum := by decide
  have hdescent : baseEnd_5665959 < baseStart_5665959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665975 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 6]
def baseStart_5665975 : Nat := 118140960795 + 5665975 * 2 ^ 59
def prefixEnd_5665975 : Nat := 4983230072969 + 3 ^ 40 * 5665975 * 2
def baseEnd_5665975 : Nat := 2909368551358574580455161

theorem tailTrace_5665975 : CollatzResearch.WordTrace tailWord_5665975 prefixEnd_5665975 2909368551358574580455161 := by
  unfold tailWord_5665975
  simp only [CollatzResearch.WordTrace]
  refine ⟨206655085648147721334847379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137770057098765147556564919 206655085648147721334847379)
  ·
    refine ⟨309982628472221582002271069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206655085648147721334847379 309982628472221582002271069)
    ·
      refine ⟨116243485677083093250851651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 309982628472221582002271069 116243485677083093250851651)
      ·
        refine ⟨174365228515624639876277477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116243485677083093250851651 174365228515624639876277477)
        ·
          refine ⟨32693480346679619976802027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174365228515624639876277477 32693480346679619976802027)
          ·
            refine ⟨49040220520019429965203041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32693480346679619976802027 49040220520019429965203041)
            ·
              refine ⟨36780165390014572473902281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49040220520019429965203041 36780165390014572473902281)
              ·
                refine ⟨27585124042510929355426711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36780165390014572473902281 27585124042510929355426711)
                ·
                  refine ⟨41377686063766394033140067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27585124042510929355426711 41377686063766394033140067)
                  ·
                    refine ⟨62066529095649591049710101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41377686063766394033140067 62066529095649591049710101)
                    ·
                      refine ⟨2909368551358574580455161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62066529095649591049710101 2909368551358574580455161)
                      ·
                        rfl

theorem cell23_5665975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_5665975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665975 prefixEnd_5665975 := by exact prefixLift 5665975
  have htrace : WordTrace (prefixWord ++ tailWord_5665975) baseStart_5665975 baseEnd_5665975 := by
    simpa [prefixWord, tailWord_5665975, baseEnd_5665975] using wordTrace_append hprefix tailTrace_5665975
  have hstable : (prefixWord ++ tailWord_5665975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665975).length < 2 ^ (prefixWord ++ tailWord_5665975).sum := by decide
  have hdescent : baseEnd_5665975 < baseStart_5665975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665982 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_5665982 : Nat := 118140960795 + 5665982 * 2 ^ 59
def prefixEnd_5665982 : Nat := 4983230072969 + 3 ^ 40 * 5665982 * 2
def baseEnd_5665982 : Nat := 2909372145723156053067629

theorem tailTrace_5665982 : CollatzResearch.WordTrace tailWord_5665982 prefixEnd_5665982 2909372145723156053067629 := by
  unfold tailWord_5665982
  simp only [CollatzResearch.WordTrace]
  refine ⟨25831917619890295191294025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137770227306081574353568133 25831917619890295191294025)
  ·
    refine ⟨19373938214917721393470519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25831917619890295191294025 19373938214917721393470519)
    ·
      refine ⟨29060907322376582090205779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19373938214917721393470519 29060907322376582090205779)
      ·
        refine ⟨43591360983564873135308669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29060907322376582090205779 43591360983564873135308669)
        ·
          refine ⟨16346760368836827425740751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43591360983564873135308669 16346760368836827425740751)
          ·
            refine ⟨24520140553255241138611127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16346760368836827425740751 24520140553255241138611127)
            ·
              refine ⟨36780210829882861707916691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24520140553255241138611127 36780210829882861707916691)
              ·
                refine ⟨55170316244824292561875037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36780210829882861707916691 55170316244824292561875037)
                ·
                  refine ⟨20688868591809109710703139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55170316244824292561875037 20688868591809109710703139)
                  ·
                    refine ⟨31033302887713664566054709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20688868591809109710703139 31033302887713664566054709)
                    ·
                      refine ⟨2909372145723156053067629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31033302887713664566054709 2909372145723156053067629)
                      ·
                        rfl

theorem cell23_5665982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_5665982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665982 prefixEnd_5665982 := by exact prefixLift 5665982
  have htrace : WordTrace (prefixWord ++ tailWord_5665982) baseStart_5665982 baseEnd_5665982 := by
    simpa [prefixWord, tailWord_5665982, baseEnd_5665982] using wordTrace_append hprefix tailTrace_5665982
  have hstable : (prefixWord ++ tailWord_5665982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665982).length < 2 ^ (prefixWord ++ tailWord_5665982).sum := by decide
  have hdescent : baseEnd_5665982 < baseStart_5665982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665992 : List Nat := [2, 1, 3, 1, 2, 1, 5, 1, 1, 2, 4]
def baseStart_5665992 : Nat := 118140960795 + 5665992 * 2 ^ 59
def prefixEnd_5665992 : Nat := 4983230072969 + 3 ^ 40 * 5665992 * 2
def baseEnd_5665992 : Nat := 2909377280529701013942583

theorem tailTrace_5665992 : CollatzResearch.WordTrace tailWord_5665992 prefixEnd_5665992 2909377280529701013942583 := by
  unfold tailWord_5665992
  simp only [CollatzResearch.WordTrace]
  refine ⟨103327852844543066619108115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137770470459390755492144153 103327852844543066619108115)
  ·
    refine ⟨154991779266814599928662173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103327852844543066619108115 154991779266814599928662173)
    ·
      refine ⟨58121917225055474973248315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154991779266814599928662173 58121917225055474973248315)
      ·
        refine ⟨87182875837583212459872473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58121917225055474973248315 87182875837583212459872473)
        ·
          refine ⟨65387156878187409344904355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87182875837583212459872473 65387156878187409344904355)
          ·
            refine ⟨98080735317281114017356533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65387156878187409344904355 98080735317281114017356533)
            ·
              refine ⟨9195068935995104439127175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98080735317281114017356533 9195068935995104439127175)
              ·
                refine ⟨13792603403992656658690763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9195068935995104439127175 13792603403992656658690763)
                ·
                  refine ⟨20688905105988984988036145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13792603403992656658690763 20688905105988984988036145)
                  ·
                    refine ⟨15516678829491738741027109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20688905105988984988036145 15516678829491738741027109)
                    ·
                      refine ⟨2909377280529701013942583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15516678829491738741027109 2909377280529701013942583)
                      ·
                        rfl

theorem cell23_5665992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_5665992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665992 prefixEnd_5665992 := by exact prefixLift 5665992
  have htrace : WordTrace (prefixWord ++ tailWord_5665992) baseStart_5665992 baseEnd_5665992 := by
    simpa [prefixWord, tailWord_5665992, baseEnd_5665992] using wordTrace_append hprefix tailTrace_5665992
  have hstable : (prefixWord ++ tailWord_5665992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665992).length < 2 ^ (prefixWord ++ tailWord_5665992).sum := by decide
  have hdescent : baseEnd_5665992 < baseStart_5665992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666050 : List Nat := [3, 4, 1, 1, 4, 1, 1, 2, 1, 2, 3]
def baseStart_5666050 : Nat := 118140960795 + 5666050 * 2 ^ 59
def prefixEnd_5666050 : Nat := 4983230072969 + 3 ^ 40 * 5666050 * 2
def baseEnd_5666050 : Nat := 2909407062407661787017317

theorem tailTrace_5666050 : CollatzResearch.WordTrace tailWord_5666050 prefixEnd_5666050 2909407062407661787017317 := by
  unfold tailWord_5666050
  simp only [CollatzResearch.WordTrace]
  refine ⟨51664455280719002285956901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137771880748584006095885069 51664455280719002285956901)
  ·
    refine ⟨9687085365134812928616919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51664455280719002285956901 9687085365134812928616919)
    ·
      refine ⟨14530628047702219392925379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9687085365134812928616919 14530628047702219392925379)
      ·
        refine ⟨21795942071553329089388069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14530628047702219392925379 21795942071553329089388069)
        ·
          refine ⟨4086739138416249204260263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21795942071553329089388069 4086739138416249204260263)
          ·
            refine ⟨6130108707624373806390395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4086739138416249204260263 6130108707624373806390395)
            ·
              refine ⟨9195163061436560709585593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6130108707624373806390395 9195163061436560709585593)
              ·
                refine ⟨6896372296077420532189195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9195163061436560709585593 6896372296077420532189195)
                ·
                  refine ⟨10344558444116130798283793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6896372296077420532189195 10344558444116130798283793)
                  ·
                    refine ⟨7758418833087098098712845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10344558444116130798283793 7758418833087098098712845)
                    ·
                      refine ⟨2909407062407661787017317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7758418833087098098712845 2909407062407661787017317)
                      ·
                        rfl

theorem cell23_5666050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_5666050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666050 prefixEnd_5666050 := by exact prefixLift 5666050
  have htrace : WordTrace (prefixWord ++ tailWord_5666050) baseStart_5666050 baseEnd_5666050 := by
    simpa [prefixWord, tailWord_5666050, baseEnd_5666050] using wordTrace_append hprefix tailTrace_5666050
  have hstable : (prefixWord ++ tailWord_5666050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666050).length < 2 ^ (prefixWord ++ tailWord_5666050).sum := by decide
  have hdescent : baseEnd_5666050 < baseStart_5666050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666056 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 3, 3, 2]
def baseStart_5666056 : Nat := 118140960795 + 5666056 * 2 ^ 59
def prefixEnd_5666056 : Nat := 4983230072969 + 3 ^ 40 * 5666056 * 2
def baseEnd_5666056 : Nat := 2909410143291588763542289

theorem tailTrace_5666056 : CollatzResearch.WordTrace tailWord_5666056 prefixEnd_5666056 2909410143291588763542289 := by
  unfold tailWord_5666056
  simp only [CollatzResearch.WordTrace]
  refine ⟨103329019980427136084273011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137772026640569514779030681 103329019980427136084273011)
  ·
    refine ⟨154993529970640704126409517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103329019980427136084273011 154993529970640704126409517)
    ·
      refine ⟨58122573738990264047403569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154993529970640704126409517 58122573738990264047403569)
      ·
        refine ⟨43591930304242698035552677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58122573738990264047403569 43591930304242698035552677)
        ·
          refine ⟨8173486932045505881666127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43591930304242698035552677 8173486932045505881666127)
          ·
            refine ⟨12260230398068258822499191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8173486932045505881666127 12260230398068258822499191)
            ·
              refine ⟨18390345597102388233748787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12260230398068258822499191 18390345597102388233748787)
              ·
                refine ⟨27585518395653582350623181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18390345597102388233748787 27585518395653582350623181)
                ·
                  refine ⟨10344569398370093381483693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27585518395653582350623181 10344569398370093381483693)
                  ·
                    refine ⟨3879213524388785018056385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10344569398370093381483693 3879213524388785018056385)
                    ·
                      refine ⟨2909410143291588763542289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3879213524388785018056385 2909410143291588763542289)
                      ·
                        rfl

theorem cell23_5666056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_5666056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666056 prefixEnd_5666056 := by exact prefixLift 5666056
  have htrace : WordTrace (prefixWord ++ tailWord_5666056) baseStart_5666056 baseEnd_5666056 := by
    simpa [prefixWord, tailWord_5666056, baseEnd_5666056] using wordTrace_append hprefix tailTrace_5666056
  have hstable : (prefixWord ++ tailWord_5666056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666056).length < 2 ^ (prefixWord ++ tailWord_5666056).sum := by decide
  have hdescent : baseEnd_5666056 < baseStart_5666056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666072 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 2, 1, 5]
def baseStart_5666072 : Nat := 118140960795 + 5666072 * 2 ^ 59
def prefixEnd_5666072 : Nat := 4983230072969 + 3 ^ 40 * 5666072 * 2
def baseEnd_5666072 : Nat := 2909418358982060700942215

theorem tailTrace_5666072 : CollatzResearch.WordTrace tailWord_5666072 prefixEnd_5666072 2909418358982060700942215 := by
  unfold tailWord_5666072
  simp only [CollatzResearch.WordTrace]
  refine ⟨103329311764398153450564235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137772415685864204600752313 103329311764398153450564235)
  ·
    refine ⟨154993967646597230175846353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103329311764398153450564235 154993967646597230175846353)
    ·
      refine ⟨116245475734947922631884765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154993967646597230175846353 116245475734947922631884765)
      ·
        refine ⟨43592053400605470986956787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116245475734947922631884765 43592053400605470986956787)
        ·
          refine ⟨65388080100908206480435181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43592053400605470986956787 65388080100908206480435181)
          ·
            refine ⟨24520530037840577430163193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65388080100908206480435181 24520530037840577430163193)
            ·
              refine ⟨18390397528380433072622395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24520530037840577430163193 18390397528380433072622395)
              ·
                refine ⟨27585596292570649608933593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18390397528380433072622395 27585596292570649608933593)
                ·
                  refine ⟨20689197219427987206700195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27585596292570649608933593 20689197219427987206700195)
                  ·
                    refine ⟨31033795829141980810050293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20689197219427987206700195 31033795829141980810050293)
                    ·
                      refine ⟨2909418358982060700942215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31033795829141980810050293 2909418358982060700942215)
                      ·
                        rfl

theorem cell23_5666072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_5666072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666072 prefixEnd_5666072 := by exact prefixLift 5666072
  have htrace : WordTrace (prefixWord ++ tailWord_5666072) baseStart_5666072 baseEnd_5666072 := by
    simpa [prefixWord, tailWord_5666072, baseEnd_5666072] using wordTrace_append hprefix tailTrace_5666072
  have hstable : (prefixWord ++ tailWord_5666072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666072).length < 2 ^ (prefixWord ++ tailWord_5666072).sum := by decide
  have hdescent : baseEnd_5666072 < baseStart_5666072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666095 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 8]
def baseStart_5666095 : Nat := 118140960795 + 5666095 * 2 ^ 59
def prefixEnd_5666095 : Nat := 4983230072969 + 3 ^ 40 * 5666095 * 2
def baseEnd_5666095 : Nat := 2909430169037114110954609

theorem tailTrace_5666095 : CollatzResearch.WordTrace tailWord_5666095 prefixEnd_5666095 2909430169037114110954609 := by
  unfold tailWord_5666095
  simp only [CollatzResearch.WordTrace]
  refine ⟨206659462407712981829215739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137772974938475321219477159 206659462407712981829215739)
  ·
    refine ⟨309989193611569472743823609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206659462407712981829215739 309989193611569472743823609)
    ·
      refine ⟨232491895208677104557867707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309989193611569472743823609 232491895208677104557867707)
      ·
        refine ⟨348737842813015656836801561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232491895208677104557867707 348737842813015656836801561)
        ·
          refine ⟨261553382109761742627601171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348737842813015656836801561 261553382109761742627601171)
          ·
            refine ⟨392330073164642613941401757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261553382109761742627601171 392330073164642613941401757)
            ·
              refine ⟨147123777436740980228025659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 392330073164642613941401757 147123777436740980228025659)
              ·
                refine ⟨220685666155111470342038489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147123777436740980228025659 220685666155111470342038489)
                ·
                  refine ⟨165514249616333602756528867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220685666155111470342038489 165514249616333602756528867)
                  ·
                    refine ⟨248271374424500404134793301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 165514249616333602756528867 248271374424500404134793301)
                    ·
                      refine ⟨2909430169037114110954609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 248271374424500404134793301 2909430169037114110954609)
                      ·
                        rfl

theorem cell23_5666095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_5666095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666095 prefixEnd_5666095 := by exact prefixLift 5666095
  have htrace : WordTrace (prefixWord ++ tailWord_5666095) baseStart_5666095 baseEnd_5666095 := by
    simpa [prefixWord, tailWord_5666095, baseEnd_5666095] using wordTrace_append hprefix tailTrace_5666095
  have hstable : (prefixWord ++ tailWord_5666095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666095).length < 2 ^ (prefixWord ++ tailWord_5666095).sum := by decide
  have hdescent : baseEnd_5666095 < baseStart_5666095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
